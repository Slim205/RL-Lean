import dataclasses
from dataclasses import dataclass
from typing import Callable, Dict, Optional, Tuple, Type, Union

import equinox as eqx
import jax.numpy as jnp
import jax.random as jrandom

import haliax as hax
import haliax.nn as hnn
from haliax import Axis, NamedArray
from haliax.jax_utils import maybe_rng_split, named_call, shaped_rng_split
from haliax.nn.scan import Stacked
from levanter.compat.torch_serialization import (
    StateDict,
    StateDictSerializationMixin,
    apply_prefix,
    flatten_linear_layers,
    stack_state_dict,
    unflatten_linear_layers,
    unstack_state_dict,
)
from levanter.compat.hf_checkpoints import HFCheckpointConverter
from levanter.models.attention import AttentionBackend, AttentionMask, dot_product_attention
from levanter.models.llama import LlamaConfig, LlamaEmbedding, _apply_rotary_pos_emb, llama_rotary_pos_emb, LlamaMlp, LlamaTransformer, LlamaRMSNorm
from levanter.models.lm_model import LmConfig, LmHeadModel
from levanter.utils.flop_utils import lm_flops_per_token
from levanter.logging import silence_transformer_nag
from levanter.types import BlockFoldable


silence_transformer_nag()
from transformers import PretrainedConfig as HfConfig  # noqa: E402
from transformers import Qwen2Config as HfQwenConfig  # noqa: E402


@LmConfig.register_subclass("qwen")
@dataclass(frozen=True)
class QwenConfig(LlamaConfig):
    """Extends LlamaConfig with Qwen specific features"""

    use_sliding_window: bool = False
    sliding_window: Optional[int] = None
    max_window_layers: int = 0  # Only apply sliding window beyond this layer

    def __post_init__(self):
        assert (
            self.num_heads % self.num_kv_heads == 0
        ), f"num_heads={self.num_heads} not divisible by num_kv_heads={self.num_kv_heads}."

    def hf_checkpoint_converter(
        self, ref_checkpoint: Optional[str] = None
    ) -> HFCheckpointConverter["QwenConfig"]:  # type: ignore
        return HFCheckpointConverter(
            self.__class__,
            reference_checkpoint=self.reference_checkpoint if ref_checkpoint is None else ref_checkpoint,
            trust_remote_code=True,
            tokenizer=ref_checkpoint if self.tokenizer is None else self.tokenizer,
            HfConfigClass=HfQwenConfig,
        )

    @classmethod
    def from_hf_config(cls, hf_config: HfConfig):
        return QwenConfig(
            seq_len=hf_config.max_position_embeddings,
            hidden_dim=hf_config.hidden_size,
            intermediate_dim=hf_config.intermediate_size,
            num_layers=hf_config.num_hidden_layers,
            num_heads=hf_config.num_attention_heads,
            num_kv_heads=hf_config.num_key_value_heads,
            activation_function=hf_config.hidden_act, #return them here is an option
            initializer_range=hf_config.initializer_range,
            layer_norm_epsilon=hf_config.rms_norm_eps,
            rope_scaling=hf_config.rope_scaling,
        )

    def to_hf_config(self, vocab_size: int, config_overrides: Optional[Dict] = None) -> HfQwenConfig:
        if config_overrides is None:
            config_overrides = {}

        return HfQwenConfig(
            max_position_embeddings=self.seq_len,
            hidden_size=self.hidden_dim,
            intermediate_size=self.intermediate_dim,
            num_hidden_layers=self.num_layers,
            num_attention_heads=self.num_heads,
            num_key_value_heads=self.num_kv_heads,
            use_sliding_window=self.use_sliding_window,
            sliding_window=self.sliding_window,
            max_window_layers=self.max_window_layers,
            hidden_act=self.activation_function,
            initializer_range=self.initializer_range,
            rms_norm_eps=self.layer_norm_epsilon,
            vocab_size=vocab_size,
            rope_scaling=self.rope_scaling,
            **config_overrides,
        )

    @property
    def model_type(self) -> Type["QwenLMHeadModel"]:
        return QwenLMHeadModel

    def flops_per_token(self, vocab_size: int):
        return lm_flops_per_token(
            hidden_dim=self.hidden_dim,
            intermediate_dim=self.intermediate_dim,
            num_layers=self.num_layers,
            num_kv_heads=self.num_kv_heads,
            num_heads=self.num_heads,
            seq_len=self.seq_len,
            vocab_size=vocab_size,
            glu=True,
        )


# Modified attention class for Qwen
class QwenAttention(StateDictSerializationMixin, eqx.Module):
    config: QwenConfig = eqx.field(static=True)
    q_proj: hnn.Linear
    k_proj: hnn.Linear
    v_proj: hnn.Linear
    o_proj: hnn.Linear

    @staticmethod
    def init(config: QwenConfig, *, key) -> "QwenAttention":
        Embed = config.Embed
        QHeadsPerGroup = hax.Axis("q_heads_per_group", config.num_heads // config.num_kv_heads)

        k_q, k_k, k_v, k_o = jrandom.split(key, 4)
        q_proj = hnn.Linear.init(
            In=Embed,
            Out=(config.KVHeads, QHeadsPerGroup, config.HeadSize),
            key=k_q,
            use_bias=True,  # Qwen always uses bias in attention
            out_first=True,
        )
        k_proj = hnn.Linear.init(
            In=Embed, Out=(config.KVHeads, config.HeadSize), key=k_k, use_bias=True, out_first=True
        )
        v_proj = hnn.Linear.init(
            In=Embed, Out=(config.KVHeads, config.HeadSize), key=k_v, use_bias=True, out_first=True
        )
        o_proj = hnn.Linear.init(
            In=(config.Heads, config.HeadSize),
            Out=Embed,
            key=k_o,
            use_bias=False,  # Qwen doesn't use bias in o_proj
            out_first=True,
        )
        return QwenAttention(config, q_proj, k_proj, v_proj, o_proj)
    def _rope_scale_factor(self) -> float:
        # hasattr for gemma and I'm feeling lazy
        if hasattr(self.config, "rope_scaling") and self.config.rope_scaling is not None:
            assert self.config.rope_scaling["type"] == "linear"
            return self.config.rope_scaling["factor"]
        return 1.0

    @named_call
    def __call__(
        self, x: NamedArray, mask: Optional[NamedArray | AttentionMask], layer_idx: int = 0, *, key=None
    ) -> NamedArray:
        key_q, key_k, key_v, key_o = maybe_rng_split(key, 4)

        # QKV projections
        q = self.q_proj(x, key=key_q).rearrange((..., "kv_heads", "q_heads_per_group", "position", "head_size"))
        k = self.k_proj(x, key=key_k).rearrange((..., "kv_heads", "position", "head_size"))
        v = self.v_proj(x, key=key_v).rearrange((..., "kv_heads", "position", "head_size"))

        # Apply rotary embeddings
        cos, sin = llama_rotary_pos_emb(
            self.config.HeadSize, x.resolve_axis("position"), scale=self._rope_scale_factor()
        )
        q, k = _apply_rotary_pos_emb(q, k, cos, sin)

        k = k.rename({"position": "key_position"})
        v = v.rename({"position": "key_position"})

        # Apply sliding window attention if configured and past max_window_layers
        if (
            self.config.use_sliding_window
            and self.config.sliding_window is not None
            and layer_idx >= self.config.max_window_layers
        ):
            raise ValueError("Sliding Window Attention is not currently supported.")

        # Perform attention
        attn_output = dot_product_attention(
            "position",
            "key_position",
            "head_size",
            q,
            k,
            v,
            mask,
            attention_dtype=jnp.float32 if self.config.upcast_attn else x.dtype,
            use_flash=self.config.use_flash_attention,
            attn_backend=self.config.attn_backend,
            flash_block_size=self.config.flash_attention_block_size,
        )

        attn_output = attn_output.flatten_axes(("kv_heads", "q_heads_per_group"), "heads")
        attn_output = attn_output.astype(x.dtype)

        attn_output = self.o_proj(attn_output, key=key_o)
        return attn_output

    def from_state_dict(self, state_dict: StateDict, prefix: Optional[str] = None):
        # unflatten the linear layers of HF state_dict to match the shape of LlamaAttention
        d = {}
        d.update(unflatten_linear_layers(apply_prefix(prefix, "q_proj"), state_dict, self.q_proj, True))
        d.update(unflatten_linear_layers(apply_prefix(prefix, "k_proj"), state_dict, self.k_proj, True))
        d.update(unflatten_linear_layers(apply_prefix(prefix, "v_proj"), state_dict, self.v_proj, True))
        d.update(unflatten_linear_layers(apply_prefix(prefix, "o_proj"), state_dict, self.o_proj, True))

        return super().from_state_dict(d, prefix)

    def update_state_dict(self, state_dict: StateDict, prefix: Optional[str] = None) -> StateDict:
        # flatten the linear layers of LlamaAttention to match the shape of HF state_dict
        my_dict: StateDict = {}
        super().update_state_dict(my_dict, prefix)

        my_dict.update(flatten_linear_layers(apply_prefix(prefix, "q_proj"), self.q_proj, True))
        my_dict.update(flatten_linear_layers(apply_prefix(prefix, "k_proj"), self.k_proj, True))
        my_dict.update(flatten_linear_layers(apply_prefix(prefix, "v_proj"), self.v_proj, True))
        my_dict.update(flatten_linear_layers(apply_prefix(prefix, "o_proj"), self.o_proj, True))

        state_dict.update(my_dict)
        return state_dict


# Modified decoder layer for Qwen
class QwenDecoderLayer(eqx.Module):
    config: QwenConfig = eqx.field(static=True)
    self_attn: QwenAttention
    mlp: LlamaMlp  # Can reuse Llama MLP as structure is similar
    input_layernorm: LlamaRMSNorm
    post_attention_layernorm: LlamaRMSNorm

    @staticmethod
    def init(config: QwenConfig, *, key) -> "QwenDecoderLayer":
        k_attn, k_mlp = jrandom.split(key, 2)

        attn = QwenAttention.init(config, key=k_attn)
        mlp = LlamaMlp.init(
            config.Embed,
            config.Mlp,
            config.activation_function,
            key=k_mlp,
            use_bias=config.use_bias,
        )
        ln_1 = config.mk_LayerNorm(config.Embed)
        ln_2 = config.mk_LayerNorm(config.Embed)

        return QwenDecoderLayer(config, attn, mlp, ln_1, ln_2)

    @named_call
    def __call__(self, x: NamedArray, mask: Optional[NamedArray | AttentionMask], *, key=None) -> NamedArray:
        k_attn, k_mlp = maybe_rng_split(key, 2)

        residual = x
        x = self.input_layernorm(x)
        attn_output = self.self_attn(x=x, mask=mask, key=k_attn)
        x = residual + attn_output

        residual = x
        x = self.post_attention_layernorm(x)
        mlp_output = self.mlp(x, key=k_mlp)
        output = residual + mlp_output
        return output


# Modified transformer for Qwen
class QwenTransformer(LlamaTransformer):
    config: QwenConfig = eqx.field(static=True)
    layers: BlockFoldable[QwenDecoderLayer]
    norm: LlamaRMSNorm

    @staticmethod
    def init(config: QwenConfig, *, key) -> "QwenTransformer":
        S = Stacked
        if not config.scan_layers:
            from haliax.nn.scan import BlockSeq

            S = BlockSeq

        # Initialize layers with their indices
        layers = S.init(config.Layers, QwenDecoderLayer, gradient_checkpointing=config.gradient_checkpointing)(
            config,
            key=shaped_rng_split(key, config.num_layers),
        )

        ln_f = config.mk_LayerNorm(config.Embed)
        return QwenTransformer(config, layers, ln_f)


# Modified LM head model for Qwen
class QwenLMHeadModel(eqx.Module, LmHeadModel[QwenConfig], StateDictSerializationMixin):
    transformer: QwenTransformer
    embeddings: LlamaEmbedding  # Can reuse Llama embeddings
    lm_head: Optional[hnn.Linear]

    @property
    def config(self) -> QwenConfig:
        return self.transformer.config

    @property
    def Vocab(self) -> Axis:
        return self.embeddings.Vocab

    def activations(
        self, input_ids: NamedArray, attn_mask: Optional[AttentionMask | NamedArray] = None, *, key=None
    ) -> NamedArray:
        """
        Compute the activations for the next token in a sequence.
        Args:
            input_ids: token IDs with shape {Pos}
            attn_mask: attention mask with shape {Pos, KeyPos}
            key: PRNGKeyArray for random number generation

        Returns:
            NamedArray: activations with shape {Pos, Embed}

        """
        x = self.embeddings.embed(input_ids)
        x = self.transformer(x, attn_mask=attn_mask, key=key)

        return x

    def get_lm_head(self) -> hax.NamedArray:
        if self.lm_head is None:
            return self.embeddings.token_embeddings.weight
        else:
            return self.lm_head.weight

    def resize_vocab(self, new_size: int, key=None) -> "LmHeadModel[LlamaConfig]":
        new_Vocab = self.Vocab.resize(new_size)
        k1, k2 = maybe_rng_split(key, 2)
        new_embeddings = self.embeddings.resize_embeddings(new_size, key=k1)
        if self.lm_head is not None:
            new_lm_matrix = hax.tree_util.resize_axis(self.lm_head.weight, self.Vocab, new_size, key=k2)
            new_lm_head = dataclasses.replace(self.lm_head, Out=new_Vocab, weight=new_lm_matrix)
            return dataclasses.replace(self, embeddings=new_embeddings, lm_head=new_lm_head)
        else:
            return dataclasses.replace(self, embeddings=new_embeddings)

    @classmethod
    def init(cls, Vocab: Axis, config: QwenConfig, *, key) -> "QwenLMHeadModel":
        k_t, k_emb = jrandom.split(key, 2)
        transformer = QwenTransformer.init(config, key=k_t)
        embeddings = LlamaEmbedding.init(Vocab, config, key=k_emb)
        lm_head = hnn.Linear.init(In=config.Embed, Out=Vocab, key=k_emb, use_bias=False, out_first=True)
        return QwenLMHeadModel(transformer, embeddings, lm_head)

    def _state_dict_key_map(self) -> Dict[str, Optional[str]]:
        return {"transformer": "model", "embeddings": None}

    def __call__(
        self,
        input_ids: NamedArray,
        attn_mask: Optional[Union[NamedArray, AttentionMask]] = None,
        *,
        key=None,
    ) -> NamedArray:
        """
        Args:
            input_ids (NamedArray): [batch, position]
                Indices of input sequence tokens in the vocabulary.
            attn_mask (Union[NamedArray, AttentionMask], optional): [batch, position]
                Mask to avoid performing attention on the padding token indices of the encoder input.
                The attn_mask from training pipeline may be an AttentionMask object instead of NamedArray
        """
        k_t, k_head = maybe_rng_split(key, 2)
        x = self.embeddings.embed(input_ids)
        x = self.transformer(x, attn_mask=attn_mask, key=k_t)
        lm_logits = self.lm_head(x, key=k_head)
        return lm_logits

    def from_state_dict(self, state_dict: StateDict, prefix: Optional[str] = None):
        # unflatten the linear layers of HF state_dict to match the shape of LlamaMlp
        d = state_dict.copy()
        d.update(
            unflatten_linear_layers(
                apply_prefix(prefix, "lm_head"), state_dict, self.lm_head, out_dims_first_in_dict=True
            )
        )
        return super().from_state_dict(d, prefix)

    def update_state_dict(self, state_dict: StateDict, prefix: Optional[str] = None) -> StateDict:
        my_dict: StateDict = {}
        super().update_state_dict(my_dict, prefix=prefix)

        my_dict.update(
            flatten_linear_layers(apply_prefix(prefix, "lm_head"), self.lm_head, out_dims_first_in_dict=True)
        )

        state_dict.update(my_dict)
        return state_dict

