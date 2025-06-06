# levanter version of https://github.com/tatsu-lab/stanford_alpaca/blob/main/train.py
import json
import logging
import os
from dataclasses import dataclass
from typing import Dict, Optional, Union

import fsspec
import jax
import jax.random as jrandom
import numpy as np
import transformers

import haliax as hax
from haliax.nn import cross_entropy_loss

import levanter
from levanter import callbacks
from levanter.compat.hf_checkpoints import HFCheckpointConverter, save_hf_checkpoint_callback
from levanter.data import Dataset
from levanter.data.sharded_dataset import JsonDataset, JsonlDataset, WrappedHFDataset
from levanter.models.lm_model import LmExample, LmHeadModel
from levanter.optim import OptimizerConfig
from levanter.trainer import Trainer, TrainerConfig
from levanter.utils import fsspec_utils
from levanter.utils.hf_utils import num_cpus_used_by_tokenizer
from levanter.utils.py_utils import non_caching_cycle
from levanter.models.attention import AttentionMask

# Differences:
# - We use the huggingface dataset version of alpaca rather than checking it in
# - Levanter doesn't (currently) do epochs, just steps.
# - We use Levanter's distributed preprocessing, which is a bit overkill for this dataset but is a good example.
#   (The original's preprocessing is very slow, which is usually fine, but not good for preemptible nodes.)
# - We use fast tokenizers. I don't know why the original code doesn't use them.
# - We produce Levanter's LmExample class instead of a dict, and loss masks are used instead of the -100 sentinel value.

# Ways this script could be improved:
# * Could tune hparams more for throughput

# Original
#    Copyright 2023 Rohan Taori, Ishaan Gulrajani, Tianyi Zhang, Yann Dubois, Xuechen Li
#
#    Licensed under the Apache License, Version 2.0 (the "License");
#    you may not use this file except in compliance with the License.
#    You may obtain a copy of the License at
#
#        http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS,
#    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#    See the License for the specific language governing permissions and
#    limitations under the License.


# TODO
# * make a pad_stack function that can pad and stack arrays in one go
# * make batch loader support pad_stack

class LmWeightedExample(LmExample):
    tokens: hax.NamedArray
    loss_mask: hax.NamedArray
    weights: jax.numpy.float32 = 1.0
    attn_mask: AttentionMask = AttentionMask.causal()

logger = logging.getLogger(__name__)

# copy paste from alpaca

DEFAULT_PAD_TOKEN = "[PAD]"
DEFAULT_EOS_TOKEN = "</s>"
DEFAULT_BOS_TOKEN = "<s>"
DEFAULT_UNK_TOKEN = "<unk>"

@dataclass
class TrainArgs:
    optimizer: OptimizerConfig
    trainer: TrainerConfig

    max_tune_length: int = 2048  # maximum length of the input to the model during tuning
    train_data: str = "tatsu-lab/alpaca"  # Path to the training data, or huggingface dataset name.
    train_data_cache_dir: str = "cache/"  # Path to cache the tokenized data. can be gcs
    eval_data: Optional[str] = None  # Path to the training data, or huggingface dataset name.
    eval_data_cache_dir: str = "cache/"  # Path to cache the tokenized data. can be gcs

    model_name_or_path: str = "EleutherAI/llemma_7b"
    tokenizer_name_or_path: str = "meta-llama/Llama-3.1-8B-Instruct"
    trust_remote_code: bool = False  # Trust remote code when loading from HuggingFace checkpoints.

    model_cache_dir: Optional[str] = None  # Path to cache the model. must be local.

    hf_save_path: Optional[str] = "alpaca_hf_ckpts"  # Path to save the HuggingFace checkpoint, can be gcs
    save_freq: Optional[int] = None

# Encoder/Decoder dataset for Alpaca.
# We basically do string interpolation of the (instruction, input, output) triples with the prompt,
# and mask out the prompt and padding.
class SupervisedDataset(Dataset[LmWeightedExample]):
    def __init__(self, preproc_dataset, tokenizer):
        self.preproc_dataset = preproc_dataset
        self.tokenizer = tokenizer

    def __iter__(self):
        for raw_ex in self.preproc_dataset:
            ex = self.tokenizer.pad(
                {k: np.expand_dims(v, 0) for k, v in raw_ex.items() if k != "weight"}, return_tensors="np", padding="max_length"
            )
            ex = {k: v[0] for k, v in ex.items()}
            input_ids = hax.named(ex["input_ids"], "position")

            Pos = input_ids.resolve_axis("position")
            loss_mask = hax.arange(Pos) >= ex["source_lens"]
            targets = hax.roll(input_ids, -1, Pos)
            loss_mask = loss_mask & (targets != self.tokenizer.pad_token_id)

            yield LmWeightedExample(
                tokens=input_ids,
                weights=raw_ex["weight"],
                loss_mask=loss_mask,
                attn_mask=AttentionMask.causal()
            )

def mk_dataset(data_dir: str, data_cache_dir: str, batch_size: int, tokenizer: transformers.PreTrainedTokenizerBase):
    dataset = JsonDataset([data_dir])  # Assuming config.data is the path to your JSON file

    def preprocess(batch):
        input_ids = []
        weights = []
        source_lens = []

        for example in batch:
            prompt = example['prompt']
            target = example['target'] + tokenizer.eos_token
            weight = example.get('weight', 1.0)
            
            tokens = tokenizer(prompt + target, padding=False, truncation=False)["input_ids"]
            target_tokens = tokenizer(target, padding=False, truncation=False)["input_ids"]
            source_len = len(tokens) - len(target_tokens) + 1
            
            if len(tokens) > tokenizer.model_max_length:
                source_len = max(source_len - (len(tokens) - tokenizer.model_max_length), 1)
                tokens = [tokenizer.bos_token_id] + tokens[-tokenizer.model_max_length + 1:]

            input_ids.append(tokens)
            weights.append(weight)
            source_lens.append(source_len)

            # assert tokenizer.decode(tokens[source_len:min(source_len + 10, tokenizer.model_max_length)]).startswith(('>\n ', '> ')) or (len(target_tokens) > tokenizer.model_max_length)
            assert source_len <= tokenizer.model_max_length

        # Pad sequences to max length in batch
        max_len = max(len(ids) for ids in input_ids)
        padded_input_ids = [ids + [tokenizer.pad_token_id] * (max_len - len(ids)) for ids in input_ids]

        return {
            "input_ids": np.array(padded_input_ids),
            "source_lens": np.array(source_lens),
            "weight": np.array(weights, dtype=np.float32),
        }

    dataset = dataset.map_batches(preprocess, batch_size=batch_size, num_cpus=num_cpus_used_by_tokenizer(tokenizer))
    dataset = dataset.build_or_load_cache(data_cache_dir, await_finished=False)

    dataset = SupervisedDataset(dataset, tokenizer)

    return dataset

def train(config: TrainArgs):
    levanter.initialize(config)

    # Randomness in JAX is tightly controlled. We pass around a key that is used to generate random numbers.
    model_key, training_key = jrandom.split(jrandom.PRNGKey(config.trainer.seed), 2)

    # This is largely the same as in Alpaca. Only change is we use the fast tokenizer.
    tokenizer = transformers.AutoTokenizer.from_pretrained(
        config.tokenizer_name_or_path,
        cache_dir=config.model_cache_dir,
        model_max_length=config.max_tune_length,
        padding_side="right",
    )
    num_new_tokens = add_special_tokens(tokenizer)
    logger.info(f"Added {num_new_tokens} new tokens")

    # Since Levanter has different implementations of models from HF, we need to convert the HF checkpoint.
    # This class is a wrapper around the HF checkpoint converter that also downloads the checkpoint if necessary.
    converter = HFCheckpointConverter.from_hf(config.model_name_or_path, trust_remote_code=config.trust_remote_code)
    if hasattr(tokenizer, "vocab") and tokenizer.vocab != converter.tokenizer.vocab:
        logger.warning("The tokenizers appear to be different. You may want to check this.")
    converter = converter.replaced(reference_checkpoint=config.model_name_or_path, tokenizer=tokenizer)
    model_config = converter.config_from_hf_config(converter.default_hf_config)

    if config.max_tune_length > model_config.Pos.size:
        logger.warning(
            f"max_tune_length ({config.max_tune_length}) is greater than the model's maximum length"
            f" ({model_config.Pos.size}). "
        )

    optimizer = config.optimizer.build(config.trainer.num_train_steps)

    with Trainer(config.trainer, optimizer, compute_weighted_loss) as trainer:
        # Levanter has two kinds of data loaders: sharded and replicated. Replicated is simpler and allows for
        # single pass training. Sharded only loads a subset of the data on each device, and is more efficient for large
        # datasets. We use replicated here since the dataset is small.
        logger.info("Loading training data.")
        train_dataset = mk_dataset(config.train_data, config.train_data_cache_dir, trainer.config.train_batch_size, tokenizer)
        train_loader = trainer.replicated_loader(train_dataset, trainer.TrainBatch)
        train_loader = non_caching_cycle(train_loader)
        logger.info("Done loading training data.")

        # how we shard parameters across devices
        compute_axis_mapping = trainer.compute_axis_mapping
        parameter_axis_mapping = trainer.parameter_axis_mapping

        logger.info(f"Loading checkpoint from {config.trainer.load_checkpoint_path}")
        model: LmHeadModel = converter.load_pretrained(  # type: ignore
            model_config.model_type, model_config, axis_mapping=parameter_axis_mapping, dtype=trainer.mp.param_dtype
        )
        # this must be in jit b/c it uses arrays across accelerators (b/c of FSDP)
        model = hax.named_jit(lambda m: m.resize_vocab(len(tokenizer)))(model)

        if config.eval_data is None:
            logger.warning("No evaluation datasets provided.")
        else:
            logger.info("Loading eval data.")
            eval_dataset = mk_dataset(config.eval_data, config.eval_data_cache_dir, config.trainer.eval_batch_size, tokenizer)
            
            cb = levanter.eval.cb_tagged_lm_evaluate(
                trainer.EvalBatch, [(eval_dataset, ['val'])], trainer.device_mesh, compute_axis_mapping, None
            )
            trainer.add_hook(cb, every=config.trainer.steps_per_eval)
            logger.info("Done loading eval data.")

        vocab_size = len(tokenizer)
        flops_per_token = model_config.flops_per_token(vocab_size)
        flops_per_example = 3 * flops_per_token * model_config.Pos.size if flops_per_token is not None else None
        trainer.add_hook(
            callbacks.log_performance_stats(model_config.Pos.size, trainer.config.train_batch_size, flops_per_example), every=1
        )
        logger.info("Creating trainer state.")
        state = trainer.initial_state(training_key, model=model)
        logger.info("Done.")

        # force the training to start from the beginning
        state = state.reset_step()

        # We also save HF checkpoints periodically (and at the end of training).
        if config.hf_save_path is not None:
            full_save_path = os.path.join(config.hf_save_path, trainer.run_id)

            trainer.add_hook(
                save_hf_checkpoint_callback(full_save_path, converter, upload_to_hf=False),
                every=config.save_freq or config.trainer.num_train_steps,
            )
        logger.info("Starting training.")
        info = trainer.train(state, train_loader)

def add_special_tokens(tokenizer, use_unk_instead_of_adding=False):
    special_tokens_dict = dict()
    if use_unk_instead_of_adding:
        if tokenizer.unk_token is None:
            raise ValueError("use_unk_instead_of_add is True but tokenizer doesn't have an unk token")

    unk = tokenizer.unk_token if use_unk_instead_of_adding else None

    if tokenizer.pad_token is None:
        special_tokens_dict["pad_token"] = DEFAULT_PAD_TOKEN if not use_unk_instead_of_adding else unk
    if tokenizer.eos_token is None:
        special_tokens_dict["eos_token"] = DEFAULT_EOS_TOKEN if not use_unk_instead_of_adding else unk
    if tokenizer.bos_token is None:
        special_tokens_dict["bos_token"] = DEFAULT_BOS_TOKEN if not use_unk_instead_of_adding else unk
    if tokenizer.unk_token is None:
        special_tokens_dict["unk_token"] = DEFAULT_UNK_TOKEN

    return tokenizer.add_special_tokens(special_tokens_dict)

def compute_weighted_loss(
    self,
    example: LmWeightedExample,
    *,
    key=None,
    reduction: Optional[hax.ReductionFunction] = hax.mean,
    reduction_axis: Optional[hax.AxisSelection] = None,
) -> jax.numpy.ndarray | hax.NamedArray:
    """
    Computes the weighted cross-entropy loss for a language modeling example. If reduction is not None, the loss is 
    reduced across the reduction axis (with reduction_axis=None meaning all axes). If reduction is None, the loss is 
    not reduced, and the result is a named array with axes (*batch axes, sequence_length).
    """
    logits = self(example.tokens, example.attn_mask, key=key)
    logits = logits.astype(jax.numpy.float32)
    targets = hax.roll(example.tokens, -1, axis=self.Pos.name)
    target_y = hax.nn.one_hot(targets, self.Vocab, dtype=logits.dtype)
    
    # Compute the cross-entropy loss without reduction
    ce_loss = cross_entropy_loss(
        logits, self.Vocab, target_y, reduction=None
    )
    
    # Apply weights to the loss
    # weighted_loss = ce_loss * example.weights[..., None]
    weighted_loss = ce_loss * example.weights[..., None]
    mean_weights = reduction(hax.ones_like(ce_loss) * example.weights[..., None], where=example.loss_mask, axis=None)

    # Perform reduction if specified
    if reduction is not None:
        weighted_loss = reduction(weighted_loss, where=example.loss_mask, axis=reduction_axis)
    
    return weighted_loss / mean_weights

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    levanter.config.main(train)()
