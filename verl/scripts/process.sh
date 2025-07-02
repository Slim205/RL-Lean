#!/usr/bin/env bash
set -euo pipefail

# ---------- CONFIGURABLE PARAMETERS ---------- #
CHECKPOINT_ROOT="/n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/deepseek_RL_4/mathlibV4"
HF_BASE_MODEL="deepseek-ai/DeepSeek-Prover-V1.5-SFT"        # same as your example
EVAL_DATASET="datasets/minif2f.jsonl"
N_SAMPLES=32       # -n
CTX_LEN=60         # -c
GPUS=4             # -g
SPLIT=test         # -s
RESULT_BASE="results/minif2f"      # where all run directories go
TMP_DIR_PREFIX="model_V4_"         # will become model_V4_40, model_V4_80, ...
# --------------------------------------------- #

echo ">>> Starting conversion + evaluation for every checkpoint under $CHECKPOINT_ROOT"
for ckpt in "${CHECKPOINT_ROOT}"/global_step_*; do
  # extract just the step number (e.g. 40, 80, 280)
  step="$(basename "$ckpt" | sed 's/^global_step_//')"

  actor_path="${ckpt}/actor"
  target_dir="./${TMP_DIR_PREFIX}${step}"          # lives inside verl/scripts
  result_dir="${RESULT_BASE}/deepseek-RL-step${step}"

  echo -e "\n=== [STEP $step] Converting -> ${target_dir} ==="
  python model_merger.py merge \
      --backend fsdp \
      --local_dir "${actor_path}" \
      --target_dir "${target_dir}" \
      --hf_model_path "${HF_BASE_MODEL}"

  echo "=== [STEP $step] Evaluating -> ${result_dir} ==="
  sh eval/eval.sh \
      -i "${EVAL_DATASET}" \
      -s "${SPLIT}" \
      -m "${target_dir}" \
      -o "${result_dir}" \
      -n "${N_SAMPLES}" \
      -c "${CTX_LEN}" \
      -g "${GPUS}"

  echo "=== [STEP $step] Done ==="
done

echo -e "\nAll checkpoints processed ✅"
