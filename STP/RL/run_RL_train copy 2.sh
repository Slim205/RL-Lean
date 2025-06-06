#!/bin/bash
source .bash_alias.sh
EXP_DIR="$STORAGE/STP_LeanWorkbook_merged"
DATASET_CONFIG="./dataset_configs/leanworkbook.json"
TRAIN_FROM="deepseek-ai/DeepSeek-Prover-V1.5-SFT"
SFT_DATASET="$STORAGE/data/SFT/mathlib.json"

TPU_NAME=$(curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/description)
ZONE_FULL_PATH=$(curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/zone)
ZONE=$(echo "$ZONE_FULL_PATH" | awk -F'/' '{print $NF}')

source ~/venv_vllm/bin/activate

WANDB_API_KEY=$WANDB_API_KEY TPU_NAME=$TPU_NAME ZONE=$ZONE python RL_step3_final_model.py \
    --base_model $TRAIN_FROM \
    --exp_dir $EXP_DIR \
    --sft_dataset $SFT_DATASET \
    --dataset_config "$DATASET_CONFIG" \
    --epoch 1 \
    --lr 1e-4 \
    --include_synthetic_examples \
    --merge_from "$STORAGE/STP_LeanWorkbook" \
    --merge_from_rounds 12