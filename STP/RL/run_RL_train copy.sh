#!/bin/bash

EXP_DIR="/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook_merged"
DATASET_CONFIG="./dataset_configs/leanworkbook.json"
TRAIN_FROM="deepseek-ai/DeepSeek-Prover-V1.5-SFT"
SFT_DATASET="/n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/mathlib.json"

module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL


python RL_step3_final_model.py \
    --base_model "deepseek-ai/DeepSeek-Prover-V1.5-SFT" \
    --exp_dir "/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook_merged" \
    --sft_dataset "/n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/mathlib.json" \
    --dataset_config "./dataset_configs/leanworkbook.json" \
    --epoch 1 \
    --lr 1e-4 \
    --include_synthetic_examples \
    --merge_from "/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook" \
    --merge_from_rounds 12