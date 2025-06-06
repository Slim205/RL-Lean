#!/bin/bash
#SBATCH --job-name=stprepo
#SBATCH --nodes=1  
#SBATCH --ntasks-per-node=1
#SBATCH --gpus-per-node=4
#SBATCH --cpus-per-task=24
#SBATCH --time=06:00:00
#SBATCH --mem=128GB
#SBATCH --partition=serial_requeue
#SBATCH --constraint=a100
#SBATCH --export=ALL 

export SLURM_STEP_TASKS_PER_NODE=$SLURM_NTASKS_PER_NODE
export SLURM_JOB_NUM_NODES=$SLURM_NNODES

BASE_MODEL="/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/ec631qtl/step-999"

EXP_DIR="/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook_merged"
DATASET_CONFIG="./dataset_configs/leanworkbook.json"

module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL

#
python RL_step1_generate.py --model "/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/ec631qtl/step-999" --exp_dir "/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook_merged/round0" --seed 0 --temperature 1.0   --dataset_config "./dataset_configs/leanworkbook.json" --sampler "Sampler_base" --conjecture_multiplier 1 --samples_per_statement 64 --statements_per_round 0 --gpu 2 --cpu 24
#python RL_step2_train.py --base_model "/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/ec631qtl/step-999"  --exp_dir "/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook_merged/round0" --epoch 1 --lr 5e-5

# Define the total number of rounds
TOTAL_ROUNDS=1
START_ROUND=0

# Loop through each round
for ((ROUND=$START_ROUND; ROUND<TOTAL_ROUNDS; ROUND++)); do
    # Determine the model to use
    if [ "$ROUND" -eq 0 ]; then
        MODEL="$BASE_MODEL"
        SEED="$ROUND"
        SPL=64
    else
        PREV_ROUND=$((ROUND-1))
        MODEL="$EXP_DIR/round${PREV_ROUND}/RL_model"
        SEED="$ROUND"
        SPL=32
    fi

    # Define the experiment directory for the current round
    CURRENT_EXP_DIR="$EXP_DIR/round${ROUND}"

    echo "=============================="
    echo "Starting Round ${ROUND}"
    echo "Generating data with model: $MODEL"
    echo "Experiment Directory: $CURRENT_EXP_DIR"
    echo "Seed: $SEED"
    echo "=============================="

    # Step 1: Generate Data
    python RL_step1_generate.py \
        --model "$MODEL" \
        --exp_dir "$CURRENT_EXP_DIR" \
        --seed "$SEED" \
        --temperature 1.0 \
        --dataset_config "$DATASET_CONFIG" \
        --sampler "Sampler_base" \
        --conjecture_multiplier 1 \
        --samples_per_statement $SPL \
        --statements_per_round 0 \
        --gpu 4 \
        --cpu 24

    echo "Data generation for Round ${ROUND} completed."

    # Step 2: Train Model
    echo "Starting training for Round ${ROUND} with base model: $MODEL"

    python RL_step2_train.py \
        --base_model "$MODEL" \
        --exp_dir "$CURRENT_EXP_DIR" \
        --epoch 1 \
        --lr 5e-5

    echo "Training for Round ${ROUND} completed."
done

echo "All rounds completed successfully."