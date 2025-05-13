#!/bin/bash

# we frequently deal with commands failing, and we like to loop until they succeed. this function does that for us
function retry {
  for i in {1..5}; do
    "$@"
    if [ $? -eq 0 ]; then
      break
    fi
    if [ $i -eq 5 ]; then
      >&2 echo "Error running $*, giving up"
      exit 1
    fi
    >&2 echo "Error running $*, retrying in 5 seconds"
    sleep 5
  done
}

# Exit immediately if a command exits with a non-zero status
set -e

source .bash_alias.sh
# Define variables
EXP_DIR="$STORAGE/STP_LeanWorkbook"
BASE_MODEL="$STORAGE/SFT/ygfu8isg/step-114"

DATASET_CONFIG="./dataset_configs/leanworkbook.json"

# Fetch TPU metadata
TPU_NAME=$(retry curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/description)
ZONE_FULL_PATH=$(retry curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/zone)
ZONE=$(echo "$ZONE_FULL_PATH" | awk -F'/' '{print $NF}')

source ~/venv_vllm/bin/activate

# Define the total number of rounds
TOTAL_ROUNDS=12
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
    TPU_NAME="$TPU_NAME" ZONE="$ZONE" python RL_step1_generate.py \
        --model "$MODEL" \
        --exp_dir "$CURRENT_EXP_DIR" \
        --seed "$SEED" \
        --temperature 1.0 \
        --dataset_config "$DATASET_CONFIG" \
        --sampler "Sampler_base" \
        --conjecture_multiplier 1 \
        --samples_per_statement $SPL \
        --statements_per_round 0

    echo "Data generation for Round ${ROUND} completed."

    # Step 2: Train Model
    echo "Starting training for Round ${ROUND} with base model: $MODEL"
    WANDB_API_KEY=$WANDB_API_KEY \
    TPU_NAME="$TPU_NAME" ZONE="$ZONE" python RL_step2_train.py \
        --base_model "$MODEL" \
        --exp_dir "$CURRENT_EXP_DIR" \
        --epoch 1 \
        --lr 5e-5

    echo "Training for Round ${ROUND} completed."
done

echo "All rounds completed successfully."