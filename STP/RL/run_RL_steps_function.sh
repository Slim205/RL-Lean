BASE_MODEL="/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/tsw6rwex/step-229"

EXP_DIR="/n/netscratch/amin_lab/Lab/slim/STP/storage/STP_LeanWorkbook_merged"
DATASET_CONFIG="./dataset_configs/leanworkbook.json"


TOTAL_ROUNDS=5
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
    /n/netscratch/amin_lab/Lab/slim/env/bin/python RL_step1_generate.py \
        --model "$MODEL" \
        --exp_dir "$CURRENT_EXP_DIR" \
        --seed "$SEED" \
        --temperature 1.0 \
        --dataset_config "$DATASET_CONFIG" \
        --sampler "Sampler_base" \
        --conjecture_multiplier 1 \
        --samples_per_statement $SPL \
        --statements_per_round 0 \

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