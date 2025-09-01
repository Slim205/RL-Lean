BASE_MODEL="kfdong/STP_model_Lean_0320"

EXP_DIR=/n/netscratch/amin_lab/Lab/slim/Lean/storage/Expert_V2

TOTAL_ROUNDS=24
START_ROUND=0

# Loop through each round
for ((ROUND=$START_ROUND; ROUND<TOTAL_ROUNDS; ROUND++)); do
    if [ "$ROUND" -eq 0 ]; then
        MODEL="$BASE_MODEL"
        SEED="$ROUND"
    else
        PREV_ROUND=$((ROUND-1))
        MODEL="$EXP_DIR/round${PREV_ROUND}/RL_model"
        SEED="$ROUND"
    fi


    CURRENT_EXP_DIR="$EXP_DIR/round${ROUND}"
    mkdir -p $CURRENT_EXP_DIR
    echo "=============================="
    echo "Starting Round ${ROUND}"
    echo "Generating data with model: $MODEL"
    echo "Experiment Directory: $CURRENT_EXP_DIR"
    echo "Seed: $SEED"
    echo "=============================="

    ## Step 1: Generate Data
    python generate_and_test.py \
        --model_name $MODEL \
        --iteration $ROUND\
        --path "$CURRENT_EXP_DIR/train.json" \
        --n_sample 0 \

    python prepare_sft_data.py \
        --path "$CURRENT_EXP_DIR/train.json" \
        --STORAGE  "$CURRENT_EXP_DIR/data/" \

    echo "Data generation for Round ${ROUND} completed."

    # # Step 2: Train Model
    echo "Starting training for Round ${ROUND} with base model: $MODEL"
    python training.py \
        --model_name_or_path $MODEL  \
        --CURRENT_EXP_DIR  $CURRENT_EXP_DIR\

    echo "Training for Round ${ROUND} completed."

    echo "Starting Evaluation for Round ${ROUND} with base model: $MODEL"

    sh eval/eval.sh -i eval/minif2f.jsonl -s test -m "$EXP_DIR/round${ROUND}/RL_model"  -o "$CURRENT_EXP_DIR/minif2f-1/" -n 1 -c 32 -g 1
    sh eval/eval.sh -i eval/minif2f.jsonl -s test -m "$EXP_DIR/round${ROUND}/RL_model"  -o "$CURRENT_EXP_DIR/minif2f-32/" -n 32 -c 64 -g 4

    echo "Evaluation for Round ${ROUND} completed."


done

echo "All rounds completed successfully."