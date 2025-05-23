#!/bin/bash
# Check if the correct number of arguments are provided
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <MODEL> <EXP_DIR>"
    exit 1
fi

MODEL=$1
EXP_DIR=$2

source .bash_alias.sh
TPU_NAME=$(curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/description)
ZONE_FULL_PATH=$(curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/zone)
DATASET_CONFIG="./dataset_configs/miniF2F_ProofNet.json"
ZONE=$(echo "$ZONE_FULL_PATH" | awk -F'/' '{print $NF}')

source ~/venv_vllm/bin/activate
TPU_NAME=$TPU_NAME ZONE=$ZONE python generate_and_test.py --model $MODEL --exp_dir $EXP_DIR --temperature 1.0 \
        --save_file_name "tests" --raw_dataset_config $DATASET_CONFIG --seed 1