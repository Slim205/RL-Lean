#!/bin/bash
source .bash_alias.sh
TPU_NAME=$(curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/description)
ZONE_FULL_PATH=$(curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/zone)
ZONE=$(echo "$ZONE_FULL_PATH" | awk -F'/' '{print $NF}')

gcloud compute tpus tpu-vm ssh $TPU_NAME --zone $ZONE --worker=all \
--command "source ~/venv310/bin/activate; ray stop; cd ~/STP; mkdir -p ~/.logs; \\
HUGGING_FACE_HUB_TOKEN=$HUGGING_FACE_HUB_TOKEN WANDB_API_KEY=$WANDB_API_KEY python levanter/examples/weighted_lm.py \\
--config_path levanter/config/sft.yaml \\
--trainer.checkpointer.base_path $STORAGE/SFT_ckpt \\
--hf_save_path $STORAGE/SFT \\
--train_data $STORAGE/data/SFT/mathlib_leanworkbook.json \\
--train_data_cache_dir $STORAGE/data/SFT/mathlib_leanworkbook_cache \\
--eval_data $STORAGE/data/SFT/eval.json \\
--eval_data_cache_dir $STORAGE/data/SFT/eval_cache &> ~/.logs/sft.log"