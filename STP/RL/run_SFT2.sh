ray stop

python levanter/examples/weighted_lm.py \
    --config_path levanter/config/sft.yaml \
    --trainer.checkpointer.base_path /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT_ckpt \
    --hf_save_path /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT \
    --train_data /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/SFT_prover_V5/train.json \
    --train_data_cache_dir /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/SFT_prover_V5/train_cache \
    --eval_data /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/SFT_prover_V5/test.json \
    --eval_data_cache_dir /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/SFT_prover_V5/test_cache 
