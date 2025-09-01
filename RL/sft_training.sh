ray stop

python levanter/examples/weighted_lm.py \
    --config_path ./sft.yaml \
    --trainer.checkpointer.base_path ./storage/conjecturer_V1/SFT_ckpt \
    --hf_save_path ./storage/conjecturer_V1/SFT \
    --train_data ./storage/conjecturer_V1/data/prover/train.json \
    --train_data_cache_dir ./storage/conjecturer_V1/data/prover/train_cache \
    --eval_data ./storage/conjecturer_V1/data/prover/test.json \
    --eval_data_cache_dir ./storage/conjecturer_V1/data/prover/test_cache 
 