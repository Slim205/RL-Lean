module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL
python generate_and_test.py  --model kfdong/STP_model_Lean_0320 --exp_dir /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results --temperature 1.0 --save_file_name "tests" --raw_dataset_config dataset_configs/miniF2F_ProofNet.json --seed 1 --cpu 18 --gpu 2

python generate_and_test.py  --model EleutherAI/pythia-70m --exp_dir /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results --temperature 1.0 --save_file_name "tests" --raw_dataset_config dataset_configs/miniF2F_ProofNet.json --seed 1 --cpu 8 --gpu 2


# update the function that uses all_execute code and it will make it work

# change the batch size and make it work

# reinstall lean