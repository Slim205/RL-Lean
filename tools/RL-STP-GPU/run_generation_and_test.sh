#!/bin/bash
#SBATCH --job-name=stprepo
#SBATCH --nodes=1  
#SBATCH --ntasks-per-node=1
#SBATCH --gpus-per-node=1
#SBATCH --cpus-per-task=12
#SBATCH --time=01:00:00
#SBATCH --mem=24GB
#SBATCH --partition=gpu_test  
#SBATCH --export=ALL 

module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL

nohup python generate_and_test.py  --model  /n/netscratch/amin_lab/Lab/slim/STP/storage/v4/round11/RL_model  --exp_dir /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results_V4_11_32 --temperature 1.0 --save_file_name "tests" --raw_dataset_config dataset_configs/miniF2F_ProofNet.json --seed 1 > ../storage/logs/v4_11_32.log 2>&1 &
python generate_and_test.py  --model  /n/netscratch/amin_lab/Lab/slim/STP/storage/v4/round6/RL_model  --exp_dir /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results_V4_6_32 --temperature 1.0 --save_file_name "tests" --raw_dataset_config dataset_configs/miniF2F_ProofNet.json --seed 1 

/n/netscratch/amin_lab/Lab/slim/STP/storage/v2/round6/RL_model
python summary.py --log_path /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results_V4_10_32/generated_proofs_tests.jsonl.gz --split miniF2F --max_iter 32
python summary.py --log_path /n/netscratch/amin_lab/Lab/slim/STP/benchmark_results1/generated_proofs_tests.jsonl.gz --split proofnet --max_iter 32


