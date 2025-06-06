#!/bin/bash
#SBATCH --job-name=sft
#SBATCH --nodes=1               
#SBATCH --ntasks-per-node=1        
#SBATCH --gpus-per-node=1      
#SBATCH --cpus-per-task=16
#SBATCH --time=24:00:00
#SBATCH --mem=256GB
#SBATCH --partition=gpu
#SBATCH --export=ALL
#SBATCH --output=%x-%j.out       


export SLURM_STEP_TASKS_PER_NODE=$SLURM_NTASKS_PER_NODE
export SLURM_JOB_NUM_NODES=$SLURM_NNODES

module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01
conda activate /n/netscratch/amin_lab/Lab/slim/env
cd /n/netscratch/amin_lab/Lab/slim/STP

ray stop

/n/netscratch/amin_lab/Lab/slim/env/bin/python levanter/examples/weighted_lm.py \
    --config_path levanter/config/sft.yaml \
    --trainer.checkpointer.base_path /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT_ckpt \
    --hf_save_path /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT \
    --train_data /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/mathlib_leanworkbook.json \
    --train_data_cache_dir /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/mathlib_leanworkbook_cache \
    --eval_data /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/eval.json \
    --eval_data_cache_dir /n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/eval_cache 
