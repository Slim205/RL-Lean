#!/bin/bash
#SBATCH --job-name=stprepo
#SBATCH --time=12:00:00
#SBATCH --mem=128GB 
#SBATCH --export=ALL
#SBATCH --partition=gpu_test --nodes=1 --ntasks-per-node=1 --cpus-per-task=2 --gpus-per-node=1

export SLURM_STEP_TASKS_PER_NODE=$SLURM_NTASKS_PER_NODE
export SLURM_JOB_NUM_NODES=$SLURM_NNODES

ssh holygpu8a22101

module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL

echo "Node 0"
ray stop
ray start --head --port=6379  
sleep 20
bash run_RL_steps_function.sh
