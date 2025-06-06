#!/bin/bash
#SBATCH --job-name=stprepo
#SBATCH --time=01:00:00
#SBATCH --mem=25GB 
#SBATCH --export=ALL
#SBATCH --partition=gpu_test --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1

export SLURM_STEP_TASKS_PER_NODE=$SLURM_NTASKS_PER_NODE
export SLURM_JOB_NUM_NODES=$SLURM_NNODES

module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL

HEAD_NODE=$(scontrol show hostname $SLURM_NODELIST | head -n1)

srun  bash -c '
    echo "Node 0"
    ray stop
    ray start --head --port=6379 --num-cpus=16 --num-gpus 1
    sleep 20
    bash run_RL_steps_function.sh
'

wait