#!/bin/bash
#SBATCH --job-name=stprepo
#SBATCH --nodes=2                     
#SBATCH --ntasks-per-node=1           
#SBATCH --cpus-per-task=8           
#SBATCH --time=00:30:00
#SBATCH --mem=128GB
#SBATCH --export=ALL
#SBATCH --gpus-per-node=1
#SBATCH --partition=gpu_test

export SLURM_STEP_TASKS_PER_NODE=$SLURM_NTASKS_PER_NODE
export SLURM_JOB_NUM_NODES=$SLURM_NNODES


module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL

HEAD_NODE=$(scontrol show hostname $SLURM_NODELIST | head -n1)

srun bash -c '
    if [ $SLURM_NODEID -eq 0 ]; then
        echo "Node 0"
        ray stop
        ray start --head --port=6379 --num-cpus=8 
        sleep 30
        bash run_RL_steps_function.sh
    else
        sleep 20
        echo "Node 1"
        ray start --address='$HEAD_NODE':6379  --num-cpus=8 
        sleep 3000000
    fi
'
