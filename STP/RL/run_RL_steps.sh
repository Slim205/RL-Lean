#!/bin/bash
#SBATCH --job-name=stprepo
#SBATCH --time=72:00:00
#SBATCH --mem=812GB 
#SBATCH --export=ALL
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=64 --gpus-per-node=4
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1
#SBATCH hetjob
#SBATCH --partition=gpu --nodes=1 --ntasks-per-node=1 --cpus-per-task=16 --gpus-per-node=1

export SLURM_STEP_TASKS_PER_NODE=$SLURM_NTASKS_PER_NODE
export SLURM_JOB_NUM_NODES=$SLURM_NNODES

ssh holygpu8a22203
module load python/3.12.5-fasrc01
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/STP/RL
ray stop
ray start --address=holygpu7c26106:6379 

HEAD_NODE=$(scontrol show hostname $SLURM_NODELIST | head -n1)

srun --het-group=0 bash -c '
    echo "Node 0"
    ray stop
    ray start --head --port=6379  
    sleep 20
    bash run_RL_steps_function.sh
' &
srun --het-group=1 bash -c '
    sleep 10
    echo "Node 1"
    ray start --address='$HEAD_NODE':6379  --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=2 bash -c ' 
    sleep 10
    echo "Node 2"
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=3 bash -c '
    sleep 10
    echo "Node 3"
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=4 bash -c '
    sleep 10
    echo "Node 4"
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=5 bash -c '
    sleep 10
    echo "Node 5"
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=6 bash -c '
    sleep 10
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=7 bash -c '
    sleep 10
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  
srun --het-group=8 bash -c '
    sleep 10 
    ray start --address='$HEAD_NODE':6379 --num-cpus=16 --num-gpus=1
    while true; do sleep 1000; done
' &  

wait