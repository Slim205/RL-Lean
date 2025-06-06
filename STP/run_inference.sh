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
        ray start --head --port=6379  
        sleep 3000000000

    else
        sleep 10
        echo "Node 1"
        ray start --address='$HEAD_NODE':6379 
        sleep 30000000000
    fi
'