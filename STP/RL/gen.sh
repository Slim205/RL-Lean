ssh holy8a14106


module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/
ray start --address='holygpu8a22606:6379'

ssh holygpu8a22404
ssh holygpu8a22105
ssh holygpu8a22201
ssh holygpu8a22503
ssh holygpu8a22401
ssh holygpu8a22606
ssh holy8a14104
ssh holy8a14106
ssh holy8a14107
ssh holy8a14103
ssh holy8a14102
