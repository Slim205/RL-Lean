
ssh holy8a14102
#ssh sbarkallah@holygpu8a22604
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/


module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env_verl
cd /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer
pkill -9 -f 'python' -u sbarkallah
pkill -9 -f 'python' -u sbarkallah
pkill -9 -f 'repl' -u sbarkallah
pkill -9 -f 'lake' -u sbarkallah
top  -u sbarkallah

(601 was used instead of 606)
nohup bash run_deepseek7b_llm.sh > out606V333333.log 2>&1 &


sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/minif2f/deepseek-V4-SFT-1 -n 1 -c 32 -g 4
sh eval/eval.sh -i datasets/mathlib.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/mathlib/SFT-1 -n 1 -c 100 -g 4 
sh eval/eval.sh -i datasets/leanworkbook.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/leanworkbook/SFT-1 -n 1 -c 100 -g 4 

sh eval/eval.sh -i datasets/leanworkbook_full.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/leanworkbook_full/SFT-1 -n 1 -c 100 -g 4 

nohup sh eval/eval.sh -i datasets/mathlib_train.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/mathlib_train/SFT-32 -n 32 -c 100 -g 4 > eval504.log 2>&1 &
 

sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/model_Vtest -o results/minif2f/deepseek-Vtest-RL -n 1 -c 100 -g 4

sh eval/eval.sh -i datasets/mathlib.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/model_V13 -o results/mathlib/deepseek-V13-RL -n 1 -c 100 -g 4

/n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/Deepseek_RL_2/deepseek_RL_3/global_step_240/actor

python model_merger.py merge \
    --backend fsdp \
    --local_dir /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/deepseek_RL_4/mathlibV21/global_step_160/actor \
    --target_dir ./model_V21  \
    --hf_model_path deepseek-ai/DeepSeek-Prover-V1.5-SFT

29.51 Vs 31.15 Vs 31.15 Vs 30.75

cd ..
conda deactivate 
conda activate env_verl/
cd verl/scripts/

cd ..
cd ..
conda deactivate 
conda activate env/
cd Goedel-Prover
sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/model_V21 -o results/minif2f/deepseek-V21-RL -n 1 -c 100 -g 4



nohup bash run_deepseek7b_llm.sh > out601V111111.log 2>&1 &


# 401 is in use not 102
nohup python -m server > log401VVV3.log 2>&1 & 

nohup python  trace_data_tactics.py  > traceV202.log 2>&1 &

107 / 401 : normal
102 : all tactics