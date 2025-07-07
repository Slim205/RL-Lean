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

nohup bash run_deepseek7b_llm.sh > out301V13.log 2>&1 &


sh eval/eval.sh -i datasets/leanworkbook.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/leanworkbook_test/deepseek-SFT -n 1 -c 64 -g 1
nohup sh eval/eval.sh -i datasets/leanworkbook_hinter.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/leanworkbook_hinter/SFT-32 -n 32 -c 64 -g 1 > eval603_pass32.log 2>&1 &
sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/model_Vtest -o results/minif2f/deepseek-Vtest-RL -n 1 -c 100 -g 4


python model_merger.py merge \
    --backend fsdp \
    --local_dir /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/leanworkbook/leanworkbook_V12/global_step_120/actor \
    --target_dir ./leanworkbook_V12_120  \
    --hf_model_path deepseek-ai/DeepSeek-Prover-V1.5-SFT

30.75 Vs 29.51 Vs 31.15 Vs 31.15 Vs 30.75

cd ..
conda deactivate 
conda activate env_verl/
cd verl/scripts/

cd ..
cd ..
conda deactivate 
conda activate env/
cd Goedel-Prover
sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/leanworkbook_V12_120 -o results/minif2f/leanworkbook_V12_120 -n 1 -c 32 -g 1
33.20 vs 34.02 Vs 37.3 Vs 37.70
35.66 35.25 37.3 35.66
nohup bash run_deepseek7b_llm.sh > out301V9_200.log 2>&1 &

nohup python -m server > log102V6.log 2>&1 & 

nohup python trace_data_tactics_lean.py  > trace401.log 2>&1 & 
