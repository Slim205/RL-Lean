module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/

 
module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env_verl
cd /n/netscratch/amin_lab/Lab/slim/

cd /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer

pkill -9 -f 'python' -u sbarkallah
pkill -9 -f 'python' -u sbarkallah
pkill -9 -f 'repl' -u sbarkallah
pkill -9 -f 'lake' -u sbarkallah
top  -u sbarkallah 

nohup bash run_deepseek7b_llm.sh > out603V41.log 2>&1 &
nohup bash run_conjecture.sh > out501_104_105_V16.log 2>&1 &


nohup bash RL/run_SFT2.sh  > ./storage/logs/401_prover_V4.log 2>&1 &
nohup uvicorn gpu_server:app --host 0.0.0.0 --port 8000 > gpu_104V16.log 2>&1 &

nohup sh eval/eval.sh -i datasets/leanworkbook_test.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/sft_V1/SFT-test-64 -n 64 -c 64 -g 4 > sft_v1_test_64.log 2>&1 &
sh eval/eval2.sh -i datasets/minif2f.jsonl -s test -m kfdong/STP_model_Lean_0320 -o results/conjecture/STP -n 1 -c 64 -g 4
sh eval/eval2.sh -i datasets/leanworkbook_train_6K.jsonl -s test -m kfdong/STP_model_Lean_0320 -o results/conjecture/STP-6K-train -n 1 -c 64 -g 4

/n/netscratch/amin_lab/Lab/slim/verl/scripts/

python model_merger.py merge \
    --backend fsdp \
    --local_dir /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/conjecture/conjecture_V15/global_step_240/actor \
    --target_dir ./conjecture_V15_240 \
    --hf_model_path kfdong/STP_model_Lean_0320


python model_merger.py merge \
    --backend fsdp \
    --local_dir /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/leanworkbook/leanworkbook_V41/global_step_320/actor \
    --target_dir ./leanworkbookV41_320 \
    --hf_model_path deepseek-ai/DeepSeek-Prover-V1.5-SFT 

/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/r44t7p77/step-191

cd ..
conda activate env_verl/
cd verl/scripts/

cd ..
cd ..
conda activate env/
cd Goedel-Prover
sh eval/eval2.sh -i datasets/leanworkbook_test_v2.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/conjecture_V15_240 -o results/conjecture/conjecture_V15_240-test -n 1 -c 64 -g 4

sh eval/eval2.sh -i datasets/leanworkbook_test_v2.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/r44t7p77/step-191 -o results/conjecture/SFT_V1-191-test -n 1 -c 64 -g 4

sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/095w42f3/step-324 -o results/minif2f/SFT_prover_V4_324 -n 1 -c 32 -g 1

33.20 vs 34.02 Vs 37.3 Vs 37.70
35.66 35.25 37.3 35.66

nohup python -m server > log105v15.log 2>&1 & 