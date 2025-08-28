module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env 
cd /n/netscratch/amin_lab/Lab/slim/
ray stop

ray start --address='holygpu8a22102:6379'

ray start --head --port=6379 

module load cuda/12.4.1-fasrc01
module load cudnn/9.1.1.17_cuda12-fasrc01 
conda activate /n/netscratch/amin_lab/Lab/slim/env_verl
cd /n/netscratch/amin_lab/Lab/slim/

cd /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer

python RL_step1_generate.py --model "/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/tsw6rwex/step-229" --exp_dir "../storage/STP_LeanWorkbook_merged/round0" --seed 0  --temperature 1.0 --dataset_config "./dataset_configs/leanworkbook_v2.json"  --sampler 'Sampler_base' --conjecture_multiplier 1 --samples_per_statement 8 --statements_per_round 0 

pkill -9 -f 'python' -u sbarkallah
pkill -9 -f 'python' -u sbarkallah
pkill -9 -f 'repl' -u sbarkallah
pkill -9 -f 'lake' -u sbarkallah
top  -u sbarkallah 

 
nohup bash run_deepseek7b_llm.sh > out603_201V44.log 2>&1 &
nohup bash run_conjecture.sh > out104v40.log 2>&1 &


nohup bash RL/run_SFT2.sh  > ./storage/logs/202_prover_V5.log 2>&1 &
nohup uvicorn gpu_server:app --host 0.0.0.0 --port 8000 > gpu_603V40.log 2>&1 &
nohup bash run_RL_steps_function.sh  > ../storage/logs/stp_v4_ROUND0.log 2>&1 &

nohup bash run_RL_steps_function.sh  > ./storage/logs/V2_round7.log 2>&1 &

nohup sh eval/eval.sh -i datasets/sft_V6_1.jsonl -s test -m deepseek-ai/DeepSeek-Prover-V1.5-SFT -o results/sft_V6/SFT-64-Part1 -n 64 -c 64 -g 4 > sft_v6_64_1.log 2>&1 &

sh eval/eval2.sh -i datasets/minif2f.jsonl -s test -m kfdong/STP_model_Lean_0320 -o results/conjecture/STP -n 1 -c 64 -g 4
sh eval/eval2.sh -i datasets/leanworkbook_train_6K.jsonl -s test -m kfdong/STP_model_Lean_0320 -o results/conjecture/STP-6K-train -n 1 -c 64 -g 4

python model_merger.py merge \
    --backend fsdp \
    --local_dir /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/conjecture/conjecture_V28/global_step_560/actor \
    --target_dir ./conjecture_V28 \
    --hf_model_path kfdong/STP_model_Lean_0320


python model_merger.py merge \
    --backend fsdp \
    --local_dir /n/netscratch/amin_lab/Lab/slim/verl/examples/ppo_trainer/checkpoints/leanworkbook/leanworkbook_V44/global_step_360/actor \
    --target_dir ./leanworkbookV44_320 \
    --hf_model_path /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/xihn4b4x/step-100

    deepseek-ai/DeepSeek-Prover-V1.5-SFT 

cd ..
conda activate env_verl/
cd verl/scripts/

cd ..
conda activate env/
cd Goedel-Prover
sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/verl/scripts/leanworkbookV44_320 -o results/minif2f/leanworkbookV44_320 -n 1 -c 32 -g 1
sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m kfdong/STP_model_Lean_0320  -o results/minif2f/STP-1 -n 1 -c 32 -g 1

nohup sh eval_conj/eval.sh -i eval_conj/leanworkbook_test_v2.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/hccrdu5o/step-221 -o storage/conj_eval/conjecture_V2 -n 1 -c 64 -g 4 > conj_eval.log 2>&1 &
sh eval/eval2.sh -i datasets/leanworkbook_test_v2.jsonl -s test -m ../Lean/storage/Expert_V2/round6/RL_model -o results/conjecture/Expert-iter-V2-round6 -n 1 -c 64 -g 4

CUDA_VISIBLE_DEVICES=1  sh eval/eval.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/p6wj6201/step-2700 -o results/minif2f/SFT_prover_V5_2700 -n 1 -c 32 -g 1
sh eval/eval_3.sh -i datasets/minif2f.jsonl -s test -m /n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/xihn4b4x/step-100 -o results/minif2f/SFT_prover_V6-100 -n 1 -c 32 -g 1

nohup python -m server > log102v40.log 2>&1 & 