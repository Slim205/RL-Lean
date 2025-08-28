import os
import fire
import json
import shutil

def get_training_config(model_name_or_path, wandb_id, max_iters, CURRENT_EXP_DIR, batch_size):
    training_config = {
        'trainer.wandb.project': 'Expert-Iter',
       # 'trainer.wandb.resume': 'must',
        'trainer.wandb.id': wandb_id,
        'trainer.num_train_steps': max_iters,
        'trainer.train_batch_size': batch_size,
        'trainer.checkpointer.base_path': os.path.join(CURRENT_EXP_DIR, 'checkpoints'),
        'train_data': os.path.join(CURRENT_EXP_DIR, 'data', 'train.json'),
        'train_data_cache_dir': os.path.join(CURRENT_EXP_DIR, 'data', 'train_cache'),
        'eval_data': os.path.join(CURRENT_EXP_DIR, 'data', 'test.json'),
        'eval_data_cache_dir': os.path.join(CURRENT_EXP_DIR, 'data', 'test_cache'),
        'model_name_or_path': model_name_or_path,
        'save_freq': max_iters - 1,
        'config_path': 'RL_base.yaml',
        'hf_save_path': os.path.join(CURRENT_EXP_DIR, 'hf_checkpoints'),
        'optimizer.learning_rate': 1e-5,
        'optimizer.warmup': min(max_iters - 1, 5),
    }
    return training_config


def train(model_name_or_path, CURRENT_EXP_DIR,batch_size=512):

    path_to_verify =  os.path.join(CURRENT_EXP_DIR, 'RL_model','config.json')
    if os.path.exists(path_to_verify):
        exit(0)

    train_path = os.path.join(CURRENT_EXP_DIR, "data", "train.json")
    with open(train_path, "r", encoding="utf-8") as f:
        train_ds = json.load(f)

    # load data to compute number of steps
    wandb_id = CURRENT_EXP_DIR.split('storage')[1][1:].replace('/', '_')
    print("wandb_id:", wandb_id)

    max_iters = max(len(train_ds) // batch_size, 5)
    print("Number of training examples:", len(train_ds))
    print("Max iters:", max_iters)

    training_config = get_training_config(model_name_or_path, wandb_id, max_iters, CURRENT_EXP_DIR,batch_size)
    training_cmd = f'python levanter/examples/weighted_lm.py'
    for k, v in training_config.items():
        if v is None:
            training_cmd += f' --{k}'
        else:
            training_cmd += f' --{k} {v}'
    print("Running command:\n", training_cmd)
    os.system(training_cmd)

    old_path = os.path.join(CURRENT_EXP_DIR,"hf_checkpoints",wandb_id,f'step-{max_iters-1}')
    new_dir =  os.path.join(CURRENT_EXP_DIR, 'RL_model')
    print(f'Move model from {old_path} to {new_dir}')
    shutil.move(old_path, new_dir)
    
if __name__ == "__main__":
    fire.Fire(train)
