from transformers import AutoModelForCausalLM, AutoTokenizer

model_path = "/n/netscratch/amin_lab/Lab/slim/STP/storage/SFT/xihn4b4x/step-100"
model2 = AutoModelForCausalLM.from_pretrained(model_path)
model_path ='deepseek-ai/DeepSeek-Prover-V1.5-SFT'
model1 = AutoModelForCausalLM.from_pretrained(model_path)

state_dict1 = model1.state_dict()
state_dict2 = model2.state_dict()

# Make a new state dict with averaged weights
avg_state_dict = {}
for key in state_dict1.keys():
    avg_state_dict[key] = (state_dict1[key] + state_dict2[key]) / 2

# Load into model1’s architecture
model1.load_state_dict(avg_state_dict)

# Now model1 is your averaged model
save_path = "./RL_model/averaged_model"
model1.save_pretrained(save_path)
print(f"Averaged model saved to {save_path}")
from transformers import AutoTokenizer
tokenizer = AutoTokenizer.from_pretrained(model2_path)  # usually same as base
tokenizer.save_pretrained(save_path)
