from transformers import AutoModelForCausalLM, AutoTokenizer

model_path = "/n/netscratch/amin_lab/Lab/slim/verl/scripts/leanworkbookV44_160"
model = AutoModelForCausalLM.from_pretrained(model_path)
tokenizer = AutoTokenizer.from_pretrained(model_path)

# Push directly to HF
model.push_to_hub("Slim205/Lean_prover_v1")
tokenizer.push_to_hub("Slim205/Lean_prover_v1")

from transformers import AutoModelForCausalLM, AutoTokenizer

model = AutoModelForCausalLM.from_pretrained("Slim205/Lean_prover_v1")
tokenizer = AutoTokenizer.from_pretrained("Slim205/Lean_prover_v1")

print("Model and tokenizer loaded successfully 🚀")
