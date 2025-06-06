import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
# Load the DeepSeek Prover model from Hugging Face
model_name = "deepseek-ai/DeepSeek-Prover-V1.5-SFT"  
tokenizer = AutoTokenizer.from_pretrained(model_name)

# Let Hugging Face `accelerate` split the model across GPUs
model = AutoModelForCausalLM.from_pretrained(
    model_name,
    device_map="auto",  # Automatically splits across available GPUs
    torch_dtype="auto"  # Automatically selects bf16/fp16/fp32
)

# Check how the model was split
print(f"Model device map: {model.hf_device_map}")

# Define the Lean4 theorem
theorem = """
theorem infinite_subsequence_property (a : ℕ → ℝ) :
  ∃ (f : ℕ → ℕ), StrictMono f ∧
    (StrictMono (a ∘ f) ∨ (∀ n, a (f n) = a (f 0)) ∨ StrictAnti (a ∘ f)) :=
"""

# Generate proof
input_text = f"Prove the following Lean4 theorem:\n{theorem}"
inputs = tokenizer(input_text, return_tensors="pt").to("cuda:0")  # Input on GPU 0

outputs = model.generate(
    inputs.input_ids,
    max_length=1024,
    num_return_sequences=1,
    temperature=1,
)

# Decode and print
code1 = tokenizer.decode(outputs[0], skip_special_tokens=True)


import nest_asyncio
from client import Lean4Client

nest_asyncio.apply()

client = Lean4Client(base_url="http://0.0.0.0:12332")


response = client.verify([
    {"proof": code1, "custom_id": "1" } 
], timeout=200)

def change_result(results):
    transformed_results = []
    for item in results:

        response = item["response"]
        messages = response["messages"]
        
        transformed = {
            "custom_id" : item['custom_id'],
            "complete": (not any(m["severity"] == "error" for m in messages) and 
                        not any("sorry" in m.get("data", "") for m in messages) and
                        not any("failed" in m.get("data", "") for m in messages if m["severity"] == "warning"))
        }

        
        transformed_results.append(transformed)

    return transformed_results

# Transform the verification results
compilation_results = change_result(response['results'])
print(compilation_results)

