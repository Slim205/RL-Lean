import torch
import json
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams  # vLLM for faster inference

def read_jsonl_file(file_path):
    """Read a .jsonl file and return a list of dictionaries."""
    with open(file_path, 'r', encoding='utf-8') as f:
        return [json.loads(line) for line in f]

# Load the model and tokenizer
model_name = "deepseek-ai/DeepSeek-Prover-V1.5-SFT"
tokenizer = AutoTokenizer.from_pretrained(model_name)

# Initialize vLLM (much faster than standard HF pipeline)
llm = LLM(
    model=model_name,
    dtype="bfloat16",
    gpu_memory_utilization=0.9
)

# Define sampling parameters
sampling_params = SamplingParams(
    temperature=1.0,
    max_tokens=1024,
    top_p=1,
)

# Load dataset
data_path = "/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/datasets/minif2f.jsonl"
dataset = read_jsonl_file(data_path)

# Initialize Lean4 client
import nest_asyncio
from client import Lean4Client
nest_asyncio.apply()
client = Lean4Client(base_url="http://0.0.0.0:12332")
LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

pass_number=1
input_list =[]
for data in dataset:
    if data['split'] == 'test' : 
        header = data['header']
        theorem = data['formal_statement']  # Fixed typo in variable name
        input_text= "Complete the following Lean 4 code with explanatory comments preceding each line of code:\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
                header=data.get('header', LEAN4_DEFAULT_HEADER),
                informal_prefix=data.get('informal_prefix', str()),
                formal_statement=data['formal_statement'],
            )
        
#        input_text = f"Complete the following Lean 4 code:\n```lean4\n{header}\n{theorem}\n```"
        for _ in range(pass_number) : 
            input_list.append(input_text)        
print(len(input_list))
outputs = llm.generate(input_list, sampling_params)
        
        # Extract proofs
proofs = []
for output in outputs:
    generated_text = output.outputs[0].text
    try:
        # More robust proof extraction
        proof_part = generated_text.split("```lean4")[-1].split("```")[0].strip()
        proofs.append(proof_part)
    except Exception as e:
        print(f"Error parsing proof: {e}")

        # Verify proofs
verification_requests = [
    {"proof": proof, "custom_id": str(i)} 
    for i, proof in enumerate(proofs) if proof
]
        
response = client.verify(verification_requests, timeout=200)
            
            # Process results
def change_result(results):
    transformed_results = []
    for item in results:
        response = item["response"]
        messages = response["messages"]
        
        transformed = {
            "custom_id": item['custom_id'],
            "complete": (
                not any(m["severity"] == "error" for m in messages) and 
                not any("sorry" in m.get("data", "").lower() for m in messages) and
                not any("failed" in m.get("data", "").lower() for m in messages 
                if m.get("severity") == "warning")
            )
        }
        transformed_results.append(transformed)
    return transformed_results
            
compilation_results = change_result(response['results'])

print(f"Verification results: {compilation_results}")