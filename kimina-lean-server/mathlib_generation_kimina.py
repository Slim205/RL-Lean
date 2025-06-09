from datasets import load_dataset
from transformers import AutoModelForCausalLM, AutoTokenizer
from tqdm import tqdm

def generate_kimina(model_name, input_list):
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        device_map="auto",
        torch_dtype="bfloat16"
    ).eval()
    formatted_inputs = []
    for sample in input_list:
        messages = [
            {"role": "system", "content": "You are an expert in mathematics and Lean 4."},
            {"role": "user", "content": sample}
        ]
        formatted_input = tokenizer.apply_chat_template(
            messages,
            tokenize=False,  
            add_generation_prompt=True  
        )
        formatted_inputs.append(formatted_input)
    outputs = []
    for inputs_batch in tqdm(formatted_inputs, desc="Processing batches"):
        inputs = tokenizer(inputs_batch, return_tensors="pt").to("cuda:0")
        outputs_batch = model.generate(
            **inputs,
            pad_token_id=tokenizer.eos_token_id,
            max_new_tokens=1024,
            top_p=1,
            do_sample=True
        )
        outputs.append(outputs_batch[0])

    proofs = [
        tokenizer.decode(out, skip_special_tokens=True).split('lean4')[1].split('`')[0]
        for out in outputs
    ]
    return proofs
def prompt(sample):
    header ="import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\n open BigOperators Real Nat Topology Rat\n"
    sample['input'] = f"Complete the following Lean 4 code :\n```lean4\n{header}{sample['theorem']}"
    return sample

n= 100
pass_rate = 32
model_name = "AI-MO/Kimina-Prover-Preview-Distill-1.5B"
dataset = load_dataset("Slim205/mathlib_benchmark",split='train').select(range(n))
dataset = dataset.map(prompt)
redundant_list=[]
for example in dataset:
    redundant_list.extend([example['input']] * pass_rate)
proofs = generate_kimina(model_name, redundant_list)

