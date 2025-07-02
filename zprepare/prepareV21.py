import numpy as np
from datasets import DatasetDict,load_dataset

ds = load_dataset("Goedel-LM/Lean-workbook-proofs")["train"]

import re

def clean_lean_code(code: str) -> str:
    # Remove everything between /- and -/, including multiline
    code = re.sub(r'/-(.|\n)*?-/', '', code)

    # Remove lines starting with --
    lines = code.splitlines()
    cleaned_lines = [line for line in lines if not line.strip().startswith('--')]

    # Join cleaned lines
    return '\n'.join(cleaned_lines).strip()
def update(x) : 
    text = clean_lean_code(x['full_proof'])
    theorem =  text.split(':= by')[0] + ':= by'
    proof = ''.join(text.split(':= by')[1:])
    return {
        'problem_id' : x['problem_id'],
        'theorem' : theorem ,
        'proof' : proof,
    }


ds2 = ds.map(update,remove_columns=ds.column_names)
print(ds2)
ds2.push_to_hub('Slim205/Lean-workbook-RL')