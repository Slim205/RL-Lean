from datasets import load_dataset
from collections import defaultdict

# Load dataset with multiple processes and caching
dataset = load_dataset("Slim205/lean_workbook_RL", split="train")
def get_prompt_workbook(data) :
    text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
                header= 'import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n',
                formal_statement=data['formal_statement'].split('sorry')[0].strip(),
            )
            
    return text

train = dataset.select(range(88000))
