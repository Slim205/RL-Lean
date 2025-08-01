START_STATEMENT = '<statement>'
START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'
PROVER_PROMPT = (
    "Complete the following Lean 4 code:\n\n```lean4\n"
    "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\n"
    "open BigOperators Real Nat Topology Rat\n"
)
def extract_theorem(inputs):
    try:
        return 'theorem' + inputs.split('theorem')[1].split(' sorry')[0]
    except:
        return "None"


def get_prompt(theorem):
    shared_lemma = ''
    easy_theorem = theorem
    prompt = (
        f"{PROVER_PROMPT}"
        f"{INVOKED_LEMMA}\n{shared_lemma.strip()}\n"
        f"{START_LEMMA_STMT}\n{easy_theorem.strip()}\n"
        f"{START_THM}\n theorem"
    )
    return prompt
from datasets import load_dataset
ds = load_dataset('Slim205/lean_workbook_RL_V20')
data = []
def map1(sample) : 
    sample['prompt'] = get_prompt(extract_theorem(sample['theorem']))
    return sample

ds = ds.map(map1)
ds.push_to_hub('Slim205/lean_workbook_RL_V20_conj')