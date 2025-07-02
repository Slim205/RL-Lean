from datasets import load_dataset, Dataset

data_files="/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/datasets/minif2f.jsonl"

import json

data = []
with open(data_files, "r", encoding="utf-8") as f:
    for line in f:
        data.append(json.loads(line))

from datasets import Dataset, DatasetDict

# Step 1: Original dataset
dataset = Dataset.from_list(data)  # `data` is your list of dicts

# Step 2: Identify all unique split names
split_names = set(example["split"] for example in data)

# Step 3: Filter and create DatasetDict
split_dataset = DatasetDict({
    split_name: dataset.filter(lambda example: example["split"] == split_name)
    for split_name in split_names
})

# Optional: inspect the keys and sizes
print(split_dataset)

split_dataset.push_to_hub('Slim205/minif2f')