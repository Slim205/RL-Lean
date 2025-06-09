import json
from datasets import load_dataset, Dataset, DatasetDict
import os

def save_proofs(proofs, storage_file):
    """Save the proofs list to a file."""
    with open(storage_file, 'w') as f:
        json.dump(proofs, f)

def load_proofs(storage_file):
    """Load the proofs list from a file if it exists."""
    if os.path.exists(storage_file):
        with open(storage_file, 'r') as f:
            return json.load(f)
    return None

