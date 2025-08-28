from huggingface_hub import list_datasets, delete_repo, HfApi
import re

# Replace with your Hugging Face token (must have write or admin scope)
#HF_TOKEN = "your_hf_token_here"
USERNAME = "Slim205"

api = HfApi()

# List all datasets under your username
all_datasets = list_datasets(author=USERNAME)

# Filter datasets that contain 'chunk' (case-insensitive)
datasets_to_delete = [ds.id for ds in all_datasets if "chunk" in ds.id.lower()]

# Delete each one
for ds_id in datasets_to_delete:
    print(f"Deleting dataset: {ds_id}")
    delete_repo(repo_id=ds_id, repo_type="dataset")

print("Done.")
