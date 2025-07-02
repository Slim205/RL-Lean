"""build_double_dataset.py

Create a new dataset that doubles every BLOCK-sized chunk of the train/validation
splits (processed → original) while:
  • Preserving the *test* split size/content.
  • Adding a `hint` boolean column everywhere:
        - processed examples → hint=True
        - original examples → hint=False (including test split)

The resulting DatasetDict is pushed to the 🤗 Hub under DST_REPO.
"""

from datasets import load_dataset, DatasetDict, concatenate_datasets


def process_input(example):
    """Append the first non‑empty line of the proof to the theorem statement."""
    first_line = example["proof"].split("\n")[0]
    if first_line == "":
        first_line = "\n" + example["proof"].split("\n")[1]

    # Ignore very short proofs (≤3 lines)
    if len(example["proof"].split("\n")) <= 3:
        first_line = ""

    example["theorem"] = example["theorem"] + first_line
    return example


SRC_DATASET = "Slim205/mathlib_RL_v3"
DST_REPO   = "Slim205/mathlib_RL_v4"
BLOCK      = 256

# ---------------------------------------------------------------------------
# 1. Load original dataset (all splits)
# ---------------------------------------------------------------------------

ds_all = load_dataset(SRC_DATASET)

# ---------------------------------------------------------------------------
# 2. Build new dataset with doubling & hint column
# ---------------------------------------------------------------------------

new_ds_all = DatasetDict()

for split_name, ds in ds_all.items():
    if split_name.lower() == "test":
        # Keep test data pristine, but add `hint=False` column
        new_ds_all[split_name] = ds.add_column("hint", [False] * len(ds))
        continue

    batches = []
    for start in range(0, len(ds), BLOCK):
        end = min(start + BLOCK, len(ds))
        indices = list(range(start, end))

        original_batch  = ds.select(indices)
        processed_batch = original_batch.map(process_input)

        # Add hint column
        processed_batch = processed_batch.add_column("hint", [True]  * len(processed_batch))
        original_batch  = original_batch.add_column("hint",  [False] * len(original_batch))

        # Append in required order: processed first, then original
        batches.extend([processed_batch, original_batch])

    # Combine batches per split
    new_ds_all[split_name] = concatenate_datasets(batches)

    # Sanity check
    expected = 2 * len(ds)
    actual   = len(new_ds_all[split_name])
    assert actual == expected, (
        f"{split_name} split size mismatch: expected {expected}, got {actual}")

# ---------------------------------------------------------------------------
# 3. Push the new dataset to the Hub
# ---------------------------------------------------------------------------

print(new_ds_all)
new_ds_all.push_to_hub(DST_REPO, private=False)
print("✅ New dataset (doubled with hint column) uploaded to", DST_REPO)
