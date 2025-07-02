from datasets import load_dataset

# 1. Load the dataset (all splits)
ds = load_dataset("kfdong/STP_Lean_SFT")

# 2. Grab the train split
train_ds = ds["train"]

# 3. Keep only examples whose prompt includes the substring "lean_workbook"
train_filtered = train_ds.filter(lambda ex: "lean_workbook" in ex["prompt"])

# ───────────────────────────────
# Optional: drop everything else and push / convert
# ───────────────────────────────
# • To inspect:
print(train_filtered[0])             # first example after filtering
print(len(train_filtered))           # how many remain

# • If you want a pandas DataFrame:
#   df = train_filtered.to_pandas()

# • If you want to push the filtered set back to the Hub:
#   train_filtered.push_to_hub("your-username/Lean-workbook-filtered")
