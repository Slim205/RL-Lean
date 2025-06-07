from datasets import load_dataset
import re
from collections import defaultdict

# Load the dataset
dataset = load_dataset("kfdong/STP_Lean_0320", split="train")

def extract_lean_header(text):
    """
    Extract the Lean 4 header from the prompt text.
    This includes all lines between ```lean4 and the first occurrence of 'theorem'.
    """
    match = re.search(r"```lean4(.*?)theorem", text, re.DOTALL)
    if match:
        header = match.group(1).strip()
        return header
    return None

# Dictionary to count headers
header_counts = defaultdict(int)

# Process all samples
for sample in dataset:
    text = sample["prompt"]
    header = extract_lean_header(text)
    if header:
        header_counts[header] += 1

# Convert defaultdict to regular dict
header_counts = dict(header_counts)

# Print the number of unique headers and a few examples
print(f"Total unique headers found: {len(header_counts)}\n")
for i, (header, count) in enumerate(header_counts.items()):
    print(f"--- Header {i+1} (used {count} times) ---\n{header}\n")
    if i >= 4:  # Print only the first 5 for preview
        break
# --- Header 1 (used 3155573 times) ---
# import Mathlib
# import Aesop
# set_option maxHeartbeats 0
# open BigOperators Real Nat Topology Rat