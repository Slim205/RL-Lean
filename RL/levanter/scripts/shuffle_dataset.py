import json
import random
import argparse

# Define the function to shuffle the dataset
def shuffle_dataset(input_file: str, output_file: str, seed: int):
    with open(input_file, "r") as f:
        data = json.load(f)
    
    random.seed(seed)
    random.shuffle(data)
    
    with open(output_file, "w") as f:
        json.dump(data, f)

# Define the argument parser
parser = argparse.ArgumentParser(description="Shuffle a dataset in JSON format")
parser.add_argument("--input_file", type=str, required=True, help="Path to the input JSON file")
parser.add_argument("--output_file", type=str, required=True, help="Path to the output JSON file")
parser.add_argument("--seed", type=int, default=42, help="Random seed for shuffling")
args = parser.parse_args()

# Call the function with the provided arguments
shuffle_dataset(args.input_file, args.output_file, seed=args.seed)
