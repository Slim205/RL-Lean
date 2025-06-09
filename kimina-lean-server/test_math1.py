from datasets import load_dataset

# Load the original dataset
dataset = load_dataset("Slim205/mathlib", split='train')

# Define the filter function
def filter2(sample):
    return ':= by'  in sample['target'] # 

# Apply the filter
filtered_dataset = dataset.filter(filter2)

# Print information about the filtered dataset
print(f"Filtered dataset size: {round(len(filtered_dataset) / len(dataset) * 100)}") # 15%

# Push the filtered dataset to the Hub
filtered_dataset.push_to_hub('Slim205/mathlib_anomaly')
