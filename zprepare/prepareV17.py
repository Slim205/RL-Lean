import numpy as np
from datasets import DatasetDict,load_dataset
from collections import Counter

# Load your dataset
ds = load_dataset("Slim205/mathlib_RL_exp_length")["train"]

def simple_progressive_sort(dataset, batch_size=256):
    """
    Simple sorting with fixed progression:
    - Level 0: starts at 256, decreases by 10 each batch
    - Level 2: starts at 0, increases by 7 each batch  
    - Level 1: fills the rest, overflow goes to level 2
    """
    # Convert to pandas
    df = dataset.to_pandas()
    original_counts = Counter(df['diff_level'])
    print(f"Original distribution: {dict(original_counts)}")
    
    # Get all indices for each level
    indices_0 = df[df['diff_level'] == 0].index.tolist()
    indices_1 = df[df['diff_level'] == 1].index.tolist() 
    indices_2 = df[df['diff_level'] == 2].index.tolist()
    
    # Shuffle each group
    np.random.shuffle(indices_0)
    np.random.shuffle(indices_1)
    np.random.shuffle(indices_2)
    
    # Track usage
    used_0, used_1, used_2 = 0, 0, 0
    total_0, total_1, total_2 = len(indices_0), len(indices_1), len(indices_2)
    
    total_samples = len(df)
    num_batches = (total_samples + batch_size - 1) // batch_size
    
    sorted_indices = []
    
    for batch_idx in range(num_batches):
        # Calculate current batch size
        start_idx = batch_idx * batch_size
        end_idx = min(start_idx + batch_size, total_samples)
        current_batch_size = end_idx - start_idx
        
        # Target counts based on your rules
        target_0 = max(0, 256 - (batch_idx * 10))  # Start 256, decrease by 10
        target_2 = batch_idx * 4  # Start 0, increase by 7
        target_1 = current_batch_size - target_0 - target_2  # Fill the rest
        #print(batch_idx,target_0,target_1,target_2)
        # Adjust based on available samples
        remaining_0 = total_0 - used_0
        remaining_1 = total_1 - used_1
        remaining_2 = total_2 - used_2
        
        # Actual counts (can't exceed what's available)
        actual_0 = min(target_0, remaining_0, current_batch_size)
        actual_2 = min(target_2, remaining_2, current_batch_size - actual_0)
        actual_1 = min(target_1, remaining_1, current_batch_size - actual_0 - actual_2)
        
        # If level 1 is full (not enough samples), fill remainder with level 2
        remaining_slots = current_batch_size - actual_0 - actual_1 - actual_2
        if remaining_slots > 0 and remaining_2 > actual_2:
            additional_2 = min(remaining_slots, remaining_2 - actual_2)
            actual_2 += additional_2
            remaining_slots -= additional_2
        
        # If still slots remaining, use any available samples
        if remaining_slots > 0:
            if remaining_0 > actual_0:
                add_0 = min(remaining_slots, remaining_0 - actual_0)
                actual_0 += add_0
                remaining_slots -= add_0
            if remaining_slots > 0 and remaining_1 > actual_1:
                add_1 = min(remaining_slots, remaining_1 - actual_1)
                actual_1 += add_1
                remaining_slots -= add_1
            if remaining_slots > 0 and remaining_2 > actual_2:
                actual_2 += remaining_slots
        
        # Build this batch
        batch_indices = []
        
        # Add level 0
        if actual_0 > 0:
            batch_indices.extend(indices_0[used_0:used_0 + actual_0])
            used_0 += actual_0
            
        # Add level 1  
        if actual_1 > 0:
            batch_indices.extend(indices_1[used_1:used_1 + actual_1])
            used_1 += actual_1
            
        # Add level 2
        if actual_2 > 0:
            batch_indices.extend(indices_2[used_2:used_2 + actual_2])
            used_2 += actual_2
        
        # Shuffle within batch
        np.random.shuffle(batch_indices)
        sorted_indices.extend(batch_indices)
        
        # Print batch info
        pct_0 = (actual_0 / current_batch_size) * 100
        pct_1 = (actual_1 / current_batch_size) * 100  
        pct_2 = (actual_2 / current_batch_size) * 100
        print(f"Batch {batch_idx:2d}: L0={actual_0:3d}({pct_0:4.1f}%) L1={actual_1:3d}({pct_1:4.1f}%) L2={actual_2:3d}({pct_2:4.1f}%) Total={current_batch_size}")
    
    # Verify we used everything exactly once
    print(f"\nUsage verification:")
    print(f"Level 0: {used_0}/{total_0} ({'✓' if used_0 == total_0 else '✗'})")
    print(f"Level 1: {used_1}/{total_1} ({'✓' if used_1 == total_1 else '✗'})")
    print(f"Level 2: {used_2}/{total_2} ({'✓' if used_2 == total_2 else '✗'})")
    
    # Create sorted dataset
    sorted_df = df.iloc[sorted_indices].reset_index(drop=True)
    final_counts = Counter(sorted_df['diff_level'])
    print(f"Final distribution: {dict(final_counts)}")
    
    from datasets import Dataset
    return Dataset.from_pandas(sorted_df)

# Apply the sorting
print("Applying simple progressive sorting...")
np.random.seed(42)
sorted_ds = simple_progressive_sort(ds, batch_size=256)

# Verify counts match
print(f"\nFinal verification:")
print(f"Original: {dict(Counter(ds['diff_level']))}")
print(f"Sorted:   {dict(Counter(sorted_ds['diff_level']))}")
print(f"Match: {Counter(ds['diff_level']) == Counter(sorted_ds['diff_level'])}")

dataset_test = load_dataset("Slim205/mathlib_RL_exp_length", split='test')


ds2 = DatasetDict({'train'  : sorted_ds , 'test' : dataset_test })
print(ds2)

ds2.push_to_hub('Slim205/mathlib_RL_length_brackets')
