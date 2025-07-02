from datasets import load_dataset , DatasetDict

ds = load_dataset("Slim205/mathlib_RL_v3")

def fe(sample) : 
    for x in ['linarith' ,'simp' , 'omega'] : 
        if x in sample['proof'] :
            return True
    return False
new_ds = ds.filter(fe)
print(new_ds)




