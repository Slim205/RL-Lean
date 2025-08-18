from datasets import load_dataset


def extract_theorem(inputs):
    try:
        return ' '.join(inputs.split('theorem')[1].split(' sorry')[0].split()[1:])
    except:
        return "None"

ds = load_dataset('Slim205/lean_workbook_RL_V20',split = 'train')

for sample in ds : 
    theorem = extract_theorem(sample['theorem'])
    print(theorem)
    break

def get_structure()