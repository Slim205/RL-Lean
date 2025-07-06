
import datasets


dataset = datasets.load_dataset( "Slim205/lean_workbook_RL_minif2f")

train_dataset = dataset["train"].select(range(24000))
test_dataset = dataset["train"].select(range(24000,24434))

ds = datasets.DatasetDict()
ds['train'] = train_dataset
ds['test'] = test_dataset

print(ds)

ds.push_to_hub('Slim205/lean_workbook_RL_V8')