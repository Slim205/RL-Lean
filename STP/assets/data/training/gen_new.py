import json

data = []
with open('/n/netscratch/amin_lab/Lab/slim/Goedel-Prover/datasets/leanworkbook_train.jsonl', 'r') as f:
    for line in f:
        old_data = json.loads(line)
        
        data.append({'name' : old_data['name'],'split' : old_data['split'] ,'formal_statement' : 'theorem '+old_data['formal_statement'].split('theorem ')[1] + ' sorry'})

print(data[0])
with open('lean_workbook_dedup1.json', 'w') as f:
    json.dump(data,f)
