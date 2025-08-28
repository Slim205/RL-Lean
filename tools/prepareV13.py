import json
from datasets import DatasetDict,load_dataset

ds = load_dataset("Slim205/mathlib_RL_v3", split='train')


list_files = list(set([ sample['file_name'] for sample in ds]))

print(len(list_files))

mathlib_graph = { x : [] for x in list_files}

for sample in ds : 
    for x in sample['Context'].split('\n') : 
        if 'import' in x and not '#' in x : 
            dd = x[7:].split('.')
            ch = ''
            for y in dd : 
                ch = ch +  y  + '/'
            file_name = ch[:-1] +   '.lean'
            if file_name in list_files : 
                if sample['file_name'] not in mathlib_graph[file_name] : 
                    mathlib_graph[file_name].append(sample['file_name'])

s=0
maxi = 0
theo  = ''
for x,y in mathlib_graph.items() : 
    if len(y) > maxi : 
        maxi = len(y)
        theo = x
print(theo)
print(maxi)
print('============')
from typing import Dict, List, Set

def topo_parent_first(graph: Dict[str, List[str]],
                      start_nodes: List[str],
                      detect_cycles: bool = False) -> List[str]:
    """
    Return a list such that every node x appears **before** each y in graph[x].

    Parameters
    ----------
    graph : adjacency list  (edge  x → y  means  x must come before y)
    start_nodes : roots you want to traverse first
    detect_cycles : if True, raise ValueError if a cycle is encountered
    """
    order: List[str] = []      # post-order; we will reverse at the end
    seen:  Set[str] = set()
    stack: Set[str] = set()    # for optional cycle detection

    def dfs(node: str) -> None:
        if node in seen:
            return
        if detect_cycles and node in stack:
            raise ValueError(f"cycle detected involving {node}")
        stack.add(node)

        for child in graph.get(node, []):
            dfs(child)

        stack.discard(node)
        seen.add(node)
        order.append(node)     # append *after* children

    for root in start_nodes:
        dfs(root)

    order.reverse()            # now parents precede all children
    return order

theorem0 = 'Mathlib/Data/Set/Subsingleton.lean'
sorted_names = topo_parent_first(mathlib_graph,
                                 [theorem0] + list_files)

print(len(sorted_names))

for i,x in enumerate(sorted_names) : 
    for j in range(i) : 
        if sorted_names[j] in mathlib_graph[x] : 
            print('ERROR')


def numerate(sample) : 
    for i in range(len(sorted_names)) : 
        if sorted_names[i] == sample['file_name'] : 
            sample['rank'] = i
            break
    return sample
ds1 =ds.map(numerate)

ds2 = ds1.sort(['rank', 'start'])

dataset_test = load_dataset("Slim205/mathlib_RL_v3", split='test')

def map1(x) :
    x['rank'] = 0
    return x
ds_final = DatasetDict()
ds_final['train'] = ds2
ds_final['test'] = dataset_test.map(map1)

print(ds_final)
ds_final.push_to_hub('Slim205/Mathlib_RL_V13')