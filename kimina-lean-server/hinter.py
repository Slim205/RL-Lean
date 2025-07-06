import json
from datasets import load_dataset, Dataset, DatasetDict
from client.client import Lean4Client, batch_verify_proof
import fire
import os
from tqdm import tqdm
import traceback
import re

def process_state(ch) : 
    try :
      goal = ch.split('⊢')[1]
      hypo = ch.split('⊢')[0]
      new_hypo = ''
      if len(hypo) == 0 : 
        return ":" + goal
      for i, x in enumerate(hypo.split(' : ')) :
          if i == 0 : 
            new_hypo = '(' + x + ' : '
            continue

          pos = re.split(r'[ \n]', x)[-1]
          for y in re.split(r'[ \n]', x)[:-1] : 
              new_hypo += y + ' '
          if pos == '' : 
              continue
          if pos[0] != '('  :
              new_hypo += ') ('
          new_hypo += pos + ' : '
      return new_hypo + ") :" + goal
    except : 
      print(ch)
      print(traceback.format_exc())
      return ch

def process_state_final(ch) : 
    try : 
      if 'case' in ch : 
        pattern = re.compile(
            r'^case\s+(\S+)\s*(.*?)(?=^case\s|\Z)',       
            flags=re.MULTILINE | re.DOTALL
        )

        list_hints = []                                        
        for m in pattern.finditer(ch):
            name = m.group(1)                             
            body = m.group(2).strip()                   
            list_hints.append(process_state(body))
        return list_hints
      else : 
          return [process_state(ch)]
    except : 

      print(ch)
      print(traceback.format_exc())
def main2() : 
    dataset = load_dataset("Slim205/lean_workbook_RL_V8", split='train')#.select(range(1))

    with open('compilation_res_tests_V8.json', 'r') as json_file:
        compilation_results = json.load(json_file)
    dict_res = {}
    for res in compilation_results:
      dict_res[res['custom_id']] = res

    new_inputs=[]
    c = False
    for example in dataset:
      theorem =  example['problem_id'] 
      # if theorem != 'lean_workbook_plus_17652' : 
      #   continue
      goals = []
      if 'tactics' in dict_res[theorem].keys() :
        for x in dict_res[theorem]['tactics'] : 
          goals.append(x['goals'])
      example['goals'] = goals
    
      example['processed_goals'] = []
      for goal in example['goals'] : 
        if goal == 'n k : ℕ hn : 1 < n | n ^ k - 1' : 
          continue
        # if 'case ' in goal : 
        #   print(goal)
        #   print()
        #   print(process_state_final(goal))
        #   print('==========')
        #   c= True
        #   break
        example['processed_goals'].extend(process_state_final(goal))
        # except : 
        #   print(len(example['processed_goals']))
        #   print(process_state_final(goal))
        #   example['processed_goals'].extend(process_state_final(goal))

      new_inputs.append(example)
      
    train_ds = Dataset.from_list(new_inputs)
    def map1(s) :
      s['goals'] = ['']
      s['processed_goals']  = ['']
      return s
    test_ds = load_dataset("Slim205/lean_workbook_RL_V8", split='test').map(map1)
    print(test_ds)
    print(train_ds)
    hf_dataset = DatasetDict({'train' : train_ds , 'test' : test_ds})
    hf_dataset.push_to_hub('Slim205/lean_workbook_RL_hinter_V1')



if __name__ == '__main__':
    fire.Fire(main2)
