import re
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams
import json
import sys
import argparse
import os
from loguru import logger
from client.client import Lean4Client, batch_verify_proof
import time
import traceback


def get_verification_results(old_result) : 
    custom_id= old_result['custom_id']
    system_messages = old_result['error']
    old_result = old_result['response']
    try:
        result = {
            "sorries" : old_result.get('sorries', []), 
            "tactics" : old_result.get('tactics', []),
            "errors" : [m for m in old_result.get('messages', []) if m['severity'] == 'error'],
            "warnings" : [m for m in old_result.get('messages', []) if m['severity'] == 'warning'],
            "infos" : [m for m in old_result.get('messages', []) if m['severity'] == 'info'],
            "system_messages" : system_messages,
            "system_errors" : None,
        }
        result['pass'] = not result['errors']
        result['complete'] = result['pass'] and not result['sorries'] and not any("declaration uses 'sorry'" in warning['data'] or 'failed' in warning['data'] for warning in result['warnings'])
        result['verify_time']  = old_result['time']

    except:
        result = {
            "pass": False,
            "complete": False,
            "system_errors": traceback.format_exc(),
            "system_messages": system_messages,
            "tactics" : []

        }
    result['custom_id'] = custom_id
    return result


def get_complexity_scores(data_list,pass_n) : 
    LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
    model_name = 'deepseek-ai/DeepSeek-Prover-V1.5-SFT'
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    model_inputs = []
    for data in data_list:    
        text = "Complete the following Lean 4 code :\n\n```lean4\n{header}{formal_statement}".format(
                header= LEAN4_DEFAULT_HEADER,
                formal_statement=data['code'][:-6],
            )
        model_inputs.append(text)
    print(model_inputs[0])
    model = LLM(model=model_name, seed=1, trust_remote_code=True, swap_space=8,tensor_parallel_size=args.gpu, max_model_len=4096)

    sampling_params = SamplingParams(
        temperature=1,
        max_tokens=2048,
        top_p=0.95,
        n=pass_n,
    )

    model_outputs = model.generate(
        model_inputs,
        sampling_params,
        use_tqdm=True,
    )

    assert len(model_outputs) == len(model_inputs)

    def extrac_code(inputs):
        try:
            return re.search(r'```lean4\n(.*?)\n```', inputs, re.DOTALL).group(1)
        except:
            return "None"
    is_correct = {}

    to_inference_codes = []
    for i in range(len(data_list)):
        data_list[i]["model_input"] = model_inputs[i]
        data_list[i]["model_outputs"] = [output.text for output in model_outputs[i].outputs]
        data_list[i]["full_code"] = [extrac_code(model_inputs[i] + output.text) for output in model_outputs[i].outputs] 

        to_inference_codes += [{"name": data_list[i]["custom_id"], "code": code} for code in data_list[i]["full_code"]]
        is_correct[data_list[i]["custom_id"]] = 0
    batch_size = 1
    num_proc = 64
    timeout = 60 
    client = Lean4Client(base_url="http://holy8a14101:12332", disable_cache=False)

    samples= []
    for i in range(len(to_inference_codes)):
        to_inference_codes[i]["custom_id"] = f"{to_inference_codes[i]['name']}_{i}"
        samples.append({"custom_id": to_inference_codes[i]["custom_id"] , "proof": to_inference_codes[i]["code"] })

    result = batch_verify_proof(
        samples=samples,
        client=client,
        timeout=timeout,
        num_proc=num_proc,
        batch_size=batch_size,
    )

    compilation_results =[]
    for res in result : 
        compilation_results.append(get_verification_results(res))

    compilation_dict = {result['custom_id']: result for result in compilation_results}
    for code in to_inference_codes:
        custom_id = code['custom_id']  
        if custom_id in compilation_dict:
            code['compilation_result'] = compilation_dict[custom_id]
            if code['compilation_result']['complete'] : 
                is_correct[code['name']] +=1
    return is_correct
