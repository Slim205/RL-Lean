# Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving


## Abstract : 
- Goedel-Prover beats sthe SOTA performance in proof generation
- create synthetic dataset : use translated data from NL math problems (Numina) to Lean (LLM was used to check the translation)
- to generate the dataset they train a series of provers iteratively (one a prover succed in generation a proof, we add the proof to the training dataset for the next prover)
- outperforms SOTA models which employs RL
- Evaluation : miniF2F / PutnamBench / Lean Workbook

