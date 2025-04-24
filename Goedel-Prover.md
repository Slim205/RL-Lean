# Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving

https://arxiv.org/pdf/2502.07640

## Abstract : 
- Goedel-Prover beats sthe SOTA performance in proof generation
- create synthetic dataset : use translated data from NL math problems (Numina) to Lean (LLM was used to check the translation)
- to generate the dataset they train a series of provers iteratively (one a prover succed in generation a proof, we add the proof to the training dataset for the next prover)
- outperforms SOTA models which employs RL
- Evaluation : miniF2F / PutnamBench / Lean Workbook (solving new problems)

## Introduction : 
- Works on informal reasoning were successeful
- difficulty in automated verification ==> Formal reasoning (Lean, Coq, etc)
- Problem with formal math : scarcity of the data (Lean Workbook : 140K / 15.7K with fromal proofs , Open Bootstrapped : 107K with proofs from Mathlib4 )
-  miniF2F is the most used dataset (high school level / complex reasoning abilities)
-  Mathlib4 (simple manipulation of advanced math concepts / doesn't improve the perfomance on miniF2F when added to training).
-  The informal math data is not scarce
-  Numina / MATH / GSM8K /AMC / AIME / AoPs, ect
- Train two LLMs to translate from Informal to Formal math ( 1st LLM trained on Lean Workbook data, 2nd on pairs annotated by Claude)
- Use an LLM to verify that the quality of translation
- Data : 1.64 M of statements

- Perform expert iteration to train the prover ( generate proofs without interaction with lean : whole-proof generation method)
- Steps : 1) generate 16 candidates proofs using DeepSeek-Prover-V1.5-RL for each statement / 2) verify the correctness using lean compiler 3) collect data using correct proofs  4) Fine tune DeepSeek-Prover-V1.5-Base 5) re run the same process for 8 iterations
