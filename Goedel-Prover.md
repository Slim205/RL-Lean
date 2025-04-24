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


## Related Work : 
- Automated theroem proving : While Goedel-Prover also generates whole proofs, the data and methodology can be adapted to develop stepwise provers as well.
- Autoformalization and synthetic data generation : DeepSeek Prover and InternLM2.5-StepProver have implemented a translation strategy using expert iteration. Difference : formalizing the Numina dataset + private collected dataset Vs only private dataset // train 2 formalizers to enhance diversity.

## Method : 
### Statement Formalization : 
- Formalizer A: trained using F-I statement pairs sourced from Lean Workbook.
- Formalizer B: employ Claude-sonnet-3.5 to formalize 230K statements from Numina => extract 170K statements that successfully passed Lean compilation. 
- Training : SFT on Qwen2.5-Coder-32B ( 1 day on 8 H100 GPUs)
- Quality assessement : 1) Syntax check for lean : CC : Compiling Correctness ( 'by sorry' => to be able to compile) 2) FC : faithfulness and Completeness score using Qwen2.5-72-B-Instruct (4 judgments), keep FC >= .5
- For each Numina statement, we generate 8 statements using the two Formalizer => 16 statements per problem. Then test those statement on CC and FC.  Then select 1 random statement from the valid ones from each formalizer.
- Translated data : 1.78M formal statement : 860K from Numina / 68K from AOPS => 928K (760K have 2 valid statements). Then add 140K statements from Lean Workbook.

### Expert Iteration : 
- Start with DeepSeek-Prover-V1.5-RL and generate 16 proofs for each statement
- Verify those statements using lean compiler
- if one proof is valid, we retain one proof per statement (random sampling)
- SFT on DeepSeek-Prover-V1.5-Base ==> construct the prover-iter-1
- Iteration : use iter-k to generate answers and construct the iter-k+1 prover
- lr = 1e-4 / 5e-5 , epochs : 1/2, packing=True, batch_size=8


## Results : 
### Benchmarks : 
- miniF2F : 488 problem statements : high school exercices, high-school competition level : Olympiad. (they use the version provided by Xin et al : Lean 4.9)
- ProofNet : undergraduate-level mathematics, 371 problem statements in Lean. topics : real and complex analysis, linear algebra, abstract algebra, topology ( Xin et al : Lean 4.9 Version)
- Lean Workbook : (from AOPS) has 140K statement (used in training which is the same as deepSeek)
- PutnamBench : from theWilliam Lowell Putnam Mathematical Competition years 1962 - 2023. 644 lean statement (algebra, analysis, number theory, geometry, combinatorics, probability and set theory)
- NuminaTest : select 250 statement from their formalised Numina dataset.
### Main Results :

