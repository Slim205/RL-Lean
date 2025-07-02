## DeepSeek-Prover-V2: Advancing Formal Mathematical Reasoning via Reinforcement Learning for Subgoal Decomposition


# Lean version  : Lean 4.9.0
9h --> 10h : 
Use Deepseek V3 model to generate subgoals : 
have term1_pos : 0 < a / (a + b + d) := by sorry
have term1_less1 : a / (a + b + d) < 1 := by sorry

'sorry'  :indicate a subgoal

conjecture :  leverages subgoals to expand the scope of formal
statements used for model training.

### Unifying Informal Reasoning and Proof Formalization

### Cold Start by Synthetic Data.
COT kimina : start by the formal proofs and then add the informal to the prompt as CoT
deepseek : generate proofs with informal


### Reinforcement : 
binary reward 
add penalization to not deviate from the proof structure

### diff with deepseek V1.5 
more data : 
additional problems derived from autoformalization and various opensource datasets (Ying et al., 2024; Dong and Ma, 2025; Lin et al., 2025),

add data with subgoal decomposition

### SFT on 671B model


7b model is a distillation of 671B model

DeepSeek-V3 for lemma decomposition and a 7B prover model to complete
the corresponding formal proof details



No Cot : 
expert iteration using decomposite by RV.3 

Cot : annoated : proof with formal ==> SFT data ==> fine tune the 671B model 
and then distill the small model 

the difference between V2 and V1.5 : 
use the bigger model for decomposition

Results : 

V2 (coT) : 75%
Non COT : 68%
Kimina 7b : 63%
Goedlm : 57.6% 
