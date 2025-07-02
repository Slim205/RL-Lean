## DeepSeek-Prover-V1.5: Harnessing Proof Assistant Feedback for Reinforcement Learning and Monte-Carlo Tree Search

Lean version ???? 
minif2f : lean 4.9.0
10h --> 11h : 
reinforcement learning from proof assistant feedback (RLPAF).
 we propose RMaxTS, a variant of Monte-Carlo tree search that employs an intrinsic-reward-driven exploration strategy to generate diverse proof paths. 

63.5% minif2f 
50% V1
60.2% 1.5 V1.5
63 % with tree

Base model is the model pretrained on code and informal math

### SFT : 
adding detail explanatory comments to the old data

we incorporate intermediate tactic state information as an auxiliary prediction task to support the truncate-and-resume mechanism used
in the Monte-Carlo Tree Search process.

dataset source : 
Mathlib / synthetic data from previous model / Lean workbook / 
minif2f/proofnet training

expert iteration 

between each itreation : annotate the code using DeepSeek-Coder V2 236B

10K sequences. 

Similar to Lean-STaR, which performs isolated chain-of-thought reasoning before each proof step.

We use the DeepSeekCoder V2 236B  to enhance data in DeepSeek-Prover-V1 :
1- inserting a complete natural language solution at the beginning of the proof block / 2- inserting specific natural language steps for corresponding Lean tactics.

they enhanced the Lean REPL to get access to the tactics using lean-dojo

identify the tactic that triggers verification errors

During training, we use all tokens following
"/- tactic state: " as responses to calculate the supervised fine-tuning loss

### RL : 
subset of SFT data whith low success rate (we say the model can prove them)
4.5K statements for RL
COT / non-cot prompts

reward : 0/1 (sparse ==> low success rate)

Algo : GRPO 

### Exploration oriented Monte Carlo Tree Search 

submit the proof into lean to parse it into tactics.

Truncate : 
truncate to the earliest verification error
add COT that present the state tactic

use MCTS search


## Summary : 
V1.5 : 
use COT power either by using bigger model to annotate formal data or by providing existing tactics during the proof generating process.

they applied reinforcement learning using GRPO Vs expert iteration

No new autoformalisation (using old dataset)

using MCTS tree to improve sampling