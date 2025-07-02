### DeepSeek-Prover: Advancing Theorem Proving in LLMs through Large-Scale Synthetic Data : 

# 9h 30 --> 10h 30 : 


lean --version : v4.7.0
mathlib commit : 64528268b3c2cf578639bc479828882a9ecd3a82.

This approach involves translating natural language problems into formal statements, filtering out
low-quality statements, and generating proofs to create synthetic data. 


8 M formal statement to do SFT on base model => 46% pass@64 lean4minif2f

autoformaltisation + expert iteration

Autoformalisation : 
Fine tune the base model using MMA datase : translated mathlib using deepseek

execlent filtering tool : 
put the goal as False. sucessful proofs ==> have issue with the hypothesis

they generate proof for the goal and it's negation. (even if the original propositions were not correctly formalized by the model)
hypothesis : goal
hypothesis : False 

