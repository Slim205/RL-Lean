change the critic / do we need it to rate token by token ? 

sub token 



Problems with lean : 
New theorems 
using high level tactic

take 100 theorems : 
give the model the solution in large language.
what are the mistakes ? 

you need to learn how to do extract data


To do Today : 
- Read deepseek 2 paper OKok
- verify which kimina version works fine okok 
- do the evaluation on mathlib
- Try to make the 4.9 version and open a issue in their repo
- Try to make leandojo work with this version
- Use it to identify fies in minif2f data.

do 1h / per day : learn more about lean by generating proofs to minif2f

instead of sampling accross proofs we sample accross the theorems : STP/deepseek 2


Can we know what are the mathlib theorems used by the best model to 


TO do Today : 
1h (max) : try to change the code of kimina to use the 4.9.0 version
14h30 --> : 
    - create a pipline to evaluate 1 proof in lean 
    - create a pipline to evaluate a code using the old compiler
    - launch evaluation of mathlib using V4.9.0
    - construct Ultra mathlib_RL 
    - construct minif2f mathlib_RL

17/06/2026 : 
TO do : 
    - correct Verl okok
    - Make RL platform work with legacy mathlib data  10K (examples)  
    - Test the new mathlib data (with proofs  / with deepseek proofs)
    - Test your  idea with concrete examples :: construct your idea
We need the number =>
- Text samy 
- do RL using deepseek and make the performance in mathlib 100%


why we don't train on a part of the proof as a curriculm ? 
25/06/2025 : 
1) idea one : use curriculm learning
2) idea 2 : use errors to identify the 



theorem reindex_relationsSet :
    (M.reindex e).relationsSet =
    FreeGroup.freeGroupCongr e '' M.relationsSet := let M' := M.reindex e; calc
  Set.range (uncurry M'.relation)
  _ = Set.range (uncurry M'.relation ∘ Prod.map e e) := by simp [Set.range_comp]
  _ = Set.range (FreeGroup.freeGroupCongr e ∘ uncurry M.relation) := by
      apply congrArg Set.range
      ext ⟨i, i'⟩
      simp [relation, reindex_apply, M']
  _ = _ := by simp [Set.range_comp, relationsSet]



idea is it possible to train the model to give the useful permises to a given theorem. 

Use the llm to comment a proof, in this proof we did this and this and uses this.
(look on leanprogress maybe they use this idea)


ideas : 
Complexity = : DO brackets. 
and then make the percentage of the easy theorems decrease per batch
we have 40 batch 
start with 


======
Use mathlib do know the score. 
state ==> note


TODO : 
leanworkbook experiments : / complexity curriculum and  / reward -1



mathlib with all the stars (not now)

=========================
1 run baseline : find the number of epoch optimal for training and see improvement on minif2f
1 run with -1 as a reward and see if there is improvement
# 1 run with complexity curriculum (We need a gpu here. and once we fixed the dataset)

==
Compute the scores of the proofs using the dataset you have (the heuristic)


