To mathlib you add data that wasn't solve yet and we set the complexity to infi

at each iteration, when the theorems are proved, we compute their lenght of proof and we add them to the traning 

the train set has three brackets : meduim hard easy

The exponential scale spreads out scores so the gap between 20-step and 25-step proofs is far larger than between 2 and 7.

sort thorems using the exp lenght
sort repo using the number of easy theorems

then start by easy to hard repo and do SFT

then try to prove the unproved theorems the once proved they will be added to the dataset. 

SFT per repo for 1 epoch
try to solve the problems.
