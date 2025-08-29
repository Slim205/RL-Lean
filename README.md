# RL-Lean
Reinforcement learning for **formal-math reasoning** with **Lean 4**.
We train a *conjecturer* to propose useful theorem statements for a *prover*, then use those generated samples to improve the prover via SFT and RL.
<p align="center">
  <img src="photo.png" alt="Alt text" width="400"/>
</p>

## Why formal math + Lean?

Formal proofs are **machine-checkable**: the Lean compiler verifies every step, removing ambiguity compared to informal math. This also enables **synthetic data generation**—you don’t need to hand-annotate ground truth when the compiler can validate it.

## Method overview

* **Goal.** Train a conjecturer that proposes conjectures **neither too easy nor too hard** for the prover—i.e., maximally useful for training.
* **Approach.** We use **PPO** with a reward shaped by pass rate, novelty/relatedness, and batch diversity.

### Reward 

We define a base term:

$$
R_{\text{base}}
= \mathbf{1}\!\left(0 < \text{Pass@16} \le 0.5\right)
\cdot \mathbf{1}\!\left(0.4 < \cos(\texttt{new}, \texttt{old}) < 0.9\right)
\cdot \mathbf{1}\!\left(\min \cos(\text{same batch}) < 0.9\right)
$$

The $R_{\text{base}}$ term is designed to capture several key aspects :

* **Complexity** : encourages statements that are non-trivial but not too difficult for the LLM.
* **Novelty** avoids near-duplicate statements.
* **Relatedness** : ensures a meaningful connection between the statement and its conjecturer.
* **Synthetic correctness** : guarantees that statements are syntactically valid and pass the Lean compiler with by sorry.

Additionally, $R_{\text{base}}$ enforces batch-level diversity to prevent collapse. 
---

## Training pipeline

1. **Conjecturer RL:** Train with PPO using the reward above.
2. **Data collection:** Generate \~**40k** conjectures/proofs; **deduplicate**.
3. **Prover SFT:** Start from **DeepSeek-Prover-v1.5-SFT**, run **1 epoch** SFT on the collected data.
4. **Prover RL:** Further fine-tune on **LeanWorkbook** using RL.

---

## Results (MiniF2F)

| Model                     |  Pass\@1  | Pass\@32 |
| ------------------------- | :-------: | :------: |
| DeepSeek-Prover-v1.5-SFT  |   30.74   |   47.95  |
| + SFT on conjecturer data |   32.79   |   49.18  |
| + SFT + RL (LeanWorkbook) | **39.75** |   **49.18**  |

**Takeaway:** **+9** absolute improvement in Pass\@1 over the base.

---

## Implementation notes

* **RL framework:** VERL
* **SFT framework:** Levanter
* **Lean compiler service:** kimina-server
* **Base prover:** DeepSeek-Prover-v1.5-SFT

---

## Dataset & Models

* **Conjecturer-generated dataset:** ~**40k** samples (after deduplication) — [Slim205/Lean_conjecturer_data_v01](https://huggingface.co/datasets/Slim205/Lean_conjecturer_data_v01)  
* **Base model:** DeepSeek-Prover-v1.5-SFT  
* **Artifacts:**  
  * **Conjecturer:** [Slim205/Lean_conjecturer_v1](https://huggingface.co/Slim205/Lean_conjecturer_v1)  
  * **Prover:** [Slim205/Lean_prover_v1](https://huggingface.co/Slim205/Lean_prover_v1)  

---

## Acknowledgements

Built on and inspired by: **GodelLM**, **kimina-server**, **VERL**, **STP**, **Levanter**, **Lean Dojo** ,and **DeepSeek-Prover-v1.5**. Thanks to the authors and maintainers of these projects.

---


