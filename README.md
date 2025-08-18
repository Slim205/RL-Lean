# RL-Lean

Reinforcement learning for **formal-math reasoning** with **Lean 4**.
We train a *conjecturer* to propose useful theorem statements for a *prover*, then use those generated samples to improve the prover via SFT and RL.

---

## Why formal math + Lean?

Formal proofs are **machine-checkable**: the Lean compiler verifies every step, removing ambiguity compared to informal math. This also enables **synthetic data generation**—you don’t need to hand-annotate ground truth when the compiler can validate it.

---

## Method overview

* **Goal.** Train a conjecturer that proposes conjectures **neither too easy nor too hard** for the prover—i.e., maximally useful for training.
* **Approach.** We use **PPO** with a reward shaped by pass rate, novelty/relatedness, and batch diversity.

### Reward (sketch)

We first define a base term:

$$
R_{\text{base}}
= \text{Pass@8}\cdot \mathbf{1}\!\left(0 < \text{Pass@8} \le 0.5\right)
\cdot \mathbf{1}\!\left(0.4 < \cos(\texttt{new}, \texttt{old}) < 0.9\right)
\cdot \mathbf{1}\!\left(\min \cos(\text{same batch}) < 0.9\right)
$$

Then we combine $R_{\text{base}}$ with additional terms encouraging:

* **Complexity** (avoid trivial statements),
* **Novelty** (avoid near-duplicates),
* **Relatedness** (stay on-distribution),

and enforce **batch-level diversity** to prevent collapse. (See code for exact weights.)

---

## Training pipeline

1. **Conjecturer RL:** Train with PPO using the reward above.
2. **Data collection:** Generate \~**30k** conjectures/proofs; **deduplicate**.
3. **Prover SFT:** Start from **DeepSeek-Prover-v1.5-SFT**, run **1 epoch** SFT on the collected data.
4. **Prover RL:** Further fine-tune on **LeanWorkbook** using RL.

---

## Results (MiniF2F)

| Model                     |  Pass\@1  | Pass\@32 |
| ------------------------- | :-------: | :------: |
| DeepSeek-Prover-v1.5-SFT  |   30.74   |   47.95  |
| + SFT on conjecturer data |   32.79   |   49.18  |
| + SFT + RL (LeanWorkbook) | **39.75** |   49.18  |

**Takeaway:** **+9** absolute improvement in Pass\@1 over the base.

---

## Implementation notes

* **RL framework:** VERL
* **SFT framework:** Levanter
* **Lean compiler service:** kimina-server
* **Base prover:** DeepSeek-Prover-v1.5-SFT

> The conjecturer and prover models are released open source.

---


## Dataset & models

* **Conjecturer-generated dataset:** \~**30k** samples (post-dedup).
* **Base model:** DeepSeek-Prover-v1.5-SFT.
* **Artifacts:** Conjecturer and prover checkpoints (see Releases or `models/`).

---

## Project status

* ✅ Conjecturer PPO training & data generation
* ✅ Prover SFT (1 epoch)
* ✅ Prover RL on LeanWorkbook
* 📈 Reported improvements on MiniF2F

---

## Acknowledgements

Built on and inspired by: **GodelLM**, **kimina-server**, **VERL**, **STP**, **Levanter**, and **DeepSeek-Prover-v1.5**. Thanks to the authors and maintainers of these projects.

---


