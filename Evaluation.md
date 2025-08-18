# RL-Lean


| Model                   | Reported (miniF2F) | Reported (ProofNet) | Our Implementation (miniF2F) | Our Implementation (ProofNet) |
|-------------------------|--------------------|---------------------|------------------------------|-------------------------------|
| Deepseek-Prover-v1.5-RL | 50.0%              | 16.0%               | 57.17%                       | 17.7%                        |
| Goedel-Prover-SFT       | 57.6%              | 15.2%               | 62.7%                        | 18.6%                        |


| Model                   | miniF2F (Total: 488) | ProofNet (Total: 361) |
|-------------------------|----------------------|-----------------------|
|                         | **Test** (244)       | **Test** (181)        |
| **Goedel-Prover-SFT**   | 137 (56.15%)         | 27 (14.92%)           |
| **Deepseek-Prover-v1.5**| 121 (49.59%)         | 29 (16.02%)           |
|                         | **Validation** (244) | **Validation** (180)   |
| **Goedel-Prover-SFT**   | 169 (69.26%)         | 40 (22.22%)           |
| **Deepseek-Prover-v1.5**| 158 (64.75%)         | 35 (19.44%)           |
|                         | **Combined Score**   | **Combined Score**     |
| **Goedel-Prover-SFT**   | **62.7%**            | **18.6%**             |
| **Deepseek-Prover-v1.5**| **57.17%**           | **17.7%**             |