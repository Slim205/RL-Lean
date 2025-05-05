# RL-Lean


| Model                     | Paper Results (miniF2F) | Paper Results (ProofNet) | Your Results (miniF2F) | Your Results (ProofNet) | Difference        |
|---------------------------|------------------------|--------------------------|------------------------|-------------------------|------------------|
| Deepseek-Prover-v1.5-RL   | 50.0%                  | 16.0%                   | 57.17%                 | 17.7%                  | +7.17% / +1.7%  |
| Goedel-Prover-SFT         | 57.6%                  | 15.2%                   | 62.7%                  | 18.6%                  | +5.1% / +3.4%   |



| Model                     | miniF2F Test | miniF2F Validation | ProofNet Test | ProofNet Validation |
|---------------------------|--------------|--------------------|---------------|---------------------|
| **Goedel-Prover-SFT**     |              |                    |               |                     |
| Success Count             | 137/244      | 169/244            | 27/181        | 40/180              |
| Percentage                | 56.15%       | 69.26%             | 14.92%        | 22.22%              |
|                           |              |                    |               |                     |
| **Deepseek-Prover-v1.5-RL** |              |                    |               |                     |
| Success Count             | 121/244      | 158/244            | 29/181        | 35/180              |
| Percentage                | 49.59%       | 64.75%             | 16.02%        | 19.44%              |