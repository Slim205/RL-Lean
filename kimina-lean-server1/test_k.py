from vllm import LLM, SamplingParams
from transformers import AutoTokenizer

model_name = "AI-MO/Kimina-Prover-Preview-Distill-1.5B"
model = LLM(model_name)

tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)

problem = "The volume of a cone is given by the formula $V = \frac{1}{3}Bh$, where $B$ is the area of the base and $h$ is the height. The area of the base of a cone is 30 square units, and its height is 6.5 units. What is the number of cubic units in its volume?"

formal_statement = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- The volume of a cone is given by the formula $V = \frac{1}{3}Bh$, where $B$ is the area of the base and $h$ is the height. The area of the base of a cone is 30 square units, and its height is 6.5 units. What is the number of cubic units in its volume? Show that it is 65.-/
theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by
"""

prompt = "Think about and solve the following problem step by step in Lean 4."
prompt += f"\n# Problem:{problem}"""
prompt += f"\n# Formal statement:\n```lean4\n{formal_statement}\n```\n"

messages = [
    {"role": "system", "content": "You are an expert in mathematics and Lean 4."},
    {"role": "user", "content": prompt}
]

text = tokenizer.apply_chat_template(
    messages,
    tokenize=False,
    add_generation_prompt=True
)

sampling_params = SamplingParams(temperature=0.6, top_p=0.95, max_tokens=8096)
output = model.generate(text, sampling_params=sampling_params)
output_text = output[0].outputs[0].text
print(output_text)
