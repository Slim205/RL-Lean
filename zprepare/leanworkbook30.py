from vllm import LLM, SamplingParams

# Load the fine-tuned model (DeepSeek compatible)
llm = LLM(model="kfdong/STP_model_Lean_0320")

# Sampling parameters (you can tweak as needed)
sampling_params = SamplingParams(
    temperature=0.7,
    top_p=0.95,
    max_tokens=256,
    stop=["</hard theorem>", "```"]
)


theorem = """theorem imo_1968_p5 (a : R) (f : R → R) (h0 : 0 < a) (h1 : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by sorry"""
# Build your test_info
theorem ="theorem lean_workbook_plus_34146 (x y : ℝ) (h₁ : 1 < x) (h₂ : 1 < y) (h₃ : x < y) : (x - 1) * Real.log x < (y - 1) * Real.log y := by sorry"
#theorem = "theorem lean_workbook_985 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + a * c) := by"
test_info = {
    "shared_lemma_statement": '',
    "statement": theorem,
    "proof": ""
}

# Prompt construction (Lean 4)
START_STATEMENT = '<statement>'
START_LEMMA_STMT = '<easy theorem>'
START_THM = '<hard theorem>'
END_THM = '</hard theorem>'
INVOKED_LEMMA = '<lemma>'
PROVER_PROMPT = (
    "Complete the following Lean 4 code:\n\n```lean4\n"
    "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\n"
    "open BigOperators Real Nat Topology Rat\n"
)

def get_prompt(test_info):
    shared_lemma = test_info['shared_lemma_statement']
    easy_theorem = test_info['statement'] + test_info['proof']
    prompt = (
        f"{PROVER_PROMPT}"
        f"{INVOKED_LEMMA}\n{shared_lemma.strip()}\n"
        f"{START_LEMMA_STMT}\n{easy_theorem.strip()}\n"
        f"{START_THM}\n theorem"
    )
    return prompt

prompt = get_prompt(test_info)

# Generate output
outputs = llm.generate(prompt, sampling_params)


def process(out) : 
    if ':= by' in out : 
        return 'theorem ' + out.split(':= by')[0] + ':= by sorry'
    return 'None'
# Print results
print(prompt)
print("=== Model Output ===")

print(outputs[0].outputs[0].text)
print(process(outputs[0].outputs[0].text))