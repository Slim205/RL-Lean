from fastapi import FastAPI
from pydantic import BaseModel
from vllm import LLM, SamplingParams

app = FastAPI()

# Initialize the model when the app starts
model = LLM(
    model="deepseek-ai/DeepSeek-Prover-V1.5-SFT",
    seed=1,
    trust_remote_code=True,
    swap_space=8,
    tensor_parallel_size=4,
    max_model_len=4096
)

class GenerationRequest(BaseModel):
    inputs: list[str]
    pass_n: int = 1  # default value

@app.post("/generate")
async def generate(request: GenerationRequest):
    sampling_params = SamplingParams(
        temperature=1,
        max_tokens=2048,
        top_p=0.95,
        n=request.pass_n
    )
    
    outputs = model.generate(
        request.inputs,
        sampling_params
    )
    
    # Return the generated texts
    return [[text.text for text in output.outputs] for output in outputs]