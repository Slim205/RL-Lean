import os
os.environ['TOKENIZERS_PARALLELISM'] = 'false'
import ray
import torch
import torch_xla
import torch_xla.core.xla_model as xm
from transformers import AutoTokenizer, AutoModel
import argparse
import time
from typing import List, Dict
import numpy as np

@ray.remote
class LockManager:
    def __init__(self):
        self.locked = 3

    def acquire(self):
        if self.locked > 0:
            self.locked -= 1
            return True
        else:
            return False

    def release(self):
        self.locked += 1

@ray.remote(resources={"TPU": 1})  # Allocate one TPU per worker
class EmbeddingWorker:
    def __init__(self, model_name: str, model_load_lock: ray.actor.ActorHandle = None, tokenizer_path: str = "deepseek-ai/DeepSeek-Prover-V1.5-SFT"):
        """
        Initializes the ModelWorker by loading the tokenizer and model.
        The model is set to half-precision for faster inference and moved to the TPU device.

        Args:
            model_name (str): The name of the Hugging Face model to load.
            model_load_lock (ray.actor.ActorHandle): A Ray actor managing a distributed lock.
        """
        # Initialize the tokenizer (hardcoded as per user instruction)
        self.tokenizer = AutoTokenizer.from_pretrained("deepseek-ai/DeepSeek-Prover-V1.5-SFT")
        self.tokenizer.pad_token = self.tokenizer.eos_token  # Set the pad token to the end-of-sequence token

        # Acquire the Ray lock before loading the model
        if model_load_lock is not None:
            # to handle the OOM error caused by the model loading
            while not ray.get(model_load_lock.acquire.remote()):
                time.sleep(2)
        try:
            # Load the model from Hugging Face
            self.model = AutoModel.from_pretrained(model_name)
            self.model.eval()
            self.model.half()  # Use half-precision for faster inference; adjust if necessary for TPUs
            self.device = xm.xla_device()  # Set device to TPU
            self.model.to(self.device)
        finally:
            # Ensure the lock is released even if an error occurs
            if model_load_lock is not None:
                ray.get(model_load_lock.release.remote())

        # Compile the model for optimized performance if possible
        # Note: Torch XLA may handle optimizations differently
        # if hasattr(torch, "compile"):
        #    self.model = torch.compile(self.model, dynamic=True)
        #    self.model = torch.compile(self.model)
                
    def initialize(self):
        """
        Dummy method to confirm initialization.
        This can be expanded if additional setup is required.

        Returns:
            None
        """
        return None

    def compute_last_hidden_state(self, texts: tuple[str]) -> List[List[float]]:
        texts = list(texts)
        # Tokenize input texts with padding and truncation
        inputs = self.tokenizer(
            texts,
            padding='max_length',      # Pad sequences to the max_length
            truncation=True,           # Truncate sequences longer than max_length
            max_length=512,            # Define the maximum sequence length
            return_tensors="pt"        # Return PyTorch tensors
        )
        
        # Move input tensors to the TPU device
        inputs = {key: value.to(self.device) for key, value in inputs.items()}

        # Forward pass through the model without computing gradients
        with torch.no_grad():
            outputs = self.model(**inputs)
        
        # Extract the last hidden state tensor
        # Shape: [batch_size, sequence_length, hidden_size]
        last_hidden_state = outputs.last_hidden_state  # Example shape: [batch_size, 512, 768]
        
        # Extract the attention mask to identify non-padded tokens
        # Shape: [batch_size, sequence_length]
        attention_mask = inputs['attention_mask']  # Example shape: [batch_size, 512]

        # Expand the attention mask dimensions for broadcasting
        # Shape after unsqueeze: [batch_size, sequence_length, 1]
        mask = attention_mask.unsqueeze(-1)  # Shape: [batch_size, 512, 1]

        # Apply the mask to the last hidden state to zero out padded token embeddings
        # Shape: [batch_size, sequence_length, hidden_size]
        masked_hidden = last_hidden_state * mask

        # Sum the masked hidden states across the sequence length
        # Shape: [batch_size, hidden_size]
        sum_hidden = masked_hidden.sum(dim=1)  # Shape: [batch_size, 768]

        # Compute the number of non-padded tokens for each input in the batch
        # Shape: [batch_size, 1]
        num_tokens = mask.sum(dim=1)  # Shape: [batch_size, 1]

        # To avoid division by zero, replace zero counts with one
        num_tokens = num_tokens.masked_fill(num_tokens == 0, 1)

        # Compute the mean by dividing the summed hidden states by the number of tokens
        # Shape: [batch_size, hidden_size]
        mean_hidden = sum_hidden / num_tokens  # Shape: [batch_size, 768]

        # Synchronize XLA device to ensure computations are complete
        xm.mark_step()

        # Move the tensor to CPU and convert to NumPy array for serialization
        return mean_hidden.cpu().numpy().tolist()
    
    # Helper function to submit a batch and return its start index with embeddings
    def submit_batch(self, batch):
        ids, texts = zip(*batch)
        embeddings = self.compute_last_hidden_state(texts)
        return zip(ids, embeddings)

if __name__ == "__main__":
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description="Run a FastAPI server with a Hugging Face model.")
    parser.add_argument("--model_name", type=str, required=True, help="The name of the Hugging Face model to use.")
    args = parser.parse_args()

    model_load_lock = LockManager.remote()
    model_workers = EmbeddingWorker.remote(args.model_name, model_load_lock)
    result = ray.get(model_workers.compute_last_hidden_state.remote([' test' * 20] * 12))
    print(result)