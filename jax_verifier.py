import os
# Force CUDA backend and configure environment
os.environ['JAX_PLATFORMS'] = 'cuda'  # Force CUDA backend
os.environ['XLA_PYTHON_CLIENT_PREALLOCATE'] = 'false'  # Disable preallocation
os.environ['JAX_DISABLE_TPU_ENV_CHECKS'] = '1'  # Disable TPU checks
os.environ['JAX_SKIP_CUDA_CONSTRAINTS_CHECK'] = '1'  # Bypass cuDNN version check
print('Environment configured')

import jax
import jax.numpy as jnp

# Verify backend
print('\nVerification:')
print(f"JAX backend: {jax.default_backend()}")
print(f"Available devices: {jax.devices()}\n")

def tanh(x):
    y = jnp.exp(-2.0 * x)
    return (1.0 - y) / (1.0 + y)

# Test computation
grad_tanh = jax.grad(tanh)
print('Testing gradient calculation:')
print(grad_tanh(1.0))  # Expected output: ~0.4199743