import ray

ray.init(address='auto',namespace="prover")
print(ray.cluster_resources())
print("Number of nodes:", len(ray.nodes()))
