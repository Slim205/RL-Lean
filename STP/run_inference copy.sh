#!/bin/bash

# we frequently deal with commands failing, and we like to loop until they succeed. this function does that for us
function retry {
  for i in {1..5}; do
    "$@"
    if [ $? -eq 0 ]; then
      break
    fi
    if [ $i -eq 5 ]; then
      >&2 echo "Error running $*, giving up"
      exit 1
    fi
    >&2 echo "Error running $*, retrying in 5 seconds"
    sleep 5
  done
}

# Default values
TPU_NAME=$(retry curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/description)
ZONE_FULL_PATH=$(retry curl -s -H "Metadata-Flavor: Google" http://metadata.google.internal/computeMetadata/v1/instance/zone)
ZONE=$(echo "$ZONE_FULL_PATH" | awk -F'/' '{print $NF}')

VENV_PATH="~/venv_vllm/bin/activate"

# Print the values of the variables
echo "TPU_NAME: $TPU_NAME"
echo "ZONE: $ZONE"

gcloud compute tpus tpu-vm ssh $TPU_NAME --zone $ZONE --worker=all \
--command "source $VENV_PATH; ray stop; singularity instance stop -a"

# init ray on the head worker
gcloud compute tpus tpu-vm ssh $TPU_NAME --zone $ZONE --worker 0 \
--command "source $VENV_PATH; source ~/STP/RL/.bash_alias.sh; \
TPU_VISIBLE_DEVICES=0,1,2,3 ray start --head --resources='{\"TPU\": 4}';"

HEAD_WORKER_IP=$(gcloud compute tpus tpu-vm ssh $TPU_NAME --zone $ZONE --worker 0 \
--command "hostname -I")
HEAD_WORKER_IP=$(echo $HEAD_WORKER_IP | awk '{print $1}')

echo "Starting node workers"
gcloud compute tpus tpu-vm ssh $TPU_NAME --zone $ZONE --worker=all \
--command "source $VENV_PATH; source ~/STP/RL/.bash_alias.sh; \
CURRENT_IP=\$(hostname -I | awk '{print \$1}'); \
if [[ \$CURRENT_IP == $HEAD_WORKER_IP ]]; then \
  echo \"Head worker, skipping\"; \
else \
  TPU_VISIBLE_DEVICES=0,1,2,3 ray start --address=$HEAD_WORKER_IP:6379 --resources='{\"TPU\": 4}'; \
fi"

echo "Started ray server."