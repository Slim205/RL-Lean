# broadly based on https://github.com/ayaka14732/tpu-starter

# parse some arguments
# usage: ./setup-tpu-vm.sh -b|--branch <git commit or branch for levanter> -r <git repo for levanter>

if [ "$DEBUG" == "1" ]; then
  set -x
fi

REPO="https://github.com/stanford-crfm/levanter.git"
BRANCH=main

if [ "$GIT_BRANCH" != "" ]; then
  BRANCH="$GIT_BRANCH"
fi

while [[ $# -gt 0 ]]; do
  key="$1"
  case $key in
    -b|--branch)
      BRANCH="$2"
      shift
      shift
      ;;
    -r|--repo)
      REPO="$2"
      shift
      shift
      ;;
    *)
      >&2 echo "Unknown option $1"
      exit 1
      ;;
  esac
done

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

# tcmalloc interferes with intellij remote ide
sudo patch -f -b /etc/environment << EOF
2c2
< LD_PRELOAD="/usr/lib/x86_64-linux-gnu/libtcmalloc.so.4"
---
> #LD_PRELOAD="/usr/lib/x86_64-linux-gnu/libtcmalloc.so.4"
EOF



# don't complain if already applied
retCode=$?
[[ $retCode -le 1 ]] || exit $retCode


# set these env variables b/c it makes tensorstore behave better
if ! grep -q TENSORSTORE_CURL_LOW_SPEED_TIME_SECONDS /etc/environment; then
  # need sudo
  echo "TENSORSTORE_CURL_LOW_SPEED_TIME_SECONDS=60" | sudo tee -a /etc/environment > /dev/null
fi

if ! grep -q TENSORSTORE_CURL_LOW_SPEED_LIMIT_BYTES /etc/environment; then
  echo "TENSORSTORE_CURL_LOW_SPEED_LIMIT_BYTES=1024" | sudo tee -a /etc/environment > /dev/null
fi

# install python 3.10, latest git
sudo systemctl stop unattended-upgrades  # this frequently holds the apt lock
sudo systemctl disable unattended-upgrades
sudo apt remove -y unattended-upgrades
# if it's still running somehow, kill it
if [ $(ps aux | grep unattended-upgrade | wc -l) -gt 1 ]; then
  sudo kill -9 $(ps aux | grep unattended-upgrade | awk '{print $2}')
fi

# sometimes apt-get update fails, so retry a few times
retry sudo apt-get install -y software-properties-common
retry sudo add-apt-repository -y ppa:deadsnakes/ppa
retry sudo add-apt-repository -y ppa:git-core/ppa
retry sudo apt-get -qq update
retry sudo apt-get -qq install -y python3.10-full python3.10-dev git
retry sudo apt-get install -y libopenblas-base libopenmpi-dev libomp-dev sysstat task-spooler

# install inference venv
VENV=~/venv_vllm
# if the venv doesn't exist, make it
if [ ! -d "$VENV" ]; then
    echo "Creating virtualenv at $VENV"
    python3.10 -m venv $VENV
fi

cd ~
source $VENV/bin/activate
git clone https://github.com/vllm-project/vllm.git
cd vllm
git checkout v0.6.6
pip install https://download.pytorch.org/whl/nightly/cpu/torch-2.6.0.dev20241126%2Bcpu-cp310-cp310-linux_x86_64.whl https://download.pytorch.org/whl/nightly/cpu/torchvision-0.20.0.dev20241126%2Bcpu-cp310-cp310-linux_x86_64.whl
cp ~/STP/assets/setup/requirements-tpu.txt ./
pip install -r requirements-tpu.txt
VLLM_TARGET_DEVICE="tpu" python setup.py develop
pip install func_timeout wandb pgzip ujson packaging aiohttp datasets
pip install google-cloud-storage==2.14.0 google-api-core==1.34.1 grpcio==1.65.5
echo "Done."

VENV=~/venv310
# if the venv doesn't exist, make it
if [ ! -d "$VENV" ]; then
    echo "Creating virtualenv at $VENV"
    python3.10 -m venv $VENV
fi

cd ~
git clone https://github.com/kfdong/STP.git
cd ~/STP
git pull
source ~/venv310/bin/activate
pip install torch==2.4.0 --index-url https://download.pytorch.org/whl/cpu
pip install -r venv310.txt -f https://storage.googleapis.com/libtpu-releases/index.html
cd levanter
pip install -e .

source ~/venv_vllm/bin/activate

# Install lean
cd ~
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source ~/.profile
elan default leanprover/lean4:4.9.0-rc1

mkdir -p ~/lean
cd ~/lean
git clone https://github.com/xinhjBrant/mathlib4.git
cd mathlib4
lake build
cp ~/STP/assets/setup/miniF2F.lean ./
cp ~/STP/assets/setup/lakefile.lean ./
cp ~/STP/assets/setup/Main.lean .lake/packages/REPL/REPL/Main.lean
lake build miniF2F
lake exec repl < ~/lean/mathlib4/.lake/packages/REPL/test/aime_1983_p9.in > ~/lean/mathlib4/.lake/packages/REPL/test/aime_1983_p9.out

# set up the following environment variables
# export STORAGE='gs://stp_gc_storage'
# export WANDB_API_KEY=''
# export HUGGING_FACE_HUB_TOKEN=''
echo "export STORAGE='gs://stp_gc_storage'" > ~/STP/RL/.bash_alias.sh
echo "export WANDB_API_KEY=''" >> ~/STP/RL/.bash_alias.sh
echo "export HUGGING_FACE_HUB_TOKEN=''" >> ~/STP/RL/.bash_alias.sh