#!/bin/bash
#SBATCH --job-name=kc-packet
#SBATCH --account=mth260010p
#SBATCH --partition=GPU-shared
#SBATCH --qos=gpu
#SBATCH --gres=gpu:h100-80:1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=00:30:00
#SBATCH --output=logs/packet-%j.out
#SBATCH --error=logs/packet-%j.err

set -euo pipefail

module load cuda/12.6.1
nvcc -O3 -std=c++17 mersenne_packet_gpu.cu -o mersenne_packet_gpu
srun ./mersenne_packet_gpu \
  --h-bits 36 --max-steps 8 --threshold 6 \
  --output mersenne_packet_gpu_results.json
