#!/bin/bash
#SBATCH --job-name=kc-nonuniform
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --nodes=1
#SBATCH --ntasks=64
#SBATCH --cpus-per-task=1
#SBATCH --time=02:00:00
#SBATCH --output=logs/nonuniform-%j.out
#SBATCH --error=logs/nonuniform-%j.err

set -euo pipefail

mkdir -p shards logs
srun --kill-on-bad-exit=1 bash -lc '
  python3 search_nonuniform.py \
    --max-image-length 8 \
    --max-k 4 \
    --max-depth 14 \
    --max-word-length 16384 \
    --max-seed-word-length 1024 \
    --continuation-steps 100000 \
    --shard-index "$SLURM_PROCID" \
    --shards "$SLURM_NTASKS" \
    --output "shards/shard-$(printf "%03d" "$SLURM_PROCID").json"
'
