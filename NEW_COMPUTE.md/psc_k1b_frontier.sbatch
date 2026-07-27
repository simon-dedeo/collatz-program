#!/bin/bash
#SBATCH --job-name=collatz-k1b
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=03:00:00
#SBATCH --array=0-5
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k1b-%A_%a.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k1b-%A_%a.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
lambdas=(1.84 1.85 1.86 1.87 1.88 1.89)
lambda=${lambdas[$SLURM_ARRAY_TASK_ID]}
out=results/k1b-frontier-l${lambda}-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.tsv
# Fine levels are last so every completed lower-level row remains useful if a
# k=22 case reaches the four-hour cap.
for level in 20 21 22; do
  for beta in 64 128 256 512 1024 2048; do
    ./kl_soft_spectrum "$level" "$lambda" "$beta" 500 1e-7 "$out" -
  done
done
sha256sum "$out" > "$out.sha256"
