#!/bin/bash
#SBATCH --job-name=collatz-k1-soft
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=13:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k1-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k1-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
out=results/k1-soft-${SLURM_JOB_ID}.tsv
./kl_soft_spectrum 17 1.9 128 10000 1e-10 "$out" results/k1-k17-b128.bin
./kl_soft_spectrum 18 1.9 64 10000 1e-10 "$out" results/k1-k18-b64.bin
./kl_soft_spectrum 18 1.9 128 10000 1e-10 "$out" results/k1-k18-b128.bin
./kl_soft_spectrum 19 1.9 64 10000 1e-9 "$out" results/k1-k19-b64.bin
for li in $(seq 180 2 198); do
  printf -v lam '%d.%02d' "$((li/100))" "$((li%100))"
  for beta in 8 16 32 64 128 256 512 1024; do
    ./kl_soft_spectrum 19 "$lam" "$beta" 3000 1e-7 "$out" -
  done
done
sha256sum "$out" > "$out.sha256"
