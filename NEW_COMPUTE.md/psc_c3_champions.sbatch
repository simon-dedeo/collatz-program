#!/bin/bash
#SBATCH --job-name=collatz-c3-champ
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=13:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c3-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c3-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
for depth in 19 22 24 26; do
  out=results/c3-champions-d${depth}-${SLURM_JOB_ID}.tsv
  ./zero_carry_champions "$depth" 256 "$out"
  sha256sum "$out" > "$out.sha256"
done
