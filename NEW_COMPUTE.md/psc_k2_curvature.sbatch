#!/bin/bash
#SBATCH --job-name=collatz-k2-curv
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=13:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k2-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k2-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
out=results/k2-curvature-${SLURM_JOB_ID}.tsv
vec18=/ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k18.npy
vec20=/ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k20.npy
./kl_frustration_scan "$vec18" 1.8703245 "$out"
cp "$out" "$out.k18-checkpoint"
./kl_frustration_scan "$vec20" 1.8857081 "$out"
sha256sum "$vec18" "$vec20" "$out" > "$out.sha256"
