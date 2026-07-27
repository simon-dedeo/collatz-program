#!/bin/bash
#SBATCH --job-name=collatz-k2b-fix
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=00:20:00
#SBATCH --array=0-1
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k2b-fix-%A_%a.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k2b-fix-%A_%a.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
levels=(19 20)
lambdas=(1.8783127 1.8857081)
k=${levels[$SLURM_ARRAY_TASK_ID]}
lambda=${lambdas[$SLURM_ARRAY_TASK_ID]}
vec=/ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k${k}.npy
out=results/k2b-coldfix-k${k}-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.tsv
./kl_coercivity_atlas "$vec" "$lambda" 16 "$out"
if grep -q 'nan' "$out"; then
  echo "nonfinite atlas output" >&2
  exit 2
fi
sha256sum "$vec" "$out" > "$out.sha256"
