#!/bin/bash
#SBATCH --job-name=collatz-k2b
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=02:00:00
#SBATCH --array=0-4
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k2b-%A_%a.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/k2b-%A_%a.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
levels=(16 17 18 19 20)
lambdas=(1.8522343 1.8616883 1.8703245 1.8783127 1.8857081)
k=${levels[$SLURM_ARRAY_TASK_ID]}
lambda=${lambdas[$SLURM_ARRAY_TASK_ID]}
vec=/ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k${k}.npy
out=results/k2b-coercivity-k${k}-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.tsv
./kl_coercivity_atlas "$vec" "$lambda" 16 "$out"
sha256sum "$vec" "$out" > "$out.sha256"
