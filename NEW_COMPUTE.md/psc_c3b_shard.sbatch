#!/bin/bash
#SBATCH --job-name=collatz-c3b-d27
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=06:30:00
#SBATCH --array=0-2
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c3b-%A_%a.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c3b-%A_%a.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
out=results/c3b-d27-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.tsv
./zero_carry_champions 27 256 "$out" "$SLURM_ARRAY_TASK_ID" 3
sha256sum "$out" > "$out.sha256"
