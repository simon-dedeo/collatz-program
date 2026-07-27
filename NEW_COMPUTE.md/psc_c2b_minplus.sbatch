#!/bin/bash
#SBATCH --job-name=collatz-c2b
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=12:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c2b-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c2b-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
out=results/c2b-minplus-B5500000000000-${SLURM_JOB_ID}.tsv
./minplus_profile 5500000000000 160 10 100000 "$out"
sha256sum "$out" > "$out.sha256"
