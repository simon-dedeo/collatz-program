#!/bin/bash
#SBATCH --job-name=collatz-c2-minplus
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=13:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c2-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c2-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
for spec in '100000000 100 9' '10000000000 120 9' '500000000000 140 9'; do
  set -- $spec
  out=results/c2-minplus-B${1}-${SLURM_JOB_ID}.tsv
  ./minplus_profile "$1" "$2" "$3" 100000 "$out"
  sha256sum "$out" > "$out.sha256"
done
