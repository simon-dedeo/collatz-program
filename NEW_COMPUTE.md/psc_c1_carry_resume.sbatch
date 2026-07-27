#!/bin/bash
#SBATCH --job-name=collatz-c1-resume
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=13:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c1-resume-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c1-resume-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
# Job 42712600 durably completed and hashed the B=50,100,250; K=28
# stages.  Resume at its first unfinished case.
for spec in '500 28 250' '50 29 320' '100 29 320' '250 29 320' \
            '500 29 320' '50 30 400'; do
  set -- $spec
  out=results/c1-carry-B${1}-K${2}-${SLURM_JOB_ID}.tsv
  ./carry_budget "$1" "$2" "$3" "$out"
  sha256sum "$out" > "$out.sha256"
done
