#!/bin/bash
#SBATCH --job-name=collatz-policy-build
#SBATCH --account=mth260010p
#SBATCH --partition=RM-shared
#SBATCH --qos=rm
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=00:20:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/policy-build-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/policy-build-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614 python/3.8.6
make carry_policy_cegis CC=gcc
export OMP_NUM_THREADS=4 OMP_PROC_BIND=close OMP_PLACES=cores
out=results/smoke/carry-policy.tsv
./carry_policy_cegis 50 4 8 1 1 1234567 "$out" "smoke-${SLURM_JOB_ID}"
python3 verify_carry_policy.py "$out"
grep -q $'RESULT\tstatus=complete' "$out"
