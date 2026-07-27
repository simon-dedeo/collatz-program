#!/bin/bash
#SBATCH --job-name=collatz-bouncer-atlas
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=04:00:00
#SBATCH --signal=B:USR1@300
#SBATCH --array=0-3
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/bouncer-%A_%a.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/bouncer-%A_%a.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
out=results/bouncer-m12-h12-d5-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.tsv
worker_pid=""
forward_stop() { if [[ -n "$worker_pid" ]]; then kill -USR1 "$worker_pid" 2>/dev/null || true; fi; }
trap forward_stop USR1
./bouncer_atlas 12 12 5 "$SLURM_ARRAY_TASK_ID" 4 128 "$out" "production-${SLURM_ARRAY_JOB_ID}" &
worker_pid=$!
status=0
while true; do
    set +e
    wait "$worker_pid"
    status=$?
    set -e
    if kill -0 "$worker_pid" 2>/dev/null; then continue; fi
    break
done
test "$status" -eq 0
sha256sum "$out" > "$out.sha256"
