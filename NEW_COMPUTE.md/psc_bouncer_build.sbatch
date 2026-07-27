#!/bin/bash
#SBATCH --job-name=collatz-bouncer-build
#SBATCH --account=mth260010p
#SBATCH --partition=RM-shared
#SBATCH --qos=rm
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=00:20:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/bouncer-build-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/bouncer-build-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
mkdir -p logs results/smoke
module load gcc/13.3.1-p20240614
make bouncer_atlas CC=gcc
export OMP_NUM_THREADS=4 OMP_PROC_BIND=close OMP_PLACES=cores
./bouncer_atlas 2 2 2 0 1 16 results/smoke/bouncer.tsv "build-${SLURM_JOB_ID}"
python3 verify_bouncer_atlas.py results/smoke/bouncer.tsv
for shard in 0 1 2 3; do
    ./bouncer_atlas 2 2 2 "$shard" 4 16 "results/smoke/bouncer-shard-${shard}.tsv" "sharded-${SLURM_JOB_ID}"
done
python3 combine_bouncer_shards.py results/smoke/bouncer-combined.tsv results/smoke/bouncer-shard-{0,1,2,3}.tsv
python3 verify_bouncer_atlas.py results/smoke/bouncer-combined.tsv
./bouncer_atlas 4 4 4 0 1 128 results/smoke/bouncer-scale.tsv "scale-${SLURM_JOB_ID}"
./bouncer_atlas 8 8 5 0 1 4 results/smoke/bouncer-signal.tsv "signal-${SLURM_JOB_ID}" &
signal_pid=$!
sleep 1
kill -USR1 "$signal_pid"
wait "$signal_pid"
grep -q $'RESULT\tstatus=partial' results/smoke/bouncer-signal.tsv
sha256sum results/smoke/bouncer.tsv results/smoke/bouncer-scale.tsv results/smoke/bouncer-signal.tsv
