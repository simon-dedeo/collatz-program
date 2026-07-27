#!/bin/bash
#SBATCH --job-name=collatz-c3b-collect
#SBATCH --account=mth260010p
#SBATCH --partition=RM-shared
#SBATCH --qos=rm
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --time=00:20:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c3b-collect-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c3b-collect-%j.err
set -euo pipefail
: "${SOURCE_ARRAY:?submit with --export=ALL,SOURCE_ARRAY=jobid}"
cd /ocean/projects/mth260010p/sdedeo/new_compute
mapfile -t files < <(printf '%s\n' results/c3b-d27-${SOURCE_ARRAY}_*.tsv | sort)
test "${#files[@]}" -eq 3
for f in "${files[@]}"; do sha256sum -c "$f.sha256"; done
out=results/c3b-d27-combined-${SOURCE_ARRAY}.tsv
python3 combine_zero_shards.py "$out" "${files[@]}"
sha256sum "$out" > "$out.sha256"
