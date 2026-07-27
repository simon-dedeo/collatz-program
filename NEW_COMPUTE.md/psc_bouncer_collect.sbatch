#!/bin/bash
#SBATCH --job-name=collatz-bouncer-collect
#SBATCH --account=mth260010p
#SBATCH --partition=RM-shared
#SBATCH --qos=rm
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --time=00:20:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/bouncer-collect-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/bouncer-collect-%j.err
set -euo pipefail
: "${SOURCE_ARRAY:?submit with --export=ALL,SOURCE_ARRAY=jobid}"
cd /ocean/projects/mth260010p/sdedeo/new_compute
mapfile -t files < <(printf '%s\n' results/bouncer-m12-h12-d5-${SOURCE_ARRAY}_*.tsv | sort)
test "${#files[@]}" -eq 4
for file in "${files[@]}"; do sha256sum -c "$file.sha256"; done
out=results/bouncer-m12-h12-d5-combined-${SOURCE_ARRAY}.tsv
python3 combine_bouncer_shards.py "$out" "${files[@]}"
sha256sum "$out" > "$out.sha256"
