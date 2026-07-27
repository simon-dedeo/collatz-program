#!/bin/bash
#SBATCH --job-name=collatz-policy-collect
#SBATCH --account=mth260010p
#SBATCH --partition=RM-shared
#SBATCH --qos=rm
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --time=00:30:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/policy-collect-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/policy-collect-%j.err
set -euo pipefail
: "${SOURCE_ARRAY:?submit with --export=ALL,SOURCE_ARRAY=jobid}"
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load python/3.8.6
mapfile -t files < <(printf '%s\n' results/carry-policy-${SOURCE_ARRAY}_*.tsv | sort)
test "${#files[@]}" -eq 4
for file in "${files[@]}"; do sha256sum -c "$file.sha256"; python3 verify_carry_policy.py "$file"; done
out=results/carry-policy-combined-${SOURCE_ARRAY}.tsv
python3 combine_carry_policy.py "$out" "${files[@]}"
sha256sum "$out" > "$out.sha256"
