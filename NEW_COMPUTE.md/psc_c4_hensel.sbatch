#!/bin/bash
#SBATCH --job-name=collatz-c4-hensel
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=13:00:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c4-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/c4-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
for spec in '1000000000 1 1 1' '1000000000 2 1 1' '1000000000 3 1 1' \
            '1000000000000 1 2 1' '1000000000000 2 2 1' '1000000000000 3 2 1' \
            '1000000000000 2 2 2'; do
  set -- $spec
  out=results/c4-hensel-B${1}-d${2}e${3}f${4}-${SLURM_JOB_ID}.tsv
  ./hensel_atlas "$1" "$2" "$3" "$4" "$out"
  sha256sum "$out" > "$out.sha256"
done
