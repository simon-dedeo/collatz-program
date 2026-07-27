#!/bin/bash
#SBATCH --job-name=collatz-build
#SBATCH --account=mth260010p
#SBATCH --partition=RM-shared
#SBATCH --qos=rm
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=00:20:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/build-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/build-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
mkdir -p logs results
module load gcc/13.3.1-p20240614
make clean all CC=gcc
export OMP_NUM_THREADS=4
export OMP_PROC_BIND=close
export OMP_PLACES=cores
make smoke
