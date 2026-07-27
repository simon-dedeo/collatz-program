#!/bin/bash
#SBATCH --job-name=collatz-scale
#SBATCH --account=mth260010p
#SBATCH --partition=RM
#SBATCH --qos=rm
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --time=00:30:00
#SBATCH --output=/ocean/projects/mth260010p/sdedeo/new_compute/logs/scale-%j.out
#SBATCH --error=/ocean/projects/mth260010p/sdedeo/new_compute/logs/scale-%j.err
set -euo pipefail
cd /ocean/projects/mth260010p/sdedeo/new_compute
module load gcc/13.3.1-p20240614
export OMP_NUM_THREADS=128 OMP_PROC_BIND=spread OMP_PLACES=cores
mkdir -p results/scale
/usr/bin/time -v ./kl_soft_spectrum 14 1.9 64 500 1e-8 results/scale/k1.tsv -
/usr/bin/time -v ./kl_frustration_scan /ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k17.npy 1.8616883 results/scale/k2.tsv
/usr/bin/time -v ./carry_budget 50 28 250 results/scale/c1.tsv
/usr/bin/time -v ./minplus_profile 1000000 60 6 100000 results/scale/c2.tsv
/usr/bin/time -v ./zero_carry_champions 15 128 results/scale/c3.tsv
/usr/bin/time -v ./hensel_atlas 1000000 2 2 2 results/scale/c4.tsv
