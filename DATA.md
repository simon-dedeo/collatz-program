# Large data artifacts (excluded from git; GitHub 100MB limit)

- KL eigenvectors `eigvec_k{12..20}.npy` and certified-vector sidecars
  `cert_k{16..20}_C.npy`: canonical copies on PSC at
  `/ocean/projects/mth260010p/sdedeo/collatz/kl/` (transfers via DTN
  `data.bridges2.psc.edu`); working copies on this machine under
  `experiments/kl/`. Certificate JSONs (with sha256 pins of the sidecars)
  ARE committed.
- Census/family/expsum raw TSVs: `results/` (committed) and remotes
  `akdeniz:~/collatz/`, `ganesha:~/collatz/`.
