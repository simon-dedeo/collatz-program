# Archival warning for model-consultation artifacts

The files `consult_gpt.py`, `gpt_q2.py`, `gpt_body.json`, `gpt_raw.json`,
`gpt_consult_stdout.log`, and the saved consultation replies preserve the exact
prompts and responses used during the 2026-07-20 exploration. Some prompts say
that all primes below `10^6` were tested, that the theorem is true, or that
2--3 coupling is the proved mechanism. Those claims are retracted.

The actual exact scope is:

- 93 primes `5<=p<=499` in the broad grid;
- seven selected scale-test primes;
- fourteen exact-DP candidates chosen from 105 primes satisfying the separate
  cap `|<2,3>|<=400` in a scan below `10^6`.

The current claim calibration, corrected formulas, and open proof obligations
are in `docs/notes/mixed-radix-flattening.md`. These archived prompts are not
evidence and should not be quoted as the state of the project.
