# Arctic experiment status

Successor audit: 2026-07-20. Mathematical statement and proof sketches live
in `docs/notes/arctic-nogo.md`; this file records only the computational
artifacts and their scope.

## Independently checked witnesses

Running `python3 verify.py` rechecks, without z3, the five dimension-one
arctic-integer witnesses in `FOUND_AZ_d1_K2_R{1,2,3,5,6}.txt`. Each makes its
selected rule strict while weakly orienting the full system. These witnesses
falsify the naive blanket no-go; they do not contradict the calibrated
Theorem A, whose target is the pair of top dependency rules; Theorem B concerns
all seven Z rules under the stronger arctic-natural/extended setting.
The checker also verifies a separate scalar counterexample showing why Theorem
A must require **both** dependency-pair rules weak: all seven Z rules can be
weak and `I_s` strict while `I_t` remains unoriented.

## Preserved bounded sweeps

Five orphaned writers were still running when Codex took over, despite the
handoff saying all background lanes were stopped. They were terminated with
`SIGTERM` after their exact commands and open output files were resolved. All
complete rows already written were preserved:

- `dp_K1.csv`: one additional timeout row, `d=5`, `I_s`; the paired `I_t`
  query was never run. Final coverage: 9/10 planned queries.
- `sweep_d6_K3.csv`: two additional timeout rows, `d=5`, `R4,R5`. Final
  coverage: 33/84 planned queries.
- `sweepZ_d6_K3.csv`: three additional rows (`d=5,R6` timeout;
  `d=5,R7` unsat; `d=6,R1` timeout). Final coverage: 36/84 planned queries.
  This script uses the obsolete blank-free encoding rejected by the calibrated
  note, so its UNSAT row is not evidence for Theorem A or B.

An `unknown`/timeout row proves nothing, and none of these late rows advances
the all-dimension theorems. The bounded sweeps remain diagnostics and
falsification searches only.

## Current theorem status

- **Candidate Theorems A and B:** successor audit found a gap in the original global-
  slope/cyclicity proof for reducible max-plus matrices, then replaced it with
  an elementary all-dimension weighted-walk pumping argument. It is written out
  in `docs/notes/arctic-nogo.md` and Lean formalization is requested; repo policy
  keeps the general theorem provisional until then. `verify.py` checks marked
  macros for `N=1..12`, but the bounded searches are not the general proof.

No arctic job is currently running.
