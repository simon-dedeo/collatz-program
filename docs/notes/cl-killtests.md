# CL kill-tests: three time-boxed yes/no verdicts

2026-07-20. Code + CSVs: `experiments/cl-killtests/` (`test1_neutral_graph.py`,
`test2_neutral_cycle.py`, `test3_forcing_word.py`; `csv/*`). Reuses
`experiments/pressure-cert2/{automaton,exact_weights,combined,m2_profile}.py`.
All load-bearing facts are exact rationals; cross-checked on certified
eigenvectors `experiments/kl/cert_k1{5,6}_C.npy`. Extends the `(J=3,L_w=6)`
falsification of `pressure-certificate-2.md` per `gpt-falsification-triage.md`.

## TEST 1 -- does the CL obstruction persist at J=4,5? VERDICT: PERSISTS (CL class dead)

For `(J,L_w) in {(4,6),(4,12),(5,6)}`. `x4` acts as a single `3^{J-1}`-cycle on
`Q_J`, so `E_J` (first J backward-orbit points of `-1`) is J consecutive nodes on
it; the complement `C = Q_J \ E_J` is the rest plus branch chords. Results
(`csv/test1_neutral_graph.csv`): a zero-charge cycle ALWAYS exists -- the B2
self-loop at ball 2 (2 not in E_J for J<=5), plus one nontrivial SCC of size 23
(J=4) / 75 (J=5). On the aligned face the per-edge face operators are
`T,B2 -> id`, `B8 -> swap (j->2j)`; the cycle-label semigroup is `{id, swap}`,
which is exactly the stabilizer of the co-spine ray `R(2,-1,-1)`. Every
zero-charge cycle therefore has a nonconstant fixed face-vector (constrained
JSR = 1; TEST 2.B gives the exact multiplier). L_w is irrelevant at the
zero-charge level: (4,6)=(4,12). The obstruction is not resolved by mechanism 1
(charge is not a feedback set: `E_J` misses whole branch cycles) nor mechanism 2
(the aligned holonomy stabilizes, not mixes). CL class is dead; no larger J in
{4,5} revives it.

## TEST 2 -- nonlinear calibrated neutral cycle? VERDICT: EXISTS (route (a) dead)

The `-1` spine fiber under the period-2 doubling relabeling (`R8` doubles
offsets). Profile `P=(1, a*, 2-a*)`, `a* = lambda^{1-alpha}` (renorm Thm 2:
small lift `= a*` for every positive solution). Exact checks
(`csv/test2_calibrated_profileA.csv`) at `lambda in {2, lambda_18, 15/8}`:
(i) the neutral (small) lift is the STRICT actual minimizer at both steps of the
cycle (margin `= 1 - a* > 0`, e.g. `1/3` at `lambda=2`); (ii) osc is EXACTLY
constant under the relabel (`= 2/3` at `lambda=2`). The linear face is marginal:
`(2,-1,-1)` is an eigenvector of the aligned self-referential block with the SAME
eigenvalue as `(1,1,1)`, so the normalized oscillation multiplier is EXACTLY 1
(`csv/test2_marginal_multiplierB.csv`). Data cross-check
(`csv/test2_certdataC.csv`): the true `-1` fiber has strict argmin margin ~0.30
and osc ~const (0.594 -> 0.607) while the argmin lift DOUBLES 0 -> 1 across
k=15 -> 16 -- the empirical calibrated neutral cycle. Route (a) dies exactly as CL.

## TEST 3 -- strict forcing word (the rescue)? VERDICT: NO SUCH WORD (rescue fails)

Searched all `9840` residue words `|W|<=8` over phases `{2,5,8}`, true
min-composition at `lambda=2`, contraction checked on the extreme rays of the
mean-zero profile cone (`csv/test3_forcing_word.csv`). The worst-case co-spine
oscillation multiplier is EXACTLY 1 for every word => achievable `eta = 0`; no
forcing word of any length. Non-circular reason: the all-0 top window is
forward-invariant under T/B2/B8 (shift `e=0`, `x2 c=0`) and INDEPENDENT of the
ball residue, and on it `T,B2 -> id`, `B8 -> swap`, both fixing `(2,-1,-1)`. So
for EVERY residue word the adversary carries the co-spine profile on the all-0
window and osc is preserved -- the obstruction does not depend on oscillation.

## Bottom line

All three verdicts are negative for the CL / nonlinear-contraction (route (a))
program: the `-1` co-spine oscillation mode is a genuine marginal invariant that
(1) survives as a zero-charge neutral cycle at every tested J, (2) is a true
nonlinear calibrated neutral cycle (strict min selection, exactly constant osc),
and (3) cannot be broken by any finite strict forcing word. This matches the
triage recommendation: pivot the main program to cycles / finite places, or to a
non-autonomous (renewal / global-measure) decay theorem; no autonomous
projective-contraction certificate can close at the `lambda_inf = 2` boundary.
Not a claim that `lambda_inf < 2` -- only that this route is closed.
