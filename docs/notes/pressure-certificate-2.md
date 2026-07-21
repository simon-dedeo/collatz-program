# Charged spine-face Lyapunov lemma (CL) at (J=3, L_w=6): design + verdict

2026-07-20. Code: `experiments/pressure-cert2/` (modules `m1`..`m6`, CSVs in
`csv/`, witness `falsification_witness.json`). Reuses the predecessor's
certified `exact_weights.py` (alpha-sandwich, per-weight monotone rational
enclosures) and `automaton.py` (ball automaton, exact index arithmetic).
Supersedes `pressure-certificate.md`. Target: the CL lemma of
`gpt-design-review.md`. **Verdict: FALSIFIED at (J=3, L_w=6)** — the
architecture does not close; the failure is exactly MARGINAL (growth rate 1),
which does NOT imply lambda_inf < 2.

## The architecture and the charge

Augmented state s = (low window `q mod 27`) x (depth-memory top-window u-class)
x (spine-face profile cell). Blocks are L_w=6 transport moves, phases
`2,8,5,2,8,5` (events B2@0, B8@1, B2@3, B8@4; tail p^6). The homogenized
profile map (sol-contraction L1-L3, affine source terms kept) is, on the
ALIGNED top-face (all base-4 digits of u in {0,3} => all shifts 0), a fixed
3x3 form: transport/B2 label perm = identity, B8 = swap `j->2j` (fixes 0,
swaps 1,2). **Charge (only definition Lemma 5 can price, confirmed by
gpt-5.6-sol):** `e(gamma) = #{low-window edge targets in E_3}`,
`E_3 = {5,20,26} = -1,-1/4,-1/16 mod 27`. Depth memory augments the STATE but
cannot redefine e; no top-window charge is justified by Lemma 5.

## Three exact facts that force falsification

1. **The oscillation-carrying face is exactly marginal** (`m2`, `m5`, exact
   rationals). The co-spine vector `(2,-1,-1)` is fixed by every aligned perm
   (identity fixes all; the swap fixes `(2,-1,-1)`). Hence it is an eigenvector
   of the aligned block with the SAME eigenvalue as the mean `(1,1,1)`:
   at lambda=2 both equal `4681/4096`; the identity holds for EVERY lambda and
   every symmetric policy `D0=D1=D2`. **Normalized oscillation multiplier == 1
   exactly** — reproducing renormalization's transversal spectrum {0,1}
   (`renormalization-at-minus-one.md` §6.1: "no autonomous transversal decay").

2. **Zero-charge cycles exist** (`m1`, `m5`, exact). The complement
   `C = Q_3 \ E_3 = {2,8,11,14,17,23}` is a single SCC of the ball automaton
   (edges T,B2,B8) avoiding E_3; e.g. B2 self-loop at ball 2, and the
   oscillation-carrying B8 at ball 8 (siblings {5,14,23}; drop the E-sibling 5,
   keep 14,23 in C). So the marginal face is realizable with e=0.

3. **No coupling forces alignment to charge** (gpt-5.6-sol, verified). The
   top-window (aligned/oscillation) and low-window (E_3 charge) are independent
   coordinates of the same r; the <4>-orbit of -1 fills Q_J, so "near -1" is
   not a static residue; the aligned class is reachable at every ball state.

Iterating (CL) around a zero-charge (e=0) cycle gives `Phi(T^n x) <= rho^n
Phi(x)` (state potentials cancel around a cycle). A normalized-oscillation
eigenvalue 1 forces `rho >= 1`, so `R6*rho >= R6 >= s(lambda) -> 1`, violating
(SG). CL is therefore impossible at (J=3, L_w=6).

## Corroboration and validation

- **Data ground truth** (`m4`, `m5`; cert_k15/16, exact int64): mass-weighted
  mean fiber oscillation is essentially equal on E_3 vs the zero-charge balls C
  (0.077 vs 0.070 at k=15; 0.070 vs 0.064 at k=16), and ~52% of eigenvector
  mass sits off E_3. Charge does not localize oscillation at J=3.
- **Envelope** (`m3`): a monotone (mass, range) upper-bound automaton. Mass
  part is exactly Lemma 5 — `rho_mass(full) = s(2) = 1`, `s(lam18)` at lam18
  (validates the mass multipliers). Normalized oscillation growth stays >= 1
  even on the zero-charge subgraph C (1.03 at lam=2), an upper bound consistent
  with the exact marginal value 1.
- **V1** exact index arithmetic (k=7,8) and **V2** exact ball-mass domination
  on cert_k15,16 both PASS (predecessor `validate.py`, reused). The
  falsification witness was re-derived by an independent stdlib/Fractions
  script (`m5_recheck.py`) that also re-reads cert_k15 from disk.

## Note on the coexisting ECH artifacts (different charge reading)

A parallel attempt in the same folder (`combined.py`, `echarge.py`,
`echarge_results.json`, `ech*_h.json`) reads "depth-memory charge" as a
TOP-window quantity: `b(e)=1` iff the target window is UNCOVERED (the
aligned/oscillation-carrying class). It reports a subcritical restricted
pressure (`R_unc=52435/57248<1`) and a tilted gap (ECH2: `z=21/20`,
`R=553647/529600`, `theta=60/64`, integer gap `R^b<z^a`). This is only a
Lemma-5-style PRESSURE sub-lemma for a re-defined charge, under an
**unproven annealing hypothesis `U(sigma)`** on the policy's u-digit split;
it contains no oscillation carrier `Phi`, no profile map `T`, no contraction,
and no pathwise-localization certificate — i.e. it does NOT verify (CL) or
(SG). Defining the charge as "uncovered window" makes "oscillation-carrying =>
charged" true by fiat, which is exactly the localization assertion the design
review §1-3 flags as circular if assumed; gpt-5.6-sol (Q1) likewise states a
top-window charge "cannot redefine e" and "would require a separate pathwise
comparison [that] does not follow from Lemma 5." So the ECH gap does not close
the program; it relocates the same marginal wall into an undischarged
localization hypothesis. (Those files were left untouched.)

## What this means for the program

The gap estimate to lambda_inf is **cycle growth rate = 1 (marginal), i.e.
zero** — the (CL) certificate cannot prove decay because the co-spine
oscillation mode has no autonomous decay and is not charged. This is NOT
evidence that lambda_inf < 2; it is the same marginal wall the
renormalization analysis already identified. Any viable localization must make
oscillation persistence itself the charged quantity (a genuine top-window /
depth-memory charge that Lemma 5's tilt does not currently price), or replace
the finite-gap goal by a slower-than-exponential (renewal / boundary-rate)
decay theorem. The finite tail ratio reached about `0.810` at `k=19`; a later
floating-only `k=20` scan gives about `0.824`, outside the preregistered
transient range. Absolute tails still decrease, but the finite ratios no
longer justify a geometric-limit extrapolation (`renormalization-at-minus-one.md`
§6.4).

---

# Part II. The window-charged quadruple (ECH pipeline): exact results, and reconciliation

Same day, second pipeline in the same folder (`combined.py`, `blocks.py`,
`dfa.py`, `echarge.py`, `facecone.py`, `validate2.py`, `recheck.py`,
`portable_cert.py`, `scale_akdeniz.py`; portable artifact
`cert_combined_J3Lw6.json` per `CLEAN_LEAN/GPU_CERTIFICATE_SPEC.md`). Part I
falsifies (CL) for the residue charge e = #(targets in E_3) — the only charge
the existing Lemma 5 prices. Part II makes the complementary object exact:
the full quadruple for the *window* charge b(e) = 1[target window uncovered],
together with the precise hypotheses under which Lemma 5-style pricing of
that charge would be legitimate. The two verdicts agree on the mathematics;
they differ in what is assumed. Nothing here contradicts Part I's
falsification, and Part I's critique of these artifacts is accepted with one
correction: the pipeline does contain a contraction certificate and a
pathwise-localization argument — both valid only inside the single-profile
envelope model (H2 below), which is exactly where Part I's marginal co-spine
cycle escapes it.

## II.1 Construction (J=3, L_w=6; 36,864 states, 368,640 edges)

States (ball q mod 27) x (first 6 base-4 digits D of u). Depth-memory
exceptional set: window D uncovered, via the exact rule covered iff |S|=3 or
|A|=3 (S = tail+B2 shift adds, A = B8 affine adds); verified against all
12,288 interval block matrices (T0a PASS), against pressure-cert's u-cell
enumeration (T0b PASS), and on raw integers at k=9,10 including exact borrow
cells (T1 PASS). Transitions: T shift (p/4 x4), B2 shift (q2/12 x12), B8
x2-digit map with carry (q8/6 x6); at lambda=2 weights are exactly rational
(1/4, 3/4, 3/2) and every column sums to 1 exactly (x2 is
Lebesgue-preserving): the annealed combined automaton is exactly critical,
uniform left Perron vector.

## II.2 The quadruple (exact, independently rechecked from disk)

1. tau < 1 off the exceptional set (single-profile envelope, hypothesis cone
   C_2): phase 2: tau <= 1334784073716871/1335762600856060 = 0.9992674
   (840/4096 windows covered); phase 5: tau <= 0.9943328 (672/4096);
   phase 8: nothing covered at L_w=6 (first coverage 0.377 at L=9).
   Uniform-[lam18,2] tau <= 0.9993435; K-degradation in blocks_tau.csv.
2. Bad-block amplification C = 1 projectively: all 12,288 block matrices
   have no zero rows (exact), hence Hilbert-metric nonexpansive.
3. Charge density theta = 60/64: in-model, each covered visit contracts d_H
   by tau, so osc > t forces all but O_t(1) visited states uncovered.
4. Tilted potential: ECH2 z = 21/20, exact R = 553647/529600, all rows
   verified in Fractions, integer gap R^64 < z^60 PASS. Restricted form
   ECH1: R_unc = 52435/57248 = 0.91593 < 1 on the uncovered-only
   subautomaton — the aligned component (containing the -1 spine face) is
   mass-subcritical in the annealed model. Both re-verified by recheck.py
   (independent code path, from-disk h sidecars, sha256 in the cert).

Face cone (option (a), facecone.csv): on strictly aligned windows, half have
|A| = 1; the pinned-lift 2x2 face contracts (tau_face <= 0.5386/0.5389/0.9629
by phase) but the pinned-scale multiplier interval [0.6001, 1.6665] contains
1 — the same marginal mode as Part I's exact (2,-1,-1) eigenvector (there
computed as exactly 1 at the symmetric policy). Option (a) cannot close the
leak; only the charged-pressure route (option (b)) does, conditionally.

## II.3 What the window charge costs: the two hypotheses

- (H1) u-split pricing U(sigma): M(q,De) <= sigma M(q,D). The annealed
  automaton is a true domination only at sigma = 1/4. This is precisely
  sol-Q1's "separate pathwise comparison" that Lemma 5 does not supply.
  The original measurements were only for depth `6 -> 7`: sigma_max =
  0.419 (k=15), 0.343 (k=16), with mass-weighted values 0.2514, 0.2505.
  Extrapolating those numbers to the proposed depth `9 -> 10` was invalid.
  The exact streamed audit `split_ratio_audit.py` gives unrestricted maxima
  0.9847, 0.9502, 0.8172, 0.6855, 0.5514 for `k=15..19`. Even after restricting
  to source-uncovered and transport-successor-uncovered cylinders, the `k=19`
  maximum is

      1892575973641960 / 3487969866821777 = 0.5426010103...,

  at `q=26`, `D=001232200_4`, child digit zero (41 coordinates out of 164).
  It exceeds `21/50=0.42` by exact cross multiplication. Only 233 of
  3,918,396 relevant transitions violate `0.42`; their child mass is about
  `2.3525e-4` of total eligible-child mass, so the failure is rare but
  genuine. This
  refutes the proposed uniform `U(21/50)` bound (and every smaller sigma) on
  the class containing this exact feasible subeigenvector; it does not refute
  scalar H1 with a larger, non-closing constant or an eventual theorem
  specialized to selected exact critical eigenvectors. The surviving
  pressure-closing shape is a state-dependent/vector conditional cone, not one
  global sigma. Full exact rows and source hashes:
  `experiments/pressure-cert2/csv/split_ratio_audit.csv`.
  The earlier depth-six sequence continues downward through k=19
  (0.4190, 0.3430, 0.2868, 0.2722, 0.2594), which is useful finite-scale evidence
  but not an all-level estimate. The earlier mass diagnostics remain:
  nu_k(aligned) = 0.015652/0.015633 vs Haar 0.015625 (0.2%); nu_k(unc) =
  0.9004/0.9008 vs annealed 0.90625 (0.7%).
- (H2) product cone / sibling independence: the tau of II.2(1) treats the
  block's several inputs as one profile. Part I's zero-charge marginal cycle
  is the exact witness that the *true* multi-input dynamics is not dominated
  by this envelope on the aligned face. Discharging H2 = the product-cone
  certificate over (fiber, transport-reference) pairs; not built.

## II.4 Reconciled verdict and the conditional chain

- With the residue charge (only one currently priced): (CL) FALSIFIED at
  (3,6) — Part I, exact witness.
- With the window charge: quadruple EXISTS exactly at (3,6) and the leak
  closes in-model — but pricing that charge is itself hypothesis H1, and the
  in-model localization is hypothesis H2. So the marginal wall is relocated
  into (H1)+(H2), both finite and testable but neither proved. The exact
  depth-nine audit above now falsifies the proposed uniform `U(21/50)` form on
  the tested feasible subeigenvectors; only a vector/state-dependent
  pressure-closing replacement remains empirically plausible.
- Chain: [quadruple (exact)] + (H1) + (H2) + (H3: lambda-uniform rows)
  + CLEAN_LEAN's formal terminal-potential/Chernoff => C1' => delta_k -> 0
  => lambda_k -> 2; with kernel-checked R', lambda_inf = 2.
- Scaled run BLOCKED, NOT launched (`scale_akdeniz.py`): `(3,9)` = 2.36M
  states is the first point where phase 8 covers (0.377), but the exact
  depth-nine audit above invalidates the claimed measured H1 margin. Computing
  another annealed pressure row certificate before replacing scalar H1 and
  product-envelope H2 would certify only the surrogate model. The proposed
  `(6,10)` = 255M run is likewise not authorized on the current architecture.
- Nothing found estimates lambda_inf < 2. Within the autonomous annealed
  surrogate, the exceptional component is strictly subcritical
  (`R_unc < 1`) and the only non-contracting mode found is the known
  eigenvalue-one renormalization mode; neither statement controls the actual
  all-level KL mass without the missing semantic/localization theorems.

External audit of Part II (gpt-5.6-sol, authorized): `sol_audit_answer.md`
(SSL fixed via certifi); adopted claims re-verified before use.

## II.5 External audit outcome (gpt-5.6-sol, adopted after verification)

Confirmed: (i) C = 1 nonexpansiveness from no-zero-rows (column action,
interior points — our case); (ii) Chernoff orientation R^b < z^a correct,
charges additive and encoded once; reducibility costs only a polynomial
prefactor under the strict inequality; (iii) the greedy factor-6 disjoint
selection and theta = 15/16 counting. Adopted refinements: (a) localization
must be stated in *chronological cocycle time* — blocks are per-level
transport windows; since B8 acts by x2 on the window, a bounded-overlap
lemma for descent-transformed windows is required, and covered visits may
only be counted at phases holding an actual tau certificate (phases 2, 5 at
L_w = 6); (b) R_unc < 1 alone needs bounded connector norms and boundedly
many covered excursions (rows here are bounded by p + q8 = 7/4; ECH2 is the
self-contained alternative); (c) the correct discharge of H1 (and jointly
H2) is a finite two-sided/vector-state automaton retaining sibling masses
with a certified boundary conditional cone via exact LP — uniform splitting
(the annealed model) "silently assumes the desired independence", which is
exactly why it is declared a hypothesis here. Full text:
`experiments/pressure-cert2/sol_audit_answer.md`.
