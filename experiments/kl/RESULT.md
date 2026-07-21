# RESULT.md — Certification of improved Krasikov–Lagarias lower-bound exponents

Date: 2026-07-20 (extended same day through k = 19). Paper: Krasikov–Lagarias, *Bounds for
the 3x+1 problem using difference inequalities* (arXiv:math/0205002; Acta Arith. 109 (2003)
237–258). See `THEOREM.md` for the exact hypotheses and `certify.py` for the certifier. All
certificates verified in exact integer arithmetic (Python bigints; no floating point in the
verification chain).

## Bottom line

**Trust-chain correction (2026-07-21).** The feasible points below remain exact.
However, `verify_termination_obstruction.py` checks a legal `k=5` path that
invalidates the derivation of equation (3.2) and directly falsifies the
history-free subtree step in the published proof of KL Theorem 3.1. The path
and deletion tests are also independently kernel-checked in
`CLEAN_LEAN/CleanLean/KL/TerminationObstruction.lean`. A second exact checker,
`verify_all_three_deletion.py`, reaches a split at which the literal rule makes
all three minimum alternatives deletion-eligible. Neither certificate refutes
termination or Theorem 2.2. A third finite checker shows that local split
validity plus the paper's assignment-specific invariant does not preserve that
invariant across a split. CLEAN_LEAN independently checks both newer defects
and proves the abstract branch-arrival compactness theorem. Lean commit
`3d6a186` also checks the complete replacement: the well-founded all-`k`
raw-history producer, root-level occurrence provenance, live deterministic
pruning, a common positive lag, and the abstract feasible-point comparison
theorem. There is no remaining termination, deletion, provenance, or
retarded-tree assumption. Commit `331ff48` defines the literal statewise
predecessor family and proves target-pool nonemptiness, normalization, and
monotonicity. Commit `729f5fa` proves its full D1--D3 base system for every
`k>=2`, and commit `76ec861` closes the fixed-target/all-target counting
transfer. That audit also found that the paper's printed equation (2.1) is
false as an equality: exactly, `φ^7_2(1)=3` while
`φ^{14}_2(0)=φ^5_2(0)=2`. Lean commit `58f0ef8` kernel-checks the exact
targetwise decomposition and ordinary-count transfer. For the paper's full
target-class definition, infimizing gives
`φ^m_k(y) ≥ 1+φ^{2m}_k(y−1)`, which has the direction needed for the same
exponent transfer. The Lean class-2 family need not define this class-1 row;
its final wrapper uses the direct ordinary-count inclusion. Thus this is a genuine erratum—the finite counterexample is
checked by `verify_equation_2_1_obstruction.py`—but not a new conjectural
obstruction. A companion exact checker,
`verify_predecessor_base_inequalities.py`, independently verifies the
targetwise D1--D3 reverse-tree partitions and strengthened constants in 660
bounded cases; commit `729f5fa` supplies their all-`k` Lean proof and passes the
8,717-job audit. Commit `76ec861` supplies the exact cutoff, arbitrary-target,
and exponent wrappers. The finite mathematical chain is therefore complete.
See `TERMINATION_AUDIT.md`.

**The certified feasible points below give, for every positive integer
a ≢ 0 (mod 3) and all sufficiently large x ≥ x₀(a):**

    π_a(x) ≥ x^γ   for every fixed γ < log₂(λ_cert),

with the certified values

| k  | λ_cert (exact rational)   | γ_cert = log₂ λ_cert | constraints | min rel. slack | C^max (⇒ Δ₁)   |
|----|---------------------------|----------------------|-------------|----------------|----------------|
| 12 | 18064231/10^7 = 1.8064231 | 0.8531358401…        | 177,147     | 1.85e-07       | ≤ 146.97       |
| 13 | 18188232/10^7 = 1.8188232 | 0.8630053116…        | 531,441     | 2.02e-07       | ≤ 223.53       |
| 14 | 18307718/10^7 = 1.8307718 | 0.8724519749…        | 1,594,323   | 1.82e-07       | ≤ 339.26       |
| 15 | 18419679/10^7 = 1.8419679 | 0.8812479198…        | 4,782,969   | 9.50e-08       | ≤ 516.32       |
| 16 | 18522343/10^7 = 1.8522343 | 0.8892666051…        | 14,348,907  | 5.95e-08       | ≤ 793.06       |
| 17 | 18616883/10^7 = 1.8616883 | 0.8966115446…        | 43,046,721  | 3.90e-08       | ≤ 1207.44      |
| 18 | 18703245/10^7 = 1.8703245 | 0.9032885984…        | 129,140,163 | 1.23e-07       | ≤ 1834.78      |
| 19 | 18783127/10^7 = 1.8783127 | 0.9094372617…        | 387,420,489 | 1.22e-07       | ≤ 2782.62      |

All rows were verified in exact integer arithmetic at generation and from the
on-disk certificates in this worktree. Artifact-portability caveat: the
sidecars for `k=16..19` are 109 MB through 2.9 GB and are hash-pinned by the
tracked JSONs but ignored by git; a fresh clone is self-contained through
`k=15`. During the successor audit, a fresh run of the same reference verifier
again passed the `k=19` sidecar hash and all 387,420,489 inequalities. This was
an exact rerun, not a second independently implemented verifier. The generic
certificate-to-counting implication is kernel-checked in Lean, but the large
`k=19` array has not been ingested there: no concrete Lean declaration yet
constructs `LevelFeasible 19 (18783127/10^7)`. Thus the result follows under
the repo's accepted mixed exact-Python + kernel-Lean trust policy; it is not a
single end-to-end Lean-native artifact.

In the paper's own presentation style (rounding the exponent down absorbs the
a-dependent constant): **π_a(x) ≥ x^0.9094 for all a ≢ 0 (mod 3) and x ≥ x₀(a)** — improving
the 2003 record exponent 0.84 (γ₁₁ = log₂ 1.7922310 = 0.8417566) via the k = 19 system; any
fixed exponent below 0.9094372 is equally verified. Fully explicit form for any a ≡ 2 (mod 3)
not in a cycle, from Theorem 2.2 directly: π_a(x) ≥ π*_a(x) ≥ Δ₁ (x/a)^{γ_cert} for ALL x ≥ a,
with Δ₁ = 1/(4 max c^m) as tabulated (k = 19:
Δ₁ = 10^12/(4·2782615993072981) ≈ 1/11130.5).

The claimed candidates (float thresholds; γ̂ = log₂ λ̂: 0.8724524 at k = 14,
then 0.8812483, 0.8892670, 0.8966119, 0.9032890, and 0.9094376 at
k = 15–19) are all confirmed by exact feasible points, with the
uniform caveat that each *certified* value is log₂ of the rational λ_cert chosen 5e-7 below
the float threshold on the 10^-7 grid (exactly as KL themselves published the truncated
λ₁₁ = 1.7922310 rather than the float optimum) — so each certified γ is ~4e-7 below the
quoted candidate. That difference is certification margin, not a disagreement.

## What exactly was certified

For each k, the certificate `cert_k{k}.json` contains integers (A, B2, B8, C[0..3^{k-1}-1])
encoding λ = A/10^7, W2 = B2/10^15, W8 = B8/10^15, c^m = C[i]/10^12 (i indexes ascending
residues m ≡ 2 mod 3, mod 3^k; for k ≥ 15 the C array lives in a sha256-pinned int64 .npy
sidecar). `certify.py verify` re-derives the residue system from k alone
and checks, in exact integer arithmetic:

1. 10^7 < A ≤ 2·10^7 (Theorem 2.2's hypothesis 1 ≤ λ ≤ 2, and λ > 1);
2. 2^50508 < 3^31867 (hence P/Q = 50508/31867 < α = log₂3);
3. B2^Q·A^{2Q−P} ≤ 10^{15Q}·10^{7(2Q−P)} (hence W2 ≤ λ^{P/Q−2} < λ^{α−2});
4. B8^Q·10^{7(P−Q)} ≤ A^{P−Q}·10^{15Q} (hence W8 ≤ λ^{P/Q−1} < λ^{α−1});
5. C[i] ≥ 10^12 for all i (LP constraint (L0): c^m ≥ 1);
6. for every m ∈ [3^k] (LP constraints (L1)–(L3) with auxiliaries at their maximal values
   c̄^m_{k−1} of (2.15), which is the paper's own reduction — see THEOREM.md §2):
   C[i]·A²·10^15 ≤ C[4m]·10^29 + B·A²·min₃(C)  (B = B2 if m ≡ 2 mod 9, B8 if m ≡ 8 mod 9,
   absent if m ≡ 5 mod 9; indices: 4m mod 3^k; min₃ over (4m−2)/3 resp. (2m−1)/3 mod 3^{k−1}
   + j·3^{k−1}, j = 0,1,2).

Steps 2–4 make the verification immune to the irrationality of α = log₂3: since W2 < λ^{α−2}
and W8 < λ^{α−1} multiply nonnegative variables on the ≤-side, step 6 certifies a *strictly
tighter* system than L^NT_k(λ); its feasibility implies feasibility of L^NT_k(λ) itself.
Therefore the finite feasibility hypotheses of the abstract replacement
comparison hold at `(k, λ_cert)`. For any positive monotone function family
satisfying the KL base system, the kernel-checked elimination theorem gives
`φ^m_k(y) ≥ Δ₁ c^m_k λ_cert^y` for all `m ∈ [3^k]` and `y ≥ 0`, with
`Δ₁ = 1/(4 max c^m_k)`.
Commit `76ec861` performs the `π_a` transfer with the corrected one-sided
mechanism (see `THEOREM.md` §4); it does not use the false equality (2.1).

Floating point was used ONLY to search for the candidate (λ_cert and the eigenvector before
rounding down to the 10^-12 grid); nothing in the acceptance decision depends on it.

## Does any stated hypothesis in the paper limit k? — No; proof audit caveat

- Theorem 2.2 and its supporting chain (Thms 3.1, 3.2, 4.1, 5.1) are stated
  for all k ≥ 2; k ≤ 11 in §6 is a 2002 computational budget, not a hypothesis.
  The successor audit invalidates a step in the printed proof of Theorem 3.1,
  but Lean commit `3d6a186` proves an all-`k` replacement at the abstract
  base-system level. Commit `331ff48` defines the literal family and proves
  P1/P2; commit `729f5fa` proves D1--D3; commit `76ec861` proves the final
  all-target exponent wrapper. §6 proves
  λ_k ≤ λ_{k+1} by lifting feasible solutions, and poses λ_k → 2 as the open
  problem; our `k=12..19` points are new finite-level lower bounds for the very
  sequence the paper defines.
- The superscript "NT" means "No Truncation" (of advanced terms); **there are no N or T
  truncation parameters** and nothing grows with k except the number of residue classes
  3^{k-1}. The constant C^max_k (max principal variable) affects only the constant
  Δ₁ = 1/(4·C^max_k), never the exponent; it grows (≈147, ≈224, ≈339 at k = 12, 13, 14,
  vs 98.4 at k = 11), consistent with the paper's observation that C̃^max_k grows
  exponentially — harmless, as it only shifts x₀(a).
- The retarded-shift bound ν ≤ 2 used for Δ₁ holds for every k (all shifts produced by the
  back-substitution are ≥ −2 by construction; paper line 346), and requires λ ≤ 2 — satisfied.
- The derived eliminated system I_k(EL) is astronomically large for k ≥ 5 (paper Table 1) but
  is never constructed in applying Theorem 2.2 — only L^NT_k(λ) feasibility is exhibited,
  which is exactly what our certificates do. No overflow-type issue arises: our verification
  is arbitrary-precision integer arithmetic throughout.

## Interpretations / deviations from the paper (all conservative)

1. **Irrational exponents λ^{α−2}, λ^{α−1}.** The paper does not document how Applegate's
   computation handled these (Theorem 6.1: "by finding a positive feasible solution by
   computer … for λ = 1.7922310"; no exact-arithmetic device appears). We did NOT copy an
   undocumented device; we replaced the coefficients by certified rational lower bounds
   (items 2–4 above), which only tightens the LP. mpmath was not needed; the bounds are
   certified by two integer power comparisons plus 2^P < 3^Q.
2. **λ_cert below the float threshold.** The feasible region is λ ≤ λ_k (paper §6: λ_k is the
   supremum of feasible λ); we certify at λ_cert = floor(λ̂_k·10^7 − 5)/10^7, i.e. 5e-7 below
   the float estimate, mirroring KL's own truncation of λ₁₁. Direction of all inequalities
   checked is verbatim (2.9)–(2.14) — c^m on the small side. No monotonicity-in-λ claim is
   used anywhere in the certification: feasibility is checked directly at λ_cert.
3. **Eigenvector rounding.** The float Perron vector (Collatz–Wielandt ratios pinched to
   ~1+2e-7) is normalized to min = 1 and rounded DOWN on the 10^-12 grid (finer than the
   task's suggested 10^-9 — strictly safer, certificate ~2.7–24 MB).
4. **pdftotext artifacts.** In the extracted text of (2.12)–(2.14) the superscripts read
   "m+3k"; they are m+3^{k−1}, m+2·3^{k−1} (unambiguous from (2.6), (2.15), (4.6)–(4.7) and
   the k = 2 appendix). Our k = 2 system reproduces the paper's Appendix I₂ literally
   (selftest), and our float solver reproduces the full Table 2 λ-column (k = 2..11) to the
   published 10^-6 precision — strong evidence the transcribed system is theirs.
5. **Counting-transfer correction and cycle caveat.** Theorem 2.2 bounds φ^m_k, defined via inf over
   a ≡ m (mod 3^k) *not in a cycle*; Theorem 6.1 states the π_a bound for all positive
   a ≢ 0 (mod 3). Printed equation (2.1) is false as an equality; the exact
   replacement is the targetwise decomposition
   `P*_a(x)={a} ⊔ P*_{2a}(x)` for nonperiodic `a ≡ 1 (mod 3)`, which yields
   `φ^m_k(y) ≥ 1+φ^{2m}_k(y−1)` and the same lower-bound transfer. More
   directly, use `π_a(x) ≥ π_{2a}(x)`. If `a` is in any hypothetical positive
   cycle, choose a sufficiently large nonperiodic `b=2^r a ≡ 2 (mod 3)`;
   then `T^[r](b)=a` and `π_a(x) ≥ π_b(x)`. This avoids assuming that the known
   `{1,2}` cycle is the only one. We retain Theorem 6.1's statement form: γ
   strictly below `log₂ λ_cert`, `x ≥ x₀(a)`.
6. **Paper-internal precision notes.** Table 2's γ-column is log₂(λ) truncated at the 7th
   decimal (log₂ 1.7922310 = 0.8417566, printed as 0.8417560); the program-status quotes of
   "0.8417566" and our "0.8724524" refer to log₂ of the float-optimal λ, while certified
   exponents are log₂ of the (slightly smaller) rational λ_cert.

## The k = 15–19 pipeline (large candidates, local exact verification)

Levels 15–18 use candidate eigenvectors from a GPU run (bridges2 H100, `kl_gpu.py`, a cupy
port of the identical constraint system) fetched via the PSC data-transfer node
(`data.bridges2.psc.edu`; k = 18 file sha256-matched against the remote copy). **No
correctness burden rests on the GPU**: its vectors are candidates only. Float thresholds
λ̂ = 1.8419684 / 1.8522348 / 1.8616888 / 1.8703250 (the GPU run also reproduced the certified
k = 12–14 thresholds exactly, and its k = 14 eigenvector matches the locally certified vector
to 4.3e-6 relative — the expected λ̂-vs-λ_cert offset scale). The local
`k=19` eigenvector and threshold were consumed by the same verifier, although
their candidate-generation provenance is not documented in git. Pipeline per
level:

1. λ_cert = (round(λ̂·10^7) − 5)/10^7, as for k = 12–14.
2. The GPU vector (saved at λ̂) is power-iterated locally at λ_cert until
   min F(c)/c > 1 + 2e-8 — needed because moving λ̂ → λ_cert lowers the λ^{α−1} coefficient,
   and indeed the raw vectors started at cwlo ≈ 0.9999998 (20 iters sufficed for k = 15–17,
   40 for k = 18).
3. Round down on the 10^-12 grid; exact-integer verification of every constraint, now with
   a dict-free chunked verifier (`verify_exact_big`; arithmetic indexing idx(m) = (m−2)/3,
   required at this scale) — **regression-tested to agree exactly (same slack, same argmin)
   with the original k ≤ 14 verifier on all three existing certificates**, and cross-checked
   against `build_exact` for k = 2..8 in the selftest.
4. Certificate storage for k ≥ 15: int64 `.npy` sidecar (cert_k{k}_C.npy) with its sha256
   pinned inside cert_k{k}.json (inline JSON would be ~2 GB at k = 18); the verifier checks
   the digest before use.

Verification times (single core, exact bigint arithmetic): k = 15: 1.5 s;
k = 16: 3.6 s; k = 17: 10.6 s; k = 18: 29.3 s; k = 19: 86.7 s
(387,420,489 constraints, successor rerun). The k=15–18 generation/refinement
times were 3 s / 7 s / 18 s / 61 s. Verification ran on the local Mac; GPU
vectors are candidates only.

## Falsification tests (the certifier has teeth)

On the k = 12 certificate: raising λ above the threshold (A = 18064300) → 11+ constraint
failures; perturbing a single coordinate C[12345] by +1% → fails; inflating B2 by 10^-7 →
fails the W2 integer check (iii). Genuine certificates pass with min relative slack ~2e-7,
matching the Perron margin ρ(λ_cert) − 1 (CW-pinched to 12 digits) — the slack is exactly
where theory predicts, another consistency check.

Repeated on the k = 15 certificate (the chunked-verifier code path): λ raised above the
threshold (A = 18419750) → fails (11+ violations); one coordinate perturbed +1% → fails;
genuine certificate passes (slack 9.50e-08). The min-rel-slack values for k = 15–17 (~4–10e-8)
are smaller than for k ≤ 14 because refinement stops at the 2e-8 CW gate rather than running
to full convergence; k = 18's 40-iteration refinement landed at 1.2e-07. All positive, all
exact.

## Files

- `THEOREM.md` — exact hypotheses, LP definition, solver correspondence, k-limit analysis.
- `certify.py` — generator + independent exact verifier (`selftest`, `gen`, `genvec`,
  `verify` modes; dict-free chunked verification for large k).
- `cert_k{12..14}.json` — certificates with inline C (rational feasible points).
- `cert_k{15..19}.json` + local `cert_k{15..19}_C.npy` — certificates with
  sha256-pinned int64 sidecars (36 MB / 109 MB / 328 MB / 985 MB / 2.9 GB).
  Only `k=15` is tracked by git; the larger sidecars require external artifact
  transport before a fresh clone can reverify them.
- `cert_k{12..19}_report.json` — tracked verification reports.
- `eigvec_k{14..19}.npy` — candidate eigenvectors; candidates are not part of
  the exact acceptance path and are ignored by git.
- `kl_paper.txt` — pdftotext extraction of the paper (line numbers cited in THEOREM.md).
- `verify_equation_2_1_obstruction.py` — exact affine lower bounds plus two
  independent finite enumerators for the `k=2` counterexample to printed (2.1).
- `solver_k14.log` — float threshold estimates λ̂_k for k = 2..14 (CPU);
  k = 15–18 thresholds came from the GPU logs on Bridges-2. The tracked k=19
  report records `lambda_float_estimate=1.8783132`.
