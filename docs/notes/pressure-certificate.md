# Finite pressure certificate for sol's Lemma 3 + Lemma 5: construction, search results, verdict

2026-07-20. Code: `experiments/pressure-cert/` (`pressure_cert.py`, modules
`exact_weights.py`, `automaton.py`, `lemma3.py`, `lemma5.py`, `validate.py`;
CSV outputs alongside). Targets: sol-pressure.md Lemma 3 (finite-block
Birkhoff contraction) and Lemma 5 (restricted-pressure gap, certificate form
(2.9)-(2.10)). All load-bearing arithmetic exact (integer/Fraction); floats
only propose candidates that are then verified exactly.

## 1. The blocked automaton (exact)

**States.** Q_J = {xi mod 3^J : xi = 2 mod 3}, |Q_J| = 3^(J-1): the 3-adic
ball B(xi, 3^-J), uniformly in level k >= J+2.

**Mass transitions (Lemma 5 side).** Summing the eigen-equation over a ball
and using min <= mean per fiber (valid for every minimizing policy) gives the
exact domination, for any c <= F_lambda(c) and M(xi) := sum of c over the ball:

    M(xi) <= p*M(4xi) + 1[xi=2(9)]*(q2/3)*sum_i M(R2(xi)+i*3^(J-1))
                      + 1[xi=8(9)]*(q8/3)*sum_i M(R8(xi)+i*3^(J-1))

with p = lambda^-2, q2 = lambda^(alpha-2), q8 = lambda^(alpha-1). The /3 is
the essential per-fiber-mass normalization (spine multiplier q8/3, not q8):
the fiber min is <= one third of the fiber sum, and m -> r_e(m) is a bijection
of the ball onto a one-digit-coarser ball. **Key structural fact (proved,
verified J=2..7):** each state receives exactly one T-, one B2- and one
B8-edge, because R2, R8 act bijectively on ball-states; hence all column sums
equal s(lambda) = p + (q2+q8)/3 and

    rho(W_J) = s(lambda) exactly, for every J, with uniform left Perron vector.

So the mean-dominated automaton is **exactly critical at lambda = 2**
(s(2) = 1) at every truncation depth: the annealing gap (min vs mean) equals
the oscillation defect (q2+q8)*delta_k of the oscillation law, and the
dominated model concedes it. W_J is irreducible (the transport edges alone
form a single 3^(J-1)-cycle: <4> acts transitively on Q_J), so the untilted
first-return series of any E is exactly 1 at lambda=2 (renewal identity at
Perron root 1; confirmed numerically to 3e-9): **all Lemma-5 content is in
the tilt**. [Both the column-sum identity and this reading were independently
audited by gpt-5.6-sol; the bijection argument is the same one verified
in-code at J=2..7.]

**Exceptional set.** E_J = J-digit balls of the backward <4>-orbit points
-4^{-t}, t < qcut (default qcut = J). Exact residues via inv4 = 4^(-1) mod 3^J
(J=3: {26, 20, 5} = the verbatim periodic addresses (2)^inf, (20)^inf,
(2100)^inf of -1, -1/4, -1/16). NB the full orbit mod 3^J is all of Q_J
(period 3^(J-1)), so qcut is essential; E cannot be "the whole orbit".

**Weights.** Certified rational enclosures for lambda-intervals via the
alpha-sandwich 50508/31867 < alpha < 24727/15601 (verified by 2^p vs 3^q
integer comparisons) and exact cross-multiplied power comparisons; per-weight
monotonicity (p, q2 down, q8 up in lambda) reduces intervals to endpoints.

## 2. Validation against certified eigenvector data (all PASS)

- V1 (k=7,8, brute force integers): sol-contraction Lemma 1 exactly —
  transport label action j -> h+j, R2: j -> h'+j, R8: j -> h'+2j, plus two
  new exact floor identities used by the Lemma-3 engine:
  floor((4r-2)/3^N) = floor(4r/3^N) and floor((2r-1)/3^N) = floor(2r/3^N)
  (since 4r = 2, 2r = 1 mod 3).
- V2 (k=15,16, exact integer/Fraction on `cert_k*_C.npy`): both the sharp
  ball inequality M <= pM(4xi) + q_e*S_e (S_e = exact sum of fiber minima) and
  the automaton's mean-dominated form hold for every ball at J=2,3; minimal
  relative slack 1.6e-7 = the certificate slack itself, i.e. the automaton is
  tight — indexing confirmed.
- V4: empirical cone constant K = max over fibers of (max/min) = 1.85 (k=15),
  1.87 (k=16): the K=2 cone used below is realistic.
- V3 (k=15..19, float): empirical nu_k(E_J) sits just below the annealed
  stationary pi(E_J) and halves per J like it (Sec. 4); values stable in k
  (slight upward drift with lambda_k). Table: `validation.csv`.

## 3. Lemma 3 search: structural obstruction found

Blocks are L moves along the transport orbit r_t = 4^t r; unrolled, the block
is a sum of generalized-permutation 3x3 terms: tail p^L (shift perm), each B2
at time t: p^t*q2 (shift perm)*D, each B8: p^t*q8 (affine x2 perm)*D, with
D = diag in [3/(2K+1), 1] dominating all min policies inside the cone C_K.
The shifts are exact piecewise-constant functions of the **top-digit fraction
u = r/3^N in [0,1)**: base-4 digits of u are the transport overflows; at a
2-branch the branch shift equals the next transport overflow (floor identity);
at an 8-branch h' = [u_t >= 1/2]. We enumerate all u-cells exactly
(`lemma3.py::u_cells`, 4^L cells of width exactly 4^-L) and dominate.

Findings (`lemma3_census.csv`, `lemma3_blocks.csv`):

1. **L = 3 is impossible**: one 5-2-8 cycle yields 2 shift-type + 1
   affine-type permutations, which cover at most 7 of 9 matrix cells for
   every u — the induced matrix always has zeros, Birkhoff diameter infinite.
   (Max coverage over all 64 cells: 7; proven by the census.)
2. **No (J, L) can work on ball states alone**: the block matrix depends only
   on the phase (q mod 9) and on u — the mod-3^J ball state sees only low
   digits and u is invisible to it. The u-class with all base-4 digits in
   {0,3} aligns *all* permutations (coverage 5) for **every** L; it is
   adversarially realizable at every ball state. This class contains exactly
   the -1 spine (ternary all-2s => u -> 1), and on it the block reproduces
   the observed period-2 label swap j -> 1+2j with the -1 lift pinned (M6) —
   the automaton reproduces the renormalization's label action exactly.
3. On the covered u-cells (fraction 0.16-0.21 at L=6, 0.38-0.53 at L=9,
   growing with L but never 1), the certified contraction is weak:
   tau = tanh(Delta/4) = 0.995-0.99999 (Delta ~ L*ln4, driven by the p^t
   coefficient spread across the block).

**Verdict (Lemma 3): NOT certifiable at (J,L) in {(2,3),(3,3),(3,6)} — or any
(J,L) — in the single-profile, ball-state form of sol-pressure Lemma 3.** The
obstruction is identified and exact: label-shift information lives in the top
digits (the fiber-index arithmetic of sol-contraction Lemma 1), orthogonal to
the 3-adic ball coordinate. Any viable Lemma 3 must refine states by a
top-window (u-digit classes) — and then the aligned classes (which include
the -1 spine) must be declared exceptional and charged to Lemma 5's tilt, or
handled by a product cone tracking the grandchild block jointly.

## 4. Lemma 5 search: theta-region certified; gap is real but conditional

Certificate form implemented exactly as (2.9): find rational h > 0, z > 1
with sum_e w_e z^{b(e)} h(q') <= R h(q) for all q (b(e) = 1 if target in E_J;
blocked = L-th power since b is additive, so per-move accounting is complete).
h proposed by float Perron iteration, rounded to denominators 10^6, then R
computed as the exact max row ratio in Fractions — (2.9) holds by
construction with that exact R; (2.10) R z^-theta < 1 checked by exact
integer comparison. Results (`lemma5_theta.csv`, `lemma5_scaling.csv`,
`lemma5_exact_cert.json`):

- At lambda = 2 (the asymptotically relevant endpoint): theta*(J) :=
  inf_z ln R(z)/ln z equals the annealed E-visit frequency pi(E_J) — by
  convexity of t -> ln rho(W_{e^t}) the infimum is the derivative at t=0+,
  which is pi(E_J) in the irreducible Perron setup (audit-confirmed) — and
  **pi(E_J) halves per J**, the spine multiplier q8/3 = 1/2 per digit:
  0.513 (J=3), 0.280, 0.153, 0.075, 0.039, 0.020, 0.0093, 0.0046 (J=10).
  Exact instance: J=6, z=5/4, theta=1/8: R = 2021589/1975507 = 1.02333 and
  R z^-theta < 1 verified by integer comparison. **The certified theta-region
  {theta > theta*(J)} reaches any fixed theta > 0 at J ~ log2(1/theta):
  Lemma 5 is asymptotically free at lambda = 2.**
- Uniform over [lambda_18, 2] (sol's literal (2.9), 8 certified
  lambda-subintervals, single h): the certificate pays the annealing
  inflation ln s(lambda_18) = 0.0234, and theta*_uniform decays much more
  slowly: 0.614 (J=3), 0.405, 0.267, 0.175, 0.122, 0.091, 0.074, 0.065
  (J=10); left-endpoint sensitivity at J=8: 0.156 from lambda_18, 0.128 from
  1.9, 0.044 from 1.99, 0.027 from 1.999. Exact uniform instance at J=6:
  z=3/2, theta=1/4 (theta_req = 0.2278). The fix consistent with the C1'
  chain: subdivide [lambda_K, 2] with a per-piece h — legitimate since
  lambda_k is monotone, so only finitely many h-switches occur along the
  tower (audit point (3b)); the asymptotic rate is set by the lambda->2 piece.
- Empirical check (sol 4.4D): nu_k(E_J) from certified eigenvectors k=15..19
  tracks pi(E_J) from below with per-digit ratio 0.46-0.52 (annealed: 0.50);
  at fixed J it rises with k but with shrinking increments (J=8: +3.6%,
  +3.2%, +2.9%, +2.7% per level) — consistent with lambda_k -> 2, not with a
  mass plateau; the nested-neighborhood diagnostic favors subcriticality.

## 5. Honest verdict and what full certification needs

- **Lemma 5: certified gap exists** in the exact sense above, with
  theta-threshold theta*(J) ~ 2^-J at lambda=2 (exact rational certificates
  produced at J <= 6; nothing blocks J ~ 12-16 — the automaton is sparse,
  3^(J-1) states; a 32-core machine handles J=16 (14M states) with sparse
  exact rational verification in hours).
- **Lemma 3: fails structurally in the specified form at all (J,L)** — the
  quantitative bottleneck of the whole program. Without it there is no
  theta_t to feed (2.10), so **no end-to-end certificate at (J,L) in
  {(2,3),(3,3),(3,6)}: verdict NOT CERTIFIED, with the obstruction identified
  exactly** (top-digit label alignment; the aligned class is the -1 spine's).
- The failure is *not* a pressure failure: the dominated model shows no
  trace of exceptional criticality beyond the annealing gap (first-return
  sum = 1 is forced at lambda=2 by column-sum criticality, and pi(E_J) -> 0
  geometrically). Nothing here estimates lambda_inf < 2; the data-side
  diagnostics (V3) also show no plateau. The failure margin is localized in
  the missing localization lemma, not in the return-cloud pressure.
- **Minimal viable architecture for Lemma 3** (next target, refined per
  audit): a single combined automaton — (low window mod 3^J) x (top-window
  u-classes of depth L_w) — implementing "good-block contraction vs bad-block
  tilted pressure": good top-states get a certified multicone contraction,
  aligned top-states (including the -1 spine face) are handled by an explicit
  spine/face cone or by a pathwise lemma that long aligned runs force
  E_J-charge. Two audit warnings adopted: (i) the naive 9-dim product cone
  over the grandchild block does NOT obviously evade alignment — the R8
  x2-action only relabels coordinates; genuine coupling between faces must be
  exhibited by a support-primitivity computation; (ii) Haar scarcity 2^-L_w
  of the aligned class is insufficient because it is adversarially reachable
  — the charge must be deterministic (pathwise) or pressure-based. Sizes:
  (J=3, L_w=6): 9 x 4096 states — this machine; (J=6, L_w=10): ~2.5e8 —
  a 32-core/GPU job. The Lemma-5 tilt budget theta*(J) ~ 2^-J balances the
  aligned-class visit rate ~2^-L_w at L_w ~ J — concrete and testable.

## 6. Numerology pinned by this computation

- rho(W_J) = s(lambda) for all J (column-sum argument, new, one line).
- pi(E_J) halving = q8/3 at lambda=2 = exactly 1/2: sol-pressure's 1.2
  heuristic multiplier is the true per-digit rate of the whole neighborhood.
- The -1 block's label action j -> 1+2j (j=2 pinned) derived from
  h' = floor((2r-1)/3^N) = 1 at r = 3^N-1: M6's swap is exact index
  arithmetic, not a numerical accident.
