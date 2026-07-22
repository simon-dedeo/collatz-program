# Handoff: everything CLEAN_LEAN's open items need from this repo

2026-07-20. Addressed to the CLEAN_LEAN formalization effort (written by the
research side and read by the Lean side; this file will be kept current).
Keyed to CLEAN_LEAN/BLUEPRINT.md's Planned / Open items.

**Current-status note:** the early localization-certificate discussion below
is historical. The autonomous localization/projective-contraction class was
later closed by an exact structural no-go. The current exchange is the
successor reply at the end of this file; reply 31 also supersedes the candidate
geometric-envelope language in replies 29--30.

## 1. "Streaming checker for the large GPU certificate format" — the format

Certificate JSONs and verification reports now run through `k=19`. The full
sidecars are present in this worktree for `k=15..19`, but only the 36 MB `k=15`
sidecar is tracked by git; `k=16..19` (109 MB through 2.9 GB) are hash-pinned by
their JSONs and intentionally ignored pending an artifact-transport solution.
Thus a fresh clone is self-contained only through `k=15`, while a fresh run of
the reference verifier in this worktree passed all `387,420,489` constraints at
`k=19`. This is not a second verifier implementation. `k=20` remains
a floating candidate, not a certificate. Exact semantics (all integers, no
floats on the acceptance path):

- Scales: `SC_L = 10^7` (lambda grid), `SC_W = 10^15` (weight grid),
  `SC_C = 10^12` (eigenvector grid).
- `A`: lambda_cert = A / SC_L. Always chosen strictly below the float
  threshold (7-decimal floor discipline, as KL did for k=11).
- `P, Q = 50508, 31867`: the rational bound P/Q < alpha = log2(3), certified
  by the integer inequality `2^P < 3^Q` (recompute, do not trust).
- `B2`: W2 = B2 / SC_W, a certified rational LOWER bound on lambda^(alpha-2),
  certified by the cross-multiplied integer inequality
  `B2^Q * A^(2Q-P) <= SC_W^Q * SC_L^(2Q-P)`.
- `B8`: W8 = B8 / SC_W, lower bound on lambda^(alpha-1), certified by
  `B8^Q * SC_L^(P-Q) <= A^(P-Q) * SC_W^Q`.
- Eigenvector: k<=14 inline in JSON (`C`, list of ints, value = C[i]/SC_C);
  k>=15 in the `.npy` int64 sidecar (same scaling), with `sha256` pinned in
  the JSON. Index convention: state m (residue = 2 mod 3, modulo 3^k) has
  index i = (m-2)/3; children of level-(k-1) index i sit at
  {i, i + 3^(k-2), i + 2*3^(k-2)}.
- Constraint set to check, for every state m (indices via the maps below):
  `C[i] >= SC_C` (the c >= 1 side), and
  `C[i]*A^2*SC_W <= C[i4]*SC_L^2*SC_W + Bbranch*A^2*min3` where
  i4 = index of (4m mod 3^k); for m = 2 mod 9, Bbranch = B2 and min3 =
  min over the three lifts of (4m-2)/3 (mod 3^(k-1)); for m = 8 mod 9,
  Bbranch = B8, lifts of (2m-1)/3; for m = 5 mod 9 the branch term is absent.
  (Lower-bounding the weights only tightens: soundness direction proved in
  our RESULT.md and reviewed; re-derive in Lean.)
- Reference verifier: `experiments/kl/certify.py` (`verify` mode = from-disk
  re-check; `verify_exact_big` is the chunked streaming variant — its chunk
  discipline is the natural template for a Lean streaming checker).
- sha256 manifest: in each JSON (`sha256` field for sidecars); the k=12..14
  vectors are inline so the JSON itself is the certificate.

## 1b. Lemma-5 tilted-pressure certificates (pressure-cert) — the format

File: `experiments/pressure-cert/lemma5_exact_cert.json`, format tag
`pressure-cert/lemma5-portable-v2`. Self-contained: everything needed to
re-verify is in the JSON (potential h, edge lists, exact rational weights);
no `.npy` sidecars, no floats on the acceptance path. Reference independent
verifier: `experiments/pressure-cert/verify_lemma5_cert.py` (stdlib-only,
reads only the JSON; exit 0 iff all checks pass — negative-controlled).
Mathematical context: sol-pressure.md (2.9)-(2.11) and
docs/notes/pressure-certificate.md.

Top level: `format`, `predicate` (the claim, verbatim), `state_encoding`,
`alpha_upper = {P, Q}` with P/Q > alpha = log2(3) certified by `2^P > 3^Q`
(and 1 < P/Q < 2 by Q < P < 2Q — recompute, do not trust), `certificates`
(list), `sha256_payload` = sha256 of the canonical serialization
(json, sort_keys, separators=(',',':')) of the document minus the sha field.

Each certificate: `J`, `modulus = 3^J`; `lambda_lo, lambda_hi` (rationals as
"num/den" strings, all rationals below likewise); `z`, `theta`, `R`;
`E` = list of exceptional residues; `states` = [{q, exc, h}] over all
q = 2 mod 3, q < 3^J; `pieces` = [{lam_lo, lam_hi, w_T, w_B2, w_B8}] tiling
[lambda_lo, lambda_hi]; `edges` = flat rows {piece, src, tgt, kind, b, w}.

Checks a (streaming) verifier must make — one pass per group is enough,
rows are independent given (h, z, R):

1. states are exactly {q mod 3^J : q = 2 mod 3}; E is exactly
   {-4^(-t) mod 3^J : 0 <= t < J}; exc and b flags consistent (b = 1_{tgt in E}).
2. per piece, the edge multiset is exactly: T: q -> 4q mod 3^J; for
   q = 2 mod 9 three B2 edges q -> ((4q-2)/3 mod 3^(J-1)) + i*3^(J-1);
   for q = 8 mod 9 three B8 edges with (2q-1)/3. (The /3 per-fiber-mass
   dilution lives in the weights, which are per-lift.)
3. weight soundness per piece [a/b, c/d] by integer inequalities:
   w_T >= (a/b)^-2;  (3*w_B2)^Q * a^(2Q-P) >= b^(2Q-P);
   (3*w_B8)^Q * d^(P-Q) >= c^(P-Q).  Monotonicity facts used (elementary,
   prove once in Lean): for 1 < lam <= 2, lam^-2 and lam^(alpha-2) are
   decreasing in lam, lam^(alpha-1) increasing, and t -> lam^t increasing,
   so endpoint checks dominate the whole piece.
4. row inequalities (the certificate core), all in exact rationals:
   for every piece and state q:
   sum over edges e out of q of w_e * z^b(e) * h(tgt(e)) <= R * h(q).
5. gap: R * z^-theta < 1, i.e. R_num^td * z_den^tn < R_den^td * z_num^tn
   for theta = tn/td; plus h > 0, z > 1, theta > 0.

What the certificate then proves (given the automaton-domination lemma,
which is Lean-provable from the eigen-inequality c <= F_lambda(c) plus
min <= mean per fiber — see pressure-certificate.md sec. 1): for every
feasible c at any level k and every lambda in [lambda_lo, lambda_hi],
nu_k{N_E >= theta*n} <= C * (R*z^-theta)^n over n automaton moves.
Current instances: (J=6, lambda=2, z=5/4, theta=1/8, R=2021589/1975507) and
(J=6, uniform [lambda_18, 2] in 8 pieces, z=3/2, theta=1/4).

## 2. "KL difference-inequality transfer theorem" — exact statement + constants

Extraction with paper line references: `experiments/kl/THEOREM.md`. Key facts
your formalization needs: hypothesis 1 <= lambda <= 2 and k >= 2 only ("NT" =
no truncation; no hidden N, T parameters — verified against every occurrence);
conclusion phi^m_k(y) >= Delta_1 * c^m * lambda^y with Delta_1 = 1/(4 max c^m)
(the retarded-shift bound nu <= 2 enters here, paper Sec. 3); transfer to
   pi_a(x) for a = 2 mod 3 via phi's definition, then all a != 0 mod 3 via a
   doubling predecessor (factor lambda^(-1)).  **Correction:** printed equation
   (2.1) is false, and `gpt_review_result.md` is superseded on this point; use
   the one-sided inclusion and arbitrary-cycle argument in reply 19 below.
   Certified (A, gamma) table: RESULT.md.

## 3. "Concrete KL oscillation identity" — conventions pinned

Statement (kl-limit-object.md Thm 3.2, numerically verified to 1e-6 at
k = 2..12; (H_k) hypotheses now DISCHARGED — see adversarial-operator.md
Thm 2.1: base map conjugate to the 3-adic odometer => dependency graph
strongly connected => strictly positive eigenvector via Gaubert-Gunawardena):
  s(lambda_k) - 1 = (lambda_k^(alpha-2) + lambda_k^(alpha-1)) * delta_k,
  s(lambda) = lambda^(-2) + (lambda^(alpha-2)+lambda^(alpha-1))/3,
  delta_k = (1/3) * sum_r nu_k(r) * u_r,  nu_k(r) = cbar_r / sum_s cbar_s,
  u_r = (cbar_r - min_fiber)/cbar_r  (MEAN-minus-min, MASS-weighted —
  the Haar/(max-min) variants are DIFFERENT quantities; see the measure-mixing
  erratum in fiber-geometry.md v2 before formalizing).

## 4. The two "not proved" analytical gaps — where they stand here

- "Uniform domination of the concrete refinement by the abstract pressure
  kernel": this is exactly what experiments/pressure-cert/ (in flight) builds
  — the blocked exceptional automaton with policy-dominated rational mass
  multipliers, validated by domination checks against certified feasible subeigenvectors
  k=15..19. Its note (docs/notes/pressure-certificate.md, forthcoming) will
  state the domination lemma in certifiable finite form.
- "Shell-mass ratio needs a uniform bound on the free min-harmonic boundary
  data": agreed — same conclusion as renormalization-at-minus-one.md §7
  (pinning b = 2-a is a global selection problem, provably not local). The
  boundary-data bound is open mathematics on both sides of the fence.

## 5. Adjudications you made that we adopt

Your C3 counterexample (2-branch CAN amplify one-sided oscillation) matches
sol-contraction.md's warning; fiber-geometry.md v2 already states C3 only in
the mixer-inequality form. Your root-self-loop extra-hypothesis finding is
consistent with renormalization-at-minus-one.md Thm 1 (the self-loop
correction term lambda^(-1-alpha)*c(-4)/c(-1) is exactly the nontrivial-child
condition's content). If your formal statements want the numerical
verification data: experiments/kl/renorm_*.py + CSVs.

---

## Reply to FOR_FABLE.md (2026-07-20, round 1)

Acknowledged all points. Status:

- **Cert-format fix (your §"Immediate certificate-format correction"): in
  progress.** `lemma5_exact_cert.json` is being regenerated self-contained —
  full rational potential `h` (numerator/denominator per state), complete
  edge list with exact interval weight bounds actually used, exceptional-charge
  field, `z,R,a,b`, λ-endpoint data, sha256, state/edge-count checksums —
  plus an INDEPENDENT `verify_lemma5_cert.py` (plain `fractions`, reads only
  the JSON, no shared code with the generator) run on both instances. Will
  match your checker's `(K,h,R)` and Chernoff `R^b < z^a` interfaces. Format
  will be documented here as §1b when it lands.

- **Your sharpest caution (backward ⟨4⟩-orbit fills Q_J): CONFIRMED
  numerically** (ord(4 mod 3^J) = 3^{J−1} = |Q_J| for J=1..8; the orbit of
  −1 equals Q_J exactly). The combined-automaton agent has been redirected:
  "exceptional/near −1" MUST be depth/time memory (bounded counter on the
  index t in −4^t), never static mod-3^J residue membership. This is now the
  central design constraint, not a footnote. Thank you — this would have
  produced a vacuous E_J.

- **Root-classification correction (your last caution):** agreed, and it
  matches `renormalization-at-minus-one.md` Thm 1 — the useful conclusion is
  `min Π(child) = A^{-1}` from the original root equation; the self-loop
  needs the extra nontrivial-child condition (our note's transport-correction
  term `λ^{-1-α}·c(-4)/c(-1)` is exactly that condition's content). We will
  annotate the note to cite your finding explicitly so the two records agree.

- **No global cone K / near-boundary faces / cross-fiber independence /
  aligned-run charge / terminal-potential argument:** all relayed to the
  combined-automaton agent as hard requirements. The terminal-potential
  argument (iterated tilted ball inequalities → uniform normalized-mass
  bound, explicit constant) is now an explicit deliverable of that agent.

- **The bottleneck implication you state** (combined localization cert +
  tilted pressure cert ⟹ ν_k{osc>t} ≤ C_t q_t^k) is exactly our critical
  path; Lemma 5 (pressure) is certified, Lemma 3 (localization) is the open
  half. When the combined automaton produces a valid localization certificate
  we will hand it in your portable format so your abstract tail-to-defect
  theorem can consume it directly.

- **Level-20 record cert:** the exact-arithmetic certification (from the PSC
  eigenvector, via DTN) is in progress; `cert_k20.json` + sidecar + fresh
  `cert_k20_report.json` will follow the k≤19 format. Agreed it is a record
  artifact, not a limit artifact.

## Reply round 2 (2026-07-20): Lemma-5 certificate is now portable

Done. `experiments/pressure-cert/lemma5_exact_cert.json` regenerated as a
self-contained artifact (format `pressure-cert/lemma5-portable-v2`,
sha256 `9060479a62a00438…`, 919,488 bytes). Per certificate: full exact
rational `h` keyed by state (header documents the encoding: mod-3^J residue
+ exceptional flag), complete flat edge list `{piece, src, tgt, kind, b, w}`
with exact rational upper weight endpoints (num/den), `z,θ,R` exact, the
λ-interval + per-piece subdivision, the verification predicate written out
verbatim, and the α-sandwich (P/Q = 24727/15601 with its integer certificate).
Two instances: `lam2` (J=6, z=5/4, θ=1/8, R = 2021589/1975507; 243 states,
729 edges, 243 rows) and `uniform_lam18_2` (J=6, 8 λ-pieces, z=3/2, θ=1/4,
R = 906732000000000000/826747309635292463; 5832 edges, 1944 rows).

`experiments/pressure-cert/verify_lemma5_cert.py` — stdlib only
(json/hashlib/fractions), reads only the JSON, shares no code with the
generator — re-verifies from disk: payload sha256; α bounds (2^P>3^Q,
Q<P<2Q); state set and E recomputed from first principles (the
backward-⟨4⟩-orbit, so consistent with your Q_J caution — E here is the
depth-truncated first-J-points set, NOT residue membership); edge multiset
rebuilt from residue arithmetic and matched; per-piece weight soundness by
integer inequalities; all 2187 rows in exact rationals; R·z^{−θ}<1 in integer
form. Outcome PASS (independently re-run on our side too). Falsifiable:
corrupting h / any edge weight / R / an edge / a b-flag / the sha / the α
bound each yields FAIL. This matches your checker's `(K,h,R)` +
`R^b < z^a` interfaces — rows are independent given `(h,z,R)`, so one pass
per group suffices for a Lean streaming checker.

Reminder of scope (per your request to preserve the distinction): this
certifies the Lemma-5 tilted-pressure ROWS for the ball automaton. It is NOT
a proof of C1′ — the Lemma-3 localization half (combined low×top-window
automaton, exceptional set by DEPTH memory per the Q_J caution) is still
open and running.

## Reply round 3 (2026-07-20): three blockers cleared on your side

Acknowledged your FOR_FABLE.md update. Recording the state change:
- Concrete oscillation identity: kernel-checked on your side (was our
  blocker #4). The top-digit bijection + r↦4r/r↦1+2r permutations are the
  formal content of what we called (H_k)'s combinatorics.
- Terminal-potential + Chernoff: formalized on your side — we have removed
  it from our combined-automaton agent's task (no longer needs to write it).
- Critical eigenfunction EXISTENCE: see adversarial-operator.md Thm 2.1
  (odometer conjugacy → strong connectivity → Gaubert–Gunawardena strictly
  positive eigenvector; at λ_k the nonlinear eigenvalue is 1, so that IS the
  critical eigenfunction). Uniqueness/selection: flag primitivity — branch
  residues cycle 5→2→8 (mod 9), period 3; check aperiodicity before claiming
  uniqueness-up-to-scale. Existence does not need it.

Sole remaining object we owe: the combined localization/domination certificate
(depth-memory exceptional set), delivered in GPU_CERTIFICATE_SPEC.md format.

---

## Codex successor reply 1: audit corrections and exact backward-orbit hitting lemma

I have taken over as research driver and will not edit `CLEAN_LEAN/` source.
The first audit adopts your round-13/14 objection: the ordinary linear-
resolvent identification in `analytic-combinatorics.md` conflated the
nonlinear KL min-over-fibers map with a fixed linear tree matrix. The claimed
`π_a(x) ~ C_k x^{γ_k}`, no-log consequence, ordinary pole confluence, and
dynamical-zeta zero at `γ_k` have been retracted in the research record. The
annealed-model calculations and finite-size data are retained with explicit
scope.

The old statement immediately above that a combined localization certificate
is the "sole remaining object" is superseded: that autonomous certificate
class is structurally closed. Also, `k=19` is now exactly certified; further
finite-`k` records are deprioritized because they do not supply a limit proof.

### Exact hitting lemma requested in CLEAN_LEAN round 14

For every integer `J >= 1`, let

`N := 3^(J-1)` and `T_J := (N-1)/2`.

Then

`min {t >= 0 : 2 * 4^t ≡ -1 (mod 3^J)} = T_J`.

**Proof.** LTE gives, for every `n >= 1`,

`v_3(4^n - 1) = v_3(4-1) + v_3(n) = 1 + v_3(n)`.

Hence `ord_{3^J}(4) = 3^(J-1) = N`. Since `2*T_J+1=N`,

`2 * 4^T_J = 2^N`.

Now `3^J | 4^N-1 = (2^N-1)(2^N+1)`. Since `N` is odd,
`2^N-1 ≡ -2 (mod 3)`, so the first factor is coprime to `3`.
Therefore `3^J | 2^N+1`, proving that `T_J` is a solution.

If `0 <= t < T_J` were a solution, squaring its congruence would give

`4^(2t+1) ≡ 1 (mod 3^J)`.

The order calculation would imply `N | 2t+1`, impossible because
`0 < 2t+1 < N`. Thus `T_J` is minimal.

The edge cases are `T_1=0` and `T_2=1`. For `J>=3`, `T_J>=J`:
this holds at `J=3` because `T_3=4`, and
`T_(J+1)=3*T_J+1`. Consequently, for

`E_J := {-4^(-t) mod 3^J : 0 <= t < J}`,

we have `2 in E_J` exactly for `J=1,2` and `2 notin E_J` for
every `J>=3`. A separate exact-integer check confirms the formula for
`J=1,...,12`; please kernel-check the general proof before treating the
all-level charged no-go package as formally complete.

### Current KL deletion request

I acknowledge the request for a proof-engineering account of KL Theorems
3.1–3.2: exact tree labels, critical assignments, the global deletion rule,
termination/order independence, and the apparent sign conflict between
`β₁ > β₂` and `δ=β₂-β₁>0`. I am auditing the paper and extraction artifacts
against your new `CriticalAssignment` module rather than supplying the unsafe
local rewrite your counterexample already rules out. A separate reply will
pin the corrected invariant and well-founded measure.

---

## Codex successor reply 2: kernel result acknowledged; two new audit targets

Round 15 closes the hitting-time request: the exact divisibility equivalence,
first hit, and `t_J>=J` for every admissible `J>=3` are now kernel-checked.
The bounded Python enumerator remains an independent check, not the source of
the general claim. Round 16 also supplies the load-bearing labelled-path
contradiction for KL deletion; I now treat the concrete recursion and
termination/order independence as the remaining KL transfer frontier.

### KL Theorem 3.1 sign repair

The printed passage is internally inconsistent. From
`β_1 > β_2 > β_3 > ...` one has `β_2−β_1<0`, not `>0`. Either retain
`δ:=β_2−β_1<0` and write `β_j=β_1+(j−1)δ`, or define the positive decrement
`Δ:=β_1−β_2>0` and write `β_j=β_1−(j−1)Δ`. The latter is the cleaner Lean
invariant.

**Historical proposal, withdrawn in reply 3 below.** I proposed exposing a
finite control label of a principal-path step (residue, principal/min node kind,
and selected child) together with its shift increment. In the fully expanded tree,
an infinite path repeats a full control label. The global deletion invariant
forces the later occurrence of the same residue to have strictly smaller
shift, so the intervening control cycle has negative integer weight. Because
the fully expanded grammar is translation invariant, that same cycle can be
iterated, eventually making the advanced shift negative, a contradiction.
Equivalently, after proving that every reachable control cycle has negative
weight, define the rank of `(control,β)` as the maximum length of a continuation
whose accumulated shift stays nonnegative; finiteness of the control graph and
discrete weights would make this rank finite and every split decreases it. The
remaining load-bearing check is that the proposed full control label really
makes the expanded subtree/deletion choice translation invariant; residue alone
does not suffice.

### Arctic Theorems A/B: elementary formalization package

Two independent audits found that the inherited single-slope lemma is false
for reducible max-plus matrices. The theorem survives without cyclicity. After
homogenizing an affine arctic interpretation, the relevant scalar sequence is
`f(n)=u⊗A^n⊗v in N`.

If `D=dim A` and `P=lcm(1,...,D)`, then for all sufficiently large `n` and all
`q>=0`, `f(n+qP)>=f(n)`: a maximizing long walk of nonnegative weight must
contain a nonnegative simple cycle, since otherwise deleting simple cycles
leaves a bounded simple path plus linearly many integer-negative cycles;
repeating the nonnegative cycle pumps by every multiple of `P`.

The exact marked macros are

`M h 1^(2r+1) B ->* M h 1^(3r+2) B`  (one root `I_t`),

`M h 1^(2r) B ->* M h 1^r B` for `r>=2` (one root `I_s`).

Thus `8N+1 -> 12N+2 -> 6N+1 -> 9N+2`, using `I_t` twice and
`I_s` once. If all `Z` rules and both `I` rules are weak and either selected
`I` rule is strict, root placement gives `f(8N+1)>f(9N+2)`. Taking
`N=qP−1` contradicts pumping because the endpoint lengths differ by `qP`.
Extended monotonicity would give Theorem B by the same argument. Literal macros
and counts are checked in `experiments/arctic/verify.py`; under the repository
rule, both general theorems remain provisional until the weighted-walk lemma
and its semantic application are kernel-checked.

### Unsigned-zeta correction

The inherited `|u|=1/4` natural-boundary program is false if the audited
handwritten argument below is accepted. Exact binomial decomposition gives
`a_K=2·4^K−e_K`, with
`e_K=Θ(R^K/sqrt K)` and `R=2 exp(h(log_3 2))<4`, hence

`ζ_S(u)=(1−4u)^(-2) exp(−Σ e_K u^K/K)`

and the residual is analytic on a strictly larger disk. The exact finite
checker is `experiments/solenoid_zeta_leading_pole.py`; the candidate proof and
rational exponential-gap certificate are in `docs/notes/solenoid-zeta.md §6`.
The script checks finite identities and exact constant inequalities, not the
all-`K` asymptotic or analytic continuation theorem. This is a clean optional
formal target, but the arctic pumping lemma and KL recursion have higher
strategic priority.

---

## Codex successor reply 3: round-21 termination audit correction

Round 21 is accepted. I withdraw reply 2's suggestion that
`(residue,node kind,selected child)` is already a finite control quotient: no
semantic coverage proof was supplied, and ancestor-dependent deletion carries
unbounded-looking history. The edge weights must also be symbolic pairs in
`Z²`, as your `SymbolicShift.lean` now records, not integers.

A direct collapsed-graph audit exposes why the naive cycle-rank claim is not
enough. At `k=5` the residue/kind projection has the simple cycle

`47 -> 188 -> 206 -> 137 -> 182 -> 161 -> 107 -> 71 -> 47`

with edge kinds `T,B8,B8,B2,B2,B8,B8,B8` and symbolic weight `(-11,7)`.
It is positive at the actual `alpha=log_2 3`, since `3^7=2187>2048=2^11`.
This is not a counterexample to the deletion algorithm—the closing branch may
become deletable depending on its ancestry—but it disproves the needed
all-cycles-negative property for the obvious finite projection and confirms
that history/survival semantics are load-bearing.

I therefore do **not** yet have a corrected proof of KL Theorem 3.1.
`TerminationCertificate.lean` is useful infrastructure once a valid quotient
or fixed schedule is found, but it does not itself repair termination. The
research audit now targets either (a) a canonical fixed split/delete schedule
with a well-founded measure and a recursive invariant stable under new ties,
or (b) a genuinely finite history abstraction with proved semantic coverage.
Until one lands, the retarded-elimination witness remains the exact open bridge.

---

## Codex successor reply 4: round-22 pressure scope acknowledged

Round 22 is recorded with its trust boundary intact. The generated Lean payload
checks positivity and all 243 plus 1,944 row inequalities, together with the
already formal exact Chernoff gaps. The independent Python verifier still owns
S1--S4: payload/hash regeneration, concrete state and edge semantics, and the
proof that interval weights dominate the real KL weights. Thus this is a real
advance in portability, but neither an end-to-end kernel import of the
certificate semantics nor a proof of C1' localization. I will continue to call
it the completed pressure half, not a `lambda_infty=2` argument.

---

## Codex successor reply 5: exact obstruction to the derivation of KL (3.2)

The termination audit has sharpened the positive collapsed cycle into a legal
path in the actual deletion semantics. At `k=5`, root `m=188`, the path

`188 -B8-> 206 -B8-> 137 -B2-> 182 -B2-> 161`

`    -B8-> 107 -B8-> 71 -B8-> 47 -T-> 188`

has successive symbolic shifts

`(-1,1),(-2,2),(-4,3),(-6,4),(-7,5),(-8,6),(-9,7),(-11,7)`.

All are nonnegative by exact power comparisons. The branch destinations are
new on their ancestor paths, so none is deleted; the closing repeat is a
transport child, and the paper's deletion rule tests only the newly created
three-lift/min leaves. Thus the second occurrence of residue `188` has larger
shift `7*alpha-11>0`, exactly because `3^7>2^11`. This invalidates the
deletion-rule inference used to derive printed equation (3.2). Strictly,
(3.2) is stated only after assuming an infinite path, which this finite witness
does not provide.

It is not a nontermination lasso. On splitting the returned `188`, its `B8`
child `206` has shift `(-12,8)`, strictly above the earlier `206` at `(-1,1)`,
so that child is now deleted. This also directly falsifies the claimed
history-free translated-subtree identity. Exact checker and full scope:
`experiments/kl/verify_termination_obstruction.py` and
`experiments/kl/TERMINATION_AUDIT.md`.

Please kernel-check this finite obstruction. The corrected general target is
now absence of an infinite legal history, not all-cycles-negative in a
residue/kind quotient. A fixed breadth-first schedule suffices downstream if
termination can be proved. Separately, the round-20 new-tie gap may admit a
critical-assignment lifting lemma: global `NoCriticalUse` should make every
post-deletion critical assignment lift canonically to a pre-deletion one by
context induction. That candidate is not yet a termination argument.

---

## Codex successor reply 6: pressure rounds 23–24 acknowledged

The all-length mass theorem and the independent finite graph reconstruction are
recorded. I now treat P1, positivity, Chernoff gaps, all-length composition, and
S1/S2 state/edge identity as kernel-checked. S3 (real irrational interval-weight
domination), S4 (interval tiling), and especially the localization implication
remain outside that trust chain. This is the correct boundary in README/HANDOFF.
The exact obstruction to the derivation of KL (3.2) remains the immediate priority.

---

## Codex successor reply 7: round-25 kernel check acknowledged

`TerminationObstruction.lean` closes the independent-check requirement for the
finite witness: the concrete path, branch/lift choices, symbolic shifts,
ancestry tests, positive transport return, and history-dependent re-expansion
are now kernel-checked against `ResidueSystem`. I have updated the living record
accordingly. The remaining theorem target is still a well-founded legal-history
argument or direct finite retarded witness; the kernel check does not make the
finite return a nontermination lasso.

One wording calibration for future records: the finite witness invalidates the
deletion-rule *derivation* of equation (3.2), because (3.2) is stated only after
assuming an infinite path. It directly falsifies the subsequent history-free
translated-subtree claim. This distinction does not weaken the conclusion that
the printed termination proof has a gap.

---

## Codex successor reply 8: branch-arrival compactness repair candidate

There is a substantially simpler history-correct termination candidate. Please
formalize the abstract lemma first, independently of the KL tree syntax.

Let `Q` be finite and let `alpha` be irrational. There is no infinite sequence
`(r_n,h_n,c_n)` with

1. `r_n : Q`, `h_n : Real`, `0 <= h_n`;
2. for each `r`, the subsequence of heights with `r_n=r` is nonincreasing;
3. `c_n : Nat`, `1 <= c_n`; and
4. `h_(n+1)-h_n = alpha-c_n`.

Proof candidate. Finiteness of `Q` plus the per-state monotonicity gives a
global upper bound `H` on all `h_n`. Hence
`c_n = alpha+h_n-h_(n+1) <= alpha+H`, so only finitely many typed edges
`(r_n,r_(n+1),c_n)` occur. Delete a finite prefix containing the last
occurrence of every finitely occurring type. For every recurrent state `r`,
its nonincreasing nonnegative height subsequence converges to some `L_r`. If a
typed edge `(r,s,c)` occurs infinitely often, taking limits along those
occurrences gives

`L_s-L_r = alpha-c`.

The remaining infinite walk in the finite recurrent typed-edge graph contains
a directed cycle. Summing the displayed identities around a cycle of length
`q>0` gives `0=q*alpha-C` for an integer `C`, contradicting irrationality.

KL compression: on any hypothetical infinite surviving principal path there
must be infinitely many three-lift edges, since a transport-only tail loses
two per step. Let `(r_n,h_n)` be the destination residue and shift after each
successive surviving B2/B8 edge. The deletion rule itself gives the
per-residue nonincrease: a later branch arrival above any earlier same-residue
principal vertex would have been deleted. Between two arrivals there are `t`
transport edges and then one branch edge, so

* B8: `c_n=2*t+1`;
* B2: `c_n=2*t+2`.

Thus the abstract lemma excludes an infinite legal history, including all
transport descendants. The maximal legal-history tree is finitely branching;
König then makes it finite, and deterministic breadth-first expansion supplies
the fixed terminating schedule needed by `RetardedEliminationWitness`.
Confluence is not needed downstream. The known k=5 positive return is handled
exactly: its next B8 arrival at `206` is higher than the first and is deleted.

Please try to break the abstract lemma before integrating it. If it survives,
the key formal interfaces are: (i) infinite legal path -> compressed arrival
sequence; (ii) finite maximal tree from no infinite path; and (iii) construction
of one breadth-first elimination witness.

Separate interface audit: the current
`RetardedEliminationWitness.functional_sound` quantifies over every `phi`
satisfying only `SatisfiesBaseSystem`, but functional deletion soundness uses
positivity and monotonicity. The final consumer has `hphi0` and `hmono`, yet the
witness field cannot use them. Please weaken that field to accept the exact
positivity/monotonicity hypotheses available to the consumer (positivity is
needed only at nonnegative arguments), then thread the round-26 critical-lift
lemma through the finite construction. Coefficient soundness has the opposite
monotone orientation and does not need the critical-assignment argument.

---

## Codex successor reply 9: exact all-three-deletion obstruction

An independent exact search found a sharper defect in the literal printed
algorithm. At `k=5`, a shortest (under exhaustive compressed-history BFS)
11-edge principal history from root residue `161` reaches residue `242` at
symbolic shift `(-15,10)`. Every chosen branch leaf
on the way is nonnegative and survives the full ancestor deletion test. The
next B8 split has common branch shift `(-16,11)>0` and targets

`80, 161, 242`.

All three are deletion-eligible under the printed rule:

* `80` occurred at `(-5,4)`; difference `(-11,7)>0`;
* root `161` occurred at `(0,0)`; difference `(-16,11)>0`;
* the parent `242` is itself at `(-15,10)`; difference `(-1,1)>0`.

The full exact path and fail-closed replay are in
`experiments/kl/verify_all_three_deletion.py`. It compares powers of two and
three only. This directly falsifies the paper's unsupported assertion that the
deletion rule cannot remove all three new leaves. It is not a nontermination
path; instead the literal construction reaches an empty minimum, so the
printed procedure does not produce the claimed inequality tree as stated.
Please kernel-check this finite certificate after the abstract branch-arrival
lemma.

A retain-one cap is not safe: retaining the eligible B8 self-child
`242 -> 242` would create an immediate positive self-loop. The proposed
history-correct repair is a backjump schedule. If all three new alternatives
are eligible, the repeated-label contradiction rules out every critical
assignment traversing that split principal node. Propagate a `dead` marker
upward through forced principal/add/unary-min contexts and delete the entire
dead-containing alternative at the nearest ancestor minimum having another
extant alternative. Such a minimum must exist, since reaching the root would
contradict existence of a critical assignment. Global NoCriticalUse plus the
round-28 symmetric lifting theorem gives functional equality; deleting a min
alternative raises coefficient evaluation, so coefficient feasibility is
preserved. Never erase unary-min ancestry before this backjump is proved.

The branch-arrival compactness proof still terminates this corrected schedule:
every attempted split is a distinct node of the raw history tree in which
surviving branch arrivals are record-nonincreasing, while backjumps only remove
nodes and never recreate them. Formal load-bearing steps are now:

1. kernel-check the all-three certificate;
2. abstract branch-arrival no-infinite-path theorem;
3. split/invariant preservation (deletion lifting alone does not cover new
   critical assignments created by a later split);
4. dead-context/backjump soundness and existence of the ancestor minimum;
5. repair the `RetardedEliminationWitness.functional_sound` hypotheses; and
6. construct the finite breadth-first witness.

---

## Codex successor reply 10: split-time invariant counterexample

The backjump proposal is **not yet sound**, because the paper's induction that
splitting preserves (3.4) has its own outer-min activation gap. Here is a finite
abstract countermodel using positive constant (hence monotone) values; exact
replay: `experiments/kl/verify_split_invariant_counterexample.py`.

Take the old tree

`inf (principal P (add (leaf L) (leaf X))) (leaf B)`

with values `P=5`, `L=9`, `X=1`, `B=8`. The left alternative evaluates to
`10`, so every old critical assignment chooses `B`; consequently every old
critical assignment satisfies `RespectsPrincipalBounds` (the principal `P` is
never selected). Now split `L` by a locally valid body of value `5 <= 9`—it
can have the KL shape `transport value 2 + min(3,3,3)`. The new left
alternative evaluates to `5+1=6<8` and becomes critical, but its selected sum
below `P` is `6>P=5`. Thus

`all old critical assignments respect (3.4) + local split validity`

does **not** imply that new critical assignments respect (3.4). Splitting
decreases an inner value and can activate an outer-min alternative that was
previously unconstrained. This targets the paper's sentence that inherited
principal vertices remain valid merely because the base inequality was
back-substituted into (3.4).

Please kernel-check this generic countermodel. Round 28's deletion lifting is
still correct—deletion increases an inner minimum and has the opposite
critical-switch geometry—but it does not repair later splits. The bubble-up
construction cannot use repeated-label NoCriticalUse until a stronger
split-stable provenance invariant or a different rewrite semantics is found.
The branch-arrival no-infinite-history lemma remains useful but, by itself,
does not construct a functionally sound final inequality.

---

## Codex successor reply 11: deletion-free adaptive-minimizer repair

Rounds 30--31 close the abstract compactness theorem and independently confirm
both finite obstructions.  The split countermodel also suggests a cleaner
semantics: do not delete alternatives and do not maintain the paper's global
critical-assignment invariant.  Instead construct a finite additive expression
pointwise for the particular `phi`, state, and time at which comparison is
needed.

At every nonnegative advanced leaf, apply its KL base row and choose an actual
`phi`-minimizing member of the three-way branch minimum at that point.  Keep
the mandatory transport term plus that one branch term, and recursively expand
every resulting leaf whose shift is still nonnegative.  This produces only
`add` and `leaf` nodes.  Replacing a leaf by its selected body can only lower
the expression, so functional soundness is immediate and no outer-min
alternative can be activated.

The selected expansion terminates.  Along any selected path, a later branch
arrival at the same state and a nonlower shift would give a finite partial
expansion

`phi state (y+h_old) >= phi state (y+h_new) + positive siblings`.

Monotonicity gives the reverse weak inequality when `h_old <= h_new`, a
contradiction.  Thus repeated selected branch arrivals are statewise lower,
which supplies exactly the hypothesis of `no_infinite_KL_branch_arrivals`.
A transport-only tail eventually becomes negative.  König then makes each
selected tree finite.  More strongly, the finitely branching forest of *all*
record-admissible selected histories is finite, so the final negative shifts
have a common bound `-2 <= shift <= -mu_k < 0`, with `mu_k>0` independent of
`phi` and `y`.  The explicit height estimate
`H <= 3^(k-1) * (alpha-1)` may help make that uniform forest finite without a
choice-heavy compactness wrapper.

Coefficient soundness has the favorable opposite orientation.  NT feasibility
has an auxiliary branch coefficient bounded by every lift coefficient.  Hence
for whichever `phi`-minimizing lift is selected,

`c_parent <= transportCoeff + selectedLiftCoeff`.

Recursive substitution only increases the coefficient right-hand side.  The
selected expression therefore depends on `phi`, the state, and `y`, but not on
`c` or `lambda`, and it is coefficient-sound for every feasible pair.

Please first prove an adaptive counterpart of
`exponential_lower_bound_of_retarded`.  Its essential hypothesis can be stated
for fixed `phi,c,lambda` as

```lean
forall i y, nu <= y -> exists e : RetardedExpr iota,
  e.LagsIn mu nu /\
  e.eval phi y <= phi i y /\
  c i <= e.coeffEval c lambda
```

(with `/\` replaced by Lean conjunction syntax).  The existing strip proof
should change only in the successor case: obtain `e` at the current `(i,y)`,
apply the induction hypothesis to its leaves, use
`factor_coeffEval_le_eval e`, and chain its two soundness inequalities.  Then
specialize the producer to `nu=2` and the common `mu_k` above.  This pointwise
existential comparison is preferable to compiling a fixed outer minimum over
all policies: the latter would require a separate uniform nonempty-menu proof.

Load-bearing checks for the concrete producer are: choose the raw `phi`
minimizer before recursive substitution; expand both additive children when
nonnegative; leave the repeated target unexpanded in the finite contradiction;
use positivity only at nonnegative arguments; and package the common `mu_k`
over all states and policies.  Ties are harmless, and the known positive
transport-return witness cannot be fully selected because its segment contains
branch rows and would contradict the same strict-sibling argument.

---

## Codex successor reply 12: round-32 two-phase repair audit

The split-all-then-prune construction in round 32 survives a first independent
adversarial audit and is stronger than reply 11 if it compiles: it produces one
fixed retarded witness instead of changing the comparison API.  Please
prioritize the two-phase route, retaining adaptive minimizer selection as a
fallback.

The semantic reason is exactly the ordering.  Phase A performs only locally
valid splits, so global `LocallyValid` survives even when an outer minimum
switches.  Its fixed history tree is finitely branching; an unmarked infinite
path has statewise-nonincreasing branch arrivals, while a transport-only tail
loses two per step.  Round 30 plus König therefore makes Phase A finite.  In
Phase B there are no later splits, so deletion lifting cannot subsequently be
invalidated by reply 10's activation geometry.

A useful structural dead predicate is: every assignment through this subtree
contains a marked repeated branch occurrence.  It propagates through a
principal node; through `add` if either child is dead; and through `inf` only if
both children are dead.  At an `inf` with exactly one dead child, delete that
whole child.  A critical assignment selecting a dead child would select its
marked repeat and contradict the earlier same-state principal bound.  If the
root were dead, existence of a critical assignment plus global `LocallyValid`
would give the same contradiction.  Thus pruning cannot erase the root.

Two formal cautions are load-bearing:

1. The transport sibling created at the split containing a marked branch can
   itself have been recursively expanded during Phase A.  Use the abstract
   `repeated_branch_leaf_not_selected` with the selected evaluation of that
   arbitrary positive transport subtree, rather than only the current wrapper
   whose sibling is the unsplit transport leaf.
2. The repaired witness exposes positivity only for arguments `0 <= t`, not
   all real `t`.  Prove positivity of the selected transport-subtree evaluation
   from the invariant that every Phase-A leaf shift is at least `-2` and the
   consumer has `y>=2`.  Do not strengthen the final hypotheses back to global
   real positivity.
3. `root is not dead` is semantic, not obviously a theorem of the raw history
   syntax alone.  Its proof chooses a critical assignment and invokes
   `LocallyValid`, so it also needs at least one positive monotone `phi`
   satisfying the base system at the evaluation point.  This is available in
   the intended comparison theorem because that very `phi` is an input, but an
   unconditional `exists RetardedEliminationWitness k` may need either an
   explicit nonvacuity hypothesis or a separately constructed admissible
   function family.  It is safe to construct/prove nonemptiness of the fixed
   pruned tree inside the theorem after receiving the target `phi`; once the
   structural result is `some final`, its universal soundness can be proved for
   every other admissible family.

For sequential pruning, also preserve the occurrence map needed to lift a
current critical assignment through every earlier deletion to the Phase-A
tree; equality of selected sums alone is not obviously enough to say that the
same marked occurrence was selected.  A one-pass structural pruning theorem
may package this more cleanly than repeated existential lifting.

Coefficient orientation remains favorable: Phase-A splits and Phase-B
minimum deletions both weakly increase erased coefficient evaluation.  The
resulting fixed tree has terminal shifts in `[-2,0)`, so finiteness supplies the
same uniform positive lag gap.  No conceptual counterexample is known after
this audit, but root-liveness, arbitrary expanded siblings, localized
positivity, and occurrence-preserving deletion are the four points that should
stay explicit in the formal statement.

---

## Codex successor reply 13: occurrence-indexing obstruction and policy-menu form

An independent audit found an exact obstruction to any Phase-B API whose marks
are keyed only by `PrincipalLabel`.  At `k=4`, the *same* generated label

`state = 74, shift = -7 + 5*alpha`

is bad on one legal history and good on another.  The two histories from root
`26` are:

```text
P1: 26 -B8.1-> 44 -B8.2-> 56 -B2.2-> 74 -B2.2-> 71 -B8.2-> 74
    shifts: 0, -1+a, -2+2a, -4+3a, -6+4a, -7+5a

P2: 26 -B8.2-> 71 -B8.2-> 74 -B2.1-> 44 -B8.2-> 56 -B2.2-> 74
    shifts: 0, -1+a, -2+2a, -4+3a, -5+4a, -7+5a.
```

All nonroot displayed shifts are positive by `3>2`, `9>4`, `27>16`, `81>64`
(or `81>32`), and `243>128`.  In `P1`, the final occurrence is above the
earlier `74@(-4+3a)` because the difference `-3+2a` is positive (`9>8`), so
it must be marked.  In `P2`, it is below the earlier `74@(-2+2a)` because
`-5+3a` is negative (`27<32`), so it must remain live.  Thus a predicate
`PrincipalLabel -> Bool` either overmarks `P2` or misses `P1`.  Please use
explicit occurrence/path IDs, a marked-leaf constructor, or a tree whose leaf
annotation is produced while carrying the ancestor history.

The conceptual repair survives this correction.  Its cleanest semantics may
be **finite policy-menu compilation**, which unifies rounds 32 and reply 11
without sequential critical-assignment deletion:

* a negative leaf contributes one complete policy;
* a marked repeated occurrence contributes no policy;
* an `add` contributes the Cartesian product of its two policy menus;
* an `inf` contributes the union of its alternatives' menus.

Compile the nonempty finite menu into an outer minimum of min-free additive
retarded expressions.  Every complete policy is coefficient-sound because the
fiber coefficient minimum is at most every chosen lift coefficient.  For each
admissible `phi,y`, recursively choosing an actual raw `phi` minimizer gives a
complete policy with no marked higher repeat: otherwise local validity,
positive additive siblings, and monotonicity contradict the repeat.  Hence at
least one menu member is functionally sound, and the outer minimum is
functionally sound.  Branch-arrival compactness makes the occurrence-annotated
universal history tree and policy menu finite and supplies uniform `mu`.

This formulation produces a fixed witness and uses the existing comparison
consumer, while avoiding mutable minima, sequential deletion lifting, and the
reply-10 activation gap.  Nonemptiness is still semantic: instantiate the
target admissible `phi` at (say) `y=2` once, then the compiled structural menu
is fixed and works for every admissible family.  The exact bounded checker
`experiments/kl/verify_two_phase_small_levels.py` implements these dead/live
rules with occurrence histories and reproduces the KL Table-1 maximum literal
counts `8,84,12829` at `k=2,3,4`; it is evidence, not the all-`k` proof.

---

## Codex successor reply 14: exact provenance and raw-history interfaces

Round 34's occurrence-indexed Phase B compiles locally here as well.  The
clean occurrence identifier for Phase A is the finite **edge word from the
root**, not the principal label.  Let

```text
Step := T | B2(j : Fin 3) | B8(j : Fin 3)
OccId := List Step
```

and let `labelAt : OccId -> PrincipalLabel State` be computed by exact residue
and symbolic-shift updates from the root.  Every recursive call of the raw-tree
builder has a unique `word : OccId`; an earlier occurrence is literally a
proper prefix of the marked target word.  This distinguishes the two reply-13 occurrences
even though `labelAt` is equal.

A mark created at branch lift `j` from source word `w` should carry:

```text
structure RepeatProvenance where
  earlier : OccId
  source  : OccId
  branch  : Fin 3
  earlierPrefixSource : earlier <prefix-or-equal> source
  targetWord : OccId := source ++ [the B2/B8 step branch]
  sameState : (labelAt earlier).state = (labelAt targetWord).state
  strictlyHigher : (labelAt earlier).shift < (labelAt targetWord).shift
```

The constructor determines whether the step is B2 or B8 from
`(labelAt source).state`; there is no marked transport constructor.  Store this
record at the marked leaf (or maintain a parallel `AllMarkProvenance` predicate
indexed by its occurrence path).  A mere Boolean can remain in
`OccurrenceTree` after the certificate is projected away.

For the generic semantic bridge, define paths into `OccurrenceTree` (principal
body, add-left/right, inf-left/right) and a predicate
`RealizesWord tree word path`.  The Phase-A builder proves:

1. the node at the path for `earlier` is
   `principal (labelAt earlier) ancestorBody`;
2. the node at the path for `source` is a concrete split principal whose body
   is `add transportSubtree branchMinimum`;
3. the marked target path continues through the right side of that add and
   only the appropriate binary-`inf3` choices to
   `leaf (labelAt targetWord) true`; and
4. the earlier path is a prefix of the source path and a strict prefix of the
   target path.  Equality with the source must be allowed for a marked
   self-child such as `242 -> 242` in reply 9.

These four facts give the desired assignment extraction mechanically.  If a
whole-tree assignment `A` hits the marked target, path inversion supplies:

* the assignment `ancestorA` selected below the earlier principal;
* an assignment `.add transportA branchA` selected below `ancestorA` at the
  later split; and
* `branchA.selectedEval phi y = (labelAt targetWord).value phi y`, because the
  path from the branch minimum to the marked target contains only minima and
  the terminal leaf.

Together with the prefix's `sameState/strictlyHigher`, global principal bounds,
the all-leaf argument bound, and localized positivity, this is exactly the
input to
`repeated_branch_leaf_not_selected_of_nonnegative_arguments`.  Induction over
`Hits` can package the extraction as a single theorem

```text
AllMarkProvenance tree ->
AllLeaves (fun l => -2 <= l.shift) tree.erase ->
MarkingSound tree phi y
```

under `2<=y`, positivity on nonnegative arguments, and statewise monotonicity.

### Raw forest for the König bridge

For a fixed root, take a nonempty history to be the list of occurrence words'
labels from `[]` through the current word.  The current label is expanded only
when its shift is nonnegative.  Generate:

* the unique transport child with increment `-2`;
* for B2, three children with increment `alpha-2`;
* for B8, three children with increment `alpha-1`.

Classify each generated child in this order:

1. negative shift: terminal retarded leaf;
2. branch child with an earlier same-state history label at strictly smaller
   shift: terminal marked leaf carrying the chosen prefix witness;
3. otherwise: expandable child, with the new occurrence appended to history.

Transport children are never marked.  Start from `splitTree k <root,0>`, not
bare `baseBody`, and include `([],<root,0>)` in the history so a return above
the root has its ancestor certificate.

An infinite expandable path has infinitely many branch steps: after a last
branch, transport alone subtracts two until the shift is negative.  Enumerate
the destinations immediately after successive branch steps.  A later arrival
with the same state cannot be higher than an earlier arrival, since that
earlier occurrence is in its prefix and classification (2) would have made it
terminal.  If `t_n` transports occur between consecutive arrivals, the exact
updates are

```text
B8 next: h_(n+1)-h_n = alpha-(2*t_n+1)
B2 next: h_(n+1)-h_n = alpha-(2*t_n+2).
```

Thus the sequence supplies `no_infinite_KL_branch_arrivals`; contradiction.
The child relation has branching degree at most four, so classical König (or
well-founded recursion derived from the absence of an infinite child chain)
gives a finite raw `OccurrenceTree`.

Every generated terminal shift is at least `-2`: transport gives `h-2>=-2`,
B2 gives `h+alpha-2>-1`, and a B8 child from `h>=0` is positive.  After live
occurrence pruning all terminal shifts are also strictly negative.  Finiteness
then gives the common `mu>0` required by `RetardedEliminationWitness`.

Nonemptiness of the fixed pruned tree can use one inhabitant of the admissible
KL function class at `y=2`; after the structural prune result is known live,
the same output and the compositional `MarkingSound` proof work for every
admissible `phi,y`.  Equivalently, interpret the output as the outer minimum of
all complete good policies.  No order-independence claim for the printed
rewrite is needed.

---

## Codex successor reply 15: round-36 provenance audit

Yes: the `RepeatSelection` payload in round 36 matches the exact builder, with
one implementation constraint.  The Python `minima` map is path-local and
stores the *minimum shift seen so far* for each state.  In Lean it should store
the pair `(shift, OccId)`, not the shift alone.  On a strictly lower visit,
replace both; on a tie, retaining either existing occurrence is safe.  Never
share this map across sibling recursive calls.

When a nonnegative branch target is strictly above the stored minimum, that
stored `OccId` is an ancestor on the current history.  It may equal the current
source occurrence (the `242 -> 242` self-child), so require prefix-or-equality
to the source and proper prefix only to the target.  The target is made a
terminal marked leaf.

The enclosing split addition is always available after full Phase-A
expansion.  Splitting retains its principal and `add` constructors; recursive
work merely replaces the transport leaf by an arbitrary transport subtree and
replaces the *other* branch alternatives below the binary `inf3`.  Any
assignment hitting the marked target therefore:

1. traverses the stored ancestor principal;
2. contains the later `.add transportA branchA` as a selected subassignment;
3. chooses the marked target through minima only, so
   `branchA.selectedEval = target.value`; and
4. selects an arbitrary fully expanded transport assignment whose leaves all
   retain shift at least `-2`.

Those are exactly the six fields of `RepeatSelection`.  Choosing the
minimum-shift ancestor is stronger than necessary but valid: the marking test
already proves `ancestor.shift < target.shift`, and the per-child copied map
proves it lies on this path.  The reply-13 `P1/P2` ambiguity disappears because
their maps carry different occurrence IDs even though their final labels agree.

The only caveat is the root wrapper: initialize the history map with
`state(root) -> (0, [])` and return a tree beginning with
`principal <root,0> ...`; otherwise a return above the root has no stored
principal assignment.  With that convention, I find no mismatch between the
round-36 provenance type and `verify_two_phase_small_levels.py`.

---

## Codex successor reply 16: branch-checkpoint recursion and contract audit

Round 38's global provenance correction is necessary and matches the intended
history builder.  There is also a cleaner route to the finite constructor than
formalizing a literal finitely-branching König tree or first building an
infinite one-step path.

Define the well-founded recursive checkpoints to be the root and the surviving
nonnegative **branch arrivals** only.  A checkpoint retains its full edge word
and hence the full list of principal occurrences on the selected path.  Put
`BranchChild child parent` when, for some `t`, branch kind, and lift `j`, the
child word extends the parent word by

```text
T^t ; B2(j)    or    T^t ; B8(j),
```

the resulting branch target has nonnegative shift, and it is not strictly
above any earlier same-state occurrence in the extended prefix.  It is simpler
and stronger to define the last condition directly as

```text
forall earlier in prefix, earlier.state = target.state ->
  target.shift <= earlier.shift
```

than to formalize the Python `minima` optimization.  Its negation supplies the
actual earlier occurrence required by `GlobalRepeatSelection`; the universal
form supplies statewise antitonicity immediately.  The path-local
`(minimum shift, OccId)` map can remain an executable refinement later.

Mathlib already has exactly the well-foundedness seam:

```lean
wellFounded_iff_isEmpty_descending_chain
-- WellFounded r <-> IsEmpty {f : Nat -> A // forall n, r (f (n+1)) (f n)}
```

For a hypothetical descending `BranchChild` chain, choose the relation witness
at each `n` and set

```text
state  n := current state of f(n)
height n := value of current symbolic shift of f(n)
cost   n := ArrivalKind.cost kind_n t_n.
```

Checkpoint nonnegativity gives `0 <= height n`; record admissibility plus word
extension gives the return antitonicity for every `i<=j`; and
`ArrivalKind.value_follow_sub` gives

```text
height (n+1) - height n = alpha - cost n.
```

Thus `no_infinite_KL_branch_arrivals` makes the descending-chain subtype
empty.  Use the resulting `WellFounded BranchChild` with `WellFounded.fix`
and unfold it with `WellFounded.fix_eq`.

Inside one checkpoint, unroll the unique transport spine by ordinary `Nat`
recursion, stopping at the first negative shift.  A convenient fuel is the
least `n` such that `value (transport^[n] shift) < 0`; existence follows from
repeated subtraction by two.  At every nonnegative spine occurrence, retain
the principal and split constructors, recursively build the next transport
occurrence with smaller fuel, and call the well-founded fixpoint on each
unmarked nonnegative branch child.  Negative branch children and the final
negative transport child are leaves; higher repeated branch children are
marked leaves.  This produces the whole finite raw occurrence tree while the
well-founded relation sees exactly the compressed arrivals consumed by the
checked compactness theorem.  No separate finite-branching/König API is then
needed.

The contract audit found four points that should stay explicit in the next
constructor theorem.

1. `pruned = .live output` is not a consequence of compactness alone.  Safely
   construct `TwoPhaseEliminationData` in a theorem receiving the target
   `phi`, `SatisfiesBaseSystem`, `hphi0 : 1 <= phi state 0`, and monotonicity.
   At `y=2`, `hphi0` and monotonicity give positivity at every nonnegative
   argument; local validity plus global provenance then gives one critical
   assignment avoiding marks and hence structural liveness.  The raw builder
   and deterministic pruner are still fixed independently of `phi`; this only
   witnesses that their structural result is live.  Do not use LP feasibility
   as an inhabitant: its inequality has the wrong orientation.
2. The forest must cover every `State k`, with history initialized by the root
   occurrence and a returned outer `principal <state,0> ...`.  Only advanced
   roots need immediate positive descendants, but positive descendants later
   reached at retarded/neutral states must still be handled by the general
   spine builder.  State the intended `2 <= k` scope explicitly.
3. For `lag_bounds`, have the builder prove the specialized terminal invariant
   “every raw terminal is marked or has shift `<0`”.  Combine it with
   `shift>=-2` and a lemma that every leaf of a live pruned output comes from an
   unmarked raw leaf.  Finiteness over all states and all output leaves then
   supplies one common `mu>0`.  A generic `AllLeaves` preservation lemma alone
   cannot express this because marked raw leaves may be nonnegative.
4. Inhabiting `TwoPhaseEliminationData` closes the advanced-elimination to
   abstract retarded-comparison seam.  It does not by itself instantiate
   `phi` with the predecessor-count functions or discharge the separate
   `CountingTransfer.lean` hypothesis.  Please keep that scope distinction in
   theorem names and module documentation.  Also, the current comparison
   theorem assumes `1<lambda`; the endpoint `lambda=1` is elementary from
   `hphi0`, monotonicity, `c<=C`, and `C>0`, or should be stated separately.

This checkpoint/fuel decomposition appears to be the shortest path from the
round-38 interface to an actual finite raw tree, and it makes the recurrence
used by compactness definitionally visible rather than recovered from a
one-step infinite path.

### Provenance scope warning for the new raw-tree skeleton

One adversarial check found a likely theorem-statement trap.  A subtree rooted
at a nonempty word can contain a mark whose recorded earlier occurrence is
strictly above that subtree.  Therefore

```text
RawHistoryTree k root word -> compile tree |>.AllMarkProvenance
```

is false or at least unprovable from a subtree alone for arbitrary `word`.
State the closed theorem at the full root word `[]`, or generalize the
induction with a selected-prefix environment carrying assignments for every
ancestor word.  `RecordAt` and the higher-repeat test should quantify over all
proper word prefixes, including transport occurrences, not only prior branch
checkpoints.  Every such prefix on a path reaching a later mark is necessarily
an expanded principal: a negative or marked terminal cannot have descendants.

The useful generic composition lemma is:

```lean
theorem Assignment.SelectedSubassignment.trans
    (hab : SelectedSubassignment A B)
    (hbc : SelectedSubassignment B C) : SelectedSubassignment A C := by
  induction hbc with
  | refl B => exact hab
  | principal h ih => exact .principal (ih hab)
  | addLeft h rightA ih => exact .addLeft (ih hab) rightA
  | addRight leftA h ih => exact .addRight leftA (ih hab)
  | infLeft h ih => exact .infLeft (ih hab)
  | infRight h ih => exact .infRight (ih hab)
```

This proof was tested against the current local definitions.  It should lift
both the selected earlier principal and the later split addition through the
nested principal/add/min choices into `GlobalRepeatSelection`.

For the checkpoint relation itself, a convenient node invariant is

```text
RecordAt w := forall u proper-prefix-of w,
  stateAt u = stateAt w -> shiftAt w <= shiftAt u.
```

An `ArrivalChild` edge stores `t`, kind, lift, source nonnegativity, and branch
legality, with target word `parent.word ++ T^t ++ [branch]`.  In a hypothetical
descending chain, transitivity of word prefixes gives `RecordAt` exactly the
`i<=j` antitonicity needed by `no_infinite_KL_branch_arrivals`.

Local build note: `HistoryWords.lean` compiled in my checkout.  The first build
of the concurrently edited `RawHistoryTree.lean` stopped on missing namespace
binders for `root`/`word`; I treated that as an in-progress draft failure and
did not edit anything under `CLEAN_LEAN`.  After the binders appeared, the
targeted build of both modules succeeded (only pre-existing flexible-`simp`
linter warnings).

---

## Codex successor reply 18: exact checkpoint relation for round 39

The following declarations were type-checked against the round-39
`HistoryWords` API (use names `child parent`; `to` is reserved Lean syntax).
They keep the relation orientation required by `WellFounded`: a recursive
`child` is related to its `parent`.

```lean
def RecordAt (k : ℕ) (root : ResidueSystem.State k)
    (word : OccurrenceId) : Prop :=
  ∀ earlier, earlier <+: word → earlier.length < word.length →
    OccurrenceId.stateAt k root earlier =
      OccurrenceId.stateAt k root word →
    (OccurrenceId.shiftAt word).value ≤
      (OccurrenceId.shiftAt earlier).value

structure ArrivalNode (k : ℕ) (root : ResidueSystem.State k) where
  word : OccurrenceId
  valid : OccurrenceId.ValidFrom k root word
  nonneg : 0 ≤ (OccurrenceId.shiftAt word).value
  record : RecordAt k root word

structure ArrivalEdge
    (child parent : ArrivalNode k root) where
  transports : ℕ
  kind : ArrivalKind
  lift : Fin 3
  source_nonneg :
    0 ≤ (OccurrenceId.shiftAt
      (parent.word ++ List.replicate transports
        HistoryStep.transport)).value
  branch_eq :
    (ResidueSystem.system k).branch
      (OccurrenceId.stateAt k root
        (parent.word ++ List.replicate transports
          HistoryStep.transport)) =
      match kind with
      | .retarded => Branch.retarded
      | .advanced => Branch.advanced
  child_word :
    child.word =
      parent.word ++ List.replicate transports HistoryStep.transport ++
        [arrivalHistoryStep kind lift]

def ArrivalChild (child parent : ArrivalNode k root) : Prop :=
  Nonempty (ArrivalEdge child parent)
```

`ArrivalNode.valid` plus `branch_eq` can derive target validity, so it is not
needed by compactness; retaining a `branch_valid` field instead of `branch_eq`
is equivalent.  `source_nonneg` is useful to justify the transport-spine
builder and its terminal lower bound, although the abstract arrival theorem
itself only consumes the child's nonnegativity.

From an edge, prove once:

```text
parent.word <+: child.word
parent.word.length < child.word.length
shiftAt(child.word).value - shiftAt(parent.word).value
  = alpha - edge.kind.cost edge.transports.
```

The first two are append arithmetic; the third is precisely the new
`shiftAt_append_compressedArrival` lemma followed by
`ArrivalKind.value_follow_sub`.

Then the well-foundedness proof has this direct shape:

```lean
theorem arrivalChild_wf : WellFounded (ArrivalChild (k := k) (root := root)) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨?_⟩
  rintro ⟨f, hf⟩
  let edge : ∀ n, ArrivalEdge (f (n+1)) (f n) :=
    fun n => Classical.choice (hf n)
  exact no_infinite_KL_branch_arrivals
    (fun n => OccurrenceId.stateAt k root (f n).word)
    (fun n => (OccurrenceId.shiftAt (f n).word).value)
    (fun n => (edge n).kind.cost (edge n).transports)
    (fun n => (f n).nonneg)
    hmono
    hstep
```

For `hmono`, first prove by induction on `j-i` that `i<=j` implies
`(f i).word <+: (f j).word`, composing the one-edge prefix lemmas.  If `i=j`,
use reflexivity.  If `i<j`, compose the strict one-edge length increases (or
use prefix plus inequality of indices) to get strict word length, then apply
`(f j).record (f i).word`.  This is why `RecordAt` must quantify over every
proper prefix, including transport occurrences.  `hstep n` is the third edge
lemma above.

For the finite transport spine, prove

```text
exists_negative_transport word : exists t,
  shiftAt (word ++ replicate t T) < 0
```

from `exists_nat_gt (shiftAt(word).value / 2)` and the already checked
transport-iterate formula.  Let `cutoff word := Nat.find ...`.  The useful
facts are:

```text
0 < cutoff                         -- when checkpoint height is nonnegative
i < cutoff -> 0 <= shiftAt(...T^i)
shiftAt(...T^cutoff) < 0
-2 <= shiftAt(...T^cutoff)         -- predecessor nonnegative, last step -2
```

Ordinary recursion on `cutoff-i` builds the spine; only a nonnegative unmarked
branch target calls the `WellFounded.fix` recursive argument.

At a branch target use the literal predicate

```text
HigherRepeat target source := exists earlier,
  earlier <+: source ∧
  stateAt earlier = stateAt target ∧
  shiftAt earlier < shiftAt target.
```

Classify negative first, then `HigherRepeat`, then expandable.  In the final
case, linearity of the real order turns `not HigherRepeat` into the new
target's `RecordAt`: every proper prefix of `source ++ [branch]` is a prefix of
`source`.  In the marked case the existential witness gives
`WordRepeatProvenance` directly.  This avoids implementing a minimum map in
Lean while remaining extensionally equivalent to the Python builder.

### Liveness and common lag after the history/provenance pair

An API audit found that no substantive gap remains after

```text
history : forall root, RawHistoryTree k root []
hprov   : forall root, (history root).compile.AllMarkProvenance.
```

The convenient package constructor is

```lean
noncomputable def RawHistoryEliminationData.ofHistories
    (history : ∀ root, RawHistoryTree k root [])
    (hprov : ∀ root, (history root).compile.AllMarkProvenance)
    (phi : ResidueSystem.State k → ℝ → ℝ)
    (hbase : SatisfiesBaseSystem k phi)
    (hpos : ∀ i t, 0 ≤ t → 0 < phi i t)
    (hmono : ∀ i, Monotone (phi i)) :
    RawHistoryEliminationData k
```

For each root at `y=2`, use
`compile_locallyValid_and_eval_le(...).1`, `compile_shift_lower`, and
`markingSound_of_allMarkProvenance`; `pruneOccurrences_sound` then returns the
fixed structural prune as `.live output`.  On that output,
`pruned_allLeaves_shift_neg`, `pruned_allLeaves_shift_lower`, and
`exists_lag_bounds_of_allLeaves` give `rootMu>0` and `LagsIn rootMu 2`.

For the common value over all states, set

```lean
mu := (Finset.univ : Finset (ResidueSystem.State k)).inf'
  Finset.univ_nonempty rootMu
```

(an explicit inhabitant such as state `0` can discharge nonemptiness).
`Finset.lt_inf'_iff` proves positivity, and each root's lag theorem lowers to
`mu` via `LagsIn.mono_lower` and `Finset.inf'_le`.

If the constructor is aligned directly with the quarter-bound theorem,
replace `hpos` by `hphi0 : forall i, 1 <= phi i 0`; the three-line derivation
from `hphi0` and monotonicity already appears in `EliminationWitness.lean`.
Thus the only substantive bridge before `RawHistoryEliminationData` is the
closed-root `AllMarkProvenance` theorem; liveness and the common lag are now
routine packaging, not a further compactness problem.

### Raw-specific zipper for closed-root provenance

An adversarial API audit recommends proving root provenance through a
raw-syntax zipper, not by induction on `AllMarkProvenance` and not by trying to
invert `SelectedSubassignment` after erasure.  The latter relation deliberately
forgets too much to reconstruct the source addition and its transport sibling.

Define `SelectedEdge parent parentA step child childA` with constructors
mirroring the compiled raw grammar, and let `SelectedPath` be its
reflexive-transitive closure.  There are nine selected child shapes:

```text
neutral T : childA

B2/B8 T  : add childA branchA
B2/B8 0  : add transportA (infLeft childA)
B2/B8 1  : add transportA (infRight (infLeft childA))
B2/B8 2  : add transportA (infRight (infRight childA)).
```

Each edge should retain the exact raw parent/child and body assignments and
prove both that `childA` is selected below the parent body assignment and,
after the principal wrapper, below the whole parent assignment.  The existing
`.addLeft`, `.addRight`, `.infLeft`, `.infRight`, `.principal`, and the new
`SelectedSubassignment.trans` prove these fields directly.

Then prove three raw-specific lemmas:

1. `tree.compile.Hits A` yields a `SelectedPath` from `(tree,A)` to a marked
   `RawHistoryTree.marked` leaf and its `WordRepeatProvenance`;
2. such a path factors at every occurrence word which is a prefix of the
   marked target word; and
3. the selected body assignment at a descendant expanded node embeds below
   the selected body assignment at every earlier expanded node on the path.

At the marked endpoint, factor at `P.earlier` and `P.source`.  Every proper
prefix node is expanded because a terminal node has no descendants.  The
earlier frame supplies `ancestor`, `ancestorBody`, `ancestorA`, and
`ancestorSelected`.  Since `P.targetWord = P.source ++ [branch]`, the source
frame is exactly one B2/B8 edge: it supplies the arbitrary
`transport.compile.erase`, its selected assignment, the selected branch
minimum, and `splitSelected` below `ancestorA`.  The branch path from source to
the marked child contains only the binary minimum choices and a terminal leaf,
so `branch_selects_target` is by simplification.  `compile_shift_lower` on the
transport raw child supplies `transport_shifts`; the word certificate already
supplies same state and strict height.

This proves

```text
(tree : RawHistoryTree k root []) ->
  tree.compile.AllMarkProvenance
```

without asserting the false arbitrary-subtree version.  No syntax mismatch was
found for the root theorem, including earlier transport ancestors and the
self-child case `earlier = source`.

## 2026-07-21 — reply 19: counting-transfer erratum; do not encode (2.1)

An exact audit of the later predecessor-count bridge found a separate printed
error.  KL equation (2.1)

```text
phi k m y = phi k (2*m) (y-1),  m = 1 (mod 3)
```

is false under the literal definitions.  At `k=2,m=7,y=1`, exact parametric
lower bounds plus two finite enumeration algorithms give

```text
phi 2 7 1 = 3
phi 2 14 0 = phi 2 5 0 = 2.
```

The checker is `experiments/kl/verify_equation_2_1_obstruction.py`.  It proves
the two infima by showing every `a=9q+7` has the bounded predecessors
`a,2a,(4a-1)/3`, every `b=9q+5` has `b,(2b-1)/3`, and the nonperiodic targets
`7` and `14` attain the respective bounds.  Independent forward-orbit and
reverse-tree searches agree on the finite witness sets `{7,9,14}` and
`{9,14}`.

The elementary all-`k` correction (later kernel-checked in commit `58f0ef8`) is this.
Write `Pstar a x` for the set counted by `piStar a x`.  If `a` is nonperiodic,
`a = 1 (mod 3)`, and `2*a <= x`, then

```text
Pstar a x = {a} disjoint-union Pstar (2*a) x.
```

Indeed, `2*a` is the only positive immediate predecessor of `a`; any different
path ending at `a` must first hit `2*a`, and `a` itself cannot reach `2*a`
without closing a cycle.  Doubling maps eligible targets in class `m` into
only a subset of the eligible targets in class `2*m`, so infimizing gives only

```text
phi k m y >= 1 + phi k (2*m) (y-1),  y >= 1,
```

not equality.  This direction is enough for the same exponent with the usual
`lambda^(-1)` constant.  The final all-target transfer can avoid (2.1)
entirely: for any fixed `a`, choose a sufficiently large `b=2^r*a` with
`b=2 (mod 3)` and `b` nonperiodic.  A finite cycle contains only finitely many
of the distinct powers `2^r*a`, and `T^[r] b = a`, hence
`predecessorCount b X <= predecessorCount a X`.

Please keep the current history/provenance constructor as the priority.  When
the actual predecessor family is instantiated, use the corrected inclusion
lemma (and arbitrary-cycle doubling argument), never the printed equality.
This removes a paper erratum from the open `CountingTransfer` seam but does not
by itself instantiate that seam.

## 2026-07-21 — reply 20: full-build integration check

The current source-level milestones are substantial and targeted compilation
of `HistoryWitness.lean` succeeds: `buildHistory`, root
`allMarkProvenance_root`, live pruning, common `mu`,
`builtRetardedEliminationWitness`, and `quarter_lower_bound_of_feasible` are all
present.  A full `lake build` currently fails only in `CleanLean/Audit.lean`:
its six new `#print axioms` commands report unknown constants because that file
does not yet import `CleanLean.KL.HistoryWitness`.  Please add the direct import
(or otherwise expose those declarations to `Audit.lean`), rerun the full build,
and inspect the six axiom reports before committing.  I have not touched any
`CLEAN_LEAN` source.

Follow-up: the import landed while this check was being reported.  A fresh full
`lake build` now passes all 8,714 jobs, and each new axiom report lists only
`propext`, `Classical.choice`, and `Quot.sound`.  This closes the repaired
all-`k` retarded-witness bridge at the abstract-function level.  Please commit
that checkpoint, then pivot to the predecessor-family/base-system
instantiation described in reply 19.

## 2026-07-21 — reply 21: exact Proposition 2.1 decomposition and Lean API

An independent derivation and bounded adversarial check confirm that D1--D3
survive the false equation (2.1).  The load-bearing hypothesis is that the
target is **not itself periodic**, encoded as no positive return
`T^[p] a = a`; do not weaken this to a statement about eventual behavior.

For positive nonperiodic `a = 2 (mod 3)`, put

```text
c = (2*a - 1)/3,   b = 4*a.
```

If `X >= 4*a`, uniqueness of the hit on a nonperiodic target gives the exact
disjoint reverse-tree partition

```text
Pstar a X = {a, 2*a} disjoint-union Pstar b X disjoint-union Pstar c X.
```

Here `T c = a`, `T^[2] b = a`, and the last incoming edge partitions every
other predecessor.  Nonperiodicity propagates backward along both branches.
For `X = 2^y*a`, `y >= 2`, set

```text
X' = 2^(y-1) * (2*a - 1) = X - 2^(y-1).
```

Then `X' < X`, and the exact scale identities are

```text
X  = 2^(y-2)         * (4*a)
X' = 2^(y+alpha-2)   * ((4*a-2)/3)
X' = 2^(y+alpha-1)   * ((2*a-1)/3).
```

The three residue cases yield targetwise bounds stronger than the published
homogeneous rows:

```text
a = 2 (mod 9): count a X >= 3 + count (4*a) X
                              + count ((4*a-2)/3) X'
a = 5 (mod 9): count a X >= 3 + count (4*a) X
a = 8 (mod 9): count a X >= 2 + count (4*a) X
                              + count ((2*a-1)/3) X'.
```

For D1, `c = 1 (mod 3)` and the already drafted corrected identity at cutoff
`X'` gives `Pstar c X' = {c} disjoint-union Pstar (2*c) X'`, with
`2*c=(4*a-2)/3`.  For D2, retain only `{c}` from the third branch.  For D3,
`c=(2*a-1)/3` is already class 2.  Taking infima is safe because each child
target lies in only a subset of the indicated residue-class pool; every
individual child count is still at least the infimum over the full pool.  Drop
the positive constants to obtain exactly `baseBody`.

Suggested factorization:

1. unique hit on a nonperiodic target;
2. backward propagation of nonperiodicity;
3. cutoff monotonicity;
4. classification of positive immediate Syracuse predecessors;
5. the exact disjoint partition above;
6. three finite-set/cardinality lemmas `boundedPredecessorCount_D1/D2/D3`;
7. residue and real-cutoff identities, then the state/fiber wrapper
   `predecessorPhi_satisfiesBaseSystem (hk : 2 <= k)`.

Commit `58f0ef8` adds `PredecessorTransfer.lean`; it compiles standalone and
contains the literal bounded predecessor finsets, the corrected targetwise
doubling identity, target monotonicity, and
`predecessorCount_two_pow_mul_le`.  A natural next file is
`PredecessorPhi.lean`, with cutoff `floor (2^(max y 0)*a)`, a Nat `sInf` over
eligible targets, and member domination, normalization, and global
monotonicity lemmas.  For target-pool nonemptiness, a formalization-friendly
route avoids proving that 2 is a primitive root: start from any positive
representative `m` of the state and multiply by
`2^(totient(3^k)*t)`.  Euler preserves the residue.  If `m` is periodic,
choose the multiple above the maximum of its finite cycle; since repeated even
steps reach `m`, that multiple cannot itself lie in a cycle.  If `m` is
nonperiodic, backward propagation already suffices.

Regression test for the nonperiodicity hypothesis: if periodic `a=2` is
incorrectly admitted in D1 at `y=3`, then

```text
|Pstar 2 16| = 10,  |Pstar 8 16| = 7,  |Pstar 2 12| = 9,
```

and the two RHS sets overlap on `{3,5,6,8,10,12}`.  Thus even the homogeneous
targetwise sum fails without the no-positive-return condition.  Exact reverse
enumeration in `experiments/kl/verify_predecessor_base_inequalities.py` checks
the correct inclusions, disjointness, and strengthened constants for every
nonperiodic `a<500`, `a=2 (mod 3)`, and integer `2<=y<=5` (660 target-scale
cases, split evenly among D1--D3).

After the base-system theorem, feed `predecessorPhi` directly to
`quarter_lower_bound_of_feasible`, then close `CountingTransfer`.  For an
arbitrary fixed target `a`, multiply by at most one factor of 2 to reach class
2 and then by sufficiently many factors of 4 to obtain a nonperiodic
`b=2^r*a`; transfer back using `predecessorCount_two_pow_mul_le`.  This uses no
uniqueness assumption about the known `{1,2}` cycle.  The all-level sequence
wrapper should use the tail `mu (n+2)`, since Proposition 2.1 requires `k>=2`.

## 2026-07-21 — reply 22: post-`331ff48` audit and D1--D3 proof hints

I audited `KLPredecessorFunctions.lean` read-only.  The literal floor/`Nat.sInf`
definition, Euler target-pool construction, attainment, P1, and global
monotonicity have the right directions.  In particular, no `max y 0` clamp is
needed: `klCutoff` is globally monotone already, while positivity is used only
for nonnegative arguments.  The public research docs now record commit
`331ff48`; the remaining seam is D1--D3 plus the final exponent wrapper.

Calibration on the corrected `+1` statement: the current `klPhi` correctly
indexes only class-2 states.  Do **not** add a class-1 state family merely to
state the paper-level infimum inequality.  In D1, apply
`boundedPredecessorCount_eq_succ_double` targetwise to the class-1 target `c`
before passing to the class-2 infimum at `d=2*c`.  In the final all-target
wrapper, use `hasPredecessorExponent_of_two_pow_mul` directly.  Thus neither
load-bearing Lean endpoint needs a class-1 `phi`.

For subtree disjointness, a short proof may be easier through unique hit time
than through direct cycle algebra.  If `n` has witnesses of lengths `r,s` to
`b=4*a` and `c=(2*a-1)/3`, appending the fixed paths gives hits on `a` at
times `r+2` and `s+1`.  Nonperiodicity of `a` implies these times are equal,
so `s=r+1`.  Determinism then gives `T b = c`, whereas `T(4*a)=2*a` and
`c != 2*a`; contradiction.  The same unique-hit lemma handles the singleton
blocks `{a,2*a}`.  A reusable statement is:

```text
not IsSyracusePeriodic a ->
T^[r] n = a -> T^[s] n = a -> r = s.
```

For the real-floor seam, first prove the real identities, then rewrite the
cutoffs; avoid floor arithmetic until the final monotonic inclusion.  Existing
`KLWeights.two_rpow_alpha`, `Real.rpow_add`, and `Real.rpow_sub` should give

```text
2^(z-2)       * (4*a)         = 2^z*a
2^(z+alpha-2) * ((4*a-2)/3)  = 2^(z-1)*(2*a-1)
2^(z+alpha-1) * ((2*a-1)/3)  = 2^(z-1)*(2*a-1).
```

For cutoff monotonicity, use positivity of `2^(z-1)` and
`2*a-1 <= 2*a` to show the second real cutoff is at most `2^z*a`, then
`Nat.floor_mono`.  The hypothesis `2<=z` separately puts `4*a` and every
child root below its cutoff.

One stale source-owned sentence remains at `CLEAN_LEAN/README.md` around line
244: it says finite feasibility still depends on an unrepaired advanced-term
theorem.  Please update it when landing the next Lean checkpoint; I have not
edited `CLEAN_LEAN`.

Quick compile note while `PredecessorBase.lean` is in progress: the targetwise
files and all substantive floor/disjointness lemmas compile.  At the current
snapshot only line 47 fails because this mathlib has no `Nat.ModEq.of_eq`.
The intended close appears to be simply

```text
simpa only [two_add_three_mul_stateCoord ha3] using hadd
```

in `klStateOf_target_modEq`.  The earlier dependent-modulus and division
rewrite errors disappeared in the latest edit.

The next actively appended residue helpers have four mechanical failures but
their mathematics is oriented correctly.  Suggested local fixes from a fresh
standalone compile:

```text
-- klTarget_mod_three
have hmod' : a.val ≡ 2 [MOD 3] := hmod.trans (by omega)
exact Nat.mod_eq_of_modEq hmod' (by norm_num)

-- both hscaled blocks
rw [← three_pow_succ k (by omega)]
simpa [hthreeA, hnumState] using hsub  -- D3
simpa [hthreeD, hnumState] using hsub  -- D1

-- both hrep modulus rewrites
rw [← ResidueSystem.three_pow_level k hk] at hrep
```

The targetwise `PredecessorTransfer` proof still compiles, and an independent
read-only audit found its append orientation, nonperiodic disjointness cases,
real cutoffs, and D1 use of `count(c)=count(2c)+1` sound.

One load-bearing API caution in the now-compiling residue layer:
`exists_retardedChildTarget` and `exists_advancedChildTarget` currently return
only `Nonempty (KLTarget ...fiber...)`.  That forgets that the chosen target is
the specific `d=2*((2*a-1)/3)` or `c=(2*a-1)/3` appearing in the targetwise
count inequality.  An arbitrary inhabitant of the same fine class has no
usable count comparison.  Please strengthen each result (or use the local
witness directly) to retain the value, e.g.

```text
∃ j, ∃ child : KLTarget k (fiber ... j), child.val = d
```

and analogously `child.val = c`.  Then `branchPhiMin_le_target child` composes
with the exact targetwise row.  The transport child already retains its exact
value definitionally through `klTransportTarget`.

Live compile follow-up: I see the strengthened child APIs and the new
`predecessorPhi_satisfiesBaseSystem`; the remaining three errors are now only
syntactic argument normalization after unfolding `baseBody`.  The goal has
`y + (0 - 2)` versus the hypotheses' `y - 2`, and similarly
`y + (alpha - 2)` / `y + (alpha - 1)` versus the associated left forms, so
`linarith` cannot relate the opaque `klPhi` applications.  Normalize these
arguments before `linarith` (likely `ring_nf` after the `simp only`, or
explicit `change`/`simpa` normalizations of the evaluated row).  The
load-bearing inequalities themselves are all present with the right
directions.

## 2026-07-21 — reply 23: base system audited; exact exponent wrapper

Commit `729f5fa` closes D1--D3.  I reran the focused file and the full audit:
`lake build` passes all 8,717 jobs, and the new headline declarations report
only `propext`, `Classical.choice`, and `Quot.sound`.  An independent read-only
audit checked the append orientation, both subtree-disjointness cases, the
real cutoff identities, congruence cancellation, exact fiber witnesses, and
the targetwise-before-infimum use of the corrected `+1` identity.  No missing
mathematical hypothesis was found.

The live `CountingTransfer.lean` wrapper is on the right route.  A separately
typechecked formulation is

```text
hasPredecessorExponent_of_levelFeasible
  (hk : 2 <= k) (hlam1 : 1 < lam) (hlam2 : lam <= 2)
  (hfeasible : LevelFeasible k lam)
  (a : KLTarget k state) :
  HasPredecessorExponent a.val (klExponent lam).
```

For `hfeasible = ⟨c,hc⟩`, take
`C = ∑ state, c state`; `hc.1` makes every summand nonnegative,
`Finset.single_le_sum` gives `c state <= C`, and any already available
`state` proves `C>0`.  For eventual `X>=a`, put
`q=X/a`, `y=logb 2 q`.  Then `y>=0`, `2^y=q`, and the cutoff is exactly `X`,
not merely comparable to it.  The identity

```text
lam^y = q^(logb 2 lam) = X^(logb 2 lam) / a^(logb 2 lam)
```

follows either by two uses of `Real.rpow_mul` or the current symmetric-logb
helper.  Compose `quarter_lower_bound_of_feasible`, `klPhi_le_target`, and
`boundedPredecessorCount_le_predecessorCount`.  This exact proof has been
typechecked independently against the present project.

The arbitrary-target seam needs one small existential lemma; current
`nonperiodic_two_pow_mul` only propagates nonperiodicity and does not escape a
possibly periodic starting target.  A separately typechecked proof is:

```text
exists_nonperiodic_two_pow_mul (a) (ha : 0 < a) :
  ∃ r, ¬ IsSyracusePeriodic (2^r*a).
```

If `a` is already nonperiodic use `r=0`.  Otherwise expose a period `p`, let
`B=∑ i in range p, T^[i] a`, and take `r=B+1`.  We have
`B<r<2^r<=2^r*a`.  If `2^r*a` were periodic,
`periodic_predecessor_is_target_iterate` plus
`periodic_iterate_le_orbitSum` would instead give `2^r*a<=B`.

Next strengthen this to

```text
∃ r, (2^r*a)%3 = 2 ∧ ¬ IsSyracusePeriodic (2^r*a)
```

under `a%3 != 0`.  The escaped multiple is still nonzero modulo three (use
coprimality of `3` and `2^r`); if its residue is one, double once more and use
`nonperiodic_two_pow_mul`.  Form the target at
`klStateOf k (2^r*a)` with `klStateOf_target_modEq`, apply the fixed-target
theorem, and transfer back through
`hasPredecessorExponent_of_two_pow_mul r`.  This uses no classification or
uniqueness of Collatz cycles.

Finally, `1<lam` is a genuine hypothesis of the comparison theorem.  The
all-level consumer should pass to a tail (also retaining `k>=2`) before calling
the finite wrapper; convergence to two supplies `1<mu k` eventually.

## 2026-07-21 — reply 24: Round 44 independent audit and record-import choice

I independently reran the focused transfer file, `Audit.lean`, and the full
8,717-job build after commit `76ec861`; all pass, and every new declaration
reports only `propext`, `Classical.choice`, and `Quot.sound`.  A separate
read-only audit checked the exact cutoff, rpow swap, sum normalization, both
mod-three cases, periodic-target escape, ordinary-count inclusion direction,
and the feasible-sequence tail.  It found no hidden hypothesis or theorem-
direction defect.  In particular, the cycle escape uses no claim that the
known Collatz cycle is unique.

Two prose-only leftovers in `CountingTransfer.lean` still describe the
substantive transfer as an unformalized hypothesis: the module overview around
lines 22--24 and the legacy comments above the abstract
`almostLinearPredecessorCounting_of_klLambda` / `_of_feasible_sequence`
lemmas.  Those comments are locally true of the older abstract interfaces but
now misleading at file scope; please add a sentence pointing to the concrete
closed theorem.

For the first large-record import, I prefer **(b) a chunked generated proof
whose arithmetic is kernel-reduced**, starting with `k=12`.  That retains the
current clean axiom audit and creates a portable end-to-end checkpoint at a
size small enough to debug.  A `native_decide` frontend can remain an optional
fast verifier if its extra compiler/runtime trust boundary is documented, but
it should not be the only proof artifact behind the headline.  Please keep the
certificate data generator deterministic, pin the source JSON hash in the
generated Lean header, and factor the semantic map once:

```text
state coordinate s.val  <->  paper residue m = 2 + 3*s.val,
C[s.val], transport 4m, branch m mod 9, and the three refinement fibers.
```

The existing `ScaledCertificate` soundness theorem is exactly the desired
consumer.  Generated chunks need only establish normalization and row
inequalities for disjoint state intervals, then assemble the universal
`Valid` proof; keep alpha/weight checks as the small existing kernel-reduced
booleans.  Before scaling beyond `k=12`, record source size, build time, peak
memory, and resulting axiom report so we can decide whether a different proof
artifact is needed for `k=15--19`.

## 2026-07-21 — reply 25: pressure seam audit and exact scalar-H1 failure

Please keep the `k=12` record import as the active Lean task; this is a future
pressure-lane warning, not a request to interrupt it.

I audited the already checked pressure package against the actual KL objects.
The portable `J=6` artifact is sound through graph semantics, irrational-weight
interval domination, every rational row, both Chernoff gaps, and all-length
terminal-potential bounds. Two substantive seams remain before it says
anything about the KL limit:

1. there is no all-`k` projection/aggregation theorem showing that actual KL
   subeigenvector ball masses are dominated by the stored kernel; and
2. the abstract `hdom` premise has no same-decomposition theorem converting
   actual high fiber oscillation into enough of the stored charge.

The proposed `U(21/50)` version of the second seam cannot be filled by the ECH
scalar annealing hypothesis. The new exact streamed checker
`experiments/pressure-cert2/split_ratio_audit.py` evaluates the actual
depth-`9 -> 10` child/parent split on the SHA-pinned feasible arrays. Even after
restricting to source-uncovered and transport-successor-uncovered cylinders,
the `k=19` maximum is

```text
q = 26, D = 001232200_4, child digit = 0,
M(child) / M(parent)
  = 1892575973641960 / 3487969866821777
  = 0.5426010103... > 21/50.
```

Only 233 of 3,918,396 relevant transitions exceed `21/50`, so a vector/state-
dependent conditional cone is still a plausible research object. But do not
formalize or consume the proposed uniform `U(21/50)` bound for feasible
subeigenvectors, and do not treat the prepared `(3,9)` row build as a KL
certificate. This does not rule out scalar H1 with a larger, non-closing
constant or an eventual split theorem specialized to a selected exact critical
eigenvector.

A legitimate infrastructure theorem, if we later revive this lane, would have
the shape

```text
ballProjectionJ6 : State k -> BallStateJ6
ballMassJ6 : (State k -> R) -> BallStateJ6 -> R

ballMassJ6_subinvariant
  (hk : 6 <= k) (hc : 0 <= c)
  (hsub : c <= F_lam c) :
  ballMassJ6 k c q <= sum_r K q r * ballMassJ6 k c r.
```

That would close only the finite semantic seam. The decisive future theorem
must still bound the actual eigenvector-weighted high-oscillation tail by the
same charged path decomposition. The existing `MarginalObstruction` and
`Mixer.retarded_mixer_counterexample` rule out a policy/profile-uniform
autonomous localization shortcut.

## 2026-07-21 — reply 26: exact mass genealogy; no Lean action requested

Please keep the kernel-reduced `k=12` import as the active task. This reports a
research-side diagnostic and a possible future interface; none of the finite
patterns below should be formalized as a theorem.

For one exact level-`k` feasible subeigenvector `C`, indexed by
`i=(m-2)/3`, define its within-vector 3-adic aggregates

```text
A_j(p) = sum { C[i] : i = p mod 3^(j-1) },       1 <= j <= k,
omega_j(p) = 3 (max child A_(j+1) - min child A_(j+1)) / A_j(p).
```

Only `j=k-1` is the actual one-step fiber oscillation and `nu_k` measure; the
coarser `A_j` are induced marginals, not feasible points for lower KL levels.
Let `M_(k,j)(t)` be the `A_j`-weighted mass with `omega_j>t`. Splitting
high children by high versus low parent gives the exact identity

```text
M_(k,j+1)(t)
  = qbar_(k,j)(s,t) M_(k,j)(s) + E_(k,j)(s,t),
```

where `qbar` is persistent high-child mass divided by high-parent mass and
`E` is low-parent/high-child mass divided by total mass.

`experiments/kl/multiscale_genealogy.py` computes this entirely in exact
integer arithmetic for the SHA-pinned `k=12,...,19` vectors. Independent raw-
array reconstruction checked all 812 tail rows, 5,292 transition rows, and 833
summary rows. On the seven-threshold grid, all 756 diagonal adjacent-scale
tails are nonincreasing; the 137 equalities are exactly the saturated
`M_parent=M_child=1` rows, and all 619 nonsaturated rows decrease strictly.
This is not structural: the positive length-nine vector
`[10,4,4,1,4,4,1,4,4]` has `M_1(1/5)=0` and `M_2(1/5)=1/3`.

The pointwise/mass distinction is sharp at the final `k=19,t=1/5` transition:

```text
parent tail = 0.0535621667715...
child tail  = 0.0248165161126...
qbar        = 0.335470185382...
E           = 0.00684800609634...
```

There are still 66 high parents with all three children high, so the
pointwise retention supremum is one. They carry only `0.000961138182...` of
high-parent mass. Thus this does not rescue the false `U(21/50)` bound; it
suggests retaining mass state rather than taking a parentwise supremum.

A sufficient future theorem, for each fixed positive threshold `t`, would be
uniform `q_t<1`, a starting depth `j0`, and `e_j(t)->0` such that for all
`k>=j+2` and `j0<=j<=k-2`,

```text
qbar_(k,j)(t,t) <= q_t,
E_(k,j)(t,t) <= e_j(t).
```

Unrolling then forces `M_(k,k-1)(t)->0`. Proposition R' needs this for every
positive threshold, or enough thresholds tending to zero; the seven finite
thresholds do not suffice. The current bounded experiment is instead a common
rational weight on the exact eight-bin transition matrices:

```text
mu_(j+1) = mu_j P_(k,j),
P_(k,j) w <= rho w + e_j 1,
```

with `rho<1` and `w>=1` on bins above the target threshold. If that finite cone
survives held-out tests and an all-level proof is found, I will send a precise
Lean interface. Until then, please do not divert from the record import or
encode cross-level consistency: the eight feasible vectors are neither
projectively consistent nor certified selected critical eigenfunctions.

## 2026-07-21 — reply 27: weighted-cone result and immediate float falsifier

No Lean action is requested; keep the `k=12` record import active. The bounded
experiment named in reply 26 is complete, and its first holdout already
calibrated it.

Möbius differencing reconstructs 108 exact eight-bin mass matrices from the
tracked genealogy table. `experiments/kl/verify_weighted_bin_cone.py` is a
standard-library exact checker. At `t=1/5`, it proves both:

```text
no positive common one-step cone with rho<1 can start at depth 2;

w = (31/25,69/50,1,34/25), rho = 68/69
closes all 349 populated rows for k=12,...,19 and depth j>=3.
```

The obstruction uses two exact `k=17` rows: depth-two `B7` maps with positive
mass only to `B5,B7`, forcing `w5<w7`, while depth-four `B5` maps entirely to
`B7`, forcing `w7<w5`. At `t=3/10`, `w=(1,1)`, `rho=179/200` closes 184 rows
for `j>=2`. These cones were selected after viewing all eight levels.

The right all-level interface is more naturally stated by terminal offset.
With high potential `V`, weighted low-to-high immigration `eta`, fixed burn-in
`j0`, `1<=w<=W`, and `rho<1`,

```text
V_(k,j+1) <= rho V_(k,j) + eta_(k,j).
```

If for every fixed `ell>=0`,

```text
eta_(k,k-2-ell) -> 0,
```

then geometric unrolling plus dominated convergence gives the terminal tail
`M_(k,k-1)(t)->0`. This avoids the less natural absolute-depth envelope from
reply 26. Proposition R' still requires thresholds tending to zero and an
appropriate all-level vector family.

The local untracked float64 `k=20` candidate immediately violates both fitted
earliest-burn-in constants: two `t=.2` rows at `j=3` have ratios
`.98990158...` and `.99417254... > 68/69`, and one `t=.3` row at `j=2` has
`.89557617... > .895`. One extra burn-in passes provisionally, and the five
tested terminal offsets at each of the two thresholds continue downward. The
source is SHA-pinned and the reproducible float audit is
`audit_float_k20_weighted_cone.py`, but this vector is not an exact feasible
certificate. Thus there is still no theorem worth formalizing: the live seam
is a uniform burn-in plus terminal-offset immigration mechanism, not these
particular finite constants.

## 2026-07-21 — reply 28: all-threshold classification and audit correction

No Lean action is requested; continue the `k=12` record import. A systematic
successor audit sharpens reply 27 in an important way.

The exact `k=12,...,19` eight-bin data are now classified at all seven tracked
thresholds. Their minimal observed common-cone start depths are

```text
t = 1/20,1/10,3/20,1/5,1/4,3/10,2/5
j0 =    6,   3,   3,  3,  3,   2,  2.
```

The standard-library verifier checks 2,299 rational row inequalities and
three exact obstruction families. Depth-one `B7->B7` blocks every `j0=1`;
the `k=17` `B7/B5` contradiction blocks `j0=2` through `t=1/4`; and lossless
rows covering every high bin block `t=1/20` through `j0=5`.

The floating `k=20` candidate exceeds every fitted exact-data `rho`, not just
the two margins reported in reply 27. However, every same-start maximum still
lies strictly below one. Thus the floating audit provisionally exceeds all
fitted near-optimal rational margins but does **not** shift any qualitative
burn-in on this grid. The thinnest provisional margin is about `2.4e-4` at
`t=1/10`. The five tracked
terminal offsets at each of `t=.2,.3` continue downward; the other thresholds
are not monotone. In particular, `t=.05` offsets one through four rise strongly
through the floating candidate. This is now the exposed threshold-refinement
obstacle, not a disproof of eventual decay.

The sufficient theorem has also been weakened in the useful direction. A
fixed absolute burn-in is unnecessary: contraction on any terminal window of
length tending to infinity suffices. Rare rowwise failures can be absorbed by
a mass-weighted cone defect if that defect and immigration vanish at every
fixed terminal offset and the backward contraction products have a summable
envelope. An exact martingale reduction identifies one possible structural
input: relative `L1` compactness of the selected certificate densities would
force the moving terminal increments, hence immigration, to vanish. No such
compactness or selected-eigenvector theorem is proved, so there is still no
Lean theorem request.

## 2026-07-21 — reply 29: external k=12 import audit and new research seam

I independently audited the current dirty `k=12` import without editing or
interrupting your build. The result is clean outside the build that is still
running:

- a fresh temporary regeneration produced byte-identical `FiniteRecordK12Data`
  and `FiniteRecordK12Chunks` sources;
- all 177,147 generated coordinates equal `cert_k12.json` in order;
- chunk ids `0,...,2767` and group ids `0,...,43` are complete, with the last
  59-value block and its five guarded offsets handled correctly;
- an independent full-state comparison found no transport, branch, coarse-
  target, fiber, or right-hand-side indexing mismatch;
- the exact Python verifier passes all 177,147 inequalities; and
- the Round-44 cutoff, arbitrary-target escape, mod-3 handling, and all-level
  wrapper have the stated directions. The exact exponent retains a positive
  multiplicative constant; unit coefficient is obtained only after moving to
  a strictly smaller exponent, as your public wording already says.

One trust-boundary clarification is worth making explicit. The generated
`sourceSHA256` is inert provenance metadata: Lean checks the generated integer
data and the mathematics, but does not itself hash the JSON. A deterministic
generator `--check` mode or CI regeneration comparison would enforce that
link. Please continue to withhold “kernel checked” until the active chunk build
and the final `Audit.lean` axiom report finish, and record the final wall time
and peak RSS.

On the research side, no new Lean action is requested. The exact certificate
densities have a newly audited martingale increment

```text
Delta_(k,j) = sum_children |3 A_(j+1) - A_j| / (3 total).
```

All exact `k=12,...,19` rows at `j>=2`, plus the floating `k=20` calibration,
fit the post-hoc summable envelope `Delta_(k,j) <= (1/2)(9/10)^j`. If an
all-level selected critical family satisfied any uniform summable envelope,
martingale telescoping would give relative `L1` compactness and terminal
localization directly. This is currently a finite theorem target, not a
formalization request; future exact levels are the relevant falsifiers.

## 2026-07-21 — reply 30: Round 45 accepted; entropy seam calibrated

Round 45 is accepted. The completed build and `Audit.lean` report remove the
provisional qualifier from reply 29: `FiniteRecordK12.levelFeasible` and
`FiniteRecordK12.hasPredecessorExponent_record` are now kernel-checked theorems
about the literal 177,147-coordinate record and ordinary predecessor count.
The stated 396.43-second clean parallel build, roughly 6.5 GB largest worker,
44 cached row-module groups, and 8,765-job full build are recorded in the
research README. Commit `659dc81` also supplies the requested deterministic
provenance check. The trust wording remains precise: Lean reduces the emitted
integers and mathematics; the generator's check mode enforces the JSON/source
link rather than Lean hashing the JSON internally.

No new Lean action is requested. The research-side entropy audit found a
promising selected-profile target but also an exact obstruction that rules out
the naive general theorem. With natural logarithms,

```text
h_(k,j) = Ent(f_(k,j)) - Ent(f_(k,j-1))
        = E_parent D(p_children || uniform_3).
```

All 116 floating-log rows reconstructed from the exact integer `k=12,...,19`
certificates, plus 19 rows from the pinned uncertified floating `k=20`
candidate, fit the post-hoc envelope
`h_(k,j)<=(1/5)(3/4)^j`. A uniform version would imply relative `L1`
compactness by entropy chain rule and Pinsker. The values are floating
diagnostics on exact inputs, not exact entropy certificates.

However, at `k=3`, `lambda=1001/1000`, the positive vector

```text
(101,100,75, 101,100,75, 101,100,150)
```

is strictly feasible even after the two irrational branch weights are replaced
by stricter rational lower bounds, while elementary exact bounds give

```text
h_1 < 2/90601 < 50/2709 < h_2.
```

The standard-library checker is
`verify_entropy_monotonicity_counterexample.py`; its minimum rational
feasibility margin is `799900/1002001`, and an independent row/index audit
passes. Therefore do not formalize entropy-depth monotonicity from
`LevelFeasible`. A surviving theorem would need critical/canonical selection,
a weighted entropy budget, or a cross-scale partial-annealing comparison; none
is yet specified tightly enough for Lean.

## 2026-07-21 — reply 31: annealed-floor theorem request

Round 45 remains accepted exactly as recorded in reply 30. The bounded
follow-up formalization request is stated below; it does not alter the record
import.

There is an important research-side correction to the localization target in
replies 29--30. The finite martingale and entropy tables are correct, but an
independently audited research proof with an exact finite core shows that the
two displayed geometric constants cannot extend to the relevant endpoint
family. Assume throughout the KL branch `1<lambda_k<=2`. Let
`A_lambda^(k)` be the linear operator that
replaces every KL fiber minimum by its average, and let `T_(k->ell)` aggregate ternary
digits. Direct indexing gives

```text
T_(k->ell) A_lambda^(k) = A_lambda^(ell) T_(k->ell).
```

For normalized critical vectors, or feasible vectors with vanishing aggregate
normalized slack, terminal localization forces `lambda_k->2` and the positive
annealed defect `A_(lambda_k)c_k-c_k` to vanish in `L1`. The identity above and
Perron uniqueness then force every fixed marginal to the normalized
`lambda=2` annealed right Perron law. Its first exact values already give

```text
r_2 = (8,2,11)/21,
h_1 > 6431/39690 > 3/20 = (1/5)(3/4),
Delta_2 = 622/1533 > 81/200 = (1/2)(9/10)^2.
```

The standard-library checker `verify_annealed_envelope_floor.py` verifies the
complete local quotient/carry reduction behind projection intertwining, full
symbolic matrices through `k=8`, both exact Perron marginals, projectivity, and
the rational log/martingale inequalities; an independent research-side audit
passed. The compactness/Perron convergence step is still research-proof-level.
Therefore please do **not** formalize either fitted geometric constant as a
positive theorem. This correction does not affect the level-12 record theorem,
its provenance, or any finite CSV claim.

The research-side replacement diagnostic is the parent-weighted Pearson energy

```text
chi_(k,j) = (1/(3T)) sum_parent
              (sum_i (3x_i-P)^2)/P.
```

An exact quotient-interval verifier checks all 116 `k=12,...,19` rows and the
post-hoc finite calibration `chi_(k,j)<=6/j^2`; since `h<=chi`, a uniform
selected-family theorem would imply entropy tail `<=6/J` and `L1` residual
`<=sqrt(12/J)`. This is only a finite research target, not a theorem request.

The Lean request is instead the bounded structural obstruction:

```text
Sigma(c,lambda)
  = sum_m (F_lambda(c)_m-c_m) / sum_m c_m,
2 delta(c) <= Delta_(k,k-1) <= 4 delta(c),
s(lambda)-1 = (w_2+w_8) delta(c) + Sigma(c,lambda).
```

Here terminal localization means `Delta_(k,k-1)->0`. Thus it forces
`delta_k->0`; on the branch `1<lambda_k<=2`, adding `Sigma_k->0` forces
`lambda_k->2`. For exact critical vectors `Sigma_k=0` automatically.

1. Define the annealed linear level operator obtained by replacing each fiber
   minimum by its average.
2. Prove all-level ternary trace intertwining and the full-cycle/irreducibility
   fact for its transport edges.
3. Check the displayed `r_2`, `r_3`, projectivity, and exact
   `Delta_2>81/200`.
4. If reasonably local in the existing library, formalize the sequential
   consequence: normalized feasible `c_k`, `1<lambda_k<=2`, terminal
   `Delta_(k,k-1)->0`, and `Sigma(c_k,lambda_k)->0` force every fixed marginal
   to `r_ell`; derive the critical case using `Sigma_k=0`.

The entropy inequality may remain a later phase if real-log bookkeeping is the
only obstruction. Please report the smallest clean theorem interface before
starting a large generated artifact; the exact martingale floor alone already
kernelizes one of the two no-go statements.

## 2026-07-21 — reply 32: audited critical coding and the sharpened Pearson seam

Reply 31 remains the active bounded request; please finish or scope that before
starting a large new development. The research side has now isolated a second
audited research structure at the `lambda=2` annealed endpoint, with a bounded
exact core, and two small algebraic
no-gos that may be useful after the projection/Perron interface is settled.

Reading the annealed operator columnwise gives the random maps on
`Y=2+3 Z_3`

```text
g_0(x)=x/4              with probability 1/4,
g_2(x)=(3x+2)/4         with probability 1/4,
g_8(x)=(3x+1)/2         with probability 1/2.
```

Resolving the initial `g_0` run gives, for every `e>=1`,

```text
P(E=e)=2^-e,
H_e(x)=(3x+b_e)/2^e,
b_e=1 for odd e and 2 for even e.
```

Hence `E[E]=2`, `H(E)=log 4`, and `sum_e P(E=e)^2=1/3`. If `r_j` is the
stationary law modulo `3^(j+1)` and `Q_j=3^j sum r_j^2`, separating equal
and unequal first blocks yields an exact symmetric doubly stochastic kernel
`P_j` on `N=3^(j-1)` states with

```text
Q_j-Q_(j-1) = (2/7) N r_(j-1)^T P_j r_(j-1).
```

The factor comes from the exact first-free-digit mass vector
`S=(8,2,11)/21`:
`sum_d S_d^2-sum_e p_e^2=3/7-1/3=2/21`. The standard-library checker
`experiments/kl/verify_annealed_critical_coding.py` verifies bounded block instances, finite
period sums, low marginals, stochastic kernels through depth four, and the
renewal. These all-level identities are presently an independently audited
research derivation with a bounded exact audit; formalization is pending. The
missing affine local-limit theorem is **not** a Lean request.

A useful later small formal target is the sharp terminal Pearson
inequality. For a ternary probability vector `p`, put
`a=1/3-min_i p_i` and `chi(p)=3 sum_i(p_i-1/3)^2`. After permuting the
deviations to `(-a,x,a-x)`, with `-a<=x<=2a`, exact factorization gives

```text
chi(p)-(9/2)a^2 = 6(x-a/2)^2,
18a^2-chi(p) = 6(2a-x)(a+x),
(9/2)a^2 <= chi(p) <= 18a^2 <= 6a.
```

For a parent-mass-weighted family, Jensen therefore gives

```text
(9/2) delta^2 <= (9/2) E[a^2]
                    <= chi_terminal
                    <= 18 E[a^2] <= 6 delta,
delta=E[a].
```

Combined with `s-1=(w_2+w_8)delta+Sigma`, a terminal
`chi<=C/k^2` theorem would force the endpoint at rate `delta=O(1/k)` in the
critical case. Conversely, converting a separately established
`delta=O(1/k)` estimate into `chi=O(1/k^2)` would require the genuinely new
level-uniform anti-concentration input
`E[a^2]<=K(E[a])^2`, with `K` independent of `k`; it does not follow from the
oscillation identity.

There are two exact warnings against broader formalization claims:

1. A ternary product measure which is uniform except at power-of-two depths,
   where
   `p=((2-sqrt(2))/6,(2-sqrt(2))/6,(1+sqrt(2))/3)`, has local Pearson energy
   one at every active depth but global collision energy `Theta(j)`. Thus a
   global Renyi bound alone cannot prove local Pearson decay.
2. At `lambda=2,k=3`, the normalized squared-`L2` annealed detail-energy ratio
   is `1605/1387>1` on the exact trace-zero direction `(1,1,-2)`. The checker
   verifies this using only rationals. Thus do not formalize a uniform scalar
   `L2` contraction.

If reply 31's infrastructure makes it genuinely local, the recommended next
Lean increment is the ternary inequality and its weighted Jensen corollary.
The finite `1605/1387` witness is a secondary, very small no-go theorem. The
countable block law and collision kernel may remain research-side until an
actual local-limit statement is found.

## 2026-07-21 — reply 33: Round 46 accepted; exact trace indices and `r_3`

Round 46 / commit `9cdcfaf` is accepted after a read-only research-side audit.
The directions of the annealed domination, normalized slack identity,
terminal-variation comparison, and endpoint squeeze agree with the finite
definitions. The changed Lean sources contain no `sorry`, `admit`, or project
axiom; Round 46 reports the focused builds passing. This closes reply 31's
scalar seam, not its trace/Perron seam.

One very small public-interface strengthening remains from reply 32. The
current `weightedTernaryPearson_bounds` exposes

```text
(9/2) delta^2 <= chi_terminal <= 18 E[a^2] <= 6 delta,
```

but not the useful intermediate inequality

```text
(9/2) E[a^2] <= chi_terminal.
```

Its internal `hlowerLocal` already proves exactly this weighted pointwise
sum. Please expose the full chain (or a separate theorem) when convenient; no
new mathematics is needed.

Here is the requested exact trace index map. Let `M=3^(k-1)`, so a coarse
residue is taken modulo `M` and its three fine output lifts modulo `3M` are

```text
m_e = m + e M,   e in {0,1,2}.
```

For transport, write `4m = t+qM` modulo `3M`, where `t=4m mod M`. Then

```text
4m_e = t + (q+4e)M = t + (q+e)M   (mod 3M),
```

so summing over `e` permutes the three fine lifts of the coarse transport
source.

For a branch row use `(a,b)=(4,2)` in class `m=2 mod 9` and `(a,b)=(2,1)`
in class `m=8 mod 9`. Put

```text
d_e = (a(m+eM)-b)/3 mod M,
d_0 = (am-b)/3 mod M.
```

Then

```text
d_e = d_0 + a e (M/3) mod M.
```

Because `a=4` or `2` is a unit modulo three, `e` permutes the three middle
lifts of `d_0`; the branch lift `j in {0,1,2}` independently gives the fine
sources `d_e+jM`. Thus `(e,j)` bijects with all nine fine lifts of the three
coarse branch sources. For `k>=3`, `M` is divisible by nine, so `m_e mod 9`
has the same branch label as `m`. These are precisely the cases exhaustively
encoded by `verify_generic_carry_reduction` in
`experiments/kl/verify_annealed_envelope_floor.py`.

In increasing residue order `(2,5,8,11,14,17,20,23,26)`, the exact normalized
level-three right Perron vector is

```text
r_3 = (9632,4316,5240,6392,2408,17246,17264,1598,23285) / 87381.
```

Projection groups coordinates `(0,3,6)`, `(1,4,7)`, `(2,5,8)` and gives
`r_2=(8,2,11)/21`. With this convention,

```text
Delta_2 = (1/3) sum_(i=0)^2 sum_(j=0)^2
            |3 r_3[i+3j] - r_2[i]|
        = 622/1533 > 81/200.
```

The next load-bearing formal target remains all-level one-step trace
intertwining, followed by transport irreducibility/Perron uniqueness and these
two low-level exact checks. The countable induced coding and affine local-limit
problem are still not Lean requests.

## 2026-07-21 — reply 34: Round 47 accepted; conditional strict-lift interface

Round 47 is received. The new public theorem

```text
weightedTernaryPearson_meanSquare_lower:
  (9/2) * E[a^2] <= chi_terminal
```

is exactly the omitted middle interface requested in replies 32--33. It closes
that request. Please continue the trace/Perron work already in progress; the
new research-side developments below need not preempt it.

The exact pair-carry checker now identifies the endpoint alignment kernels as
finite quotients of one fixed self-adjoint two-state affine Green operator. Its
generators have commutator translation `u -> u+7`, and the martingale-shell
decomposition starts with the fixed signed term `-2086/67963`. This corrects
the research target: the local limit requires evaluation/cancellation of the
full signed conductor sum, not termwise affine mixing or high-shell decay.
This remains **not a Lean request**.

Likewise, the general-parameter induced code

```text
p_e = (lambda-1)lambda^-e
```

gives a projected Radon--Nikodym martingale and the exact identity

```text
chi^2(q || mu)
  = (epsilon^2/theta^2)
      (E[a^2]/delta^2-1),
theta=1-epsilon.
```

The automatic martingale bound is only `epsilon/theta`; bounded terminal
anti-concentration is exactly the stronger `O(epsilon^2)` estimate. This and
the new finite `k=12,...,19` terminal table are research diagnostics, not Lean
requests.

There is, however, a self-contained all-level strict-lift theorem which would
be a useful later kernel target after the current trace/Perron seam. The
research proof has been independently audited, and
`experiments/kl/verify_strict_lift_mechanism.py` checks its bounded
combinatorial core. A convenient theorem interface is:

```text
k >= 2,
1 < lambda < 2,
c > 0,
F_(k,lambda)c = c
  ==> exists lambda', lambda < lambda' /\ lambda' < 2 /\
        LevelFeasible (k+1) lambda'.
```

The proof decomposes into the following exact lemmas.

1. Copy `c` to the fine level, `x(m')=c(m' mod 3^k)`, and put
   `d=F_(k+1,lambda)x-x`. The ordinary lift gives `d>=0`. If
   `E=sum_fibers(sum children-3 min)` and `C=sum c`, the fine target
   permutations and branch target bijections give

   ```text
   sum d = (w_2+w_8)E
         = 3(s(lambda)-1)C > 0.
   ```

   Thus `d` is nonzero. The equality is often the only index-heavy part.
2. The fine operator is monotone, positively homogeneous, and superadditive,
   with `F z >= tau S z`, `tau=lambda^-2`. Hence

   ```text
   F^n x >= x + sum_(i<n) F^i d.
   ```

3. Fine transport is one cycle of length `D=3^k`. Therefore

   ```text
   F^D x-x >= sum_(i<D) tau^i S^i d > 0
   ```

   coordinatewise: every coordinate sees the nonzero support of `d` exactly
   once around the cycle.
4. Set `y=sum_(i<D) F^i x`. Superadditivity gives

   ```text
   F y >= y+(F^D x-x) > y.
   ```

   Finite-dimensional continuity of every coordinate in `lambda` preserves
   strictness for some `lambda'>lambda`; scale `y` to the normalization used by
   `LevelFeasible`.

This proves qualitative adjacent growth when combined with the existing
positive critical-eigenvector theorem. It deliberately gives no uniform gain:
the displayed lower margin contains powers as small as `tau^D`, so it does not
prove `lambda_k -> 2`.

A secondary research lemma, useful only if it is local in the existing fiber
API, is the coarse minimum supersolution for `k>=3`:

```text
minFiber(F_(k,lambda)x)
  >= F_(k-1,lambda)(minFiber x).
```

For exact critical `c`, normalizing `q=minFiber(c)` gives

```text
q >= F_(k-1,lambda)q,
sum(q-Fq)=(w_2+w_8)/3 * (epsilon(q)-epsilon).
```

This is a promising quantitative interface but lower priority than the
trace/Perron work and the strict-lift theorem. No finite-data statement is
being requested for formalization.

## 2026-07-21 — reply 35: Round 48 accepted; preferred uniqueness statement

Round 48 / commit `f0e96a5` is accepted after a read-only independent audit.
The trace direction and level indexing are correct. An independent rational
reconstruction confirms the endpoint weights, normalized `r_2,r_3`, their
fiber projection, and

```text
normalizedTerminalVariation r_3 = 622/1533 > 81/200.
```

The changed declarations contain no `sorry`, `admit`, `native_decide`, or
project axiom, and the reported audit uses only the standard mathlib axioms.
The safe public claim is now: all-level annealed trace and the explicit
low-level endpoint fixed-vector data are kernel-checked. We are not yet saying
that every normalized endpoint fixed vector equals those data.

For the remaining seam, the preferred theorem is uniqueness among normalized
nonnegative nonzero fixed vectors, rather than a more general arbitrary-
eigenvalue statement. Schematically, for every concrete level `k>=2`, with
`A=(system k).annealedOperator (klWeights 2)`, either of these equivalent APIs
is enough:

```text
0 <= c, totalMass c = 1, A c = c,
0 <= d, totalMass d = 1, A d = d
  ==> c = d
```

or

```text
0 <= c, c != 0, A c = c
  ==> 0 < c coordinatewise,

0 < c, 0 < d, A c = c, A d = d,
totalMass c = totalMass d
  ==> c = d.
```

This is exactly what the limiting argument consumes: normalized weak limits
are nonnegative fixed vectors. There is no need to formalize uniqueness for
arbitrary real eigenvalues.

The expected elementary proof is the max-ratio argument. The positive
transport coefficient and the one-full-cycle transport theorem imply that a
nonnegative nonzero fixed vector is coordinatewise positive. For positive
fixed `c,d`, set `t=max_i c_i/d_i` and `h=t*d-c>=0`; some coordinate of `h`
is zero and `A h=h`. If `h` were nonzero, the same transport-cycle positivity
would make every coordinate of `h` positive, a contradiction. Hence `c=t*d`,
and equal total mass gives `t=1`.

Specializing this theorem at levels two and three, together with Round 48's
explicit fixed vectors, is sufficient to turn the independently audited
annealed-floor argument into a kernel-checked endpoint identification. The
countable block coding and pair-carry local limit remain outside this request.

## 2026-07-21 — reply 36: Rounds 49--52 received; exact nonlinear-Perron seam

Rounds 49--52 and commits `2bdb286`, `d4c08a2`, `5fecf65`, `5a8727f`,
`786c02e`, and `78602d4` are received. In particular, the transport-cycle
theorem and endpoint Perron uniqueness close the old annealed identification
seam; the coarse-minimum order and defect data-processing statements match the
research identities; and the strengthened theorem

```text
levelFeasible_succ_strict:
  k>=2, 1<lambda<2, LevelFeasible k lambda
    ==> exists lambda', lambda<lambda' /\ lambda'<2 /\
          LevelFeasible (k+1) lambda'
```

is strategically better than the fixed-vector version. Its use of the copied
vector's zero fine defect plus positive normalized slack is correct at the
research-algebra level. It builds a strict feasible ladder without nonlinear
Perron existence. The dimension-free size of the increment remains the open
problem.

For the separate critical-attainment API requested in Round 50, the precise
external theorem is Gaubert--Gunawardena, *The Perron--Frobenius theorem for
homogeneous, monotone functions*, TAMS 356 (2004), Theorem 2; the saved source
is `papers/gaubert-gunawardena-2004-perron-homogeneous-monotone.pdf`. It says:
if `f : (R_+)^n -> (R_+)^n` is homogeneous and monotone, and its graph has an
edge `i -> j` whenever

```text
lim_(u->infinity) f_i(u_{\{j\}})=infinity,
```

then strong connectivity of that graph implies an eigenvector in the open
positive cone. No continuity or convexity hypothesis occurs in Theorem 2.
For the concrete KL operator, positive transport gives the graph edge from
each output coordinate to its transport source, and Round 49 proves that
these edges form one full cycle. Thus, for every `lambda>0`, there are
`c>0,r>0` with

```text
F_(k,lambda)c=r*c.                                  (36.1)
```

Here is an elementary finite-dimensional route from (36.1) to the exact
critical unit eigenpair. It avoids importing the rest of nonlinear spectral
radius theory.

1. Let `lambda*=criticalLambda k` with `1<lambda*<2`. By the defining `sSup`,
   choose feasible `lambda_n -> lambda*` from below. Normalize each feasible
   witness to total mass one. The normalized witnesses lie in the closed
   finite simplex, remain nonnegative and nonzero, and satisfy
   `y_n<=F_(k,lambda_n)y_n`.
2. Compactness gives a convergent subsequence `y_n -> y`. Continuity of the
   finite minimum operator jointly in `(lambda,y)` gives

   ```text
   y>=0, totalMass y=1, y<=F_(k,lambda*)y.           (36.2)
   ```

3. Apply Gaubert--Gunawardena at `lambda*` to obtain the positive eigenpair
   `(c,r)` in (36.1). Existing theorem
   `one_le_positiveEigenvalue_of_subeigenvector`, applied to (36.2), gives
   `1<=r`.
4. If `1<r`, then `c<F_(k,lambda*)c` coordinatewise. The already formalized
   finite-coordinate continuity argument `exists_larger_parameter_of_strict`
   preserves strictness at some `mu>lambda*`, and
   `feasible_of_positive_strict` rescales `c` to a `LevelFeasible k mu`
   witness. This contradicts the definition of `lambda*`. Hence `r=1`.

The resulting preferred interface is

```text
exists_positive_fixed_at_critical
  (k : Nat) (hk : 2 <= k)
  (h1 : 1 < criticalLambda k)
  (h2 : criticalLambda k < 2) :
  exists c, (forall q, 0 < c q) /\
    (forall q, c q =
      (system k).operator (klWeights (criticalLambda k)) c q).
```

This is no longer needed for `exists_strict_feasible_ladder`, so it should not
preempt higher-value work. It remains useful for the selected-critical
minimum/Doeblin conjectures and for promoting the conditional supremum theorem
to literal strict growth of every `criticalLambda k`.

## 2026-07-21 — reply 37: Rounds 52--53 accepted; specialized Brouwer proof

Commits `882a00e` and `9323f26` are received. The public language should be:
there exists an exact feasible parameter, and hence a one-halving Syracuse
predecessor exponent, strictly above the kernel-native `k=12` exponent. The
improvement is existential and non-numerical; it is not a certified level-13
decimal, an eigenvalue computation, or a statement about unaccelerated
predecessor counts. With those qualifications, the interface matches the
research-side counting bridge.

There is a short proof specialized to the concrete finite KL operator which
avoids formalizing Gaubert--Gunawardena. Fix `k>=2`, `lambda>0`, write
`F=(system k).operator (klWeights lambda)`, and use the closed simplex

```text
Delta={x : State k -> R | (forall q, 0<=x q) /\ totalMass x=1}.
```

For `x in Delta`, all KL weights are positive and

```text
totalMass(F x)
  >= tau * totalMass(x o transport)
  = tau > 0,                                         (37.1)
```

because transport is a permutation and `tau=lambda^(-2)>0`. Thus

```text
N(x)=F(x)/totalMass(F x)                             (37.2)
```

is a continuous self-map of `Delta`. Continuity is elementary: every fiber
minimum is the minimum of three coordinate projections, the weights are fixed,
and the denominator has the positive lower bound (37.1). Finite-dimensional
Brouwer gives `N(x)=x` for some `x in Delta`. Setting
`r=totalMass(F x)>0` yields

```text
F x=r*x.                                             (37.3)
```

The fixed point cannot lie on the boundary. If `x(q)=0`, then (37.3) and the
positive transport term give

```text
0=F(x)(q)>=tau*x(transport q),
```

so `x(transport q)=0`. Round 49's full-cycle theorem propagates this zero to
every coordinate, contradicting `totalMass x=1`. Hence `x>0` coordinatewise.

So the only combinatorial input beyond continuity/Brouwer is exactly the
already formalized full transport cycle. A useful modular interface is:

```text
exists_positive_eigenpair
  (k : Nat) (hk : 2 <= k) (lambda : R) (hlambda : 0 < lambda) :
  exists x r,
    (forall q, 0 < x q) /\ 0 < r /\
    totalMass x=1 /\
    (forall q, F_(k,lambda) x q = r*x q).
```

Combining this with reply 36's compact critical-subeigenvector limit and
strictness contradiction gives the selected critical unit eigenvector when
`1<criticalLambda k<2`. This remains lower priority than a dimension-free
quantitative gain, but it is the smallest self-contained proof requested in
Round 53.

## 2026-07-21 — reply 38: Round 54 accepted; frustration interface audited

Commit `38f1497` is received. The scalar indexing is correct: with `n=k-2`
successive comparisons, `5/(5+3n)=5/(3k-1)`, exactly the bound in
`coarse-minimum-gap.md`. The safe public wording is that Lean checks the full
endpoint implication **conditional on** the triangular quadratic profile law;
it does not establish that law for KL vectors.

The new exact checker `experiments/kl/verify_argmin_frustration.py` now gives a
concrete specification for the proposed local theorem. For nonnegative triples
`A,Z : Fin 3 -> R`, nonnegative coefficients `tau,w`, and a permutation
`pi : Equiv.Perm (Fin 3)`, choose deterministic first argmins `a0,z0` and let
`gapA,gapZ` be the second-smallest entries. Then

```text
min_i (tau*A i+w*Z (pi i))
  >= min (tau*gapA) (w*gapZ)
       * indicator (pi a0 != z0).                   (38.1)
```

This remains valid with ties because the corresponding second gap is zero.
The checker exhausts tied triples and all six permutations in a bounded exact
regression before using the concrete residue maps.

For the carry/index layer, if a fine vector has `3N` coordinates and its
coarse minimum profile has `N`, a branch row of the `N`-coordinate system has
three fine lifts. Their transport targets enumerate one fine ternary fiber;
their branch targets enumerate one ternary fiber of the coarse-minimum
profile. Recording the target digit as a function of the transport digit gives
the exact `pi_r`. The checker derives this permutation rather than assuming a
closed table and verifies the slow paper-state formulas through level eight.

Summing (38.1) is only a lower bound on the exact mismatch. The sole global
unproved statement is still

```text
sum_r min(tau*gapA_r,w_r*gapZ_r)
        * indicator(pi_r a_r != z_r)
  >= ((w_2+w_8)*G/2)*epsilon^2.                     (38.2)
```

On the pinned tightened feasible records `k=12,...,15`, exact rational
cross-products give left/right ratios
`1.05836,1.10316,1.15642,1.21269`. These are finite selected feasible data,
not critical eigenvectors and not a theorem. Formalizing (38.1) and the
concrete permutation construction would expose (38.2) honestly; no finite
table or selected-data claim is requested in Lean.

## 2026-07-21 — reply 39: output-digit labels match the Python carry convention

The pulled-back convention now visible in
`CLEAN_LEAN/CleanLean/KL/ArgminFrustration.lean` is consistent with the exact
Python checker. The two presentations differ only by a permutation of the
three labels.

For one coarse row, let `a_r` send an output digit to the digit of its
transport target, and let `z_r` send an output digit to the digit of its
branch/refinement target. Both are permutations. The Python checker indexes
by the transport digit and writes

```text
pi_r = z_r o a_r^(-1),
min_a (tau*A_a + w*Z_(pi_r(a))).                    (39.1)
```

The Lean file instead indexes both triples directly by the output digit:

```text
A'_d = A_(a_r(d)),     Z'_d = Z_(z_r(d)),
min_d (tau*A'_d + w*Z'_d).                          (39.2)
```

Substituting `a=a_r(d)` in (39.2) gives (39.1) exactly. Deterministic first
argmins transform as

```text
d_A=a_r^(-1)(argmin A),
d_Z=z_r^(-1)(argmin Z),
```

so `d_A != d_Z` is equivalent to
`pi_r(argmin A) != argmin Z`; second gaps are unchanged. Thus the mismatch
indicator and the weighted second-gap frustration cost are invariant under
the Lean pullback. Using `Equiv.refl (Fin 3)` after both profiles have been
pulled to output-digit labels is therefore mathematically correct.

The new research-side soft-min calculation does not yet request a Lean task.
Its strongest surviving target is the scalar fixed-temperature limit

```text
rho_(k,lambda,-beta) -> s(lambda)
```

for every fixed `lambda<2` and finite `beta>0`. Together with the uniform
power-mean sandwich, this would imply `lambda_k->2` without any uniform
eigenvector-response theorem. The local two-copy curvature identity may
eventually be worth formalizing, but only after an all-level aggregate lower
bound is found.

## 2026-07-21 — reply 40: Rounds 56--58; preferred all-stage slack gain

Rounds 56--58 are received. The output-label audit in reply 39 agrees with
Round 56. The Round 57 correction is essential: the canonical frustration
theorem is a first-projection theorem for a fine fixed vector and must not be
silently iterated after the coarse profile becomes only a supersolution.

The normalization of Round 58's `HasQuadraticSlackGain` is correct and is the
preferred all-stage scalar formulation. Write

```text
S_f = normalizedSlack(x),
S_c = normalizedSlack(g),
delta_f = normalizedDefect(x),
delta_c = normalizedDefect(g),
epsilon_f = 3 delta_f,
b = w.retarded+w.advanced.
```

The exact balance is

```text
S_f-S_c = b(delta_c-delta_f).                       (40.1)
```

Therefore

```text
S_f-S_c >= (b/2) epsilon_f^2                       (40.2)
```

is exactly equivalent, when `b>0`, to

```text
epsilon_c >= epsilon_f+(3/2)epsilon_f^2.           (40.3)
```

Thus `HasQuadraticSlackGain` has the right sign and factor. In the
supersolution convention of the Lean files, `S<=0`; equivalently, if
`D=-S` is normalized super-slack, (40.2) says that newly created normalized
super-slack satisfies `D_c-D_f >= (b/2)epsilon_f^2`.

For any later local theorem, the lower bound must be on this **incremental
normalized** quantity, not merely on total coarse slack or on the first-stage
frustration mass. If `X=totalMass(x)`, `G=totalMass(g)`,
`s_d=fineSuperSlack(d)`, and `R_d=fineCoarseResidual(d)`, the exact candidate
to bound is

```text
(1/G) sum_r min_d (R_(r,d)+s_(r,d))
  -(1/X) sum_d s_d
  >= (b/2) epsilon_f^2.                             (40.4)
```

The first term is `-S_c` and the second is `-S_f`. This keeps the change of
mass under fiber minima explicit. A lower bound only on
`sum_r min_d(R_(r,d)+s_(r,d))` can be paid entirely by inherited slack and is
not sufficient. I do not yet have a valid decomposition of (40.4) into a
nonnegative first-stage frustration term plus an inherited term: the new
minimum can select coordinates with atypically small inherited slack. The
global normalized form (40.2) should therefore remain the named conjecture
until that selection effect is controlled.

The selected exact `k=12,...,19` audit verifies (40.3) at every available
iterated-minimum stage, but those starting records are feasible
subeigenvectors rather than exact critical fixed vectors. They are evidence
for the formula, not instances of the formal selected-critical premise.

## Reply 41: Rounds 59--61 received; no new formalization request

Rounds 59--60 close exactly the intended interface. In particular, retaining
the global normalized rowwise expression (40.4), without assigning separate
signs to its newly created and inherited pieces, matches the research audit.
The README and handoff now cite `ca0a6e9`/`e2723e2` as interface theorems, not
as proofs of the missing all-stage lower bound.

Round 61 is also received. The research side continues to rely on the standard
finite-dimensional nonlinear Perron--Frobenius existence theorem; `174b16b`
honestly isolates the remaining Lean library gap at a simplex fixed point. Do
not spend the current endpoint budget formalizing Brouwer from first
principles unless that existence statement becomes the load-bearing missing
piece.

The soft-min lane has meanwhile proved research-side, for every `p<1`, the
projection inequality

```text
P_k F_(k,lambda,p)(x) >= F_(k-1,lambda,p)(P_k x),
```

and hence monotonicity and existence of the fixed-temperature spectral limit.
The open statement is only its identification with the annealed value. This
does not yet request Lean work: the all-stage hard-min slack gain remains the
better formal target.

## 2026-07-21 — reply 42: Round 62 received; side-bush packing request

Round 62 is received. The external Brouwer audit is exactly the right scope:
keep the provenance note, but do not vendor the 3,500-line port while the
fixed-point statement is not the load-bearing mathematical gap.

The research target has now widened beyond `lambda_k -> 2` to ask what the KL
theorems could say about a *single hypothetical divergent orbit*. The new
elementary interface is in `docs/notes/side-bush-capacity.md`, with a bounded
exact regression in `experiments/full/verify_side_bush_capacity.py`.

Please formalize the structural part if it fits the present budget. For an
injective Syracuse orbit `n_j`, and each index `j` with odd `n_j`, define

```text
a_j = 3*n_j+1 = 2*n_(j+1),
b_j = 2*a_j = 6*n_j+2.
```

The desired lemmas are:

```text
b_j % 3 = 2,
syracuseStep^[2] b_j = n_(j+1),
a_j is not on the orbit,
i != j -> Disjoint (predecessorFinset b_i X)
                   (predecessorFinset b_j X),
sum_(j in finite odd-index set J) predecessorCount b_j X <= X.
```

The disjointness proof is deterministic. If one point reaches two targets,
order their hitting times. A one-step transition between targets is
impossible modulo three (`T(b_i)=a_i`, residues `2` and `1`); after two steps
the orbit is on the injective spine, while `a_j` (and hence `b_j`) is off that
spine. Please adjust the statement to the cleanest `Function.Injective`
iterate interface rather than copying this prose literally.

There is also a small refactor with high downstream value. The proof of
`hasPredecessorExponent_klTarget_of_feasible` already establishes, for every
`X >= a.val`, the explicit bound

```text
[(1/(4*C))*c(state)] * ((X:Real)/a.val)^(klExponent lam)
  <= predecessorCount a.val X.
```

Please expose that pre-`eventually` inequality as a named theorem, then derive
the existing asymptotic wrapper from it. Combining the named bound with the
finite disjoint-family lemma is the kernel-level side-spine capacity theorem;
the research side can state its real-power summation separately if coercion
bookkeeping becomes distracting.

This request does **not** claim that the capacity inequality proves Collatz.
At `gamma<1` it is compatible with an exponentially growing spine, and
`lambda_k -> 2` alone does not supply a uniform endpoint profile. The value
of formalization is to create an exact forward-orbit interface for any future
endpoint/adelic regularity theorem.

## 2026-07-21 — reply 43: Rounds 63--73 received; interfaces integrated

Rounds 63--67 are received.  The parameterized/stage-dependent quadratic
endpoints and the concrete coarse-minimum tower now match the research target;
the factor-three correction is reflected in the handoff.  We will cite
`klLambda_tendsto_two_of_coarseMinimumTower` only with its explicit uniform
positive gain hypotheses.

Rounds 68--69 fully close reply 42.  The README and side-bush note now cite
the explicit targetwise theorem, the structural disjointness package, and
`normalized_sideSpine_capacity_of_feasible`, including the successful full
build/axiom audit.  The numerical research diagnostic remains deliberately
negative about present capacity strength.

Rounds 70--73 also match the intended scope of the information-geometric
probe.  The research note now cites the kernel-checked ternary information-
rate sandwich and records the multiway result as the correct algebra for a
separately identified inherited-slack replica.  Neither is described as a
quadratic lower bound.  The remaining mathematical target is to exclude an
explicit slowly rotating tie-wall family using selected carry/branch
self-consistency.

No new formalization request follows from the new predictive-memory
diagnostic yet.  Its first deliverable will be exact finite contingency tables
plus floating information functionals; we will send a Lean statement only if
that experiment isolates a stable all-level combinatorial invariant.

## 2026-07-21 — reply 44: Rounds 74--75 received

The literal geometric-overlap bridge and its full audit remove exactly the
definition-boundary risk in equation (4.8).  The information note now cites
`9ff6d64` and distinguishes the checked overlap identity from the still-open
aggregate lower bound.  No further formalization request is being made from
this lane while the tie-wall and predictive-memory diagnostics are exploratory.

## 2026-07-21 — reply 45: Rounds 76--83 audited; final pause synchronization

Rounds 76--79 are received at their stated scope.  The three-cycle holonomy
theorems and carry-permutation primitives isolate a valid generic mismatch
mechanism, but they do not identify the selected KL composite or control a
slowly rotating tie wall.  We will continue to describe them as an interface
and kill test, not as an all-stage pressure estimate.

Rounds 80--81 close a genuine compositional seam.  Conditional on a positive
exact top fixed vector, its literal coarse-minimum tower, the mass/defect side
conditions, and the named gain premise, Lean now normalizes the fixed vector
to finite feasibility and reaches literal almost-linear predecessor counting
in one theorem.  This neither constructs the fixed tower nor proves its gain;
the exact `k=12,...,19` certificate vectors are feasible subeigenvectors, not
instances of that fixed-tower hypothesis.

The Round 82 variable-gain and checkpoint consumers are also the right weaker
endpoint interfaces.  In the research convention, where `epsilon_(k,t)` is
indexed from the finest selected profile toward successive coarse minima, the
target is a structurally specified sequence

```text
0 = t_(k,0) < ... < t_(k,m_k),
epsilon_(k,t_(i+1))
  >= epsilon_(k,t_i) + a_(k,i) epsilon_(k,t_i)^2,
a_(k,i) >= 0,
sum_(i<m_k) a_(k,i)/(1+a_(k,i)) -> infinity.
```

This is the reverse of Lean's coarse-to-fine indexing
`e_(k,j)=epsilon_(k,k-j)`.  In particular, the existing executable per-stage
coefficient is

```text
(epsilon_(t+1)-epsilon_t)/epsilon_t^2,
```

not the same displayed quotient read without reindexing.  Every adjacent
coarsening of the exact selected `k=12,...,19` records already has coefficient
at least `3/2`, so ordinary fixed-depth block tables would only repackage known
finite evidence.  The useful theorem would choose checkpoints from renewal or
carry structure independently of the observed defect values and prove the
net inequality all-level.

The axis distinction is essential.  Checkpoints index loss of ternary
precision, while `5 -> 2 -> 8 -> 5` is the spatial orbit of transport inside
one fixed precision.  Coarse projection preserves the branch class, so three
precision steps are not one carry orbit.  The holonomy lane can feed the new
consumer only after a separate theorem aggregates within-level spatial
frustration and turns it into cross-depth gain, perhaps by an amortized
tie-wall/second-gap potential.  We will not describe fixed three-depth blocks
as carry-aligned.

Round 83 also matches the research definitions at the literal boundary.
`ternaryColdMean` is the normalized negative power mean in equation (2.1) of
`docs/notes/softmin-replica.md`; the factor `3^(1/beta)` is exactly (2.2).
Replacing only the refinement-fiber minimum while retaining the nonnegative
transport term gives precisely the rowwise comparison (2.3), not a softened
transport surrogate.  The transfer premise

```text
r*x <= F_beta(x),        3^(1/beta) < r
```

therefore supplies the intended exact hard feasible witness after
normalization.  Allowing arbitrary witness levels is also the correct endpoint
scope.  The surviving research input is fixed-temperature saturation, or
certified positive soft subeigenvectors crossing the displayed factor along
parameters tending to two; Round 83 does not claim either input.

Commits `4419b30` and `eaa2f0d` have now landed and the final 8,784-job audit is
recorded.  The predictive-memory probe is closed as nonproductive, so it
creates no Lean request.  The project is pausing here: there is no outgoing
formalization request.  On a future restart, use `../RESUME.md` and
`../CLEAN_LEAN/CLEAN_LEAN_RESUME.md` before opening a new round.

## 2026-07-21 — Kontorovich reply 1: certificate schema and periodic-word target

I audited commit `4f7a3df` against the worker now in
`experiments/kontorovich/`.  The interfaces match:

- Python indexes `word=[k_0,...,k_(N-1)]` from zero, with every `k_i>0`.
- `total_halvings=S_N=sum k_i`, `accelerated_steps=N`, and
  `ordinary_steps=S_N+N`; the last convention matches Lean's faithful
  unaccelerated odd step followed by `k_i` halvings.
- Python's forward recurrence `A <- 3*A+2^S` and Lean's head-recursive
  `affineOffset` compute the same displayed
  `A_N=sum_j 3^(N-1-j)2^S_j`; the `199` regression agrees.
- The portable JSON stores decimal strings for `seed`, `orbit`, and
  `affine_constant`, but parsing is outside the theorem.  Both verifiers
  recompute all redundant fields.  Closure is first claimed for the fully
  accelerated odd map, then Lean's `step_iterate_ordinaryDuration` transfers
  it to the ordinary map.
- The disproof gate is exactly `seed != 1`.  The valid seed-`1` artifact is a
  regression, never a disproof.

The next high-value theorem is the no-periodic-glider obstruction from
`docs/notes/kontorovich-program-synthesis.md` Section 4.  A generic arithmetic
statement avoids 2-adics.  For a nonempty word `w`, set

```text
P=3^(length w), Q=2^(totalValuation w), A=affineOffset w, D=Q-P.
```

If `WordLegal x (List.replicate m w).flatten` for every `m`, concatenation
and `valuationWord_affine_identity` give

```text
Q^m divides P^m*x+A_m,
A_m=A*sum_(i<m) P^(m-1-i)Q^i,
D*A_m=A*(Q^m-P^m).
```

Therefore `Q^m | P^m*(D*x-A)`.  Since `Coprime P Q`, this implies
`Q^m | D*x-A` for every `m`.  With `Q>=2` (nonempty legal word has positive
valuations), choose `m` so `Q^m>|D*x-A|` and conclude `D*x=A`.  The clean
consumer statement is:

```text
positive x + same nonempty legal word at every block
  -> runWord x w = x.
```

An eventual-periodic corollary applies this to the positive tail.  A sign
corollary then says a supercritical block `Q<P` cannot occur forever on a
positive orbit, since `A>0`; a subcritical periodic itinerary is a cycle.
Please choose the simplest representation of repeated-word legality and
integer subtraction (`Int` may make `D*x-A` cleaner).  This closes only
literal eventually periodic valuation software.  It must not be generalized
to morphic or one-counter gliders.

## Kontorovich request: negative-cycle shadow macro (2026-07-21 19:52 EDT)

The new exact worker `experiments/kontorovich/search_shadow.py` uses negative
cycles only as finite controllers for positive states.  A useful reusable
theorem would be the following shifted-coordinate macro identity.

Let a signed state `c<0` be fixed by a legal nonempty word `w`; put
`P=3^|w|`, `Q=2^sum(w)`, and assume `P>Q`.  For a positive natural state
`x_M=c+Q^M h_M` with odd positive `h_M`, the orbit shadows `M` copies of `w`
until the final valuation.  If that final valuation is the controller value
plus `e_M`, its positive endpoint is exactly

```text
x_(M+1)=(c+P^M h_M)/2^e_M.
```

If this endpoint also has the form `c+Q^(M+1)h_(M+1)`, and `e_M<=E`, then for
all sufficiently large `M` it is strictly larger than `x_M` because
`P^M>2^E Q^M` (the constant term has the favorable sign for `c<0`).  An
infinite exact renewal sequence should therefore instantiate the existing
`MacroGlider` endpoint after a finite checked prefix.  Even just the algebraic
endpoint and eventual-growth lemmas, with legality left as explicit premises,
would give the search a sound formal target.  The bounded Python search found
no renewal; this request is an interface, not a candidate claim.

The phase-changing follow-up has one finite regression worth preserving.  For
the `-5/-7` signed cycle, the positive seed `53403857` follows controller
phases `-7,-5,-7,-7`, counter levels `1,2,3,4`, and collision extras
`2,3,1,1`, with exact macro-states

```text
53403857 -> 15019835 -> 2376185 -> 1691641 -> 1354843.
```

The same canonical seed survives the fourth macro, but `1354843` is congruent
to neither phase modulo `8^5`, so this is explicitly not an infinite witness.
It may be useful as a `native_decide`/example test for the signed shadow
identity; the general theorem should still take an arbitrary phase sequence.

## Kontorovich request: certify the `-1` outward regression (2026-07-21 20:08 EDT)

The signed fixed controller omitted from the first worker is `c=-1`, `w=[1]`.
Please add it to the Boolean signed-controller examples if convenient.  The
new worker's strongest finite outward regression is

```text
seed 24017279
levels 7,8,9
collision extras 4,3,1
macro states 24017279 -> 25647359 -> 82164223 -> 1579334395.
```

The same canonical seed realizes the first two and all three macros, but the
endpoint difference from `-1` is not divisible by `2^10`; exact continuation
reaches `1`.  As with the earlier phase example, this belongs only in the
non-soundness-critical regression module.  The existing
`CertifiedCyclePhaseShadowOrbit` appears to be the right infinite endpoint;
the search currently supplies no inhabitant.

A second finite `-1` regression has a longer canonical-stability run.  With
constant collision extra `e=1` at levels `1,2,3,4`, seed `121` has macro
states

```text
121 -> 91 -> 103 -> 175 -> 445.
```

It is the canonical seed for the depth-two, depth-three, and depth-four
prefixes, but `445+1` is not divisible by `2^5`, so level five fails.  Please
keep this in examples only; it is not an all-level witness.

## Kontorovich packet census regression (2026-07-21 20:51 EDT)

The exact GPU census plus Python replay found a longest bounded chain of seven
renewals.  A compact representative is

```text
seed 30603607965, initial packet h=15301803983, start level 1
extras 2,1,3,2,2,2,1
states 30603607965 -> 11476352987 -> 12910897111 -> 5446784719
       -> 6893586911 -> 13087043903 -> 37267402367 -> 318374253823.
```

The eighth renewal fails, and exact continuation reaches `1`.  This need not
be added to Lean unless it is useful as a recurrence/scheduler regression;
the existing all-level endpoint already has the right shape.

## Kontorovich request: dyadic--triadic packet gate (2026-07-21 21:28 EDT)

Simon's warning that a Collatz instruction may span the whole integer led to
a forward decoder for the existing packet recurrence.  Fix positive `m,e`
and put

```text
M = 2^(m+e+2),
r = least residue modulo M satisfying
    3^m r = 1 - 2^e + 2^(m+e+1)  (mod M),
s = (3^m r + 2^e - 1)/2^(m+e+1).
```

Because `3^m` is odd, `r` exists uniquely modulo `M`; the extra congruence bit
should make both `r` and `s` positive odd.  The useful theorem is the affine
gate equivalence for positive odd packets:

```text
2^e (2^(m+1) h' - 1) = 3^m h - 1
  <-> exists q : Nat,
        h  = r + 2^(m+e+2) q /\
        h' = s + 2*3^m q.
```

The forward direction also proves the literal valuation of `3^m h-1` is
exactly `e`, since `2^(m+1)h'-1` is odd.  The same gate has the triadic
scheduler already present in the module:

```text
2^(m+e+1) h' = 2^e-1  (mod 3^m).
```

Please choose whatever modular-inverse or parameterized-residue formulation
is least painful in Lean; an equivalent theorem assuming the defining range,
congruence, and quotient equation for `r,s` would still be valuable.  The
research-side checker is `experiments/kontorovich/packet_gate.py`; its finite
tests pass, but the universal algebra is the requested seam.  This theorem
would certify one delocalized instruction family, not a closed controller and
not a counterexample.

## Kontorovich request: two-rail splash gate (2026-07-21 22:02 EDT)

Simon's “splash the gap” idea now has a small universal algebraic seam.  For
positive odd payloads `P,Q,P'`, let the input be `-1+2^(r+1)P`.  Assuming

```text
3^(r+1)P - 1 = 2^a(1+2^(2s+2)Q),
1 + 3^(s+1)Q = 2^b(-1+2^L P'),
```

the exact valuation word should be

```text
[1]^r ++ [1+a] ++ [2]^s ++ [2+b]
```

and the endpoint should be `-1+2^L P'`.  A theorem with the two displayed
equalities and positivity/oddness as explicit premises is sufficient; the
research-side modular solver need not be formalized yet.  The smallest
standard regression is

```text
r=4, s=1, a=b=1, L=6,
P=2961, Q=22485, P'=1581,
94751 -> 101183,
valuations [1,1,1,1,2,2,3].
```

The Python worker intersects these complete affine gate families to build 247
outward rounds from a 10,040-digit seed, but the seed changes at the next
depth and reaches `1`.  So the requested theorem certifies a reusable finite
gate only, not an infinite glider or a counterexample.

## Kontorovich request: standard partial-theta unrolling (2026-07-21 22:31 EDT)

Rounds 29--32 have been absorbed; in particular, the affine-loop correction
is now the main worker target.  There is one small optional formal seam left
by `StandardTwoRail.lean`.  From the proved recurrence and exact factor of
three, set `P_r=3U_r` after the first gate.  Then

```text
2^(r+8) U_(r+1) = 3^(r+3) U_r + 23,   r>=5.
```

For every `K>=1`, exact backward unrolling should give

```text
U_5 = -23 * sum_(n=0)^(K-1)
              2^(n(n+25)/2) / 3^((n+1)(n+16)/2)
      + 2^(K(K+25)/2) U_(5+K) / 3^(K(K+15)/2).
```

Any convenient denominator-cleared natural/integer/rational formulation is
useful.  This identifies the unique `Q_2` candidate with

```text
-(23/3^8) * F(2/3, 2^13/3^9),
F(q,z)=sum_(n>=0) q^(n(n-1)/2) z^n.
```

Please do not assert irrationality: Väänänen--Wallisser (1991) studies exactly
this p-adic function, but the full theorem hypotheses have not yet been
recovered and audited.  The research-side finite checker is
`experiments/kontorovich/standard_two_rail_theta.py`; its 247-round artifact
checks the cleared identity and 33,333 bits of 2-adic precision.  Formalizing
the finite identity is lower priority than any progress on affine return-map
circuits.

## Kontorovich correction: fixed affine returns are periodic-word no-gos (2026-07-21 22:37 EDT)

There is an important correction to round 32 and to my 22:31 request.  An
outward `AffineTwoRailLoop` may be a sound conditional disproof endpoint, but
a self-link or one fixed finite return route repeats one fixed nonempty
valuation word forever.  The earlier `repeated_legal_block_fixed` theorem
therefore appears to make every outward instance impossible.

The coefficient obstruction says the same thing directly.  A fixed legal
word with `N>0` odd steps and total valuation `S>0` maps an affine input family
with stride `d` to an output family with stride

```text
d * 3^N / 2^S.
```

If the output is `x(c+m*u)` for the same input family `x(u)=x0+d*u`, then
coefficient equality forces

```text
3^N = 2^S * m,
```

impossible for natural `m`.  In the concrete two-rail solver, input payload
stride has positive 2-adic valuation while output payload stride is exactly
twice an odd power of three; composing a fixed shape cycle gives the same
dyadic denominator.

If convenient, please prove a no-inhabitant theorem for an outward
`AffineTwoRailLoop` (and ideally a fixed finite affine return circuit) by
reusing the periodic-block theorem.  This does not invalidate the conditional
`not_conjecture`; it calibrates the search target.  A successful finite
controller must **branch on the changing tail**, producing a genuinely
aperiodic sequence of gate words, or carry an unbounded shape parameter such
as the standard schedule's increasing `r`.  Searching a single affine
self-return is now deprioritized.

## Kontorovich result: Väänänen--Wallisser closes the standard schedule (2026-07-21 22:47 EDT)

I recovered the open full text of Väänänen--Wallisser (Manuscripta Math. 65,
1989, 199--212):

```text
https://gdz.sub.uni-goettingen.de/download/pdf/
PPN365956996_0065/LOG_0016.pdf
```

Their theorem applies, not merely its abstract.  They use

```text
f_q(x)=sum_(n>=0) q^(-n(n+1)/2) x^n,
f_q(qx)=x f_q(x)+1.
```

Our value maps exactly as

```text
F(2/3,2^13/3^9)=f_(3/2)(2^12/3^8).
```

Set `ell=1`, `sigma=0`, `q=3/2`, `alpha=4096/6561`, and `p=2`.
Nonzero rationality and reduced `q` are immediate; the pairwise-alpha
condition is vacuous.  Their size condition becomes

```text
gamma=1-log(2)/log(3) < (3-sqrt(5))/2=Gamma.
```

The exact separator `3/8` discharges it:

```text
2^8 > 3^5       => gamma < 3/8,
5*4^2 < 9^2     => 3/8 < Gamma.
```

The theorem makes `1` and `f_(3/2)(4096/6561)` linearly independent over
`Q`, hence the latter irrational in `Q_2`.  Combined with commit `806bf8c`,
the normalized positive payload stream cannot exist, so the infinite standard
two-rail schedule is closed.  The exact research-side hypothesis checker is
`experiments/kontorovich/standard_two_rail_irrationality.py`.

If useful, please kernel-check the elementary parameter identity and the two
integer inequalities, and expose a theorem which consumes a hypothesis that
this cited value is irrational to derive `not NormalizedStandardPayloadStream`.
Do not attempt to formalize the external transcendence theorem itself unless
you judge that surprisingly small.

## Kontorovich request: the two-rail LSB prefix decoder (2026-07-21 22:56 EDT)

The branching controller has an exact prefix-code interpretation.  Fix
`r>=1`.  Every positive-parameter gate shape `(s,a,b,L)` with `L>=2` has input
payload family

```text
P = P0 mod 2^E,   E=a+b+2s+L+3,
```

among odd `P`.  These are LSB-first binary codewords.  They should be pairwise
prefix-free because the literal state uniquely recovers the parameters:

```text
a    = v2(3^(r+1)P-1),
2s+2 = v2((3^(r+1)P-1)/2^a - 1),
b    = v2(1+3^(s+1)Q),
L    = v2((1+3^(s+1)Q)/2^b + 1).
```

Thus the changing unbounded payload, rather than an autonomous phase, selects
the next word.  The exact Kraft mass among odd 2-adic payloads is

```text
sum_(a,b>=1,s>=0,L>=2) 2^(-(E-1)) = 1/6.
```

The new worker `experiments/kontorovich/two_rail_prefix_code.py` independently
decodes every base member, checks all 902,496 codeword pairs per rail length
through `E<=20`, and obtains bounded mass `5433/32768 < 1/6` for each
`r=1..16`.  The universal claims requested, if useful, are uniqueness of the
decoded `(s,a,b,L)` from two exact gates with the same `r,P`, hence dyadic-
cylinder disjointness/prefix-freeness.  Formalizing the infinite geometric sum
is optional; the more important interface is a payload-dependent decoder that
can emit a genuinely aperiodic `MacroGlider.word` stream.

## Kontorovich request: exact saturated-map compiler bridge (2026-07-21 23:04 EDT)

The prefix transducer contains a literal block of Eliahou--Verger-Gaugry's
divergent saturated-word map

```text
U(n)=(3n+1)/2 if n odd,  (3n+2)/2 if n even.
```

Take the source gate shape `(r,s,a,b,L)=(5,0,2,1,2)` and target shape
`(1,0,2,1,2)`.  Their complete affine link is

```text
source family index z =   95 +  128*t,
target family index w = 1640 + 2187*t.
```

On this seven-bit address, the `U` digits are `[1,1,1,1,1,2,1]`, and exact
iteration gives the universal identity

```text
U^7(95+128*t)=1640+2187*t.                    (U7)
```

Thus one outward Collatz splash gate compiles seven append-`1/2` operations in
rational base `3/2` on its unbounded nonlocal family index.  The saturated
orbit itself enters at

```text
U^41(0)=26906975=95 mod 128,
U^48(0)=459730910,
440843894591 -> 470764451891
```

through this gate.  The linked target gate then shrinks and its endpoint does
not decode another two-rail renewal; the ordinary source reaches `1`.  This is
one compiler primitive, not a glider.

The worker is `experiments/kontorovich/two_rail_u_bridge.py`.  In a bounded
shape audit it checks 67,500 coefficient-compatible links, finds three exact
`U^D` links with `R=D`, and only the displayed source family is outward.  If
useful, please instantiate the two affine families/link and prove (U7) for all
`t`; their composition would kernel-check the first exact bridge from the
published rational-base program into the Collatz splash ISA.  The next
research target is a payload-dependent sequence of such blocks, not repetition
of this fixed edge.

## Kontorovich request: parity-complete splash ISA (2026-07-21 23:22 EDT)

Simon's “splash the gap” suggestion found a genuine missing branch in the
current `TwoRailGate` grammar.  The present type encodes only an even
intermediate `+1`-rail gap `2s+2`.  If that gap is odd, `2s+1`, the cleanup
wire instead ends at

```text
X = 1 + 2*3^s*Q.
```

Its next accelerated step has valuation exactly one and

```text
T(X) = 2+3^(s+1)Q = -1+2^L P'                 (OddCatch)
```

whenever `3(1+3^s Q)=2^L P'`.  Here `Q,P'` are positive odd and `L>=1`.
The case `L=1` is a legal zero-delay `-1` rail: it has no valuation-one wire
ticks before its next collision, so the complete decoder needs rail length
`r>=0` rather than the current strict `ampTicks_pos` interface.

With positive first/second collision extras, the two complete affine cylinder
families have input strides

```text
even cleanup: 2^(a+b+2s+L+3),
odd catcher:  2^(a+2s+L+2),
```

and the same output stride `2*3^(r+s+2)`.  Their Kraft masses among odd
2-adic payloads, now with `L>=1`, are exactly

```text
even = 1/3,   odd = 2/3,   total = 1.
```

More importantly, there is a direct total-decoder theorem.  For every
`r>=0` and positive odd `P`, put

```text
A = 3^(r+1)P-1,
a = v2(A),
Y = A/2^a.
```

If `Y=1`, the macro reaches `1`.  Otherwise `G=v2(Y-1)>=1`; even `G`
uniquely gives the existing cleanup branch and odd `G` uniquely gives
`OddCatch`.  The terminal odd state has a unique `L=v2(endpoint+1)>=1`.
Thus every payload either halts explicitly or decodes one unique parity
splash.  The exact worker and artifact are
`experiments/kontorovich/complete_splash_isa.py` and
`complete_splash_isa_audit.json`.

If useful, please formalize (in a new generalized type, without weakening the
existing stable API):

1. the all-payload `OddCatch` legality/endpoint theorem;
2. its complete affine cylinder and input/output strides;
3. the parity-split total decoder, including `r=0,L=1` and the explicit
   `Y=1` halt alternative;
4. optionally the two geometric Kraft sums—the total-decoder theorem is the
   higher-value endpoint.

The artifact also contains a new compiler witness:

```text
U^12(1023+4096t)=132860+531441t,
source (10,0,4,2,11), target (10,2,1,3,2).
```

Both source and target families are universally outward.  On the saturated
orbit's time-622 member, the next formerly rejected payload decodes as the
odd catcher `(r,s,a,L)=(1,0,3,6)`; it shrinks.  The full ordinary seed reaches
`1`, so this is a finite two-outward-gate example, not a bridge chain.

## Kontorovich request: the first odd saturated bridge (2026-07-21 23:32 EDT)

The new bounded complete-ISA graph search found a very small bridge which may
be the cleanest test of the generalized odd-family/compiler interface:

```text
source OddCatcher shape (r,s,a,L)=(1,0,1,1),
target OddCatcher shape (r,s,a,L)=(0,0,1,1),
source family index z = 7+8*t,
target family index w = 26+27*t,
U^3(7+8*t)=26+27*t.
```

Both selected gate families are universally outward.  The `U` digit word is
`[1,1,1]`.  This should now be a compact consumer of round 48's odd prefix
families and rounds 44--46's saturated-cylinder logic, except that the latter
currently names `AffineTwoRailFamily`.  If the emerging complete-splash sum
type supports a generalized affine link, please instantiate this odd-to-odd
edge and prove its source and target outwardness.  It is only one edge: the
target's complete coefficient-compatible list has no outgoing saturated
bridge, so do not package it as an infinite chain.

The exact worker is
`experiments/kontorovich/complete_u_bridge_graph.py`.  Its source box is

```text
r=0..15, s=0..4, a=1..4,
b=1..4 on even sources, L=1..16, both branches.
```

It checks all 25,600 sources and 2,751,680 compatible links, finding 18 exact
saturated bridges (14 odd-source, four even-source); 11 have outward targets.
For those 11 distinct targets it exhausts the complete 718-candidate
second-edge lists and finds zero renewal.  This is bounded at the first source
but complete for the immediate continuation of each hit.

There is also a universal three-gate Collatz subcylinder of the `U^12` edge.
Restrict its original tail to `t=16u`; then

```text
source index  = 1023+65536u,
target index  = 132860+8503056u,
catcher index = 39716626454+3^26*u,
```

and the target endpoint decodes as odd catcher `(r,s,a,L)=(1,0,1,2)`.
All three gates are outward for every `u`.  At `u=0`:

```text
2199021754367 -> 2229023590399
              -> 5083728186203
              -> 8578791314219.
```

The seed reaches `1`; this is a useful finite generalized-link regression,
not a requested all-level theorem unless it falls out cheaply from the new
interface.

## Kontorovich request: universal outward splash router (2026-07-21 23:50 EDT)

Round 51's odd compiler edge and round 52's deterministic ISA reveal a simple
all-parameter routing theorem.  For arbitrary `r>=0,L>=1`, consider an odd
catcher with

```text
cleanTicks=0, toPlusExtra=1, outputGap=L.
```

Its word is

```text
[1]^r ++ [2,1],
```

so it has `N=r+2` odd steps and `S=r+3` total halvings.  Since

```text
3^(r+2)>2^(r+3)
```

for every `r` (base `9>8`, then multiply by `3>2`), every legal member is
outward: the positive affine offset only strengthens the leading-multiplier
inequality.  The output gap `L` is arbitrary, so this family routes any
incoming rail length to any desired next rail length.

If convenient, please prove a theorem of the form

```text
OddCatcherGate.cleanTicks=0 ->
OddCatcherGate.toPlusExtra=1 ->
gate.start < gate.endpoint
```

without enumerating `r,L`.  A canonical base-gate constructor for every
`r,L` would be stronger and would match the worker's complete affine family,
but the universal outward lemma is the key seam.

The research-side consequence is now exact.  Among the 11 two-outward
saturated nodes in `complete_u_bridge_graph_audit.json`, one ordinary relay
produces 22 transitions but only a fixed periodic self-loop.  With the router
inserted between two ordinary affine links, every ordered pair compiles:

```text
A --saturated--> B --ordinary--> R_(r,L)
  --ordinary--> C --saturated--> D.
```

`complete_u_router.py` constructs and literally replays all `11^2=121`
five-gate affine families; every gate is outward.  The least node-0-to-node-0
member is

```text
71675 -> 120953 -> 136073 -> 153083 -> 258329 -> 290621.
```

This proves complete *finite* control flow in the current compiler alphabet,
not an infinite ordinary program.  An infinite aperiodic node word still
selects nested dyadic cylinders whose limit need not be a natural.  Round
52's `InfiniteCompleteSplashProgram` is therefore exactly the right endpoint:
the next research object must be a public `(railLength,payload)` recurrence,
not another proof-carrying gate type.

## Kontorovich request: autonomous router recurrence (2026-07-22 00:08 EDT)

Commit `fedb5ca` closes the universal-growth request.  Eliminating the
exogenous node schedule exposes a smaller public recurrence.  If consecutive
router gates have amplifier lengths `r,r'`, input/output payloads `P,P'`, and
the first gate's output gap is `r'+1`, its two balance equations imply

```text
2^(r'+3) * P' = 3^(r+2) * P + 3.                 (R)
```

Conversely, for natural `r,r'` and positive odd `P,P'`, (R) should construct
the exact router gate `(r,0,1,r'+1)`: it forces
`v_2(3^(r+1)P+1)=r'+3`, and

```text
Q = (3^(r+1)P-3)/4
```

is positive odd and satisfies both gate balances.  Could you package this as
a proof-carrying `RouterPayloadStep` or an equivalent theorem, with exact
linkage to `CompleteSplashState.next`?  The desired all-level seam is:

```text
r P : Nat -> Nat
positive/odd payloads
forall n, 2^(r(n+1)+3)*P(n+1)=3^(r(n)+2)*P(n)+3
initial sparse state > 4
--------------------------------------------------
not Collatz.Conjecture
```

`fedb5ca` supplies outwardness, so the recurrence should discharge both
canonical decoding and linkage rather than ask for another outwardness field.
It is not merely an externally prescribed dyadic address sequence: each next
gap is certified by the current ordinary payload equation.

There is also a useful autonomous normal form.  (R) forces `3 | P'`; after the
first step write `P_n=3H_(n-1)`.  Then

```text
A = 3^(r_n+2) H_(n-1) + 1,
r_(n+1) = v_2(A)-3,
H_n = A / 2^v_2(A),                    provided v_2(A)>=3.
```

Formalizing the recurrence-to-gate direction is the priority; the valuation
normal form is optional if `padicValNat` bookkeeping would slow the seam.

## Kontorovich follow-up: one-register radix swap (2026-07-22 00:18 EDT)

Commit `e9f791b` completely answers the priority request.  The recurrence has
an exact one-register quotient which may be a useful next theorem, but it is
secondary to the endpoint already proved.

For every recurrence output, (R) modulo three gives `3 | P'`.  Past the first
step put `P_n=3H_n` and

```text
y_n = 3^(r_n+2) H_n.
```

Then

```text
2^(r_(n+1)+3) H_(n+1) = y_n+1,
e_n := v_2(y_n+1) = r_(n+1)+3,
y_(n+1) = 3^(e_n-1) * (y_n+1)/2^e_n.           (F)
```

Moreover `3 ∤ H_(n+1)` because `y_n+1=1 (mod 3)`, so
`v_3(y_(n+1))=e_n-1` and `r_(n+1)` is recoverable from `y_(n+1)`.
The natural domain is

```text
9 | y,       y % 8 = 7.
```

It gives `e>=3`; (F) remains divisible by nine and is strictly larger than
`y` since `3^(e-1)/2^e >= 9/8`.  Survival is exactly the additional condition
`F(y)%8=7`.

If inexpensive, please package either:

1. the divisibility/core recurrence theorems `3|P'` and the equation for
   `H,H'`; or
2. a `RouterRadixOrbit` using proof-carrying exponents/factorizations rather
   than fighting executable `v_2`, with a conversion to
   `InfiniteRouterPayloadRecurrence`.

There is also a clean word-level check: `router_word_eq` expands under the
shortcut map to `1^(r+1) ++ [0,1]`; concatenated streams avoid `00` and `010`.
This identifies the pure-router counterexample class with a sparse
finite-type parity language.  It does not conflict with the autonomous
finite-state no-go: a finite automaton accepts many aperiodic words, while a
payload-independent finite-state generator emits only an eventually periodic
one.

## Kontorovich follow-up: minimal break-off counter (2026-07-22 00:22 EDT)

Commit `c10e5b5` proves exactly the requested valuation normal form.  A final
change of coordinate makes the search object unusually small.  Put

```text
y = 8k-1.
```

Then `9|y` is equivalent to `k=8 (mod 9)`.  Factor

```text
k = 2^j u,         u odd.
```

The radix swap is legal precisely when

```text
8 k' = 3^(j+2) u + 1.                            (B)
```

When (B) holds, three useful facts are elementary:

1. `k'=8 (mod 9)` automatically, because `j+2>=2` and
   `8k'=1 (mod 9)`;
2. `k'>k`, by the already-proved inequality
   `3^(j+2)>2^(j+3)`;
3. with `y'=8k'-1`, one has `y'=3^(j+2)u`, so the next router registers are
   exactly `r'=j,H'=u`.

Conversely, for current `k=8 (mod 9)`, factor
`8k-1=3^(r+2)H` with `3∤H`; set `P=3H`.  Then (B) is exactly

```text
2^(j+3) * (3u) = 3^(r+2) * (3H) + 3,
```

the public router recurrence from `e9f791b`.

If cheap, please expose a proof-carrying `BreakoffCounterOrbit` with sequences
`k,j,u,r,H` and these two exact factorizations, then compile it to
`InfiniteRouterPayloadRecurrence`.  The executable one-register presentation

```text
B(k) = (3^(v_2(k)+2) * oddPart(k) + 1)/8
```

is the research target, but the formal structure need not fight valuations:
the factorization witnesses are acceptable.  The theorem should say that any
infinite positive orbit of (B), starting in `k=8 (mod 9)`, refutes Collatz.
No such orbit is currently supplied.

## Kontorovich follow-up: regenerative three-bit delay gate (2026-07-22 00:40 EDT)

Commits `a1a5fd0` and `7293975` exactly close periodic opcode programs and
the executable-map seam.  Simon's spatial “splash the gap” idea has now
produced a universal finite instruction inside the break-off map.  For
naturals `q>=1`, `q'>=1`, `j>=0`, start from

```text
k = 9 * 2^(3*q) * c - 1.
```

The opcode-zero branch has the exact delay identity

```text
B(9*2^(3*q)*c-1) = 9*2^(3*(q-1))*(9*c)-1.
```

After `q` such steps the collision is `3^(2*q+2)c-1`.  Supply odd `u,c'`
with

```text
3^(2*q+2)c - 1 = 2^j u,
3^j u + 1 = 2^(3*(q'+1)) c'.
```

Then one more break-off instruction lands exactly at

```text
k' = 9*2^(3*q')c' - 1.
```

Eliminating `u` gives the compact balance

```text
2^(j+3*q'+3)c' = 3^(j+2*q+2)c + 2^j - 3^j.
```

The Python checker `experiments/kontorovich/breakoff_delay_gate.py` constructs
the unique residue of `c modulo 2^(j+3*q'+4)` that makes the two valuations
exact; its bounded audit passes 8,704 literal macro replays.

If this fits the current executable-breakoff work cheaply, please formalize a
proof-carrying `BreakoffDelayGate` (the two displayed factorizations are fine)
and prove the `q`-tick delay identity plus the collision-to-clean-delay
endpoint.  A universal existence theorem for the residue class is optional;
the most useful seam is that supplied exact factorizations compile into a
finite `BreakoffCounterOrbit` segment.  This is deliberately not an infinite
orbit claim—the open problem is linking the outgoing `c'` into the next input
cylinder along a genuinely aperiodic sequence.

## Kontorovich follow-up: native mixed-radix tail instruction (2026-07-22 00:58 EDT)

Commit `eac55d3` fully answers the regenerative-gate request; thank you.  The
next research-side calculation explains why this is a programming primitive,
but does not yet justify the variable-length infinite-chain flattening seam.

For two gates with matching boundary delay, write the first output and second
input coefficient families as

```text
c_out = o + 2*3^A*t,
c_in  = r + 2^(m+1)*s.
```

When the second collision opcode is positive, `o,r` are both odd.  Therefore
linkage reduces to

```text
3^A*t = (r-o)/2 (mod 2^m),
```

which always has a unique `t_0 mod 2^m`.  After the least nonnegative lift,
the whole link family is

```text
t=t_0+2^m*v,
s=s_0+3^A*v,        0<=s_0<3^A.
```

Thus one splash reads/deletes a low binary address and appends an `A`-trit
word.  The exact worker now audits 4,608 bounded link shapes and, for the
fixed first gate `(q,j,q')=(1,1,1)` (`A=5`), finds within next-opcode bound 34
and next-delay bound 44 an exact address for every one of the 243 five-trit
words.

No Lean action is urgent here: a supplied-tail-equation `BreakoffDelayLink`
would be cheap but adds little beyond `BreakoffDelayGate.run`, while universal
existence needs modular-inverse bookkeeping.  The higher-value future seam is
the variable-length infinite-chain flattener you identified, once the
research side has an actual returning dispatcher or symbolic all-level gate
chain.  For now the honest open target is exactly that returning aperiodic
program, not more finite routing.

## Kontorovich follow-up: affine seam received (2026-07-22 01:03 EDT)

Commits `1711620`, `54e506f`, and `5254194` are incorporated into the research
map.  In particular, `no_ordinary_tail_of_addresses_change` changes the PL
design constraint in a useful way: the program cannot obtain its infinite
control stream by asking for fresh low bits of one fixed initial tail forever.
A viable dispatcher must eventually stabilize that initial address and then
generate its aperiodic control from payload state transformed by the hardware.

No further formalization request yet.  I am treating exact blocks of simple
divergent base-`3/2` writers as possible payload generators and will return
only if a linked all-level architecture survives the symbolic kill tests.

## Kontorovich follow-up: canonical base graph and direct-push no-go (2026-07-22 01:22 EDT)

The exact worker `search_delay_base_graph.py` now exhausts all 1,010,000
delay shapes `q,q'=1..100,j=0..100` under the strongest ordinary-address
specialization: the source uses affine tail zero and its output must equal the
next family's tail-zero coefficient.  There are ten raw hits, but seven have
`8|c` and merely hide another complete delay cell.  Of the three normalized
links, none has a second base edge.  This is bounded Python evidence and does
not need a Lean enumeration.

Two very small universal lemmas would sharpen the PL failure boundary if they
are cheap:

1. **Delay normalization.**  With `BreakoffDelayGate.start` notation, prove
   the arithmetic reassociation

   ```text
   9*2^(3*q)*(8*d)-1 = 9*2^(3*(q+1))*d-1.
   ```

   This formally identifies the factor-of-eight hits as coordinate aliases,
   not distinct spatial programs.

2. **A direct affine link is not a binary push.**  The worker's link has

   ```text
   firstTail(v)=a+2^m*v,
   secondTail(v)=b+3^A*v,       A>0.
   ```

   Please prove `3^A != 2^p` for every `p` when `A>0` (parity handles `p>0`,
   size handles `p=0`), and preferably the wrapper that `secondTail` cannot
   equal `b'+2^p*v` for every `v`.  The same coefficient obstruction applies
   to any fixed finite composition because its write exponent is a positive
   sum.

This no-go is intentionally narrow.  It says the current one-residual-tail
affine encoding cannot directly implement Cocke--Minsky's binary stack push.
It does not exclude a payload-dependent branch sequence, a nonlinear pairing
of two packet registers, or a collision turnaround that changes the encoding.

## Kontorovich follow-up: nonlocal sacrificial gap amplifier (2026-07-22 01:43 EDT)

Simon's suggested collision cleanup now has a small positive algebraic core.
For the complete five-trit dispatcher, the link stride is `3^5`.  For
`1<=L<=7`, choose its certified word `b=3^5-2^L` and residual
`v=K*2^L-1`.  Then

```text
b+3^5*v = 2^L*(3^5*K-1).
```

If additionally

```text
3^5*K-1 = 2^D*H,
```

the output tail is exactly `2^(L+D)*H`.  The Python artifact constructs the
unique odd `K (mod 2^(D+1))` making `H` odd and replays the seven concrete
writer links for `D=1..32`.

Please formalize only the cheap universal factorization seam, preferably over
`Nat` in the shape most reusable with `AffineBreakoffDelayLink`:

1. under `2^L <= 3^A`, prove
   `(3^A-2^L)+3^A*(K*2^L-1)=2^L*(3^A*K-1)` with the natural-subtraction
   positivity assumptions made explicit; and
2. if `3^A*K-1=2^D*H`, rewrite the same output as `2^(L+D)*H`.

An `Int` identity plus a clean nonnegative specialization is also fine.  No
valuation library is required, and I am not asking Lean to prove the bounded
writer lookup or an infinite controller.  The remaining research seam is to
expose this internal tail factor as a later public delay and return its odd
part to another Mersenne packet.

## Kontorovich follow-up: regenerative finite ether (2026-07-22 02:05 EDT)

A concrete finite delay medium now survives the symbolic kill tests.  Let
`E=(1,2,1)`.  Its actual self-link from `breakoff_delay_gate.py` is

```text
t=20+256*v,
t'=57+729*v.
```

Please prove the cheap universal invariant

```text
256*(473*t'+12)=729*(473*t+12).
```

This makes `v_2(473*t+12)=8*n` an exact `n`-cell ether counter without asking
Lean to develop a valuation API: a factorization
`473*t+12=2^(8*n)*h` can simply be rewritten once per self-link.

There is also a real defect return using `H=(1,136,1)`.  The two certified
links `E -> H -> E` meet with

```text
v=177+256*u,
w=504+729*u.
```

Writing the returned `E` tail as `t=C+S*u` and substituting `u=256*K-1`, the
worker computes fixed odd `r,A` with

```text
473*t+12=256*(r+A*K).
```

The huge concrete constants are recorded in
`breakoff_ether_defect_audit.json`; they need not be hard-coded if a generic
lemma is cleaner.  The useful theorem shape is:

1. from `t=C+S*(256*K-1)` and `473*(C-S)+12=256*r`, prove
   `473*t+12=256*(r+473*S*K)`; and
2. if `r+473*S*K=2^D*h`, conclude
   `473*t+12=2^(D+8)*h`.

The artifact instantiates this for `D=8*n-8` and replays `n=2..32`, but Lean
should prove only the universal identities.  No chain flattener is requested:
the open research seam is a symbolic map from the exposed ether boundary into
a new defect input with larger `n`, not the already-certified finite runs.

## Kontorovich follow-up: returning ether glider ISA (2026-07-22 02:16 EDT)

The exposed boundary now returns.  The `j=136` defect is universally ruled
out as a receiver because its `E`-tail address is even and an exactly exhausted
ether boundary is odd.  The compatible defect is `H=(1,1,1)`, with actual
links

```text
E -> H:  67+128*v -> 381+729*v,
H -> E: 151+256*w -> 144+243*w.
```

They meet for

```text
v=170+256*u,       w=485+729*u.
```

At `u=32*K-1`, direct arithmetic gives

```text
t=5668704*K-59148,
473*t+12=32*(83790531*K-874281).
```

After selecting exact ether depth `8*n` and solving the exposed boundary
address, the worker obtains for every `n>=1` the complete returning macro

```text
K=R_n+2^(8*n+15)*q -> K'=S_n+3^(6*n+11)*q.
```

It starts at an `E` state ready for `H`, executes the two defect links and
`n` ether self-links, and ends at the next `E` state ready for `H`.  Python
replays `n=1..32`, two tails each.  The exhausted-tail staircase `n -> n+1`
fails at its next link for `n=1..128`, but nonzero macro tails remain open.

This is now enough to justify the variable-length flattener you offered in
round 62, if it remains cheap.  The useful kernel endpoint is deliberately
conditional:

1. package a finite returning block as a `breakoffRun` from one public
   break-off state to the next, with positive length and strict growth;
2. flatten any infinite sequence of such linked positive-length blocks into
   an `ExecutableBreakoffOrbit`; and
3. conclude `not_collatz_of_executable_breakoff_orbit`.

Please do **not** formalize the modular-inverse construction of `R_n,S_n` or
the bounded staircase table yet.  In addition to the generic flattener, the
cheap arithmetic lemmas worth keeping are the concrete identities above and
the ether invariant from the previous request.  This creates a small trusted
target for a future Python-generated all-level macro recurrence without
claiming that one exists now.

## Kontorovich follow-up: autonomous ether counter (2026-07-22 02:26 EDT)

The full returning macro now has a public one-register normal form.  Set

```text
Y=83790531*K-874281.
```

For length `n>=1`, write `Y=2^(8*n-5)*h`, with `h` odd, and assume

```text
3^(6*n+11)*h+51 = 2^20*Y'.
```

Then `Y'` is exactly the transformed register of the returning macro.  The
large-constant cancellation is the literal integer identity

```text
2^20*(-874281)-3^11*(-5175081)=51.
```

The Python CRT constructor proves coefficientwise, for `n=1..128`, that this
branch is identical to

```text
K=R_n+2^(8*n+15)*q -> K'=S_n+3^(6*n+11)*q.
```

Please keep the Lean target small:

1. prove the displayed constant identity by normalization;
2. package the generic algebra saying that the old boundary quotient and
   `Y=83790531*K-874281` imply
   `Y'=(3^(6*n+11)*h+51)/2^20`; and
3. after the variable-block flattener, expose a conditional endpoint: an
   infinite successful orbit of the public `Y` map, together with the packet
   invariant, gives `not Collatz`.

There is no request to formalize CRT existence, the 128-branch table, or an
infinite orbit.  The important research fact is that future candidates can be
stated as one explicit natural-register recurrence with no hidden gate list.

## Kontorovich follow-up: three-bit-capped super-ether (2026-07-22 02:47 EDT)

Simon's "splash the gap" overhang closes the defect at a second scale.  The
one-cell glider is a 23-bit background macro; the two-cell glider is its
defect.  A fully exhausted background has the wrong parity, but retaining
exactly three bits makes the boundary `9 mod 16`, the next defect input.

After removing a common `3^7`, the public second-scale register is

```text
V=-8744697538656344367967+671265207750760396088265*K.
```

Its returning branch is

```text
V=2^(23*N+3)*g,
V'=(3^(17*N+40)*g-17)/2^51.
```

The cheap normalization identity is

```text
2^54*(-8744697538656344367967)
 -3^33*(50679661+120751555*(-234676942119623))
=-2^3*17.
```

Please treat this as lower priority than the variable-block flattener.  If it
is cheap after that work, prove the displayed integer identity and the small
mod-16 phase calculation (`8`, `G=3`, `C=13`, boundary `q=9`).  Do not
formalize the 64-branch artifact or claim an infinite hierarchy.  The useful
conditional endpoint remains: any infinite successful orbit of the public
register macro, compiled to linked positive blocks, refutes Collatz.

## Kontorovich follow-up: finite renormalization pattern (2026-07-22 03:00 EDT)

The capped construction has now passed exact arithmetic through six finite
levels, with collision signs `+,-,+,-,+,-` and binary cell widths
`8,23,77,254,839,2771`.  This is not yet an induction theorem.  The generic
algebraic shape is nevertheless small: a parent register

```text
V=2^(a*n+b)*g,
V'=(3^(c*n+d)*g+s*17)/2^e
```

uses branch one as background, branch two as defect, retains `a+b` boundary
bits, and—when the phase identity holds—normalizes to the same shape with
sign `-s`.

The exact worker now shows the intended generic parameters: branch `j` may be
the background and adjacent branch `j+1` the defect, with retained cap
`a*j+b`.  The level-one artifact checks `j=1..64` and three nonconstant
four-step choice words.  If you package the conditional algebra lemma, please
take `j` as a parameter rather than hard-coding one; the phase and normalized
numerator remain supplied hypotheses.

Please do not interrupt the variable-block flattener for this.  After it, the
useful theorem would be a parameterized *conditional* algebra lemma: supplied
affine B/H link identities, a supplied cap-phase equality, and a supplied
normalized numerator `=-s*17` imply the child public-register formula.  The
large six-level coefficients and the claim that the hypotheses persist at
all levels should remain outside Lean for now.

## Kontorovich follow-up: invariant unit slice (2026-07-22 03:33 EDT)

There is one very cheap generic lemma if useful after the flattener.  From

```text
V = 2^x*(17*h),
V' = (3^y*(17*h)+s*17)/2^e
```

and an exact division hypothesis, factor `17` to obtain

```text
V/17 = 2^x*h,
V'/17 = (3^y*h+s)/2^e.
```

The worker checks the associated packet residue and affine coefficients
through six levels.  Please formalize only the generic factor/cancellation
identity if essentially free; the branch table and existence of an infinite
unit orbit remain outside Lean.

## Kontorovich follow-up: infinite nesting is 2-adic only (2026-07-22 03:41 EDT)

There is a second cheap generic lemma, after the variable-block flattener.
For one adjacent-defect renormalization put

```text
E = E_B+E_H,
X = q_raw-2^E,
I = E+r,
q = X+2^I*K,
```

with `q_raw>0`, `r>=0`, and positive child packet `K`.  Exact rearrangement
gives

```text
q=q_raw+2^E*(2^r*K-1)>0.
```

If convenient, state the rearrangement over `Int` and the positivity corollary
over `Nat`, so truncated natural subtraction does not obscure the identity.
The semantic consequence is that every recursive child extension enters its
parent at a strictly positive tail, hence differs from the canonical tail-zero
parent packet.  Combined with the existing ordinary-tail theorem, canonical
addresses from an infinite adjacent-defect nesting cannot describe one natural
program.

Please keep this behind the flattener in priority.  It is a no-go only for
adding infinitely many hierarchy levels.  It does not exclude an autonomous
infinite orbit of the `+/-1` unit register at any fixed finite level.

## Kontorovich follow-up: signed radix-swap normal form (2026-07-22 04:07 EDT)

The fixed-level unit law has a cheap generic restatement.  From

```text
H=2^(a*n+b)*h,
H'=(3^(c*n+d)*h+s)/2^e,
```

put `p=a*n+b+e`, `q=c*n+d`, `W=2^e*H`, and `W'=2^e*H'`.  Then

```text
W=2^p*h,
W'=3^q*h+s.
```

For centered values `y=W-s`, `y'=W'-s`, the signed-router comparison is

```text
3^(p-1)*(y+s)/2^p = 3^(p-1-q)*y'
```

whenever `q<p`.  The worker checks this on 768 members and checks that `h` is
coprime to six, so the binary and ternary exponents are exact.  At the six
finite hierarchy levels, `p-1-q` is respectively

```text
2*n+3, 6*n+13, 20*n+45, 66*n+151, 218*n+501, 720*n+1657.
```

If essentially free after the flattener, please package only the generic
algebraic identity and exact-valuation corollary from supplied coprimality.
The research interpretation is that a second rail must bank the missing
factor `3^(p-1-q)`; there is no request to formalize such a rail or claim that
the trim is an executable Collatz step.

## Kontorovich follow-up: constant-rate unit clocks are irrational (2026-07-22 04:29 EDT)

Every arithmetic schedule `n_t=n0+k*t`, with fixed natural `k>=1`, is now
closed by the same external Väänänen--Wallisser theorem as the standard
two-rail schedule.  For

```text
p(n)=a*n+b+e,   q(n)=c*n+d,
2^(p(n_(t+1)))*h_(t+1)=3^(q(n_t))*h_t+s,
```

finite backward unrolling gives the unique `Q_2` candidate

```text
h0=-s/3^(q(n0)) *
   F(2^(a*k)/3^(c*k), 2^(p(n0+k))/3^(q(n0+k))).
```

The generic coefficient conversion is

```text
F(2^(a*k)/3^(c*k),z)
  =f_(3^(c*k)/2^(a*k))((3^(c*k)/2^(a*k))*z),
alpha=(3^(c*k)/2^(a*k))*z=2^(p(n0))/3^(q(n0)).
```

For all six finite parameter rows, exact arithmetic has `3^c>2^a>1` and
`3*a>=4*c`.  Taking `k`th powers preserves the first inequalities, while `k`
cancels from the logarithmic ratio.  Together with `2^8>3^5` and `45<64`,
this gives

```text
gamma=1-a*log(2)/(c*log(3))
     <1/6<(3-sqrt(5))/2.
```

Thus the 1989 theorem at `ell=1`, `sigma=0`, `p=2`, and theorem parameter
`q=3^(c*k)/2^(a*k)` makes `f_q(alpha)` irrational for every `n0>=1,k>=1`;
the nonzero rational scale cannot be a natural core.  The Python artifact
checks the generalized coefficient law and hypotheses.  Its six finite
eight-transition linked branch replays remain explicitly a `k=1` regression;
it does not reprove the external theorem.

This is lower priority than the flattener.  If the earlier standard-theta
machinery makes it cheap, please package the generic finite unrolling with a
positive natural parameter `k`, the coefficient conversion, exact size
inequalities, and the implication from a supplied Väänänen--Wallisser
irrationality premise to no natural unit stream.  There is no request to
encode all six huge finite parameter rows.

## Kontorovich request: two-layer unit gap splash (2026-07-22 04:49 EDT)

Simon's “other bits eat the bad parts and regenerate the gap” suggestion now
has a small generic algebraic seam.  Let `P` be odd, let `p,L,D` be positive,
and suppose integers `s,A,B,C,z,B2` satisfy

```text
P*A+s=2^p*C+2^(p+L)*B,
B+P*z=2^D*B2.
```

Then for every natural or integer tail `u`, direct ring arithmetic gives

```text
P*(A+2^(p+L)*(z+2^D*u))+s
  =2^p*(C+2^(L+D)*(B2+P*u)).
```

Useful cheap corollaries are:

- if `C` is odd, the right core is odd and the first valuation is exactly
  `p`;
- modulo `2^L` the right core is `C`;
- its bits in positions `L,...,L+D-1` are zero;
- the residual tail is the affine map `u -> B2+P*u`.

In the research construction, `P=3^q`.  `C` is chosen modulo
`2^(p_next+1)` so that `v2(3^q_next*C+s)=p_next`; `A` and `z` then exist
uniquely by odd modular inversion.  Restricting `u` once modulo the odd
register stride produces genuine linked unit branches.  The worker and exact
artifact are
`experiments/kontorovich/unit_gap_regenerator.py` and
`unit_gap_regenerator_audit.json`.

If essentially free after the current flattener, please package only the
generic displayed identity, parity/exact-valuation consequence, and gap
congruence.  There is no request to formalize the six large register rows or
to infer an infinite orbit.  The live research problem is no longer existence
of a finite splash: it is whether the affine residual packet can generate its
own future sacrificial words instead of consuming an infinite 2-adic stack.

## Kontorovich request: formula repetend splash (2026-07-22 05:05 EDT)

The generic splash has a very small formula specialization.  For naturals
`q,T,D,C,K`, sign `s`, and integer/natural `R`, assume

```text
3^q*R+s=2^T*C.
```

Then ring arithmetic gives

```text
3^q*(R+2^(T+D)*K)+s
  =2^T*(C+2^D*3^q*K).
```

If `C` is odd, the valuation on the left is exactly `T`; the output core is
`C mod 2^D` in the evident shifted sense and has `D` cleared positions before
the remote packet.  In research we construct

```text
R=(2^T*C-s)/3^q
```

from the divisibility premise `2^T*C=s (mod 3^q)`.  We then intersect `T` with
the affine target schedule `T=a*n'+B`.  Concrete modular certificates do this
at all six finite unit levels; the first is already
`q=17,C=5,T=105734623,n'=13216826`.  Higher `T` values have up to 3,235
decimal digits, so the worker verifies them without expanding `2^T`:
`experiments/kontorovich/unit_repetend_splash.py` and
`unit_repetend_splash_audit.json`.

If cheap, the displayed identity, integrality constructor from divisibility,
and exact-valuation corollary are useful generic seams.  There is no request
to import the enormous concrete CRT rows.  This construction proves one
formula-generated nonlinear jump, not a returning orbit; renewal of
`C+2^D*3^q*K` remains the research problem.

## Kontorovich request: stable quotient and double splash (2026-07-22 05:16 EDT)

The sign-negative repetend renews once through a generic elementary lemma.
For `m>=1`, define (over naturals or integers, after proving divisibility)

```text
c_m=(2^(3^(m-1))+1)/3^m.
```

From

```text
2^(3^(m-1))=-1+3^m*c_m
```

and cubing, direct ring arithmetic gives

```text
c_(m+1)=c_m-3^m*c_m^2+3^(2*m-1)*c_m^3.
```

In particular `c_(m+1)=c_m (mod 3^m)`.  The useful finite-precision
corollary is: for `M>=P>=1`, `c_M=c_P (mod 3^P)`.

A second cheap binomial seam is the following.  If `Q>=P`, `k` is odd, and

```text
x=-1+3^Q*c,
k*c=1 (mod 3^P),
```

then

```text
x^k=-1+3^Q (mod 3^(Q+P)).
```

Terms of binomial degree at least two vanish because `2Q>=Q+P`.  These two
lemmas justify the research construction

```text
T1=3^(q1-1)*k,
R1=(2^T1+1)/3^q1,
R1=1 (mod 3^P).
```

At concrete level two, `P=90`; a 45-digit `k` also makes `T1` lie in the
affine exponent class.  The resulting two-splash chain is recorded by
`experiments/kontorovich/unit_double_repetend.py` and
`unit_double_repetend_audit.json`.  If cheap, the recurrence, stabilization,
and binomial congruence are the useful generic formal seams.  Please do not
materialize the concrete exponent or infer an infinite orbit: the current
research result is exactly two nonlinear renewals, and a third externally
preloaded correction would still face the ordinary-address gate.

## Kontorovich request: repetend core-energy no-go (2026-07-22 05:24 EDT)

The pure infinite continuation closes by a short ordered-ring argument.  For
`q>=3`, first prove

```text
3^(q-1)>=2*q+1.
```

The base `q=3` is `9>=7`; multiplying the induction hypothesis by three is
more than enough for the successor.  Hence, for every positive odd `k` and

```text
T=k*3^(q-1),
```

we have

```text
2^T >= 2^(2*q+1)=2*4^q>2*3^q.
```

If positive naturals `h,h'` satisfy the sign-negative unit relation

```text
2^T*h'=3^q*h-1,
```

then `h>2*h'`.  Iteration gives `h_0>2^N*h_N>=2^N`, excluding an infinite
positive sequence of consecutive full-order marker-one splashes.

The research checker `experiments/kontorovich/unit_repetend_energy.py` audits
the concrete exponent classes at levels `2,4,6`.  The useful formal target is
only the generic inequalities and finite-chain telescope.  Scope this tightly:
it does not exclude other markers or rare repetend discharges separated by
amplifying charge phases.  That interleaved charge--discharge architecture is
now the live research lane.

## Kontorovich request: generic charge--discharge quotient (2026-07-22 05:34 EDT)

The first charge phase uses only a generic two-step elimination.  If

```text
2^P*a=3^Q*x-1,
2^R*y=3^S*a-1,
```

then ring arithmetic gives

```text
2^(P+R)*y=3^(Q+S)*x-(3^S+2^P).
```

If an odd positive `d` divides `x` and `y`, and
`3^S+2^P=d*c`, division gives

```text
2^(P+R)*(y/d)=3^(Q+S)*(x/d)-c.
```

Research uses the concrete level-two values `P=77`, `S=57`,

```text
d=(3^57+2^77)/5=314038802961906688057474567,
c=5.
```

The packet-register stride is coprime to `d`, so one affine packet class is
divisible by `d` and the composition preserves it.  The resulting public law
is

```text
G=2^(23*N+3)*g
 -> G'=(3^(17*N+97)*g-5)/2^128.
```

The research artifact `experiments/kontorovich/unit_charge_discharge.py`
checks this by both direct CRT and literal two-unit composition.  If cheap,
please package only the generic elimination/division identity and perhaps the
obvious composition-to-macro seam.  Do not import the large register rows or
infer an infinite orbit.  The current result is a finite-level autonomous ISA
whose every branch is outward; an infinite successful positive orbit remains
the missing counterexample witness.

## Kontorovich request: recursive `-5` splash algebra (2026-07-22 05:46 EDT)

The quotient construction self-regenerates.  If one public ISA has

```text
G=2^(23*N+3)*g,
2^e*G'=3^(17*N+d)*g-5,
```

and `G'` executes its one-cell branch, two-step elimination gives

```text
2^(2*e+26)*G''
 =3^(17*N+2*d+17)*g-5*(3^(17+d)+2^(26+e)).
```

After restricting to endpoints divisible by
`D=3^(17+d)+2^(26+e)` and dividing, the collision is again `-5` with

```text
d'=2*d+17,       e'=2*e+26.
```

Starting at `d=97,e=128`, induction gives

```text
d_j=114*2^j-17,
e_j=154*2^j-26,
D_j=3^(114*2^j)+2^(154*2^j).
```

The research-side all-depth coprimality proof is also short.  If a prime
`r!=3` divides `D_j`, then the order modulo `r` of `3^114/2^154` is divisible
by `2^(j+1)`, hence `2^(j+1)|r-1`.  For a prime divisor of the fixed 80-bit
register stride this forces `j<=78`; Python checks all 79 remaining gcds
exactly.  The `r=3` case is immediate.  A separate ordinary-nesting
obstruction is just

```text
rho+D*K > K
```

for naturals `rho>=0,D>1,K>0`: deeper positive child packets strictly enlarge
their ancestor address, so this infinite hierarchy cannot stabilize to one
natural.

If cheap, the useful Lean seams are the generic two-step identity, the closed
forms by induction, and the elementary lift inequality.  The finite 79-gcd
table and huge register offsets should remain research-side unless there is a
very inexpensive native certificate route.  Scope: this proves arbitrarily
deep finite regeneration and closes infinite canonical nesting; it does not
exclude an autonomous infinite orbit at a fixed finite charge level.

## Kontorovich request: fixed-form charge bouncer (2026-07-22 06:05 EDT)

The fixed-level research target now has a short generic derivation.  Let

```text
A=3^114, B=2^154, F=(A-B)/5,
Z=F*G-2^26.
```

For the concrete charge register, `F*r-2^26` is divisible by the stride, so
`Z` is integral.  The one-cell public law implies by ring arithmetic

```text
B*Z'=A*Z.
```

For `N=m+1`, the general public law similarly gives

```text
2^(154+23*m)*Z'
 =3^(114+17*m)*Z
  +2^26*A*(3^(17*m)-2^(23*m)).
```

At a defect source write `Z=2^26*y`.  If

```text
E=3^(17*m)*(y+1)-2^(23*m),
v2(E)=23*m+154*h,
```

then executing the defect and `h-1` homogeneous backgrounds yields

```text
y'=3^(114*h)*E/2^(23*m+154*h).
```

Research additionally has `m=v2(y+1)/23`; another positive multiple of 23
in `v2(y'+1)` selects the next defect.  The worker
`experiments/kontorovich/unit_charge_bouncer.py` compares this map with
literal bounded macro families.

If cheap, useful Lean seams are the two displayed fixed-form identities and
the finite telescope through `h-1` homogeneous backgrounds.  The large
concrete offset divisibility can remain research-side.  Please do not infer
an infinite orbit: the new result is an exact autonomous partial map, and an
infinite positive accepted `y` sequence is precisely the missing witness.

## Kontorovich request: reverse bouncer decoder (2026-07-22 06:16 EDT)

The accepted fixed-form step is injective by elementary valuation readback.
If the forward transition has

```text
E=3^(17*m)*(y+1)-2^(23*m),
v2(E)=23*m+154*h,
y'=3^(114*h)*E/2^(23*m+154*h),
```

then `E/2^(...)` is not divisible by three.  Hence

```text
h=v3(y')/114,
q=y'/3^(114*h).
```

Rearranging the forward identity gives

```text
3^(17*m)*(y+1)=2^(23*m)*(1+2^(154*h)*q).
```

Because `y=0 (mod 3)`, it follows that

```text
m=v3(1+2^(154*h)*q)/17,
y=2^(23*m)*(1+2^(154*h)*q)/3^(17*m)-1.
```

If cheap, a generic forward-then-reverse theorem would make the bouncer's
information preservation kernel-checked.  The research verifier now checks
this on all bounded macro members.  The arithmetic resonance
`114*23-154*17=4` is only a search clue, not a theorem claiming an orbit.

### Semantic audit against rounds 68--70

The new `m` is **not** the recursive hierarchy level.  The bouncer remains at
one fixed level-two charge register.  Here `m=N-1` is the variable defect
opcode read from `v2(y+1)`; after that one defect, the same transition executes
`h-1` copies of the *different* homogeneous one-cell law.  Thus successive
positive `Z` states do not all obey one fixed affine-gain recurrence unless
the opcode schedule has been artificially frozen.

Nor is `m` known or intended to be nondecreasing.  The exact artifact contains
all transitions `m -> m'` with `m,m'=1..4`, including strict decreases and
oscillations.  So `MonotoneFixedFormDispatcher` is not presently instantiated:

- hierarchy level: fixed at two;
- defect opcode `m`: variable and potentially decreasing;
- affine law within a block: one `m`-defect, then `h-1` homogeneous backgrounds;
- ordinary control state: the evolving unbounded positive integer `y`.

Round 68 correctly closes repetition of one fixed `m`/affine law, already a
periodic sublane.  Round 69 correctly closes increasing canonical hierarchy
addresses.  The reversible two-valuation map deliberately lies between those
interfaces.  A useful next formal question is whether its exact forward and
reverse equations imply any monotone *derived* rank despite oscillating `m`;
none is currently known research-side.

## Kontorovich response: zero extension lifts and splash banks (2026-07-22 07:00 EDT)

Rounds 75--78 give the right endpoint.  Research confirms the exact finite
zero condition: the current minimal output is already in the next input
progression iff the old-tail extension residue is `rho=0`.

The new worker
`experiments/kontorovich/unit_charge_zero_lift.py` exhausts every word through
depth four over the 16 opcodes `(m,h)` with `1<=m,h<=4`, followed by every
next opcode:

```text
prefixes:             69,904
extensions:           1,118,464
zero extension lifts: 0
max terminal v2 by depth: 3,9,13,16
```

The closest event shares only 16 low bits against a required 177.  This is a
bounded exact audit, not the generic nonzero theorem.  In particular, the
growing maximum valuations mean research does not assert a fixed mod-16 (or
other fixed-modulus) invariant.

The next candidate prompted by Simon is a multi-collision splash bank: one
distributed bit island strikes, another absorbs the collision debris, and a
third reseeds the next delayed gap.  Once the phase words are fixed this will
compile to a vector of affine dyadic links.  The desired formal endpoint is
already exactly
`no_realization_of_frequently_nonzero_extension_lifts`; no new Lean request
is necessary until research has a symbolic recurrence for the bank's
substitution-scale `rho_k`.

## Kontorovich request: regenerative carry-repetend cell (2026-07-22 07:10 EDT)

Simon's splash-bank suggestion has produced a small generic identity worth
formalizing if cheap.  Suppose

```text
3^q*A+s = 2^p*C + 2^(p+L)*B,
r=v3(B),
D=2*3^(q-r-1),
3^(q-r) | 2^D-1,
z=B*(2^D-1)/3^q.
```

For the concrete certified records `0<B<3^q` and `r<q`.  Then `z` is a
positive natural smaller than `2^D`, and

```text
B+3^q*z=2^D*B,
A+2^(p+L)*(z+2^D*u)
  --first unit collision-->
C+2^(L+D)*(B+3^q*u).
```

The research artifact `experiments/kontorovich/unit_carry_repetend.py`
checks the concrete order and register embeddings at six levels.  A reusable
Lean lemma need not mention the huge constants; the useful semantic statement
is that a finite catcher word translates the isolated carry unchanged across
a clean gap.  Please retain the scope: this is one finite glider/ether cell,
not an infinite rail or a counterexample.

## Kontorovich request: strike--scrub--turnaround existence (2026-07-22 07:25 EDT)

There is now a formula-compressed third phase after the carry translator.
Research-side exact arithmetic is in
`experiments/kontorovich/unit_carry_turnaround.py`; the only genuinely
theorem-level seam is the enormous 2-power congruence.

Use the sign-negative level-two unit constants

```text
p(n)=23*n+54,      q(n)=17*n+40,
source=target=1,   B=1,   H=17,
D=ord_(3^57)(2)=2*3^56,
P=D+2=p(g),        g=(P-54)/23.
```

The first two collisions can be arranged so that

```text
3^57*A-1 = 2^77*C + 2^(77+L)*B,
B+3^57*z = 2^D*B,
3^57*C-1 = 2^p(ell)*H,
h2 = H + 2^(D+1)*3^57*(1+3^57*u).
```

Eliminating `A,C` reduces the first alignment to one explicit class

```text
2^p(ell) =
 -(2^77+3^57) /
  (2^77*(17+2*3^57))                 (mod 3^114).
```

The worker computes the base-two discrete log by exact ternary lifting and
gets

```text
ell = 985704136832889032287826201378021826095996227497733368
      (mod 2*3^113).
```

This class is even.  For the turnaround require the unique class

```text
3^(17*ell+40)*17 = 1+2^P             (mod 2^(P+1)).
```

Because `17=1 (mod 8)`, the target after division by 17 is in the even-power
subgroup generated by 3.  `orderOf_three_twoPow` gives that subgroup the
required size.  Its exponent class makes `ell` even, so CRT is compatible
with the explicit `2*3^113` class above.  This produces an ordinary finite
positive `ell`; it need not be expanded.

Finally choose the invariant ordinary tail `u=u0+4*M*w` with `u0=1 mod 4`.
The third collision has exact division `P` and returns

```text
h3 = R + 2*M*3^(q(ell)+114)*w.
```

Since the coefficient after the displayed factor two is odd, for every
`E>=1` and odd target word `T` there is a unique `w mod 2^(E-1)` with
`h3=T mod 2^E`.  Thus the three-collision macro is a universal *finite*
dyadic reseed interface.

If cheap, please formalize:

1. subgroup membership/existence of the 2-adic `ell` class from
   `orderOf_three_twoPow`;
2. the parity-compatible CRT with an arbitrary even `ell3` class modulo
   `2*3^k`;
3. the final odd-coefficient dyadic-writer lemma.

Scope is crucial: this compiles any one next catcher word but does not make
the infinite linked tail ordinary.  It is a finite strike--scrub--turnaround,
not yet a counterexample.

## Kontorovich reply: Thue--Morse theorem search (2026-07-22 07:32 EDT)

I do not yet have a published theorem whose checked hypotheses close the
round-82 rational `Q_2` value.  The current literature audit is:

- Väänänen, *Algebraic independence of certain Mahler numbers* (2015),
  arXiv:1507.02510, treats nonzero algebraic points in the ordinary complex
  open unit disk; that statement does not transfer automatically to `Q_2`.
- Bugeaud, *On the rational approximation to p-adic Thue--Morse numbers*
  (2021), arXiv:2110.01855, treats the standard signed Thue--Morse number at
  argument exactly the prime `p`, not an arbitrary rational `z=a0*a1`.
- T. Q. Wang, *p-adic Transcendence and p-adic Transcendence Measures for the
  Values of Mahler Type Functions* (2006), DOI
  `10.1007/s10114-005-0534-4`, may be relevant, but I have not recovered and
  audited its precise function, regularity, argument, and nonvanishing
  hypotheses.

Please keep the value-exclusion hypothesis open.  None of these citations is
currently a licensed irrationality seam for the bouncer reduction.

## Kontorovich reply: even powers of three are exactly `1 mod 8` (2026-07-22 07:34 EDT)

Thank you for catching the membership seam.  Here is the preferred elementary
finite-group proof.  Put `N=P+1` (so certainly `N>=3`) and

```text
U_N={x in (Z/2^N Z)^x : x=1 mod 8}.
```

There are exactly `2^(N-3)` such residue classes, represented uniquely by
`1+8*j`, `0<=j<2^(N-3)`.  Every power of `9` lies in `U_N`.  From

```text
order_N(3)=2^(N-2)
```

one gets

```text
order_N(9)=2^(N-3):
9^k=1  =>  3^(2k)=1  =>  2^(N-2) | 2k
                              =>  2^(N-3) | k,
```

and `9^(2^(N-3))=3^(2^(N-2))=1` gives the reverse bound.  Hence `<9>` is a
subset of `U_N` with the same finite cardinality, so `<9>=U_N`.

For the turnaround target

```text
X=(1+2^(N-1))*17^(-1) mod 2^N,
```

both factors are `1 mod 8` (`N` is enormous), so `X` belongs to `U_N` and
therefore `X=9^j=3^(2j)` for some `j`.  Taking `beta=2j` gives the required
even exponent.  Since `17*ell+40=beta` and both `beta,40` are even, `ell` is
even as well.

Please kernel-check the subgroup cardinality/equality rather than treating it
as a consequence of order alone.  The research artifact currently regards
this elementary group argument plus `orderOf_three_twoPow` as its theorem
dependency; once this lands, the turnaround existence seam is closed.

## Kontorovich reply: concrete nonexceptional Thue--Morse coding (2026-07-22 07:35 EDT)

For round 82, the cleanest favored pair is

```text
(m0,h0)=(1,1),     (m1,h1)=(2,1).
```

Put `x=r`, `y=r^2`, and `t=s`.  Since the recharge opcode is the same for
both symbols,

```text
e1-e0
 =(x-y)+t*(y*(1-x)-x*(1-y))
 =(x-y)*(1-t)
 =(r-r^2)*(1-s).
```

Here `r=2^23/3^17` and `s=2^154/3^114`, so both factors are visibly nonzero
in `Q_2`.  Thus this coding is not in the exceptional rational-collapse case,
and its Mahler argument is the explicit

```text
z=a0*a1=r^3*s^2.
```

This selects a simple theorem-test instance; it does not supply the missing
irrationality theorem or claim that the prescribed schedule is an autonomous
bouncer ray.

## Kontorovich request: fixed-length synthesized-marker turnaround (2026-07-22 07:43 EDT)

There is a stronger construction which removes the uncontrolled preceding-
length residue from the fixed-marker macro.  Keep the second instruction at
one cell (`p,q` exponents `77,57`) and synthesize the marker instead.

Put `L=78`, `B=1`, `D=2*3^56`, `P=D+2`,
`g=(P-54)/23`, and `q_g=17*g+40`.  First choose the unique
`h3 mod 3^114` satisfying

```text
2^154*h3 + 2^77 + 3^57*(2^155+1) = 0  (mod 3^114).
```

For every `t`, set

```text
H =h3+3^114*t,
C =C0+2^77*3^57*t,
A =A0+2^154*t.
```

The definitions of `A0,C0` then give identically

```text
3^57*A-1=2^77*C+2^155,
3^57*C-1=2^77*H.                                   (SM1)
```

Both divisions are exact because `A,C,H` are odd.  Now use the already
proved odd-coefficient writer to choose the unique `t mod 2^(P+1)` with

```text
3^(q_g+114)*t
 =1+2^P-3^q_g*h3                 (mod 2^(P+1)).    (SM2)
```

Thus `3^q_g*H=1+2^P mod 2^(P+1)`, making the third division exactly `P`.
No even-power subgroup theorem is needed for this version.  The marker has
at most `P+183` bits, hence the same scale as `D`, rather than requiring an
instruction length represented modulo `2^(P-1)`.

With `z=(2^D-1)/3^57` and the source-register restriction
`u=u0+4*M*w`, the three-collision chain has tail coefficients

```text
input:   2^(D+157)*M,
output:  2*M*3^(q_g+114).                            (SM3)
```

Here

```text
q_g+114=773644327083924272402582364
```

is even, and

```text
3*(q_g+114)/2-(D+156)
 =113771224571165334176850348 > 0.
```

Therefore `3^(q_g+114)>2^(D+156)` by `9>8`: the output affine coefficient is
strictly larger than the input coefficient.  This is an outward finite
turnaround family, still not an invariant family or infinite orbit.

The exact worker is
`experiments/kontorovich/unit_marker_turnaround.py`.  If cheap, please package
SM1--SM3 using `exists_oddCoefficient_solution_mod_twoPow`; the most valuable
Lean endpoint is existence of an odd `H,A,C` with the three exact valuations
and the strict coefficient inequality.  A fully materialized small surrogate
in the worker replays all three divisions.

### Stable SM1 numerals (2026-07-22 07:49 EDT)

The final worker and reconstructing artifact now pass.  The stable canonical
`t=0` values are

```text
h3=888671312022010265821814286644910407747986487213173648,
C0=85534103469586980153598642936122702009766783904139,
A0=8232608341659632170436083629694859204415351179.
```

The defining formulas, rather than decimal reduction, should be primary in
Lean:

```text
h3=(-2^77-3^57*(2^155+1))*inverse(2^154) mod 3^114,
C0=(2^77*h3+1)/3^57,
A0=(2^77*C0+2^155+1)/3^57.
```

Artifact: `experiments/kontorovich/unit_marker_turnaround_audit.json`.

## Kontorovich request: all-opcode marker bank collapses to rank one (2026-07-22 07:57 EDT)

Allow every later legal third division, indexed by `j>=0`:

```text
P_j=D+2+23*j,
g_j=g_0+j,
q_j=q_0+17*j,
Q_j=q_j+114.
```

Write the marker lift as

```text
t=t_j+2^(P_j+1)*s.
```

To keep the remote contribution invisible modulo `2^(P_j+1)`, exactness
forces

```text
1+3^57*u_j=0 (mod 2^(P_j-D)),
u=u_j+2^(P_j-D)*((M-1)*s+M*w).
```

This makes the two apparent tail registers collapse.  The marker lift enters
the source with exponent

```text
154+(P_j+1)=P_j+155,
```

while the remote tail enters with exponent

```text
155+D+(P_j-D)=P_j+155.
```

The `M-1` coefficient cancels the marker lift in the invariant register.
After the third division the same combination reappears.  Therefore, for
suitable constants `X_j,Y_j`, the whole register-preserving bank has the exact
one-register normal form

```text
v=s+w,
x_j=X_j+2^(P_j+155)*M*v,
y_j=Y_j+2*M*3^Q_j*v.                                (MB1)
```

This is a useful negative and positive result at once.  It closes the naive
interpretation of the marker and remote islands as two independent stacks,
but exposes an unbounded variable-length tag instruction.  Every opcode has
positive coefficient drift: `j=0` is the already checked `9>8` inequality,
and each increment multiplies the ratio by

```text
3^17/2^23 =129140163/8388608 > 1.                   (MB2)
```

A fixed `j` repeated forever is in the already closed periodic valuation-word
lane.  The live target is a payload-selected unbounded `j`, not a fixed
self-feed.

Research artifact:
`experiments/kontorovich/unit_marker_bank.py`.  It checks the public formulas
for `j=0..15` and fully materializes six small three-collision analogues.  If
cheap, please formalize MB1 generically from the displayed exponent
equalities and MB2 from `3^17>2^23`.  The valuable semantic endpoint is:
exact third-division alignment forces rank one; it does not create a second
free counter.

### Correction: register coupling in MB1 (2026-07-22 08:10 EDT)

The initial 07:57 request wrote the remote lift as if the marker tail could
vary while its register phase stayed fixed.  That is false: the raw three
divisions remain exact, but the source leaves the public level-two invariant.
The corrected formula above couples the remote tail with coefficient `M-1`.
The equal source exponents then give

```text
2^(P_j+155)*s
 +2^(P_j+155)*(M-1)*s
 =2^(P_j+155)*M*s,
```

and the same identity holds after the third division.  Please formalize only
the corrected `v=s+w` / common-`M` statement.  The corrected research artifact
also checks the odd register difference in each small replay.  Rank one and
the coefficient ratio are unchanged because the common factor `M` cancels.

## URGENT RETRACTION: SM/MB paths are not unit-semantic (2026-07-22 08:23 EDT)

Please do **not** formalize the concrete synthesized-marker requests SM1--SM3
or MB1--MB2.  A fresh source/target audit found that their three raw divisions
do not form a legal linked unit path.  The public transition law is

```text
n -> m: 3^q(n)h-1=2^p(m)h',
p(n)=23n+54, q(n)=17n+40.
```

The advertised route used exponent sequence `(57,57,q_g)`.  But after the
second transition its state sequence was `1 -> 1 -> 1`; the third source was
therefore state `1` and had to use `q(1)=57`, not `q_g`.  The modular divisions
and coefficient comparisons were internally exact but attached to
incompatible source/target labels.  The research workers and artifacts have
been removed.  `RankOneBankBoundary.lean` remains a valid abstract logical
warning if it is independent of MB, but it must not be cited as validating the
concrete bank.  Any in-progress concrete link theorem based on MB should be
abandoned or clearly quarantined.

The corrected legal return route is

```text
1 -> 1 -> g -> g -> 1.
```

Put

```text
P=23g+54, Q=17g+40, R=114+2Q, S=154+2P,
C_g=3^(2Q+57)+2^77*3^(2Q)+2^(77+P)*3^Q+2^(77+2P).
```

Four direct substitutions give

```text
3^R h-C_g=2^S h'.                                  (RQ1)
```

The actual autonomous reproduction obligation is now explicit:

```text
3^R(g)F(g)-C_g=2^S(g)F(f(g)),                       (RQ2)
```

with all four intermediate quotients positive odd.  The new exact worker is
`experiments/kontorovich/unit_return_quine.py`; it literally replays the legal
route for `g=1..16` and checks the symbolic mixed-base constant.

### New formalization request: rational successor-quine no-go

For `f(g)=g+1`, set

```text
z_g=2^(23g+54)/3^(17g+40), c=2^23/3^17,
A=3^114, D=2^154,
B(z)=(3^57+2^77)+2^77 z+2^77 z^2.
```

Then (RQ2) for an ansatz `F(g)=r(z_g)` is the rational-function identity

```text
A*r(z)-D*z^2*r(c*z)=B(z).                            (RQ3)
```

Please formalize, if reasonably cheap:

```text
there is no r in Q(z) satisfying (RQ3).
```

Suggested proof over an algebraic closure: if a nonzero finite `alpha` is a
pole of `r`, cancellation at `alpha` forces `c*alpha` to be a pole.  Iteration
gives infinitely many poles because `0<c<1`, contradiction.  A pole at zero
cannot cancel: `r(z)` has order `-m` while `z^2 r(cz)` has order `2-m`.
Thus `r` is a polynomial.  Positive degree `d` creates the unmatched degree
`d+2` term on the left of (RQ3), while degree zero cannot produce the nonzero
linear coefficient of `B`.  The research worker exact-checks the Laurent
polynomial degree portion; the pole argument is not yet promoted as a checked
result.

The disproof search will try to evade this boundary using nonlinear or
automatic self-writing updates, beginning with `g -> 2g`, for which

```text
z_(2g)=(3^40/2^54) z_g^2.
```

## Kontorovich request: perfect-23rd-power bouncer quine (2026-07-22 09:03 EDT)

The corrected return-bank audit redirected the constructive search to the
already autonomous, reversible `-5` charge bouncer.  Its exact radix equations
at one accepted transition are

```text
C^m u       =1+B^h q,
D^m' u'     =1+A^h q,
A=3^114, B=2^154, C=3^17, D=2^23.
```

The fixed register also forces `F | u,u'`, where

```text
F=(A-B)/5
 =493006936424420884140154671288273660376560866054730997.
```

The first payload encoding which literally regenerates its own address type is

```text
u=F*r^23,        u'=F*r'^23.                        (PQ0)
```

The exponent 23 is hardware-selected: `D=2^23`, so `v2(r')` contributes an
integral number of *next* defect cells without changing the encoding.  This is
the current direct attempt to make the program reproduce, rather than another
finite word writer.

Eliminating `q` gives the necessary closure equation

```text
A^h C^m r^23 - B^h D^m' r'^23 = (A^h-B^h)/F.       (PQ1)
```

For the shortest recharge `h=1`, `A-B=5F`, so

```text
3^(114+17m) r^23 - 2^(154+23m') r'^23 = 5.         (PQ2)
```

Absorbing complete 23rd powers reduces the dependence on `m,m'` to

```text
3^e X^23 - 2^16 Y^23 = 5,
e=(114+17m) mod 23.                                 (PQ3)
```

The new exact worker
`experiments/kontorovich/unit_charge_power_quine.py` enumerates the complete
23rd-power residue sets and proves:

```text
p=47:  e in {4,6,15}
p=139: e in {6,15}
p=461: e in {15}.
```

Thus 22 of 23 exponent classes are locally impossible; only

```text
e=15,  equivalently m=5 (mod 23),
3^15 X^23 - 2^16 Y^23 = 5                           (PQ4)
```

survives.  The artifact reconstructs the prime factorization

```text
F=173*168803*1707499*33826633*73768171
  *317905672921*12463506446779
```

and hashes every exact finite-field stage.  Please kernel-check PQ1--PQ4 if
cheap.  The most valuable semantic endpoint is a theorem that any accepted
`h=1` transition preserving the family (PQ0) supplies an integer solution to
PQ4.  Register/valuation conditions make PQ1 necessary but not sufficient, so
an impossibility for PQ4 cleanly kills this reproducing rail.

PARI/GP's default `thueinit`/`thue` diagnostic returned no solutions to PQ4,
but that path may assume GRH.  Its unconditional `thueinit(...,1)` certification
is still running on Akdeniz.  Please do not promote the PARI outcome unless an
unconditional certificate or independently checkable theorem is obtained.

### Resolution of the external PQ4 seam (2026-07-22 09:25 EDT)

The default PARI computation is already unconditional by PARI's documented
criterion.  On Akdeniz, PARI/GP 2.15.4 checked

```text
P(x)=3^15*x^23-2^16
polisirreducible(P)=1
T=thueinit(P), T[2].no=1
thue(T,5)=[]
```

The current PARI `thue` documentation states that, although flag-zero
initialization can generally depend on GRH, the result is unconditional when
the attached tentative class number is one.  The exact executable is
`experiments/kontorovich/unit_charge_power_quine_thue.gp`, SHA-256
`c4541ea4c0cdcac65d2738bef9fffd378ae0fe4c7495409b46be08cd80d76e48`.
This remains an external-PARI theorem seam, not something Lean should import
as an axiom.  Your conditional theorem
`no_shortest_recharge_power_quine (hPQ4 : ¬ PQ4Solution)` is exactly the right
kernel boundary; the research README now combines it with the scoped external
enumeration.

The constructive search is moving to `h=23`, where
`A^23=3^4*C^154` and `B^23=D^154`.  Both coefficients are complete 23rd powers
and the three local sieves leave all exponent classes.  The exact artifact is
`experiments/kontorovich/unit_charge_power_resonance_audit.json`, SHA-256
`db7e620c936bcb9b126a70e183f33ad0880159942329e5c04476c7035fdcfe9c`.
No new Lean request is made yet; the next obligation is to derive an actual
multi-rail correction identity, not merely another necessary equation.

## Kontorovich request: public-state 23rd-power quine (2026-07-22 09:47 EDT)

A stronger reproduction type is available at the same resonance.  Encode the
*public bouncer state* as

```text
y=s^23.
```

If an accepted step has recharge `h=23` and odd collision quotient `q=t^23`,
then its output is automatically

```text
y'=A^23*t^23=(A*t)^23.
```

Thus the public data type literally reproduces; no output-to-input payload
identification remains.  The exact transition condition is

```text
C^m*(s^23+1)=D^m*(1+(B*t)^23),                    (SPQ1)
v2(s+1)=23m,                                      (SPQ2)
```

where the second equality uses odd-exponent LTE
`v2(s^23+1)=v2(s+1)`.  The first equation also forces the symmetric condition
`v3(1+B*t)=17m` when the valuations are exact.  Register congruences remain
separate: `s^23=0 (mod M)`, `s^23=-1 (mod F)`, and the analogous conditions
for `A*t`.

The pure coefficient subclass `m=23k` is impossible by a very short size
argument.  SPQ1 becomes

```text
(3^(17k)*s)^23 + (3^(17k))^23
  = (2^(23k+154)*t)^23 + (2^(23k))^23.            (SPQ3)
```

Please kernel-check the following endpoint if cheap:

```text
theorem no_state_power_quine_of_m_multiple_23
    (k s t : Nat) (hk : 0 < k) (hs : 0 < s) (ht : 0 < t)
    (hval : 2^(529*k) ∣ s+1)
    (heq : SPQ3 k s t) : False
```

Proof: put `U=3^(17k)`, `Z=2^(23k)`, `X=U*s`,
`Y=2^(23k+154)*t`.  Since `U>Z`, SPQ3 gives

```text
0 < Y^23-X^23 = U^23-Z^23 < U^23.
```

Integral `Y>X` implies `Y^23-X^23 >= X^22`, so
`(U*s)^22<U^23`, hence `s^22<U`.  But `hval` gives
`s >= 2^(529k)-1 > 2^(528k)`, while
`U=3^(17k)<2^(34k)`.  Therefore

```text
s^22 > 2^(11616k) > 2^(34k) > U,
```

a contradiction.  This closes only `m=0 (mod 23)`.  The 22 residual defect
classes remain the live public-state quine lane and reduce to genuinely
scaled degree-23 equations; please do not generalize the no-go beyond the
stated hypothesis.

## Kontorovich request: Roth bridge closes infinite pure-state runs (2026-07-22 10:14 EDT)

There is a much stronger endpoint, and it covers **every** recharge which can
preserve the public-state type.  If an accepted bouncer transition starts and
ends at 23rd powers, exact ternary readback gives `23 | h` because
`v3(y')=114h` and `gcd(114,23)=1`.  Write `h=23*ell`; then the collision odd
part is itself `t^23`, and the transition equation is

```text
C^m*(s^23+1)=D^m*(1+(B^ell*t)^23),                (GSPQ)
y=s^23,                 y'=(A^ell*t)^23,
m,ell,s,t > 0.
```

Thus this is the entire pure public-23rd-power data type, not merely `h=23`.
For

```text
a=(17m)/23,       e=(17m)%23,
U=3^a,            X=U*s,
Y=2^m*B^ell*t,    Z=2^m,
```

GSPQ becomes the exact gap equation

```text
Y^23-3^e X^23 = C^m-D^m > 0.                     (RB1)
```

When `e != 0`, let the positive real `alpha` satisfy
`alpha^23=3^e`.  Factoring the difference of powers and using
`C^m-D^m<C^m=alpha^23 U^23` gives

```text
0 < Y/X-alpha < alpha/s^23.                       (RB2)
```

The valuation condition `2^(23m) | s+1` makes `s >= 2^(23m)-1`.
The deliberately crude comparison `U<s` therefore holds for every `m>0`
(e.g. `U^23<=3^(17m)<2^(34m)`, while `s>2^(2m)`).  Hence, if `p/q=Y/X` is
reduced,

```text
q <= X=U*s < s^2,
```

so RB2 is eventually stronger than

```text
0 < p/q-alpha < 1/q^11.                           (RB3)
```

Roth's theorem (used externally, not requested as a Lean axiom) says that an
algebraic irrational `alpha` admits only finitely many reduced rational
approximants with exponent greater than two.  There are only 22 nonzero
coefficient classes.  The missing `e=0` class is already killed by
`no_state_power_quine_of_m_multiple_23`.

Finally, GSPQ itself gives strict state growth.  Put `z=B^ell*t`.  Since
`C>D`, it forces `z^23+1>s^23+1`, hence `z>s`; and `A>B` gives

```text
A^ell*t > B^ell*t > s.
```

Consequently an infinite pure-state run would have strictly increasing roots
and, by pigeonhole, infinitely many increasingly accurate approximants to one
fixed `alpha`, contradicting Roth.  This does **not** prove that individual
transitions in the remaining 22 classes are absent.  It proves that no
infinite Collatz counterexample can live wholly in the public 23rd-power type.
Corrected/multi-rail encodings remain open.

Please kernel-check the elementary bridge if reasonably cheap, preferably as
separate theorems:

1. GSPQ normalizes to RB1 for arbitrary `ell`;
2. GSPQ implies `B^ell*t>s` and therefore `A^ell*t>s`;
3. `2^(23m) | s+1`, `m>0` imply `U<s` and `X<s^2`;
4. over `ℝ`, RB1 plus `alpha>0`, `alpha^23=3^e` implies RB2.

Keep the final Roth finiteness implication explicitly external unless Mathlib
already has an appropriate theorem.  The exact executable companion is
`experiments/kontorovich/unit_charge_state_power_quine.py`.

## Kontorovich request: hidden-`F` register is a writable nonlinear ISA (2026-07-22 10:39 EDT)

The cofactor register from round 98 does **not** automatically lift to a
second factor of `F`.  Instead it carries a genuine nonlocal instruction.
This is constructive information, so please keep it separate from the Roth
no-go.

For arbitrary recharge `h=23*ell`, put

```text
z=B^ell*t,                    s'=A^ell*t,
s+1 = D^m F w,                z+1 = C^m F v,
s'+1 = D^m' F w'.
```

The public-state equation gives

```text
w Q(s)=v Q(z),                Q(x)=(x^23+1)/(x+1).       (HF1)
```

The exact expansion at the register root is

```text
Q(-1+u)=23-253u+1771u^2-... .                            (HF2)
```

Since `gcd(23,F)=1`, HF1 has one collision lift `v` modulo each
`F^n` for every input `w`.  The first nonlinear carry is

```text
v = w + 11 F (C^m-D^m) w^2                  (mod F^2).  (HF3)
```

The output relation is exact.  With

```text
S_ell=(A^ell-B^ell)/(A-B),
```

one has

```text
D^m' w' = C^m v + 5 S_ell t.                           (HF4)
```

Because `A=B (mod F)` and `B^ell*t=z=-1 (mod F)`, this reduces to the
first-digit instruction

```text
B D^m' w' = B C^m w - 5 ell                  (mod F).  (HF5)
```

All of `5,B,C,D` are units modulo `F`.  Consequently, for every input
residue `r`, desired output residue `r'`, and positive defect opcodes `m,m'`,
there is a unique recharge class

```text
ell = B*5^(-1)*(C^m r-D^m' r')                (mod F)   (HF6)
```

which writes `r'`.  The least positive representatives in the audit have up
to 54 decimal digits.  This is precisely Simon's anticipated nonlocal
instruction: a recharge length spread across the whole number addresses an
arbitrary next value of a 179-bit hidden register.

At the next precision the instruction is already nonlinear.  If `r=w mod F`,
then modulo `F^2` the exact audit checks

```text
D^m' w' = C^m w - 5 ell B^(-1)
  + F*(11 C^m(C^m-D^m)r^2
       +5 ell B^(-1) C^m r
       -25 binom(ell,2) B^(-2)).                         (HF7)
```

The executable
`experiments/kontorovich/unit_charge_hidden_register.py` reconstructs the
cofactor Taylor polynomial, Hensel-lifts HF1 uniquely through `F^3`, checks
HF3 and HF7, and synthesizes exact first-digit writes to five unrelated
targets.  It also uses CRT to construct visible-register roots with arbitrary
nonzero `w mod F`, exact `v2(s+1)=23m`, and `F^2` not dividing `s+1`.
Therefore the *visible register side conditions alone* do not force a second
`F`; no transition is claimed by those CRT rows.

Please kernel-check the inexpensive universal spine, preferably without
formalizing the executable digit-lifter yet:

1. `F^2 | Q(-1+F*d*w)-(23-253*F*d*w)`;
2. HF1 plus `v=w+F*delta` implies
   `F | delta-11*(C^m-D^m)*w^2`;
3. the geometric identity defining `S_ell` and HF4;
4. for `ell>0`, `F | S_ell-ell*B^(ell-1)`;
5. HF5, stated without inverses as the divisibility
   `F | B*D^m'*w'-(B*C^m*w-5*ell)`;
6. if cheap, the modular existence/uniqueness corollary HF6 from the already
   checked coprimalities.

Scope warning: HF5/HF6 are a **necessary F-adic register transducer**.  They
do not prove that the selected `ell` is the actual exact 2-adic collision
valuation, that its lift is an ordinary positive integer, or that the
transducer has an infinite Collatz realization.  The constructive next task
is to couple this writable register to the valuation decoder, not to promote
an F-adic program as a counterexample.

## Kontorovich request: quadratic two-rail type and the mod-8 correction (2026-07-22 11:10 EDT)

The degree-23 public type is too rigid.  A lower-degree homogeneous two-rail
type reproduces automatically because both recharge coefficients are squares.
For

```text
N_d(x,u)=x^2+d*u^2,
A=3^114=(3^57)^2,       B=2^154=(2^77)^2,
```

one has, for every `h>0`,

```text
B^h N_d(t,v)=N_d(2^(77h)t,2^(77h)v),
A^h N_d(t,v)=N_d(3^(57h)t,3^(57h)v).              (QN1)
```

This makes the exact reproduction equation a rank-four quadric rather than a
degree-23 Thue equation:

```text
C^m*(N_d(x,u)+1)=D^m*(1+B^h*N_d(t,v)).             (QN2)
```

There is one useful universal failure.  Every accepted input has
`2^23 | y+1`, hence `y=7 (mod 8)`.  Every accepted output has the same residue;
since `A^h=1 (mod 8)`, its odd collision quotient `q` is also `7 (mod 8)`.
But a sum of two squares is never `3 (mod 4)`.  Therefore the tempting `d=1`
type contains no accepted transition at all.

The correction is to take `d=7 (mod 8)`.  The executable uses the
hardware-matched

```text
d_hw=13*(C-D)=5*13*19*1271069=1569770215=7 (mod 8),
```

which ramifies every non-ternary prime forced by the public register.  Exact
CRT witnesses independently inhabit the input and output endpoint types, and
an exact rational point shows that the homogenized QN2 at `m=h=1` is rationally
soluble.  These facts do **not** yet provide one coupled integral transition.

Please kernel-check only the cheap universal spine if useful:

1. QN1 for arbitrary natural `d,h,t,v`;
2. an accepted bouncer input satisfies `y % 8 = 7`;
3. an accepted output `A^h*q` satisfies `q % 8 = 7`;
4. `x^2+u^2` cannot be `7 (mod 8)`.

The executable certificate is
`experiments/kontorovich/unit_charge_quadratic_norm.py`.  Scope warning: QN1
is a data-type closure identity, and the CRT rows inhabit its endpoints only
separately.  Until QN2, exact valuations, positivity, and output-to-input
iteration are coupled, there is no ordinary transition or counterexample.
