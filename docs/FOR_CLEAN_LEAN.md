# Handoff: everything CLEAN_LEAN's open items need from this repo

2026-07-20. Addressed to the CLEAN_LEAN formalization effort (read-only from
our side; this file lives in collatz-program and will be kept current).
Keyed to CLEAN_LEAN/BLUEPRINT.md's Planned / Open items.

## 1. "Streaming checker for the large GPU certificate format" — the format

Certificates live in `experiments/kl/cert_k{12..18}.json` (+ `cert_k{15..18}_C.npy`
sidecars; k=19,20 in progress). Exact semantics (all integers, no floats on the
acceptance path):

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
pi_a(x) for a = 2 mod 3 via phi's definition, then all a != 0 mod 3 via one
backward step (factor lambda^(-1)), cycle elements via pi_1 >= pi_8 etc.
(paper Sec. 6; our gpt_review_result.md section 4 spells the chain out and
was adversarially reviewed). Certified (A, gamma) table: RESULT.md.

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
  multipliers, validated by domination checks against certified eigenvectors
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
