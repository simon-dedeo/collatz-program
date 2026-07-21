# Collatz program — strategy memo

v2, 2026-07-20 (v1 same day; [verify] tags resolved against the literature
sweep — full landscape with sources in `LANDSCAPE.md`, raw briefs in
`landscape/`). Everything in §4 is backed by artifacts in this repo.

> **Successor-audit notice (updated 2026-07-21):** this v2 memo preserves the
> historical program that generated the repo, so several “running” lines below
> are no longer current. Use `README.md` as the live state map. In particular:
> all inherited background jobs are stopped; `k=19` has now passed a fresh
> exact 387,420,489-constraint run of the reference verifier (large sidecar local, not in
> git). An exact obstruction invalidates the printed KL Theorem 3.1 termination
> proof; that obstruction is
> now independently kernel-checked in Lean. A second exact witness makes all
> three leaves of a new minimum deletion-eligible, contradicting another
> invariant asserted by the printed construction; a finite semantic countermodel
> also blocks its split-invariant induction. CLEAN_LEAN independently checks
> both newer obstructions and proves the abstract branch-arrival compactness
> theorem. The leading repair now compiles all complete occurrence-aware
> record-admissible additive policies into one fixed outer minimum. A bounded
> checker reproduces the published small-level literal counts, and Lean commit
> `3d6a186` now checks the all-`k` history producer, occurrence provenance,
> live pruning, common lag, and abstract feasible-point comparison. The literal
> family and P1/P2 are checked in `331ff48`; commit `729f5fa` checks D1--D3.
> Commit `76ec861` checks the final fixed-target/all-target exponent wrapper,
> so the `k=19` counting result is established under the mixed exact-Python +
> kernel-Lean trust policy. Commits `4c7fcc3`/`659dc81` now kernel-check the
> first large record at exact `k=12`; the headline `k=19` data are not yet
> Lean-ingested;
> the analytic-
> combinatorics ordinary-pole identification is retracted;
> the unsigned-zeta natural boundary at `|u|=1/4` has a candidate refutation
> by a handwritten leading-pole factorization plus exact finite checks (formal
> check pending);
> and a candidate arctic all-dimension repair uses a weighted-walk pumping
> lemma after the original reducible-slope argument failed. Do not restart a
> lane from this memo without checking
> the README failure ledger and its note.
>
> The later pressure audit also refutes the proposed pointwise `U(21/50)`
> split on the exact `k=19` feasible point: the maximum tested restricted ratio
> is `0.542601...`, not `<=0.42`. A separate exact multiscale genealogy audit
> is favorable in mass—zero increases among 756 tested diagonal tail rows—but
> is finite evidence on `k=12,...,19`, not a localization theorem. The rational
> common-weight search exactly classifies the finite burn-in at all seven
> thresholds. The floating `k=20` audit breaks every fitted margin but
> no qualitative cone or minimal start. Immigration improves at `t=.2,.3` but
> rises at `.05`. A direct exact audit now computes 116 density-martingale
> increments; all 108 at `j>=2` fit the post-hoc summable envelope
> `(1/2)(9/10)^j` from depth two, as does floating `k=20`. A uniform version
> would force `L1` compactness and localization, but an independently audited
> annealed projection/Perron research proof shows that this particular fit
> cannot be uniform for `1<lambda_k<=2`: the
> forced endpoint law has `Delta_2=622/1533>81/200`. A companion floating-log
> entropy audit finds decreasing selected profiles and the post-hoc envelope
> `(1/5)(3/4)^j`, but an exact positive `k=3` feasible vector with `h_2>h_1`
> refutes monotonicity on the full feasible cone, while the annealed floor
> `h_1>6431/39690>3/20` also closes the displayed entropy fit as an endpoint
> law. The replacement exact audit puts all 116 selected Pearson-energy rows
> below the finite calibration `chi_(k,j)<=6/j^2`. Polynomial energy/entropy
> control consistent with the annealed floor, or direct selected-family
> compactness, is the live seam; the expanding-window immigration/defect
> recurrence is the fallback. See
> `docs/notes/multiscale-genealogy.md`.

## 0. Ground rules

Ambition in action, calibration in claims. Every mathematical claim we advance
must be backed by a machine-checkable artifact: a Lean proof, or a finitely
verifiable certificate (a cycle, a checkable automaton, an exhaustive search
with stated bounds). Anything else is a conjecture and gets labeled as one.

External-review gate: claims we are about to lean on get independent external
review (GPT, key on file; use judiciously — only when a review preempts >30
minutes of work) AND internal verification; neither alone suffices (precedent:
the SMELL.md errata — external review killed one claim of ours, our check
killed one claim of the reviewer's).

## 1. Hard constraints any strategy must respect

1. **Logical form.** The conjecture is Π⁰₂. Unlike Π⁰₁ statements (Goldbach,
   RH-equivalents), independence would not imply truth. The split: "no
   nontrivial cycle" is Π⁰₁ (independence ⇒ truth); "no divergent orbit" is
   genuinely Π⁰₂ — a divergence disproof could itself be unprovable (Conway
   2013 exhibits an explicit 7-fraction FRACTRAN game, via Rickard, that never
   halts but unprovably so). No Π⁰₁-equivalent of the full conjecture is
   known; producing one would itself be a structural breakthrough.
2. **No uniform argument can work.** Conway 1972: generalized Collatz maps
   simulate arbitrary computation (even with all offsets b_i = 0); Kurtz–Simon
   2007: "every orbit reaches 1" for the generalized class is Π⁰₂-complete —
   the exact top of the hierarchy, so the class-level problem is maximally
   hard. Any proof must consume arithmetic specific to (2,3).
3. **Disproof shapes** (Lean: `Collatz.counterexample_shape`): divergent orbit
   or nontrivial cycle. Current squeeze: seeds < 2⁷¹ excluded (Barina, Jan
   2025); no m-cycles for m ≤ 91 and any nontrivial cycle has ≥ 2.18×10¹¹
   T-steps with > 1.375×10¹¹ odd terms (Hercher 2023 + Barina). A divergent
   orbit has no finite witness. The published Krasikov–Lagarias argument claims
   that one divergent orbit forces ≥ x^0.84 divergent seeds below x, but the
   successor audit found a gap in its printed advanced-term termination
   bridge. Lean commit `3d6a186` repairs the abstract elimination seam, and
   `331ff48` checks the literal family and P1/P2. Commit `729f5fa` checks
   D1--D3; commit `76ec861` checks the final exponent wrapper, so that crowding
   consequence is now established under the repo's mixed verifier policy. Independently,
   an orbit bounded below by C₀ forces positive
   density absorbed (Tao Remark 1.4). Counterexamples, if any, come in crowds
   — a disproof must be structural, not exhibitional.
4. **Why almost-all methods stall at almost-all.** Tao's own Remark 1.4:
   upgrading f(N)→∞ to a constant is "likely almost as hard as the full
   conjecture." The logarithmic measure is not T-invariant; iterating density
   results dumps mass into the exceptional set. Drift is exhausted at
   "almost all."
5. **Ergodic completion sees only noise.** On ℤ₂, T is conjugate to the full
   2-shift (parity-vector map Q∞; Lagarias 1985), strongly mixing for Haar.
   Collatz ⟺ ℤ⁺ ⊆ Φ((1/3)ℤ) (Bernstein 1994): a statement about where a
   Haar-null set sits inside a solved system. Proof structure must be
   invisible-to-Haar — i.e., genuinely arithmetic.
6. **No-go theorems for automated methods.** Zantema's 7-rule rewriting system
   (termination ⟺ Collatz) admits no natural-number matrix-interpretation
   termination proof in any dimension (Yolcu–Aaronson–Heule 2021). No infinite semilinear
   T-invariant set avoiding {1,2} exists (Monks 2006 corollary) — so any
   regular divergence certificate must be sparse and non-semilinear, or
   finite (= a cycle). The 2-automatic case is open; see §3.3 and §4.

## 2. Why the coefficient sandwich saturates (census data)

Census to N = 10^10 on akdeniz (experiments/fate.c; Brent cycle detection;
divergence proxy = exceeding 2^120; zero step-cap hits anywhere):

| map | reach 1 | other cycles | presumed divergent |
|---|---|---|---|
| 3x−1 | — | mins {1, 5, 17} only; basins 32.70/32.50/34.80% | 0 |
| 3x+1 | 100.000000% | none | 0 |
| 5x+1 | 0.0182% (min-1 basin) | mins {13, 17}: 0.0284%/0.0071% | 99.9463% |

In the coefficient family the only order parameter is drift; both neighbors
are themselves open in the worst case. The *proven* version of this
picture is Gonçalves–Greenfeld–Madrid 2021: Tao-type almost-all results hold
across the whole subcritical family C_{p,q,r} (q < p^{p/(p−1)}) — confirming
that drift-based methods see only the family-level structure, never the
specific point. Unexplained data: 3x−1 basin shares drift with height (min-1
basin 32.7% overall, 46.9% in the top block) — worth a look.

## 3. The machine-graded space of Collatz-like structures

Not coefficient space: a space of *machines computing the map*, graded by
complexity, Collatz as a limit point from several directions. "Distance from
Collatz" = complexity of the difference-machine.

### 3.1 From below: the carry/dependency tower T_w

The single Collatz step is already a 3-state transducer (carry ∈ {0,1,2}) on
LSB-first binary; the unbounded memory lives in the *iteration* — carry
cascades couple bit i of the t-th image to unboundedly lower bits of n. Over
F₂[x] the coupling is absent, and the function-field analogue is a solved
problem: every polynomial reaches 1, stopping time O(deg^1.5)
(Hicks–Mullen–Yucas–Zavislak 2008; refined by Alon–Behajaina–Paran 2024).
There is even a real-dynamics analogue with a *bounded* threshold on a co-null
set (Inselmann 2024) — outside integer arithmetic the hard part evaporates.
So define the tower by dependency range: T_w = the 3n+1 step with carries
assumed 0 beyond distance w (carry-lookahead truncation). T_w(n) = T(n) iff no
carry chain exceeds w; pointwise convergence, never uniform; each T_w is a
strictly local (sliding-window) map.

Caveats: (i) orbit behavior is not continuous under pointwise convergence —
the tower's value is **frontier-mapping, not limit-taking**; (ii) locality per
step doesn't guarantee decidability at any finite w (CA reachability is
undecidable in general). The BB-shaped bet: small-w levels fall to current
decider technology; where they stop falling is the measurement. Sharp
question: which certificates are semicontinuous in w?

### 3.2 From above: adversarial envelopes E_δ

Vary the quantifier, not the map: an adversary may replace the odd step by a
different affine branch within a budget (density-δ of steps / k total / only
in residue set R). E_0 = Collatz; full budget provably fails; the robustness
radius of (at least) the almost-all statements measures which structure is
load-bearing. First target: game value iteration on residue automata mod 2^k.

### 3.3 The certificate channel (BB decider port)

The step is a rational transduction, so the Collatz graph is an automatic
graph and the conjecture is a reachability statement in it; every *proposed*
regular certificate is decidably checkable (Büchi-arithmetic closure;
Bruyère–Hansel–Michaux–Villemaire 1994). Known structure of the finite
horizon is fully tame: stopping-time classes are congruence classes mod 2^k
(Terras 1976) and each bounded-odd-steps layer is 2-automatic
(Shallit–Wilson 1992; explicit regexps in Stérin 2020). The open part is
exactly the unbounded closure: is Pred(1) 2-automatic? does a sparse,
non-semilinear 2-automatic T-invariant set avoiding {1,2} exist? (Infinite
semilinear: dead by Monks 2006. Finite: the cycles problem.)

**Historical session snapshot (superseded by README):** no regular divergence certificate with ≤ 7
DFA states exists (LSB-first binary; exhaustive canonical enumeration: q≤4
83,968 / q=5 5.1M / q=6 379.6M / q=7 32.79B DFAs; verified searcher with
property-tested transducer and positive/negative controls; q=5,6 reproduced
independently on a second machine; the later q=8 run completed negative). Base-3
(MSD-first, independent channel per notes/two-bases.md): none with ≤ 5 states
(29.3B DFAs at q=5; searcher mutation-tested and OEIS-cross-validated). Next rungs, straight
from bbchallenge's arsenal (see LANDSCAPE.md §3.3 table): SAT-searched NFA
certificates (FAR) over the Yolcu–Aaronson–Heule mixed binary–ternary
alphabet; then weighted automata (WFAR) whose weights track ν₂/ν₃ valuations
— the class that could, unlike pure regularity, express drift. Known barrier
worth respecting: bbchallenge's arsenal fails precisely on drift cryptids
(individual-orbit parity statistics), which is the divergence side of
Collatz; the port's best expected yield is on the cycle/invariant side, plus
frontier cartography.

**Two-bases constraint** (`notes/two-bases.md`): via Cobham 1969 + a corollary
of Monks 2006, any divergence certificate recognizable in two multiplicatively
independent bases is finite and hence a nontrivial-cycle witness (elements
> 2⁷¹). So base-2 and base-3 certificate searches are provably independent
channels — and the base-3 search is now queued.

### 3.4 The Diophantine shadow

Cycles = integer points on explicit varieties indexed by parity words
(Böhm–Sontacchi); all cycle exclusions are continued-fraction + linear-forms
squeezes on these (Steiner → Simons–de Weger → Hercher). Two published levers
nobody has pulled: re-run Hercher's bootstrap at X₀ = 2⁷¹ (his input was
3·2⁶⁹), and the Rhin constant 13.3 in the linear-forms bound. Deformation
axis: continued-fraction convergents of log₂3 give exactly-solvable rational
approximant models converging to the multiplicative shadow; the carry tower
(§3.1) is the additive shadow; Collatz is the coupling.

### 3.5 Meta-theorem target: the undecidable collar

Conjecture (provable-looking): every mod-d-agreement neighborhood of T in
residue-affine map space contains maps with undecidable convergence (hide a
register machine in a thin residue class, riding Conway/Kurtz–Simon).
Formalizes "no uniform sandwich"; identifies the constraints whose removal
re-enables Turing-completeness — i.e., what a proof may consume. Note:
Kurtz–Simon has never been mechanized in any proof assistant; the Coq
FRACTRAN undecidability chain (Larchey-Wendling–Forster) is portable to Lean.
Serious target.

### 3.6 The fibered family over the parity shift (Cryptid coordinates)

The BB(6)/BB(7) frontier problems and Collatz are different bounded
functionals of the *same base object* — the parity symbolic dynamics of
×3/÷2-type arithmetic:

- **Antihydra** (BB(6) gatekeeper): H(n) = ⌊3n/2⌋ from 8; counter +2 on even,
  −1 on odd; halts iff counter hits −1. Equivalent to parity statistics of
  ⌊K(3/2)^n⌋ — the Mahler Z-number genre, open since 1968.
- **Hydra, Bigfoot, Space Needle**: same base dynamics, different functionals
  (mirrored boundary; mod-6 residue hit with a drifting counter; hitting a
  power of 2 through a ν₂-valuation functional).
- **Collatz**: subcritical base, functional = absorption at 1.
- **Solved contrast**: the BB(5) champion's map g(x) = (5x+18)/3, (5x+22)/3,
  ⊥ by x mod 3 — halting orbit finite from 0; but "halts from every x" is
  Aaronson's open Conjecture 22, the minimal *computation-generated*
  Collatz-sibling.

**Empirical family structure — now mapped** (full report with exact,
numerically-verified recurrences: `CRYPTIDS.md`). Headline findings:

1. **Universality of the base map.** Minimal hard machines in three different
   substrates (2-symbol TMs, 5-symbol TMs, FRACTRAN) independently converge
   on ×3/2-type parity dynamics (Antihydra/Hydra ⌊3n/2⌋; Bigfoot ×4/3 mod 6;
   Fenrir ×5/2; Lucy's Moonlight ×8/3 mod 3). Extremal computation *finds*
   this family without human choice — strong evidence the parity symbolic
   dynamics of small-rational multiplication is one canonical hard object.
2. **The discriminating axis is the functional, not the map.** Solved
   champions: halting = value in a fixed residue class (measure-1 event,
   finite certificate). Hard non-halting cryptids: an integrated
   parity-balance counter hitting an exact boundary against positive drift
   (halting prob. decays geometrically: (1/φ)^n for step-set (+2,−1), 2^{−n}
   for biased ±1). Hard "valueless" variants (Space Needle): exact hit of an
   exponentially thin set (powers of 2) — 2-adic valuation under addition.
   Hard *halting* cryptids (Lucy's Moonlight): drift toward the boundary,
   hardness migrates into the halting-time value (~10^2902 steps).
3. **Rigidity is the only exit.** Every machine ever moved from the hard
   column to the solved column went via discovered algebraic rigidity:
   eventual exact periodicity (Skelet 1), a structured counter with provable
   invariant (Skelet 17, Gray code), or a closed form making residues
   eventually periodic (BMO 3/4/7). No analytic/probabilistic argument has
   ever closed one.
4. **Conspicuous gap:** the wild sample contains no critical/zero-drift
   cryptid. The frontier avoids criticality; Collatz (subcritical,
   all-seeds) and the cryptids (supercritical, single-seed) occupy opposite
   corners of (drift sign) × (seed quantifier), evaluating the same
   deviation-from-equidistribution object.
5. Partial negative structure exists: Antihydra's parity sequence is provably
   **not Sturmian** (via Dubickas 2009) — the only rigidity class excluded
   so far. Michel's "with parameter" taxonomy (finite automaton riding the
   arithmetic) contains a solved 2→3-with-parameter machine — the Hydra base
   map on the halting side, 17 years earlier.

Family coordinates (empirically instantiated): multiplier p/q; branch
alphabet/measure; functional type (residue membership / counter boundary /
thin-set hit / halting-time value); drift sign of the halting observable;
counter step-set; presence of rigidity. Consequences: (a) parity-control
techniques transfer across the whole family — Bigfoot (cleanest: biased ±1
walk, P(halt)=2^{−(a+1)}) is the right first attack target, not Collatz;
(b) point 3 says the *search for rigidity* (conjugacies to counters, closed
forms mod m — automatable!) is the proven-productive move, which is exactly
what our certificate searches mechanize; (c) point 4 marks "critical drift"
as unexplored territory where new structure may be visible.

## 4. Artifact status

- **Lean** (`formal/Formal/Collatz.lean`, sorry-free, builds): statement;
  positivity; powers of 2; descent reduction; fueled-checker soundness +
  `native_decide` verification to 10⁴; only-trivial-cycle-through-verified;
  certificate principle (`not_conjecture_of_invariant_set`); bounded ⇒
  eventually periodic; `counterexample_shape`.
- **Census** (`experiments/fate.c`, `results/akdeniz/`): §2 table; zero
  anomalies across 3 × 10^10 orbits.
- **DFA certificate search** (`experiments/dfacert/`): verified searcher
  (transducer property-tested against __int128 arithmetic; closure checker
  validated on controls; enumeration cross-checked against published ICDFA
  counts). Current result: no certificate through q=8; the old q=7 and q=8
  jobs are complete and no DFA writer is running.

## 5. Lean roadmap

0. **Align definitions with ccchallenge.org** (the new bbchallenge-style
   Collatz formalization effort; 371 papers tracked) and formal-conjectures'
   canonical `collatz_conjecture`; contribute rather than fork. Audit-watch:
   the claimed Tao formalization (gotrevor/tao-collatz) pends statement audit.
1. Syracuse map + parity vectors + Terras congruence structure (elementary,
   missing from mathlib — mathlib has zero Collatz).
2. Verified certificate checker: "DFA A passes closure checks ⇒ ¬Conjecture",
   instantiating `not_conjecture_of_invariant_set` — makes any future
   certificate discovery an immediate formal disproof. Then the FAR/WFAR
   verifier (≈ small linear algebra, busycoq's search/verify split).
3. Böhm–Sontacchi cycle equation; Hercher-style bounds with linear-forms
   input as flagged hypothesis; re-run bootstrap at 2⁷¹ (publishable, §3.4).
4. Kurtz–Simon mechanization via the Coq FRACTRAN chain (§3.5).
5. T_w definitions + T_0 solvability as the first tower rung (§3.1).

## 6. Landscape

See `LANDSCAPE.md` (28k chars, fully sourced): hard constraints, exact
state-of-the-art table, BB decider-technology port table, automata/p-adic
structure, formalization landscape, and a ranked 10-item action list. Raw
domain briefs (7, JSON with per-fact sources) in `landscape/`.

## 6b. Cracks hunt (see CRACKS.md — 17 ranked, briefs in cracks/)

Top-5 play-out queue with first moves (full detail in CRACKS.md §2):
1. **Mahler–Cartier rigidity** (virgin junction): Lemma 0 note (normalization
   + bi-Mahler exclusion corollary — verified by hand, folded into
   notes/two-bases.md); then the quantitative 2-Mahler-annihilator exclusion
   computation against the 2⁷¹ frontier; Galois track via
   Dreyfus–Hardouin–Roques. Jackpot: "no 2-Mahler certificate" ⟹ subsumes
   all DFA exhaustions at once.
2. **Termination-order barrier ladder**: a provisional arctic (max-plus)
   unary-`Z` no-go candidate survives after replacing a false reducible-slope
   argument with weighted-walk pumping. It is an analogue of YAH's unary-`Z`
   natural-matrix results, not closure of their explicit mixed-base-`T`
   challenge; self-embedding rung is free.
3. **Exponential sums at the cycle modulus**: ⟨2⟩-orbit symmetry lemma +
   32-core transfer-matrix atlas of |S_{K,L}(ξ)|; the reduction theorem
   "square-root cancellation ⇒ cycle finiteness" is the only known
   cycle-attack orthogonal to Baker.
4. **Carries spectral chain**: prove det(xI−K_{m,2}) = (x−1)∏_O(x^{|O|}−2^{−|O|})
   — answers a question Diaconis–Fulman explicitly left open; numerically
   verified already by the brief.
5. **Constrained JSR / path-complete (SOS) certificates**: homogeneous
   impossibility lemma (negative 2-adic cycles force naive JSR ≥ 3/2), then
   cone-constrained SOS sweep on mod-2^k lifts — the analytic dual of our
   DFA exhaustion.

Recorded no-gos worth citing (each provable today; CRACKS.md §3): O₂
K-theory/ideal blindness; behavioral-metric degeneracy; mod-2^n blindness to
divergence (De Bruijn fullness); growth-based proof-theoretic unprovability
structurally inapplicable (stopping times are ~log n, not fast-growing).

## 6c. Smell search (keyword-blind; see SMELL.md, briefs in smell/)

Headline: **the Krasikov–Lagarias method is a nonlinear Perron eigenproblem**
(Gaubert–Gunawardena / Collatz–Wielandt — Lothar Collatz's own theorem), and
policy/power iteration extends their 20-year-old table. The solver reproduces
all published values `k=2..11`; exact-rational certificates now pass through
`k=19`, with `γ₁₉=0.9094372617…`. The finite counting implication is
kernel-checked generically; the exact `k=12` record is now also one Lean theorem,
while the `k=19` rows remain externally exact-verified rather than Lean-ingested.
The theorem-grade open step is the limit
`λ_k→2`, not another fixed-level feasibility check.
The newest exact diagnostic separates pointwise and mass contraction: the
prepared uniform `U(21/50)` split fails, while all 756 tested within-vector
genealogy tails are nonincreasing. Exact rational cones classify the observed
high-bin matrices at all seven thresholds. The floating `k=20` candidate
exceeds every fitted margin while remaining below one at every same-start
maximum; the tracked `t=.2,.3` terminal-offset immigration values also
continue downward, while offsets one through four rise at `t=.05`. The sharper
martingale diagnostic has 116 exact increments, with all 108 at `j>=2` inside
a simple post-hoc summable depth envelope; floating `k=20` remains inside it.
The selected entropy profiles also fit a post-hoc geometric envelope, but
feasibility-only depth monotonicity is exactly refuted at `k=3`. An audited
annealed-floor research proof additionally shows that neither fitted geometric constant can be
the all-level critical/vanishing-slack law. The exact replacement diagnostic
certifies `chi<=6/j^2` on all 116 selected rows; the live problem is to prove
polynomial energy/entropy control consistent with the annealed floor, or direct
compactness for an all-level selected critical or normalized-slack-vanishing
family. The cone/immigration theorem is now the fallback, not another finite
fit.
Also top-ranked (SMELL.md §1): Mahler 1968 Z-numbers ↔ Antihydra rarity
theorem (golden-ratio counting via no-11 subshift); Antihydra as a robust-
queueing/discrepancy problem, with the former unconditioned finite-computation
lottery ticket closed because `m_k=k`; powers-Presburger decidability tracing
the m-cycle frontier (KLNOW SODA 2025); constrained-JSR multinorms collapsing
to scalar-weight LPs (Karp cycle mean) — the weighted certificate search at
10^6 states; Bartholdi automatic-actions pumping → ω-regularity no-go target
subsuming all DFA exhaustions. Fourteen dead ends recorded in SMELL.md §4 —
do not re-search those.

## 6d. Reverse-mining bbchallenge (see REVERSE-MINING.md, briefs in reverse-mining/)

34 techniques translated into standard mathematics; 2 judged plausibly-new
(context-universal shift-template certificates — eventual periodicity certified
polylog in the preperiod, number-free; and the measured certificate-rank census
over program space), ~20 "known-math-with-new-twist" where the bridges to
established theory (odometers/Bratteli–Vershik, path-complete barriers,
porous invariants, Medvedev lifts, Martin-Löf tests) exist on neither side.
Strategic consequences adopted:

1. **Certificate search redirect**: stop blind DFA state-count exhaustion after
   q=8; switch to (a) principled congruence-generator families (mod-3^k towers,
   carry automata, cache-policy folds — FAR universality says the congruence
   IS the certificate), and (b) the dim-2 WFAR: integer weight pairs (odd
   steps, halvings) making 3^a/2^b additive, polyhedral accept sets, Farkas
   witnesses, SAT-modulo-difference-logic synthesis. Convergence note: the
   smell search independently arrived at the same object from control theory
   (multinorm scalar collapse → Karp cycle-mean LPs). Two literatures, one
   tool; build once.
2. **Free negative theorem**: order-n SFT/window certificates are provably
   blind to Collatz (mod-2^n dynamics is the full De Bruijn shift) — never
   spend compute there.
3. **Porous invariants** (Ouaknine et al. CAV 2021, explicitly motivated by
   Collatz-like loops) × bbchallenge rule tables: the fusion most likely to
   mechanize new cryptid partial results (their UNPROVEN_PARITY failures).
4. **Critical-drift experiment protocol** exists in the wild: cryptid breeding
   ("Mother of Giants") = one-cylinder perturbation families sweeping stopping
   times over 10^10000 range; fit exp(c/|drift|), plot the phase diagram the
   community never drew (feeds experiments/family/).
5. **Certificate-rank framing**: our q≤8/q≤5 negative results are measurements
   of Collatz's rank in a now-mapped hierarchy; the Skelet-10 lesson says try
   re-coordinatization (rational-base 3/2 numeration) before concluding
   trans-regular rank — queue an AFS-numeration DFA search.

## 6e. Results ledger (2026-07-20, session 1; historical snapshot)

**Status warning.** This section records the first-session ledger. The current
state is in `README.md`; in particular all jobs named below are stopped, and
the k=19 exact certificate supersedes the k=18 headline.

1. **EXACT FINITE CERTIFICATE; COUNTING CONSEQUENCE NOW ESTABLISHED:** the k=19
   feasible point gives `π_a(x) ≥ x^γ` eventually for every fixed
   `γ < 0.9094372617`, `a ≢ 0 mod 3`, `x ≥ x₀(a)`, improving the 2003 KL record
   0.84. Levels k=12..19 pass exact integer verification, falsification
   controls, and SHA-256-pinned checks (`experiments/kl/RESULT.md`), but the
   successor audit invalidates the published advanced-term termination bridge,
   and a later exact `k=2` audit refutes printed equation (2.1). Lean commit
   `3d6a186` supplies a checked occurrence-aware retarded witness and abstract
   comparison. Commit `729f5fa` proves D1--D3 for the literal family of commit
   `331ff48`, and `76ec861` formalizes the useful one-sided all-target transfer.
   The displayed counting bound is therefore established, with the explicit
   caveat that the k=19 sidecar is checked by exact Python rather than imported
   into Lean. The sidecar is local and ignored by git; k=20 never became a certificate.
   Pre-registered dichotomy fits (notes/kl-limit-object.md): data favor
   γ_∞ near 1 (branch A ⟹ x^{1−ε} counting), γ_∞ ≤ 0.95 disfavored ~9–30×;
   exact oscillation law s(λ_k)−1 = (λ^{α−2}+λ^{α−1})δ_k proved (Thm 3.2).
2. **THEOREM (proved, exactly verified): the DF multiplication-carries spectrum**
   det(xI−K_{m,b}) = (x−1)∏_O(x^{|O|}−b^{−|O|}), gcd(m,b)=1 — answers
   Diaconis–Fulman §5.2's open question; + exact K^L and TV formulas.
   notes/carries-spectrum.md. Syracuse corollary: exact 2^{−r} window
   decorrelation under Haar (honest caveat: ℤ⁺ is null).
3. **THEOREM (proved, symbolically verified): Lemma 0** — BM equation ⟺
   aₙ = a_{T(n)}; kernel = component space; bi-Mahler exclusion for exotic
   components (analytic upgrade of the two-bases note).
   notes/mahler-cartier-lemma0.md.
4. **Negative results (exhaustive, cross-validated): no regular divergence
   certificate ≤ 8 states (base 2), ≤ 5 states (base 3).**
5. Census + atlas data: fate census 3×10^10; expsum K≤22 (sqrt cancellation
   typical, 3-power major arcs extremal); family phase diagram (ganesha,
   only the landed partial state is retained; critical/grid3 was stopped).
6. Strategy corpus: LANDSCAPE, CRACKS (17), SMELL (93 finds + errata),
   REVERSE-MINING (34 translations), CRYPTIDS; arctic no-go pre-think
   (notes/arctic-prethink-gpt.md, strategy positive).

## 7. Historical experiment queue (do not execute as a live queue)

This was the first-session queue. It is preserved for provenance, not current
authorization or status; consult the README living map before reviving any item.

1. dfacert q=7/q=8 (now complete negative); preserve the exact artifacts.
2. FAR/SAT-searched NFA certificates on the YAH alphabet (§3.3).
2b. Base-3 (MSD-first) DFA certificate search — provably independent channel
   (`notes/two-bases.md`); then base 6.
3. Tao's c_n recursion to large n; numerical test of β = 1 (his
   equidistribution conjecture; cheap, high-information — LANDSCAPE #4).
4. Hercher bootstrap at X₀ = 2⁷¹ (LANDSCAPE #2).
5. T_w implementation (w = 0..3): census + exhaustive automata analysis.
6. Adversarial game value iteration mod 2^k.
7. Cryptid family table → coordinates for §3.6 (agent pending).
8. 3x−1 basin-share-vs-height structure (§2).
9. Design and study a **critical cryptid** (zero-drift halting observable) —
   the empirically empty point of the family (§3.6 finding 4); criticality
   is where scale-invariant structure should be visible.
10. Play-out queue from the cracks + smell-search syntheses (pending).
