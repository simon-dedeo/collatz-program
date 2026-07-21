# Smell-Search Synthesis: Keyword-Blind Mathematics Bearing the Collatz Signature

> **CURRENT STATUS OVERRIDE (2026-07-21).** This document is a historical
> research snapshot. The finite feasible certificates remain exact, but the published advanced-elimination
> proof has three checked defects and its equation (2.1) has the exact
> counterexample `φ^7_2(1)=3≠2=φ^{14}_2(0)`. Commit `58f0ef8` checks the
> targetwise one-sided correction and ordinary-count transfer. Lean commit
> `3d6a186` checks the corrected retarded witness and abstract comparison;
> `331ff48` defines the literal predecessor family and proves P1/P2, and
> `729f5fa` proves its D1--D3 base system. Commit `76ec861` closes the fixed-
> target/all-target exponent wrapper. The `k=19` counting result is established
> under the mixed exact-Python + kernel-Lean trust policy, but the large record
> is not yet one Lean-native artifact. See `README.md`,
> `experiments/kl/RESULT.md`, and `experiments/kl/TERMINATION_AUDIT.md`.
>
> A later exact pressure audit refutes the prepared pointwise `U(21/50)` split
> at `k=19` (`0.542601...>0.42`). The successor mass-genealogy audit is more
> promising but still finite: all 756 equal-threshold adjacent-scale tails for
> the eight `k=12,...,19` feasible subeigenvectors are nonincreasing, with 619
> strict nonsaturated decreases. Rational weighted-bin cones close exactly
> after exactly classified finite burn-ins; the floating `k=20` audit then
> exceeds every fitted margin but no qualitative cone or minimal start. The
> `.2,.3` immigration signal is favorable but the `.05` offsets rise. All 116
> exact density-martingale increments fit a post-hoc summable depth envelope
> from `j=2`, and floating `k=20` does too. Proving an all-level envelope is the
> live question; expanding-window contraction plus terminal-offset
> immigration/defect decay is the fallback, not
> another assertion of the false pointwise bound. See
> `docs/notes/multiscale-genealogy.md`.

> **ERRATA & external verification (2026-07-20, from independent GPT review +
> our follow-up checks — see gpt_sol_feedback.txt):**
>
> 1. **#1 (KL record).** (a) Orientation: the feasible side of the system as
>    implemented is c ≤ F_λ(c) (growth rate ≥ 1, decreasing in λ; threshold at
>    r = 1) — the "r(F_λ) ≤ 1" wording below is reversed relative to the code;
>    the certification agent has been instructed to take the direction from
>    KL's paper itself. (b) The 4-step to-proof list (equivalence, Perron
>    hypotheses, exact certificate, careful Thm 2.2 invocation) matches our
>    running certification plan. (c) Prior-art scare resolved: arXiv:2512.13760
>    v1 (Dec 15, 2025) claimed x^0.946 but was self-revised two days later to
>    x^0.3227 — below the record; math.GM, no affiliation. Record framing
>    stands, pending our certification.
> 2. **#2 (Mahler).** Corrections accepted: Mahler proves ≤ x^0.7 (the
>    Fibonacci count gives O((log x)·x^{log₂φ}) — a log factor remains);
>    the double-convergence series is S_m = Σ_j ε_{m+j}(2/3)^j (ratio 2/3,
>    NOT (3/2)^m), = 3r_m in ℝ and = −3g_m in ℚ₂; "same machine" means
>    structural similarity, not survivor-set equivalence. The first move
>    (cylinder-residue bijection) was externally validated — reviewer sketched
>    the proof via invertibility of 3 mod 2^k.
> 1b. **#1 (KL record): HISTORICAL CLAIM, SUPERSEDED AS END-TO-END
>    CONFIRMATION (2026-07-20 evening).**
>    Exact-rational feasible points at k = 12, 13, 14 verified in pure integer
>    arithmetic against KL Thm 2.2 (experiments/kl/cert_k*.json; THEOREM.md,
>    RESULT.md); gpt-5-pro adversarial review of the full chain returned
>    VERDICT: CONFIRMED (gpt_review_result.md); that verdict is now superseded. The exact
>    finite statement is LP feasibility at the displayed λ; the then-claimed
>    consequence `π_a(x) ≥ x^γ` for every fixed
>    `γ < log₂(18307718/10⁷) = 0.8724519…` is now recovered by the repaired
>    trust chain described in the status override above.
> 1c. **Crack 3 empirical sharpening** (expsum atlas, K ≤ 22 exhaustive): the
>    brief's ⟨2⟩-orbit symmetry claim |S(2ξ)|=|S(ξ)| is FALSE (the true
>    relation is the intertwining S(2ξ) = S₀(ξ) + S₁(3ξ); only conjugation
>    symmetry holds). Typical ξ shows textbook square-root cancellation
>    (mean|S| ~ C^0.471, R² = 0.9999); the max decays slowly and its argmax
>    sits on 3-power major arcs (ξ ≈ jM/3^t) — so a uniform-power-saving
>    theorem only needs to beat the 3-adic major arcs, exactly Tao's
>    skew-walk regime.
> 3. **#3 (Antihydra lottery ticket): WITHDRAWN.** m_k = k for all k,
>    trivially: 1 is an odd fixed point of ⌊3n/2⌋ and the length-k parity
>    itinerary is bijective on residues mod 2^k, so the all-odd word always
>    occurs — the unconditioned window computation is vacuous (our own text
>    contained the caveat; the "lottery ticket" framing was wrong). What
>    survives: halting ⇒ O_n − n/2 ≥ n/6 + O(1) (linear discrepancy, the real
>    content); queueing/network-calculus machinery converts proven window
>    bounds into certificates but cannot source them; unbalance ≠ density
>    excess (first-passage analogue must be proved separately); "balanced
>    drivers never halt" needs a prefix condition. Salvage: seed-specific
>    finite-state abstractions with max cycle mean < 2/3 — i.e., this lane
>    merges into PQ-3's occupation-measure/certificate program.

Ranking metric: **(collatz-blindness) × (tightness of hypothesis-match) × (concreteness of transfer)**. Temperature scale as used by the hunters: **cold** = verified, low-risk, hypotheses checked; **warm** = real match with honest gaps; **hot** = speculative but high-payoff. Three independent agents converged on Mahler 1968 and two on max-cycle-mean certificates — convergences are flagged, since they are the strongest signal the smell is real.

---

## 1. Ranked Shortlist (Top 8)

### #1. Nonlinear Perron roots and the Krasikov–Lagarias finite systems — finite transfer checked, limit open **[warm; highest payoff on the board]**
**Refs:** Gaubert–Gunawardena, *Perron–Frobenius for homogeneous monotone functions*, TAMS 2004 — https://www.ams.org/journals/tran/2004-356-12/S0002-9947-04-03470-1/ ; Biggins, *Spreading speeds in reducible multitype BRW* — https://arxiv.org/abs/1003.4716 ; Biggins–Sani 2005 — https://www.cambridge.org/core/journals/advances-in-applied-probability/article/convergence-results-on-multitype-multivariate-branching-random-walks/1387982E5A820FA5D1F2376CA25F97C4

**Theorem.** For monotone, homogeneous-degree-1 maps F (any min/max of nonnegative linear maps), a nonlinear spectral radius exists with the Collatz–Wielandt formula r(F) = inf_{x>0} max_i F(x)_i/x_i, computable by power/policy iteration with certified two-sided bounds. (The "Collatz" here is Lothar Collatz 1942 — the man himself, in a blind paper.) Biggins supplies the multitype-BRW front formula: count exponents are Legendre transforms of log Perron roots of tilted mean matrices.

**Match & gaps.** KL's "sup λ with L_k(λ) positively feasible" is *exactly* the threshold of the min-type (adversarial lost-3-adic-digit) tilted system on residues mod 3^k, with the feasibility orientation calibrated in the erratum above. Exact certificates now extend the table through `k=19`, where `γ₀=log₂(18783127/10⁷)=0.9094372617…`; the repaired mixed Python/Lean chain transfers every fixed smaller exponent to ordinary predecessor counting. Annealed (mean-refinement) value is exactly 2 at every k: the whole finite-k-vs-1 gap is quantified as adversarial-vs-average 3-adic refinement. The live gap is the limit `λ_k→2`, not finite feasibility or counting transfer.

**Transfer.** (i) Exact feasibility now implies `π_a(x) ≥ x^γ` eventually for
every fixed `γ<log₂λ` through the repaired KL trust chain. (ii) The k→∞ increments
empirically probe λ_k→2 (⇔ x^{1−ε} counting through the now-checked transfer)
vs stall — either is a structural theorem about the limit of the entire
difference-inequality method; the limit object (min-type transfer operator on
Z_3 driven by the ergodic isometry x↦2x, annealed value exactly 2) is a new
attack surface.

**First move.** Prove a cofinal exact feasible sequence tending to two, or the
non-autonomous pressure/localization statement that yields one. In parallel,
import the `k=12` record as a chunked kernel-reduced Lean certificate before
attempting the multi-gigabyte `k=15–19` sidecars.

---

### #2. Mahler 1968 Z-numbers — the same machine, with a proven golden-ratio counting theorem **[cold transfer; triple-independent find]**
**Ref:** Mahler, *An unsolved problem on the powers of 3/2*, J. Austral. Math. Soc. 8 (1968) — https://ems.press/content/book-chapter-files/27426 (found independently by three agents; blindness grep-verified, predates the Collatz literature).

**Theorem.** x is a Z-number if {x(3/2)^n} ∈ [0,1/2) forever. Then the integer parts obey g_{n+1} = (3g_n + parity)/2 = **ceil(3g/2)** — the mirror conjugate (n↦−n) of Antihydra's floor(3n/2); confinement forces the parity itinerary into the golden-mean subshift (no factor 11); surviving residue classes mod 2^t number Fibonacci(t+1); hence ≤ x^{log₂φ} ≈ x^0.7 Z-numbers below x. Bonus device: one series Σ ε_m(3/2)^m converges in ℝ *and* 2-adically, pinning the seed in both completions.

**Match & gaps.** Verbatim our map family; Mahler's break-off algorithm (iterate (3/2)^{a_k} with exact 2^{a_k}‖H_k valuation extraction, die when the divisibility fails) is on its face the **Space Needle** value+v₂ dynamics. The φ in his count is the *same* φ as the (1/φ)^n Antihydra heuristic — but derived from a window constraint (no-11 transfer matrix), not the ruin walk; the bijection between word classes is plausible, **not established**. Load-bearing gap: Mahler confines a pointwise fractional part; Antihydra constrains a cumulative ballot sum — pointwise confinement kills entropy instantly, drift-positive ballot survival does not. Caveat: Lagarias's bibliography lists Mahler, so the *link* is known-but-unexploited; the counting transfer is genuinely undone.

**Transfer.** (i) Cylinder-residue bijection for floor(3n/2) (Terras analogue) ⇒ for any subshift constraint L, #{seeds n ≤ 2^k with itinerary in L} = |L_k|. (ii) With L = "counter in [−1,C] forever": **#{n ≤ x whose Antihydra counter stays windowed for log₂x steps} ≤ x^{θ(C)}**, θ(C) < 1 explicit, → log₂φ = 0.694 as C→1 — the first rigorous rarity theorem behind a cryptid heuristic. (iii) Port the real/2-adic double convergence to characterize infinite survivors (countable-or-dimension-θ).

**First move.** Prove the cylinder-residue bijection (half a day, numerically verified first); transfer-matrix entropy computation for h(C).

---

### #3. Antihydra as a Lindley walk: exact discrepancy thresholds; finite lottery ticket withdrawn **[cold conversion, open arithmetic input]**
**Refs:** Bandi–Bertsimas–Youssef, *Robust Queueing Theory*, OR 2015 — https://www.mit.edu/~dbertsim/papers/Robust%20Optimization/Robust%20Queueing%20Theory.pdf ; Le Boudec–Thiran, *Network Calculus* — https://leboudec.github.io/netcal/latex/netCalBook.pdf ; van der Laan thesis (unbalance comparison) — https://pub.math.leidenuniv.nl/~tijdemanr/proefschriftvanderlaan.pdf

**Theorem.** BBY Eq.(12): the worst-case Lindley functional over all input words satisfying one-sided windowed partial-sum constraints is given exactly, with the extremal path explicit; uniform bounds in n (Thm 2). Network calculus: arrival-curve constraint + service curve ⇒ backlog ≤ sup_s{α(s)−β(s)}, deterministic, and certificates **compose** under (min,+) convolution. Van der Laan/Altman–Gaujal–Hordijk: waiting-time functionals are multimodular, minimized by balanced (Sturmian) words, with performance gaps sandwiched by the word's **unbalance**.

**Match & gaps.** Antihydra halts iff the +2/−1 counter (a Lindley sup-functional of the parity word) hits −1 against drift +1/2; halting at n forces odd-density ≈ 2/3 — a *linear* one-sided windowed discrepancy. The math is deterministic optimization and transfers exactly. Gaps: proving any arrival curve for the actual orbit from seed 8 is the open core (the theorems convert the problem, they don't solve it); unbalance theorems control long-run averages, not first passage — the first-passage analogue must be proved; and if the parity map is bijective mod 2^k, the unconditioned window maxima m_k are trivial.

**Transfer.** The surviving target is an explicitly constanted statement that
halting at time `n` forces a linear one-sided prefix discrepancy. Converting
that into an unbalance theorem or a density-one corollary needs a separate
first-passage argument. A bounded-remainder *prefix* condition would prevent
halting; asymptotic density `1/2` alone does not.

**Withdrawn first move.** The proposed unconditioned maximum satisfies
`m_k=k` for every `k`, because the all-odd itinerary occurs. Do not rerun that
search. The live version is seed-specific: synthesize a finite-state
abstraction with maximum cycle mean below `2/3`, or prove the required prefix
discrepancy directly.

---

### #4. Presburger + 2^N + 3^N: the decidability frontier that traces the m-cycle frontier **[cold]**
**Ref:** Karimov–Luca–Nieuwveld–Ouaknine–Worrell, *Presburger Arithmetic Expanded with Powers*, SODA 2025, arXiv:2407.05191.

**Theorem.** The existential fragment of ⟨Z; 0,1,<,+,2^N,3^N⟩ is **decidable** (engine: Matveev-effective Baker linear forms in logs); full FO with two multiplicatively independent powers is undecidable already at 2 quantifier-alternation blocks (Hieronymi–Schulz).

**Match & gaps.** The fixed-shape m-cycle equation n(2^K − 3^L) = Σ 3^{L−1−i}2^{a_i} is a *single existential sentence* in this theory ⇒ decidable per shape — and the decision procedure's tool (Baker) is **literally the same tool** Steiner/Simons–de Weger/Hercher use; two literatures computing the same objects unknowingly. The full cycle problem (quantify over shapes) crosses into the undecidable region — precisely mirroring why cycle exclusion stalls at bounded block-count. Gap: composition with Leroux–Sutre flattening (finite path schemes for ≤k parity blocks) is blocked in plain Presburger by the infinite monoid {3^i}; the powers-extension is exactly the escape hatch, and nobody has performed the synthesis.

**Transfer.** (i) For every fixed k, k-block Collatz cycle-existence/reachability is decidable via flatten → powers-Presburger query per pattern. (ii) Frontier conjecture worth stating as a theorem: **the m-cycle exclusion frontier coincides with the existential/2-alternation decidability frontier** of two-power Presburger — a structural explanation of where and why cycle bounds stall.

**First move.** Hand-derive φ_1 (Steiner's 1-cycle), verify it is a legal existential sentence, trace one round of the KLNOW procedure and watch Steiner's linear-forms bound drop out.

---

### #5. Constrained-JSR multinorms collapse to scalar weights: the DFA search becomes an LP at millions of states **[cold]**
**Refs:** Philippe–Essick–Dullerud–Jungers — https://arxiv.org/abs/1503.06984 (converse Lyapunov companion https://arxiv.org/abs/1410.7197); Ahmadi–Jungers–Parrilo–Roozbehani path-complete — https://arxiv.org/abs/1111.3427 ; marginal ρ=1 boundedness: Philippe–Millerioux–Jungers — https://arxiv.org/abs/1512.04887

**Theorem.** For automaton-constrained switched linear systems, CJSR < 1 ⟺ existence of a multinorm (one norm per automaton state, contraction per edge); quadratic hierarchy asymptotically tight; converse Lyapunov makes the family complete relative to the abstraction. At ρ=1, decidable sufficient boundedness conditions exist (nodal irreducibility) — inapplicable to our triangular pair, but the triangular specialization plausibly admits a bespoke complete decision procedure.

**Match & gaps.** Collatz's linear parts are the *scalars* 1/2 and 3/2, so all quadratic templates collapse to one positive weight per automaton state, and feasibility ⟺ **max cycle mean of log-weights < 0** (Karp's algorithm) — an LP feasible at millions of states vs our exhausted 7-state membership search. Proven no-go en route: any abstraction carrying only mod-2^m information admits every parity word (Terras), has constrained JSR 3/2, and can never certify anything — **weights must be indexed by value-reading (base-2 transducer) states**. Gap: affine offsets pin ρ ≥ 1 on the homogenized lift; certificates target the scalar part plus offset summability (the triangular ρ=1 theory is the right home).

**Transfer.** Upgrade membership certificates ("invariant regular set") to **convergence certificates** ("every orbit entering regular set X is ultimately bounded, hence lands in a computable finite set"), complete relative to the abstraction; infeasible automata yield Legat–Jungers–Parrilo dual occupation measures (https://arxiv.org/abs/1710.01814) that localize exactly which cycle statistics block certification.

**First move (one afternoon).** In the existing ≤7-state enumeration harness, replace the exact-invariance check with Karp max-cycle-mean over the product automaton (weights log(3/2)/log(1/2)); rerun. Every automaton that failed as an exact invariant but has all reachable cycles below odd-density log2/log3 becomes a valid quantitative certificate.

---

### #6. Divergent tails live in a "hole at 0" survivor set with Sturmian extremal words **[warm]**
**Refs:** Kalle–Kong–Langeveld–Li — https://arxiv.org/abs/1803.07338 ; Allaart–Kong entropy plateaus, arXiv:2304.06892; Sun–Li–Ding Lorenz-with-hole — https://arxiv.org/abs/2311.02465 ; exact entropy via Lu–Steiner–Zou — https://arxiv.org/abs/2509.04227

**Theorem.** For β-transformations/Lorenz maps with a hole at the critical point, the survivor-set entropy/dimension in the hole parameter is a devil's staircase with completely characterized plateaus; lexicographically extremal survivors at criticality are rotation (Sturmian) words; Lu–Steiner–Zou give the two-base-weighted entropy/dimension from one transcendental equation.

**Match & gaps.** Elementary derivation (the agent's own, the missing lemma): a divergent orbit attains its minimum > 2^71 (Barina); from the minimum on, the itinerary walk satisfies S_k ≥ −δk with δ = 1/(3·2^71) — a uniform one-sided **hole-at-0 survivor condition** Σ_δ for the two-slope (log 2, log 3/2) system. Extremal surviving words are Sturmian of slope log2/log3, i.e. the **same CF convergents (5/8, 12/19, 53/84…) that drive Simons–de Weger cycle bounds, now appearing for divergence**. Gaps: published theorems are for interval maps, Σ_δ is a walk survivor set — only the symbolic kneading machinery transfers; positive dimension says nothing about meeting ℕ; the naive ball-hole and liminf-density framings are provably wrong (see dead ends) — the orbit-minimum reformulation is the unique correct one.

**Transfer.** Compute h(Σ_δ) exactly; compute the 2-adic points of the extremal words mod 2^k ⇒ **congruence classes mod 2^k that any near-critical divergent orbit must enter** — strictly finer than the log2/log3 density bound.

**First move.** Write and verify the half-page tail lemma; then run the plateau machinery on the two-slope system.

---

### #7. No sofic model anywhere on the β = 3/2 fiber — the caricature-level integrality obstruction **[cold for the lemma; hot for the bridge]**
**Refs:** Bruin–Carminati–Kalle — https://arxiv.org/abs/1610.01872 ; Bruin–Carminati–Marmi–Profeti — https://arxiv.org/abs/1707.07488 ; Li–Sahlsten–Samuel–Steiner — https://arxiv.org/abs/1709.08035 ; Sun–Li–Ding — https://arxiv.org/abs/2211.15239

**Theorem.** Matching in constant-slope affine families forces the slope to be an **algebraic integer** ("matching cannot hold for any non-integer rational s" — the flagship non-integer rational being 3/2); SFT/sofic kneading forces monic integer relations; SFT parameters are dense in the (β,α) plane but the 3/2 fiber contains none, and Pisot slopes cannot accumulate at 3/2 (Pisot set closed).

**Match & gaps.** The Collatz circle caricature x↦(3x+δ)/2 mod 1 *is* the β=3/2 fiber; the failure mechanism (3^m ≡ 1 mod 2, never 0) is the caricature shadow of the coprimality blocking Collatz cycles. Solvable windows accumulate at the fiber only **transversally** (must move the slope). Gap, flagged hard: the bridge from "no sofic interval model" to "no regular base-2 divergence certificate" crosses the LSB-first/MSB-first transpose seam and may fail; step (i) alone is publishable.

**Transfer.** Theorem to prove: **for every α, Ω_{3/2,α} is not sofic** — eliminate α between the two eventual-periodicity relations (resultant), show the resulting polynomial in β is monic, contradict 3/2 not an algebraic integer. Then attempt the bridge to base-2 DFA certificates via the transpose/base-conversion correspondence (Sterin–Woods machinery in our library).

**First move.** CAS-verify monicity for all small period/preperiod pairs. This is a clean **Lean target** (finite algebra, resultants over ℚ).

---

### #8. Bartholdi's automatic actions: upgrade the 7-state theorem to an ω-regularity no-go **[cold target; live 2026 program]**
**Ref:** Bartholdi, *Automatic actions I* — https://arxiv.org/abs/2606.08101 (with Bondarenko–Wächter — https://arxiv.org/abs/1912.06897)

**Theorem.** Inverse-semigroup actions on ω-regular languages by Büchi-transducer maps: if the action is **bounded** (no two connected non-trivial cycles per transducer), the orbit relation is effectively ω-regular and a large FO fragment (with "same orbit", cardinality, congruence quantifiers) is decidable. Prop 5.1: the Bernoulli shift admits an automatic presentation whose orbit relation is *not* ω-regular (pumping on (…01^n0…, …00^n1^n0…)).

**Match & gaps.** S_Collatz is an automatic action in exactly his sense; **boundedness fails precisely at the ×3 carry machine** (strongly connected nontrivial cycles feeding the shift) — the automaton-theoretic face of base-2/base-3 incompatibility. His framework lacks ∃g quantification; his Part II is announced (contact Bartholdi; reconcile with our Büchi-nondefinability files first).

**Transfer.** (i) Adapt Prop 5.1's pumping to pairs (x, T^k x) with x = 1^n0^m tails (×3^j stretches blocks at a rate incommensurable with the shift): **the orbit relation of T on Z_2 in base 2 is not ω-regular** — a full no-go subsuming the ≤7-state theorem. (ii) Either-outcome theorem: prove no ω-regular encoding makes the Collatz action bounded (machine-checkable 2⊥3 statement), or find an exotic bounded encoding — which would make divergence/cycle questions decidable by his Corollary B.

**First move.** Write both branches of T as explicit Büchi transducers ({p,q,r} carry machine + shift); confirm the axioms hold and boundedness fails; draft the pumping argument.

### On the bubble (ranked 9–14, preserve for later sessions)
- **Bajpai–Bennett effective 5-term S-unit equations, S={∞,2,3}** — https://arxiv.org/abs/2308.05162 (precursor https://arxiv.org/abs/1603.07922). L=3-odd-step cycles via general machinery (coefficient n handled by Thm 6 + Rhin two-log bounds); prize is 6-term with monotone-exponent structure — new number theory + a new cycle-bound axis (terms = odd steps, orthogonal to Hercher's block axis). **[warm]**
- **Stewart 1980 two-bases digit rigidity** — https://www.degruyterbrill.com/document/doi/10.1515/crll.1980.319.63/html , https://eudml.org/doc/152278 — see Cross-connections §3; the week-provable Cobham corollary is arguably top-8 material but lives inside our existing two-bases note. **[warm]**
- **Potapov–Semukhin/Diekert BS(1,q) placement** — https://arxiv.org/abs/1910.02302 : parity-consistency is *self-enforcing* (valuation argument), so Collatz = plain vector reachability in a f.g. subsemigroup of GL(2,ℚ) sitting exactly in the open cell of their dichotomy; Bruhat–Tits trees at 2 and 3 as a principled route past regular certificates. **[hot]**
- **Substitutive-parity-word exclusion** — Mitchell https://arxiv.org/abs/2305.04817 + Berthé–Delecroix https://arxiv.org/abs/1309.3960 + Cyr–Kra https://arxiv.org/abs/1505.02748 + Donoso–Durand–Maass–Petite https://arxiv.org/abs/2003.06328 : "no divergent orbit has an aperiodic substitutive (or linearly recurrent, or finite-rank-minimal) parity word" — the certificate ladder one rung above regular; drift-exclusion lemma via Gelfond–Schneider is a one-pager, positive-drift case needs Bernstein's Φ + Mahler method. **[warm]**
- **Exel–Pardo / BS(1,3) groupoid invariants** — https://arxiv.org/abs/1409.1107 with Grigorchuk–Savchuk — https://arxiv.org/abs/1212.0605 : amenable tight groupoid, measurewise hyperfiniteness, Katsura K-theory of the Collatz algebra, Krieger type III_λ from the 3/4 drift cocycle — computable invariants nobody has computed (Mori's papers don't touch this). **[warm]**
- **KL/Bunimovich escape-rate placement of cycles** — https://arxiv.org/abs/0811.4438 , https://arxiv.org/abs/2112.14248 , https://arxiv.org/abs/0810.2229 : the known integer cycles sit at exactly the extremal slow-escape hole positions (0^N, 1^N, (10)^{N/2}, (110)^{N/3}); exact finite-time absorption orderings to test against Barina statistics. **[cold, modest payoff]**

---

## 2. Play-Out Queue: Three Hard Attacks

### PQ-1. Krasikov–Lagarias record push (from #1) — *finite phase completed; limit open*
1. **Exact finite phase complete.** Rational feasibility certificates pass for
   `k=12..19`; the strongest has `γ₀=0.9094372617…`.
2. **Counting transfer complete under the mixed trust policy.** Lean proves the
   generic finite-feasibility implication, while exact Python checks the large
   concrete records. This proves every fixed exponent below `γ₀`; it is not
   yet one Lean-native `k=19` artifact.
3. **Portability target.** A chunked kernel-reduced import of `k=12` is in
   progress before attempting the multi-gigabyte records.
4. **Mathematical target.** Prove a cofinal feasible sequence with `λ→2`, which
   would imply almost-linear predecessor counting. Finite increment fits are
   evidence, not a decision of the limit. Critical branching/spine methods are
   speculative tools only after a valid all-level localization theorem exists.
5. **Current localization test.** The exact depth-nine `U(21/50)` pointwise
   split is false, but the full within-vector genealogy shows strong
   mass-averaged behavior on the finite `k=12,...,19` grid. Its exact eight-bin
   matrices admit rational cones after exactly classified finite burn-ins. The
   floating `k=20` vector exceeds every fitted margin but keeps every same-start
   maximum below one. Its `.05` immigration trend is adverse. The cleaner
   direct audit computes 116 exact density-martingale increments and puts all
   108 at `j>=2`, plus 18 floating rows, inside `(1/2)(9/10)^j`.
   Proposition R' would follow from any uniform summable envelope for an
   appropriate selected all-level family; no such theorem or selection is
   known. The cone/immigration route remains the fallback.

### PQ-2. Antihydra rarity + discrepancy theorem (fuse #2 and #3) — *computation + proof sketch*
1. **Lottery ticket withdrawn.** The unconditioned maximum is exactly `m_k=k`;
   the all-odd word makes the proposed computation vacuous.
2. **Surviving branch.** Use the cylinder-residue bijection together with a
   genuinely seed-specific or constrained window bound. Then: (a) BBY Eq.(12)
   gives an exact prefix-discrepancy threshold; (b) Mahler-style transfer-matrix
   counting bounds bounded-window survivors; and (c) a still-missing
   first-passage analogue of van der Laan must connect drawdown to unbalance.
3. **Calibration layer.** Banderier–Flajolet kernel method (https://lipn.fr/~cb/Papers/tcs_banderier_flajolet_2002.pdf , https://arxiv.org/abs/1606.08412): exact algebraic GF of halting itineraries under the iid null (root reproduces q = 1/φ), full C·φ^{−n}·n^{−3/2} asymptotics; fit against bbchallenge simulation of the true stream — the measured deviation is itself a quantitative pseudorandomness statement, the right target for any later derandomization.
4. **Unification.** Prove the exceptional-set dimension statement: seeds whose counter returns to a boundary neighborhood infinitely often have 2-adic Hausdorff dimension log₂φ — the *same* exponent from Mahler's count and the ADDS local-time picture (https://www.math.umd.edu/~dolgop/CylinderMap6.pdf).

### PQ-3. Quantitative certificate stack (from #5, with #8 as its no-go complement) — *computation + decision-procedure proof*
1. **Afternoon 1.** Swap Karp max-cycle-mean into the ≤7-state DFA harness (product automaton, edge weights log(3/2), log(1/2)); rerun the full enumeration. Failed exact invariants with sub-log2/log3 cycle densities become valid quantitative certificates immediately.
2. **Scale.** Move from enumeration to synthesis: LP duality over value-reading (base-2 transducer) automata at 10^3–10^6 states on the 32-core machine; for every infeasible abstraction extract the Legat–Jungers–Parrilo dual occupation measure (https://arxiv.org/abs/1710.01814) — the blocking cycle statistics *are* the refinement instructions. Amortized (contraction-per-return) variants via the ω-regular JSR checkpoint design (Aazan–Girard–Greco–Mason — https://hal.science/hal-04527099), which is the formal home for Terras/Tao-style descent as searchable certificates.
3. **Make it a decision procedure.** Prove the triangular ρ=1 specialization of Philippe–Millerioux–Jungers (https://arxiv.org/abs/1512.04887): for pairs [[λ_w, c_w],[0,1]] with scalar linear parts, automaton-constrained boundedness is **decidable** — max cycle mean of log-scalars < 0 on every reachable SCC, with explicit bound max|c|/(1−γ). Then the pipeline decides, for any candidate regular language L, whether L is quantitatively divergence-free. (Boundary-mapping bonus: this also formally separates Collatz hardness from matrix-product undecidability — Blondel–Tsitsiklis needs dimension as input — https://www.mit.edu/~jnt/Papers/J081-00-vb-products.pdf .)
4. **No-go complement.** Run the Bartholdi pumping attack (#8) in parallel so that failure of the search at scale is convertible into theorems, not just exhaustion. **Lean target:** the certificate *verifier* (automaton + rational weights + cycle-mean check + soundness of the abstraction of T) is a compact decidable kernel — formalize once, reuse for every certificate found.

---

## 3. Cross-Connections

**(a) Path-complete/WFAR certificates — three communities, one computation.** The multinorm scalar collapse (#5) and Gaubert's (max,+) worst-case theorem (http://www.cmap.polytechnique.fr/~gaubert/PAPERS/IEEE-TAC-93-172-preprint.pdf) were found by *different agents* and reduce to the identical object: **max cycle mean over a product automaton** (tropical Perron root). Kozyakin's sliding-window frequency SFTs (https://arxiv.org/abs/1403.5050 , Markovian Berger–Wang arXiv:1401.2711), network-calculus arrival curves (#3), and the folklore density lemma are three languages for the same window-density certificate — build it once. Endrullis–Zantema's SAT-searched regular non-termination certificates (https://drops.dagstuhl.de/storage/00lipics/lipics-vol036-rta2015/LIPIcs.RTA.2015.160/LIPIcs.RTA.2015.160.pdf , with match-bounds and sparse tiling arXiv:2003.01696) mechanize our DFA search in a strictly larger class (rule-labeled states, tree automata) — rerun our negative result there. Ceiling: Daviaud–Guillon–Merlet tropical-JSR undecidability (https://arxiv.org/abs/1612.02647) caps the certificate landscape but leaves approximability (their Thm 5) — the engine for PQ-3. Guy–Smith/sparse-space certificates from octal games (https://link.springer.com/article/10.1007/BF01254294) are an XOR-closed certificate class *disjoint* from regular — untested against the 7-state theorem.

**(b) BRW/Krasikov–Lagarias ↔ JSR.** The nonlinear min-over-fibers system has
a useful policy-family and constrained-JSR analogy, but the earlier claim that
`λ_k` is literally a lower spectral radius is not established. The associated
policy or annealed matrices are not exact recursions for the true predecessor
count. Consequently the proposed Lalley-renewal upgrade to
`N(log x) ~ Cx^{δ_k}` is **retracted**: no sandwich theorem identifies that
linear resolvent with the nonlinear KL threshold. Dai's constrained
Berger–Wang theorem (https://arxiv.org/abs/1107.0124), Lalley's renewal theorem
(https://projecteuclid.org/journals/acta-mathematica/volume-163/issue-none/Renewal-theorems-in-symbolic-dynamics-with-applications-to-geodesic-flows/10.1007/BF02392732.full),
and Biggins–Lubachevsky–Shwartz–Weiss
(https://projecteuclid.org/euclid.aoap/1177005839) remain possible tools only
after such a bridge is proved. The annealed-versus-adversarial gap remains a
diagnostic, not an exact counting asymptotic.

**(c) Two-bases/Cobham rigidity — one constant, five faces.** Set-level: our Cobham note; point-level effective companion: Stewart 1980 (URLs above; quantitative model = arXiv:2311.17348's log log lower bound). Group-level: Potapov–Semukhin BS(1,q) open cell (https://arxiv.org/abs/1910.02302). Automaton-level: Bartholdi boundedness failing exactly at the ×3 carry machine (#8); Sutner's abelian-transducer theorems stopping exactly at the non-abelian carries (https://www.semanticscholar.org/paper/Invertible-Transducers,-Iteration-and-Coordinates-Sutner/faa52056c56027ef30940386c7180dc8f4386e48 — CMU, conversation not citation). Dynamics-level: non-soficity of the 3/2 fiber (#7). Certificate-meta-level: Bedaride–Fernique local rules (https://arxiv.org/abs/1512.04679) — pattern-enforceable slopes are *quadratic*, computation-carrying ones are *computable*; log₂3 is transcendental (Gelfond–Schneider), which is the same transcendence that powers the substitutive-parity exclusion (bubble list) and predicts the certificate frontier sits strictly between sofic and computation-embedding. Near-term theorem: **no infinite T-invariant set avoiding 1 is both 2- and 3-automatic** (Cobham → eventually periodic → kill APs with the 2-adic/3-adic action) — one week, and it upgrades the Cobham note from remark to theorem.

**(d) Cryptid functionals — φ from three unrelated proofs.** Mahler's Fibonacci residue count (#2), the Lundberg/ruin root of the Haar-ensemble theorem (Aurzada–Simon — https://arxiv.org/abs/1203.6554 ; makes (1/φ)^n a *theorem* for the ensemble), and the Banderier–Flajolet kernel root (PQ-2) — three derivations, one constant, no established bijection between them: proving the bijection is itself a result. Dimension log₂φ = 0.694 recurs in Mahler's exponent and the conjectured boundary-recurrent seed dimension (ADDS — https://www.math.umd.edu/~dolgop/CylinderMap6.pdf). The only *every-orbit* theorem in reach is Flatto–Lagarias–Pollington oscillation ≥ 1/3 (http://matwbn.icm.edu.pl/ksiazki/aa/aa70/aa7023.pdf ; confinement threshold pinned in [0.2381, 1/3] with Akiyama–Frougny–Sakarovitch and Dubickas); Dolgopyat–Sarig (https://www.math.umd.edu/~dolgop/DLT6.pdf) *proves* no temporal limit law exists for a.e. seed — classifying which single-orbit statements are even possible and closing the Beck route. The AFS rational-base numeration surfaced independently in three lanes (Bruin–Fokkink Pell-automatic zeros — https://arxiv.org/abs/2503.11734 ; temporal CLT over the zero-entropy 3/2-odometer — https://arxiv.org/abs/1705.06484 ; and the S-adic lane) as the "adapted representation" bet: redo the DFA search over AFS words. Moving-hole survivor theory (Kong–Sun–Wang — https://arxiv.org/abs/2505.02336) is the only framework shaped like the *endogenous* cryptid hole. Parameter-family portrait: Dajani–Kalle signed-binary plateau ending at η=3/2 (https://arxiv.org/abs/1703.06335 , flagged possible numerology) and the matching families (Carminati–Tiozzo tuning — https://arxiv.org/abs/1111.2554 , https://arxiv.org/abs/1004.3790 ; Tanaka–Ito rational bifurcation points — https://iopscience.iop.org/article/10.1088/1361-6544/abef75 ; infinite-measure matching — https://arxiv.org/abs/1912.10680 ; transport coefficients — https://arxiv.org/abs/0801.2413) give the template for "is the cryptid at a plateau endpoint".

**(e) Sturmian/CF-convergent thread (unplanned convergence of four agents).** KKLL extremal survivor words (#6), Bugeaud–Dubickas Sturmian rigidity for confined {ξb^n} (https://www.numdam.org/item/CRMATH_2005__341_2_69_0.pdf), Carey–Clampitt well-formed scales — the Pythagorean stacking catalog of log₂3 convergents with the Myhill two-sizes property (https://www.tandfonline.com/doi/abs/10.1080/17459737.2010.491975), balanced words minimizing Lindley functionals (#3), and Ouaknine–Worrell Positivity hardness at bounded-type numbers (https://arxiv.org/abs/1307.2779) all say: **extremal objects for every functional we care about are mechanical words of slope tied to log₂3, and the Diophantine type of log₂3 is the universal wall.** The Myhill transfer (exact two-gap structure of cycle parity words per Stern–Brocot position) is an unclaimed shrink of the cycle search space.

**(f) Decidability cartography.** Ben-Amram's interval-vs-congruence seam (1-D interval-PAF PSPACE vs Π⁰₂ with mod guards) + Finkel–Göller–Haase/Jaax–Kiefer (order guards PSPACE, parity guard open) + Asarin et al. "don't know" zone + KLNOW's existential frontier (#4) + Hosseini–Ouaknine–Worrell's all-inputs/single-orbit asymmetry (https://arxiv.org/abs/1902.07465 — the same asymmetry as Terras/Tao vs the conjecture) jointly pin Collatz at a *specific* triple intersection: congruence-partitioned, non-monotone, two-power. Space Needle formalizes as 2-D integer PAF at the Π⁰₂-complete level — a rigorous "cryptid" certification. Proof-theoretic home: Jerabek's APC1 (https://users.math.cas.cz/~jerabek/papers/apx.pdf) should prove explicit-rate Terras — formalizing this separates the drift layer from the certificate layer axiomatically and sets up independence targets. Skolem-style certificate architecture (Bilu et al. — https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2022.20 ; Bertók–Hajdu λ-smooth moduli with a runnable Sage solver — https://arxiv.org/abs/1407.6499 ; worked 4-term template Le–Miyazaki — https://arxiv.org/abs/2508.17601) is the number-theory face of the same two-sided search; WSTS completeness (https://www.sciencedirect.com/science/article/pii/S030439750000102X) says ordering-certificates are complete-hence-unsearchable in full, motivating the finite "2-automatic wqo" search as the next negative-result class.

---

## 4. Dead Ends Worth Recording

1. **Residue-only (mod 2^m) abstractions for any path-complete/multinorm/tropical certificate**: provably vacuous — Terras makes every parity word admissible, constrained JSR = 3/2. The abstraction, not the template, is the bottleneck. Never re-search.
2. **Matching/SFT on the β=3/2 fiber**: provably empty for all offsets (algebraic-integer obstruction, BCK/BCMP). Also: no point of these interval families is *conjugate* to 2-adic Collatz (entropy log 3/2 vs log 2) — only caricatures. And 3/2 is not the unique exceptional fiber (transcendental fibers are SFT-free too); what is special is the arithmetic mechanism.
3. **Temporal limit laws for the actual orbit over positive-entropy driving**: provably impossible (Dolgopyat–Sarig Thm 3.2 — ASIP ⇒ a.e. temporal lawlessness). Only zero-entropy odometer-type systems (AFS numeration) remain open.
4. **Blondel–Tsitsiklis undecidability as an explanation of Collatz hardness**: doesn't bite — dimension is part of their input; at fixed 2×2 the trend is decidability. Hardness enters via arithmetic admissibility, not matrix products.
5. **Naive hole framings**: the point-hole {1} survivor set is co-countable (vacuous); ball-hole survivor sets do **not** sandwich divergent orbits (they may revisit 1+2^mZ_2 at large values); liminf-density is not a survivor condition. The orbit-minimum/one-sided-walk reformulation (#6) is the unique correct framing.
6. **Interval-PAM decidability routes** (injective — https://arxiv.org/abs/2301.09752 ; complete — https://arxiv.org/abs/1510.04121): Collatz is neither, and all such results need order-topology pieces; parity is a 2-adic ball. Ditto Bellman/monotone decidability (Varonka–Watanabe): the branches cross, monotone reformulation provably unavailable.
7. **Plain Presburger acceleration of the 3x+1 loop**: the monoid {3^i} is infinite; the closure is 2^N/3^N-shaped, provably non-Presburger. Escape = powers-extension (#4), nothing else.
8. **The dream deterministic-vs-Markov persistence coupling lemma** (single-orbit persistence from quantitative equidistribution): does not exist anywhere in queueing/persistence/ruin/fluctuation literature. Must be proved, not found. Sparre-Andersen universality specifically fails (sign-invariance broken by drift).
9. **S-unit equations with the unbounded free coefficient n** in the cycle equation: a genuine wall in the literature (only ineffective EGST ω(N)≤4 and Bajpai–Bennett's poly-height coefficients). Also: no theory of perfect powers in *valuation-driven* recurrences (the honest answer on BMO 3: only mod-m certificates generalize).
10. **One-type BRW models of the backward tree**: fail badly (mean transform min > 1); the multitype no-11 structure is essential. CMJ/Nerman theory blocked by children-born-earlier; the Lalley/pressure route avoids it.
11. **Contracting nucleus for the BS(1,3) group completion**: closed negatively (t=×3 forces every t^n into any nucleus); only Nekrashevych's inverse-semigroup contraction (https://arxiv.org/abs/2509.05524) remains open. Hyperbolic-boundary hyperfiniteness doesn't transfer; plain orbit hyperfiniteness is trivial.
12. **The naive dichotomy "itinerary eventually periodic or positive entropy"**: false as a symbolic theorem (Sturmian embeddings); only holds at substitution-system level or under minimality+finite-rank — any Collatz version must consume integrality.
13. **Atkinson/Schmidt zero-mean cocycle recurrence, heaviness, unique ergodicity for floor(3x/2)**: all structurally inapplicable (drift ≠ 0; Bernoulli with a continuum of invariant measures). Every-orbit results must come from FLP-style admissibility combinatorics.
14. **Assorted false positives**: β-encoder robustness (univoque, not matching); rotor-router "deterministic random walks" (different object); heavy-tailed BRW; Willis scale-groups and Nekrashevych survey contain zero hidden Collatz content (greps verified); Zudilin-type ||(3/2)^k|| bounds — nothing past 2007, and they don't control floor-iterated orbits.
15. **Retrieval notes**: Stewart 1980 full text is paywalled/OCR-less (blindness verified via absence from both Lagarias bibliographies — indirect); Project Euclid blocks curl (Lalley, BLSW barrier paper — BLSW blindness unverified); use HAL for the ω-regular JSR chapter; Springer/ACM walls route via arXiv siblings.

---

## 5. Citation Index (URLs not already linked above)

- Bennett, Pillai equations: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/6862D4DFA9282A3EF0BE68C4EFD89A1C/S0008414X0002321Xa.pdf/on-some-exponential-equations-of-s-s-pillai.pdf
- Evertse–Schlickewei–Schmidt: https://arxiv.org/abs/math/0409604 · Corvaja–Zannier gcd/heights: https://arxiv.org/abs/math/0311030 · Bugeaud–Mignotte–Siksek: https://arxiv.org/abs/math/0403046
- Hofbauer–Keller (β=3/2 acim CLT): https://link.springer.com/article/10.1007/BF01215004
- D'Angeli–Rodaro–Wächter partial automaton semigroups: https://arxiv.org/abs/1811.09420 · Gillibert finiteness undecidable: https://arxiv.org/abs/1304.2295 · Willis scale groups: https://arxiv.org/abs/2008.05220 (Grigorchuk–Savchuk liftable: arXiv:2312.05427; Davis–Elder–Reeves: arXiv:1311.3362)
- Glendinning–Sidorov asymmetric holes: https://arxiv.org/abs/1302.2486
- Berger–Bethencourt Sparre-Andersen: https://arxiv.org/abs/2304.09031 · Aurzada–Mukherjee–Zeitouni persistence exponents: https://arxiv.org/abs/1703.06447
- Bezuglyi–Karpel–Kwiatkowski–Wata generalized Bratteli: https://arxiv.org/abs/2404.14654 · Adamczewski balances: https://adamczewski.perso.math.cnrs.fr/article_tcs.pdf
- Goresky–Klapper MWC/FCSR: https://www.math.ias.edu/~goresky/pdf/p1-goresky.pdf
- Agent-10 refs (no URLs supplied): KLNOW arXiv:2407.05191; Leroux–Sutre ATVA 2005 (HAL hal-00346310); Ben-Amram STACS 2013; Bacik et al. arXiv:2605.16985; Asarin–Mysore–Pnueli–Schneider I&C 2012.

All downloaded PDFs are consolidated in `/Users/simon/Desktop/COLLATZ/papers/` (per-brief lists retained in the source briefs); the KL solver is at `/Users/simon/Desktop/COLLATZ/kl_perron_solver.py`.
