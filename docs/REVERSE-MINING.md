# Reverse-Translation Synthesis: What bbchallenge Invented That Mathematics Hasn't Noticed

Sources: six close-reading reports covering (1) FAR/WFAR deciders, (2) the Skelet 1 proof, (3) the Skelet 17 proof, (4) the CTL certificate family and the BB5 pipeline, (5) rule mining (sligocki/Ligocki toolchain), (6) community epistemic practices.

---

## 1. Master Table of Extracted Techniques

| # | Technique (origin) | Verdict | One-line math translation |
|---|---|---|---|
| 1 | FAR: 8 Boolean-matrix conditions + DFA-seed certificates (deciders repo, Thm 4.9) | known-math-with-new-twist | Weakly-monotone interpretation of the TM's string-rewriting system into Boolean matrices = order-dual of Hofbauer–Waldmann matrix interpretations, certifying safety instead of termination |
| 2 | WFAR: two-sided Z-weighted DFAs + interval accept sets + sign-set widening (mitmwfar, Thm 4.10) | known-math-with-new-twist | Path-complete barrier certificate with unit-slope affine templates in one synthesized counter; invariant class = deterministic dim-1 Parikh automaton |
| 3 | SAT MitM-DFA search + BFS symmetry breaking + "certificate = seed for verified closure" (mitm_dfa.rs) | known-math-reinvented | Heule–Verwer DFA-SAT identification + Boutin-style reflection; certificate compressed below proof size via deterministic recompletion |
| 4 | Skelet 1 L1: RLE block abstraction with certified partial semiconjugacy | known-math-reinvented | Marxen–Buntrock macro machine + higher-block recoding, machine-checked |
| 5 | Skelet 1 L2: stride rule (closed-form k-th iterate of the sweep-return map) | known-math-with-new-twist | The return map is "+1" on a base-4 odometer with an affine run-length cocycle; Phi^k Presburger-definable uniformly in k, over unbounded-length RLE words |
| 6 | Skelet 1 L3: uni-cycle (acceleration of the accelerated system, untrusted exponent oracle) | known-math-with-new-twist | Depth-2 acceleration tower over parameterized words; level-3 constants exact affine functions of level-2 base (T = 4P−5) |
| 7 | Skelet 1 L4: context-universal shift-template certificate | **plausibly-new-mathematics** | Eventual-periodicity-mod-shift certified in time polylog in the preperiod (8.8e7 vs 5.42e51), period never computed |
| 8 | Skelet 1 L5: in-kernel vm_compute fast-forward (Coq-BB5) | known-math-reinvented | Textbook proof by reflection (Boutin 1997; Gonthier's 4CT) |
| 9 | Savask's sweep-section reduction: TM → unbounded-dimension counter-list rewriting | known-math-reinvented | Poincaré first-return map to a regular cross-section; induced map is a VASS-like counter system with zero-tests |
| 10 | Gray-code decoding of the parity vector (Savask/Xu/mxdys) | known-math-with-new-twist | Explicit semiconjugacy onto a dyadic-odometer-with-halving factor; fiber = digit-counting cocycle over the odometer |
| 11 | Xu's embanked invariant + ruler-sequence itinerary (N′ acceleration) | known-math-with-new-twist | Hand-rolled Vershik adic map on a two-vertex Bratteli diagram; k-induction with closure certified by digit-distance inequalities in Büchi arithmetic |
| 12 | Skelet 17 epoch renormalization: Base_k →* Base_{k+1} | known-math-with-new-twist | Self-induced orbit = renormalization fixed point with period-doubling combinatorics (Feigenbaum-attractor architecture at the "edge of halting") |
| 13 | 7-level certified simulation tower (BB5_Skelet17.v) | known-math-reinvented | CompCert-style forward-simulation composition, run "upward" to transport non-termination |
| 14 | Regular CTL umbrella (all Coq-BB5 deciders) | known-math-reinvented | Inductive invariant (Cousot–Cousot 1977) drawn from regular languages = regular model checking (Bouajjani et al. 2000) |
| 15 | Bouncers: formula tapes + shift rules (Bouncers.v) | known-math-with-new-twist | Verified acceleration/meta-transitions on head-anchored growing tapes; one finite certificate carries a ∀n⃗ family via period-crossing induction, aligned modulo word conjugacy |
| 16 | NGramCPS + fixed-history/LRU alphabet augmentation | known-math-with-new-twist | Order-n SFT cover of the half-tape languages; history lift = operationalized Medvedev's theorem closing the SLT→regular gap via a cache policy |
| 17 | RepWL + RWL_mod (threshold + modulus exponents) | known-math-reinvented | Classical (0..T−1, ≥T) counter abstraction; (threshold, mod) = the universal finite quotient of (N,+1) |
| 18 | FAR universality lemma (every regular co-CTL fits Thm 4.9 normal form) | known-math-with-new-twist | ∃ regular certificate ⟺ ∃ finite-index left congruence whose induced pushdown pre* avoids c₀; the DFA alone is the whole information content |
| 19 | Loop deciders via transcript-only detection (Alg. 1, Lemma 4.1) | known-math-with-new-twist | Head itinerary + extremality marks is a complete invariant for eventual periodicity-mod-translation (discrete domain-of-dependence statement) |
| 20 | mxdys 2026 FAR variant: cache-policy congruence templates + UCB bandit (113/1534 BB6 holdouts) | known-math-with-new-twist | Search the lattice of finite-index right congruences via structured generator families, compute-allocated by a stochastic bandit over abstract domains |
| 21 | Certificate-expressivity hierarchy: occupancy census 175M→6M→6.6K→23→17→13 | **plausibly-new-mathematics** | First measured distribution of minimal-invariant-complexity ("certificate rank") over the population of small programs; heavy-tailed like a description-length prior |
| 22 | Block_Finder: compression-guided block abstraction (MDL at worst moment) | known-math-with-new-twist | MDL model selection over conjugacies: choose the recoding minimizing description length of the worst-compressed reachable state |
| 23 | Trace-triggered guess-and-check rule proving (Past_Config + prove_rule) | known-math-with-new-twist | Daikon-style dynamic invariant inference where candidates are first-return maps on self-discovered cylinder coordinates, verified by exact symbolic execution |
| 24 | Closed-form acceleration hierarchy: Diff/Linear/Exponential rules + recursive meta-rules | known-math-with-new-twist | Presburger/affine acceleration closed under unbounded self-iteration → exp-towers of unbounded height with exact step counts (no PL tool operates in this regime) |
| 25 | ExpInt: exact arithmetic on tower integers with computable residues (Carmichael recursion) | known-math-with-new-twist | The iterated-totient folklore trick packaged as a closed arithmetic domain (add/mul/divmod/compare) over sums of towers |
| 26 | Config-algebra rule DSL + inductive validator (validator.rs, busycoq) | known-math-reinvented | Rewriting induction (Reddy 1990) on power-word-compressed configurations with stratified summaries |
| 27 | Collatz-level extraction: halting → RCWA-map reachability + drift heuristics | known-math-reinvented | Michel 1993/2015 + Lagarias–Weiss stochastic models, semi-automated and machine-checked |
| 28 | Probvious calculus: exact conditional hitting probabilities under a model measure | known-math-with-new-twist | Conditional theorem: itinerary genericity ⟹ halting event has model-measure ≤ h(N); h(N) is a supermartingale value = Martin-Löf test level, compute-indexed |
| 29 | Champion forecasts (Lucy's Moonlight "5% champion") | known-math-with-new-twist | Tail probabilities of an uncomputable integer as a random variable under per-holdout model measures; EVT at tetration scale |
| 30 | Wall arguments (BB(3,3) probvious champion) | known-math-with-new-twist | Certified basin interval of width L + jump-law domination ⟹ quantitative model-halting bound 1−exp(−pL); exact backward pruning fused with forward renewal estimate |
| 31 | Cryptid breeding via TNF adjacency (Mother of Giants) | known-math-with-new-twist | One-cylinder perturbation families of Collatz-like maps: shared drift skeleton, single exceptional rule sweeping stopping times over >10^10000 range |
| 32 | N-gram entropy as provability barometer | known-math-with-new-twist | Sofic-cover inequality (cert size ≥ exp(entropy)) used in converse as an empirical sufficient statistic for certificate existence |
| 33 | Orbit-merging quotients / TNF / cross-substrate cryptid identification | known-math-reinvented | Affine conjugacy classification (Wirsching/Matthews) + bisimulation-flavored certificates; merge-time is the one new invariant |
| 34 | BMO pipeline: verified reduction ∘ named open conjecture | known-math-reinvented | Certified many-one reductions (Coq undecidability library practice) + problem curation with certified hardness provenance |

---

## 2. Full Sections: Plausibly-New and New-Twist Techniques

### 2A. Plausibly-New Mathematics

#### 2A.1 Context-universal shift-template certificates for eventual periodicity (Skelet 1, Level 4)

**Implicit theorem (standard language).** Let (X,→) be TM dynamics, A abstract configurations over counter-annotated words, lift: A→X, fullstep one-step-sound (fullstep(a)=a′ ⟹ lift(a)→*lift(a′)). If there exist a letter s, finite word K, block F, and a *symbolic* derivation (never inspecting the context l) showing ∀l: lift(s·l, K) →⁺ lift(s·F·l, K), then (i) every such orbit never halts; (ii) each is a translated cycler with limit tape F^ω·K — with period and preperiod never computed; (iii) if fullstep^m(a₀) hits the template, eventual periodicity is certified in time O(m), with m polylog in the true preperiod (8.8×10⁷ accelerated steps vs preperiod 5.42×10⁵¹: compression ~6×10⁴³). The famous constants (period 8,468,569,863; preperiod 5.42e51) appear **nowhere** in either Skelet1.v — the certified theorem is number-free.

**Nearest theory and the precise gap.** Honkala 1986 / Durand 2013 / Mitrofanov decide ultimate periodicity for *automatic/morphic* presentations (arxiv.org/abs/0808.1657, arxiv.org/pdf/1301.2691, lamfa.u-picardie.fr/fdurand/Papiers/periodicite051112.pdf) — but this orbit is generated by data-dependent rewriting with collisions and is not automatic; the method is orbit-specific semi-decision, not class decision (the same abstract system provably contains halting configurations, per https://www.sligocki.com/2023/02/27/skelet-1-halting-config.html). Lin recurrence (BB5 paper §4.3; https://wiki.bbchallenge.org/wiki/Translated_Cycler) supplies the certificate *shape* but at raw-step granularity where the preperiod makes it physically impossible. Recurrent sets (Gupta–Henzinger–Majumdar–Rybalchenko POPL'08) and RMC certify nontermination but never *eventual periodicity*, and never through a certified acceleration tower. Gap: no published theorem states that periodicity-mod-shift admits certificates of size polynomial in description and checkable polylog in preperiod for tower-accelerable dynamics.

**Fusion opportunity.** Extract and prove the general theorem: *for 1-D rewriting dynamics on counter words admitting a sound acceleration tower with triangular-affine levels, eventual periodicity-mod-shift admits context-universal window-recurrence certificates checkable in time polylog in preperiod.* Fuse with Honkala/Durand to find the subclass (automatic collision sequences) where semi-decision becomes decision; fuse with GHMR recurrent-set synthesis to automate finding (K, F).

**Collatz/certificate application.** Direct blueprint for the rigidity exit: build a certified accelerated simulator on RLE parity words, run greedily, and match for a template φ(l) →⁺ φ(σ(l)). A σ that *grows* the context would certify a divergent orbit of a 5n+1-type map — the same schema covers both periodicity and controlled divergence. Sobering transfer: expect the abstract parity system to admit "bad" configurations, so only orbit-specific certificates are possible.

#### 2A.2 The certificate-rank census (the pipeline occupancy profile as a mathematical object)

**Implicit theorem.** Define, for each nonhalting TM, its *certificate rank* = the least tier in the tower {eventually-periodic ⊂ SFT/SLT_n covers (NGramCPS) ⊂ RLE-ideal (RepWL) ⊂ regular (FAR, universal for its tier) ⊂ regular × one blind Z-counter (WFAR) ⊂ numeration-automatic / parametrized-family induction (sporadics)} admitting an inductive invariant. The BB5 determination computed the first rank distribution over an exhaustive program population: 175,373,810 → 6,005,142 → 6,577 → 23 → 17 → 13, each tier's residue shrinking ~10³. Known strictness theorems exist at every boundary (McNaughton–Papert; Greibach's blind-counter hierarchy; SLT_n strictness), and Π⁰₁-completeness guarantees no finite tower closes — but **no known theorem predicts the occupancy profile**, i.e., the distribution of minimal-invariant complexity over random small programs.

**Nearest theory and gap.** Subregular hierarchies and counter hierarchies supply the tiers; Gödel–Turing supplies non-collapse; algorithmic information theory (Levin priors) suggests the shape. Gap: no "average-case proof complexity over program space" theory exists anywhere; termination competitions observe similar cascades but nobody has theorized them.

**Fusion opportunity.** Conjecture: rank is lower-bounded by the Kolmogorov complexity of the invariant relative to the machine, giving a Levin-style prediction of the ~10⁻³ cascade — testable against the BB6 census as it completes. This would be a new theorem *kind*: measured proof-complexity zoology.

**Collatz application.** Calibrated placement: Michel's dictionary (BB champions = Collatz-like maps), the Cryptids' resistance to the entire arsenal, ergodicity killing the bottom two tiers, and our own regular-failure-through-index-7 jointly locate Collatz at rank ≥ regular-with-large-index. The Skelet 10 lesson ("regular after a change of numeration" — Zeckendorf) says the actionable move is re-coordinatization (rational-base 3/2, Akiyama–Frougny–Sakarovitch) before concluding trans-regular rank. Either outcome makes our negative results *interpretable*: they measure Collatz's rank in a now-mapped hierarchy.

---

### 2B. The Automata-Certificate Ladder

#### 2B.1 FAR (Boolean-matrix safety interpretations)

**Implicit theorem.** u ↦ q₀T_u is a monoid morphism from tape words into ordered Boolean matrices, weakly monotone w.r.t. the rewriting preorder; halting words are sent above an absorbing threshold s, the initial word below. Eight finite matrix (in)equalities (Thm 4.9) certify non-halting. Companion universality lemma (arXiv 2504.20563): every regular co-CTL proof re-expresses in this normal form; equivalently, ∃ regular certificate ⟺ ∃ finite-index left congruence whose induced pushdown pre* (Bouajjani–Esparza–Maler CONCUR 1997, knowingly cited in the decider README) avoids c₀. The shipped certificate is the **DFA alone** — the NFA half is recomputed by saturation.

**Nearest theory and gap.** Regular model checking (Bouajjani–Jonsson–Nilsson–Touili CAV 2000) subsumes the invariant class; Hofbauer–Waldmann matrix interpretations (RTA 2006) and match-bounds (Geser–Hofbauer–Waldmann, AAECC 2004) are the identical algebra with inequality reversed (termination vs safety). Gap: **neither side cites the other**; the safety corner of the semiring ladder and the seed-compressed certificate architecture are absent from the termination literature, and match-bound completeness theory is absent from bbchallenge.

**Fusion.** Import the termination community's semiring ladder with flipped inequalities: N-matrix "counting FAR" and arctic "record-tracking FAR", SAT/SMT-searched, CeTA-style certified. Export the seed+verified-recompletion trick to shrink CeTA certificates. Run Matchbox/Torpa on BB holdout sets: is the 23-machine FAR residue exactly the non-match-bounded regular machines?

**Collatz application.** Yolcu–Aaronson–Heule (CADE 2021, arXiv 2105.14697) already do the termination dual for Collatz rewriting; FAR supplies the missing safety half. Searchable statements: "no element of regular family S ever reaches configuration set H" for residue-restricted Collatz variants; the Coq verifier ports verbatim (nothing TM-specific beyond 2-locality). The universality theorem redirects search: enumerate *congruence generators* (mod-3^k towers, carry automata — index 3^k·O(1), cheap to construct) instead of blind DFA enumeration; principled failure at moderate index is far stronger evidence of non-regularity than blind ≤7-state search.

#### 2B.2 WFAR (weighted meet-in-the-middle certificates)

**Implicit theorem.** Two deterministic Z-weighted automata read the half-tapes; global weight W = W_l + W_r; accept sets are per-control-tuple intervals, forward-closed under one-symbol pre-image enumeration with sign-derived infeasibility pruning. Three exact identifications: (a) the invariant class is deterministic dim-1 Parikh automata = blind one-counter languages (Greibach TCS 1978; Klaedtke–Rueß ICALP 2003) — the only non-regular class in the whole BB5 proof; (b) the Coq closure is interval abstract interpretation with threshold widening (Cousot–Cousot POPL 1977, verbatim); (c) it is a **path-complete barrier certificate** (Ahmadi–Jungers–Parrilo–Roozbehani, arXiv:1111.3427; barriers: arXiv:2503.19561) with unit-slope affine templates and translation-only mode dynamics — with one ingredient absent from control theory: the scalar state W is itself *synthesized* as an automaton weight function.

**Nearest theory and gap.** Everything is individually classical (Parikh automata, difference constraints/Bellman-Ford potentials, arctic interpretations — Koprowski–Waldmann RTA 2008). Gap: neither the path-complete community nor bbchallenge cites the other; nobody has built the middle of the ladder (vector weights, polyhedral accept sets, SOS templates over matrix-weighted abstractions). Deployed reality check: all 17 shipped certificates use weights in {−1,0,1}; the "Bellman-Ford" story is aspirational (footnote 49) — only the sign-definite fragment exists in code.

**Fusion.** The explicit generalization ladder: **Step 1 (LP)**: weights in Z^k, polyhedral accept sets, closure = polyhedral inclusion certified by stored Farkas multipliers. **Step 2 (SDP)**: semialgebraic accept sets, Positivstellensatz closure, validsdp-style rational verification. **Step 3**: matrix-valued weights → full AJPR machinery (CQLF, SOS hierarchies, De Bruijn expansions — which mitmwfar's `-m` flag already implements unknowingly). FAR and WFAR are the two degenerate corners of one ladder whose middle is untried.

**Collatz application.** The natural "Collatz WFAR" is dimension 2: weights (a,b) = (odd steps, halvings) making 3^a/2^b additive, with the transcendental comparison entering only via Stern–Brocot rational bounds on log₂3 — all closure checks in integer linear arithmetic, searchable by SAT-modulo-difference-logic instead of mitmwfar's blind ±1 enumeration. Michel (1993/2015) shows BB record holders *are* Collatz-like residue maps, so WFAR upgrades prove Collatz-like theorems, not analogies. Honest boundary: Antihydra-class holdouts need parity-sequence equidistribution, outside any finite-dimensional counter certificate.

#### 2B.3 NGramCPS + history/LRU augmentation

**Implicit theorem.** Algorithm 2 computes the least (L,R,C) whose concretization is step-closed and contains c₀ — exactly the order-n SFT/Markov cover of the half-tape languages (Lind–Marcus), head-anchored and two-sided. The augmentation theorem: computing the SFT cover of the system lifted over alphabet A×H (H = visit history, fixed-length or LRU) and projecting recovers regular invariants that are not locally testable — **Medvedev's theorem operationalized by a cache policy**, without either name. Killed 6,005,142 machines; LRU alone reached 182 otherwise-unreachable ones.

**Nearest theory and gap.** SFT approximation of subshifts and of CA limit sets (Culik–Pachl–Yu) is standard; view abstraction (Abdulla–Haziza–Holík, https://link.springer.com/article/10.1007/s10009-015-0406-x) is the same functor in verification, *with* completeness theorems for WQO systems that bbchallenge lacks. Gap: the ladder (window n) × (history depth h) × (eviction policy), and the question "which syntactic monoids embed in the n-gram-of-history quotient", are posed nowhere.

**Fusion.** Characterize regular invariants reachable at level (n,h,LRU); import view-abstraction completeness to predict when n-gram closure must succeed.

**Collatz application.** Negative theorem for free: the Collatz graph mod 2^n is the de Bruijn graph B(2,n) (Laarhoven–de Weger, https://arxiv.org/abs/1209.3495), and the 2-adic extension is conjugate to the full shift (Bernstein–Lagarias), so the order-n SFT cover of Collatz reach-sets is the full shift for every n: **window-based local certificates can prove nothing about Collatz proper**. Positive residue: history augmentation is *anchored* — run closure over {0,1}×(last h (step-parity, carry) pairs), a corner of regular-invariant space provably disjoint from what raw ≤7-state enumeration covered.

#### 2B.4 Bouncers (formula tapes + verified shift rules)

**Implicit theorem.** A finite certificate — n₀ concrete steps, split points, shift rules each verified by ONE bounded period-crossing run and lifted ∀n by induction (shiftrule_left_exec), a subsumption check after conjugacy alignment of period words — proves that the return map on {q}×L, L = {u₀v₁^{n₁}…v_k^{n_k}u_k}, is total and L-preserving, hence nonhalting for the whole ∀n⃗ family at once. The orbit is a linearly-growing self-similar family: verified substitution structure inside TM dynamics.

**Nearest theory and gap.** Meta-transitions/acceleration in RMC (Boigelot–Wolper; Abdulla–Jonsson–Nilsson–d'Orso 2002) covers length-preserving transducers, not the head-anchored growing-tape case; Hennie's 1965 crossing sequences supply the idea turned from lower-bound tool into positive certificate; the alignment step re-implements Lothaire's conjugacy-of-words. Gap: the *verified* induction carrying a universal quantifier through a symbolic run, and any handling of genuinely S-adic (level-2, exponentially self-similar) machines.

**Fusion.** Replace the single formula tape by a *sequence* related across scales by a nontrivial morphism σ (config(k+1) = σ(config(k))) — exactly the certificate shape of Skelet 17's endgame and the formal home of "level-2 inductive rules." RMC would call it acceleration of a non-flat loop nest; the general verified version exists nowhere.

**Collatz application.** Known predictable Collatz segments are shift rules verbatim (trailing 1^b ⟹ b odd steps with a carry cascade — one period-crossing + induction). Run the formula-tape guesser on Collatz-transducer traces of structured seeds (2^k−1, (4^k−1)/3); closure will fail, but *which repeater blocks refuse to align* is a diagnostic of where self-similarity breaks — per Michel, that breakage is the Collatz difficulty. The reusable asset: subsumption-after-conjugacy-alignment for parametrized families config(a,b) →⁺ config(f(a,b)).

#### 2B.5 FAR universality (regular proof complexity)

Covered under 2B.1; recorded separately because the lemma stands alone: the DFA/left-congruence is the entire information content of a regular nonhalting proof, inducing a "minimal certifying congruence index" invariant of machines. Fusion: classify TMs by this index; connect to match-bound decidability. Collatz: our index-7 failure is a lower bound on this invariant for Collatz; push to ~11–12 with the MITM-SAT prover (4s vs 2min per machine at depth 10–11 per BB5 data), then switch to principled congruence families.

#### 2B.6 Transcript-only loop deciders

**Implicit theorem.** For the head-worldline sequence F_M(t,g(t)) = (symbol, state), a back-to-back window repetition with head positions equal (cyclers) or one-sided-extremal (translated cyclers) forces eventual periodicity-mod-translation. Content: the space-time diagram is determined by its restriction to the head worldline plus extremality marks — a discrete domain-of-dependence/characteristics statement. Decided 175,373,810 machines.

**Nearest theory and gap.** Lin 1963 for the objects; Hennie crossing-sequence reconstruction in spirit; the extremality bookkeeping that makes it sound appears new. Gap: no complexity-theoretic theory of *which* loops exist at which scales.

**Fusion.** Morse–Hedlund-style subword-complexity thresholds on the itinerary could turn empirical step-limit schedules (130/4,100/1,050,000) into theorems ("non-detection by step L implies aperiodicity of type X") for complexity-restricted classes — Skelet 1 (preperiod 5.42×10⁵¹, period 8.47×10⁹) shows the unrestricted bound is hopeless.

**Collatz application.** The transcript analogue is the Terras parity vector (Bernstein–Lagarias conjugacy = "transcript determines tape"). Repeated parity-window + 2-adic-valuation-record extremality would certify an eventual cycle. Warning transfer: Skelet 1 proves "no small transcript repetition" is compatible with astronomically delayed periodicity — do not read simulation bounds as cycle evidence.

#### 2B.7 mxdys 2026 congruence-template portfolio (the holdout killer)

**Implicit theorem.** A "DFA generator" is a finite-memory fold φ over the block stream inducing a finite-index right congruence ≈_φ; CTL(φ) certificates are unions of ≈_φ-classes; closure of the quotient system certifies nonhalting. Search claim: certificate yield over the template library (LRU, FIFO, bounded sets, move-to-front, random DFAs, threshold+mod RLE — literally cache-eviction policies) is learnable by a UCB bandit with reward = solves per microsecond. Shift vs classic FAR: search the congruence lattice via structured generators reaching index in the thousands, not brute-force enumeration at the lattice bottom. Result: 113/1534 BB6 holdouts (https://wiki.bbchallenge.org/wiki/BB(6)).

**Nearest theory and gap.** Abstract regular model checking (Bouajjani–Habermehl–Vojnar 2004) has quotient abstractions *with CEGAR*; algorithm portfolios with bandits are SATzilla-standard. Gap: eviction-policy-indexed congruence families exist in no literature; a bandit empirically ordering *mathematical expressivity* by yield-per-CPU-second is unrecorded; no counterexample-guided refinement is used at all.

**Fusion.** (1) Replace the fixed library with L*/ICE learning — CTL closure failures are a ready-made counterexample oracle, turning the bandit into principled congruence CEGAR aimed at tape invariants. (2) The bandit's arm-ordering estimates the distribution of minimal certifying congruence indices over the machine population — data for the rank-census conjecture (2A.2).

**Collatz application.** Directly runnable: encode Collatz as the transducer, generate the ucb_gen.py arm grid (CPS_LRU × params, RWL_mod × {H≤16, mod≤6}, block n≤24), spend a CPU-month. The mod∈{1..6} coordinate is exactly where 3-adic structure enters a regular certificate. Calibration: the method's BB6 residue is dominated by Collatz-like Cryptids, so expect sub-statement certificates at best; treat systematic failure patterns as measurement.

---

### 2C. Acceleration Towers and Exact Arithmetic (Skelet 1 + rule mining)

#### 2C.1 Stride: closed-form iterates of an odometer-with-fuel (Skelet 1, L2)

**Implicit theorem.** On counter words D|x^{n₁}c₁…x^{n_m}c_m…P, the sweep-return map Phi satisfies: if n_i ≥ k·w_i (w_i = 4^{#C's left of i}), then Phi^k is an explicit affine substitution computable in one pass uniformly in k, and Phi^{n+m} = Phi^m∘Phi^n (stride_add flow law). The counter phase is conjugate to "+1" on a base-4 odometer; run-lengths evolve as an affine cocycle; Phi^k is Presburger-definable in k.

**Nearest theory and gap.** Flat/affine acceleration (Boigelot; Finkel–Leroux FSTTCS'02; LoAT, arxiv.org/pdf/1905.11187) works in fixed finite dimension; stride accelerates over words of *unbounded length* with position-dependent geometric weights 4^i. Odometer/cocycle vocabulary (Downarowicz's survey) fits exactly but was never applied. RMC transducer iteration (Jonsson–Nilsson TACAS 2000; Boigelot–Legay–Wolper CAV 2003) lacks closure theorems covering this non-length-preserving arithmetic-guarded class (searched; none found).

**Fusion.** Prove: iterates of any odometer-like (triangular, expanding integer weights) sweep-return map on RLE words are uniformly Presburger-definable with one-pass guards; fuse with Finkel–Leroux composition to *discover* stride rules automatically; fuse with cocycle theory to compute collision statistics analytically.

**Collatz application.** Collatz already has stride rules (n = a·2^k−1 ⟹ T_odd^k(n) = a·3^k−1). The ×3 carry couples adjacent runs non-triangularly, so closed forms exist exactly on rigid run patterns — the framework says precisely what to hunt: sub-dynamics where the run-length action is triangular-affine with monotone guards; those are the loci of 10¹⁹-fold certified jumps.

#### 2C.2 Uni-cycle: depth-2 acceleration with an untrusted exponent oracle (Skelet 1, L3)

**Implicit theorem.** The accelerated system contains a parameterized loop Presburger-affine in its counters; its n-th power is explicit: xs → xs−nP, append F^n/G^n, r → stride^{nT}(r), with the exact cross-level identity **T = 4P−5** tying level-3 constants to level-2's base-4 structure. The exponent chooser max_stride is deliberately unverified — an untrusted oracle inside a certified procedure, wrong guesses failing the check, never the theorem.

**Nearest theory and gap.** Frohn–Giesl (FMCAD'19, arxiv.org/pdf/2111.13952) accelerate then hunt nontermination — same architecture, but fixed dimension and depth 1. Acceleration towers of depth >1 over parameterized words appear absent from verification literature (searched: LoAT/FAST are depth-1).

**Fusion.** Retarget Frohn–Giesl modular acceleration certificates to Coq lemmas of uni_cycles shape (mechanical synthesis of level-3 rules); export Skelet 1 as the benchmark family for multi-level acceleration.

**Collatz application.** The piece our program most needs: after run-burst acceleration, search the *accelerated* orbit for affine macro-cycles with a decreasing fuel coordinate — certified 10⁴⁰-step jumps in one checked move. The T = 4P−5 phenomenon predicts level-3 constants will be exact affine functions of the level-2 multiplier (3 or 3/2): a concrete signature to search for.

#### 2C.3 Block_Finder: MDL coordinate discovery

**Implicit theorem.** For champion-like machines there exist a block size k and finite skeleton set S such that the reachable set is covered by ∪Im(C_σ) and the return dynamics on exponent vectors is piecewise affine/exponential — i.e., the TM is semi-conjugate to a *flat* counter system, with the conjugacy chosen by minimizing description length of the worst-compressed reachable tape.

**Nearest theory and gap.** Marxen–Buntrock supply the simulation; Markov partitions the analogy; flattability (Leroux–Sutre; FAST) the target property. Gap: PL assumes the counter system is given; bbchallenge *discovers* it from tape dynamics — automatic flattening synthesis exists nowhere.

**Fusion.** Treat block/skeleton discovery as automatic synthesis of a flattable counter-system simulation, then hand the result to complete acceleration engines (FAST, LoAT). Import from symbolic dynamics the discipline of *proving* the cover closed (currently the prover silently falls back when the orbit escapes).

**Collatz application.** The analogue is automated numeration-system selection: search over digit groupings/bases minimizing the description of the accelerated map — mechanizing the choice (2-adic runs vs mod-3^k refinements) we currently make by hand.

#### 2C.4 Trace-triggered guess-and-check rule proving

**Implicit theorem.** Per rule: ∀x ≥ m: F^Δ(C_σ(x)) = C_σ(f(x)) with exact polynomial step count — hypothesis from two equal first-return deltas on a skeleton (Floyd/Brent lifted to abstraction space), verified by exact symbolic macro-execution. Sound, incomplete; no characterization of which machines admit finite rule sets exists.

**Nearest theory and gap.** Daikon/ICE/guess-and-check (Ernst 2001; Sharma–Aiken CAV 2014; Garg et al. 2014) share the architecture; Kincaid's CRA (https://www.cs.princeton.edu/~zkincaid/pub/fmcad15.pdf) extracts recurrences statically but its convex wedge domain merges the 2n/2n+1 paths — it could **not** derive Hydra/Antihydra rules (over-approximations only), and it has no coordinate discovery.

**Fusion.** Pipeline order matters: Block_Finder front end → congruence abstract domain (Granger 1991; porous invariants, Ouaknine et al. CAV 2021, https://arxiv.org/pdf/2106.00662) to split residue classes into single-path affine loops → CRA/LoAT for exact closed forms, coupled inequality invariants, and certified lower bounds. Porous invariants could mechanically prove nonhalting where the Python prover returns UNPROVEN_PARITY — a Collatz-level decider the community lacks.

**Collatz application.** Mine acceleration lemmas from trajectory data in run-length coordinates (rediscover T^{2k}(a·2^k−1) = a·3^k−1 as a Diff/Linear rule); the Past_Config trigger is a cheap screen for candidate lemmas over orbit databases.

#### 2C.5 Closed-form rule hierarchy with recursive meta-rules

**Implicit theorem.** Transitive closures of guarded translations (Presburger) and affine maps (exact geometric closed forms), closed under composition *and unbounded self-application* (rule levels), generating exp-towers of unbounded height with exact integer step counts, exact residues preserved via divmod.

**Nearest theory and gap.** Octagonal-relation acceleration (Bozga–Iosif–Konečný CAV 2010) is complete exactly where apply_diff_rule fails (multiple decreasing counters); LoAT's calculus (https://loat-developers.github.io/LoAT/) generalizes the guard bookkeeping. Gap in the *other* direction: no PL tool iterates its own accelerations to unbounded tower height — LoAT/CRA bottom out in fixed SMT theories; rule levels + ExpInt operate at 10↑↑15 scale.

**Fusion.** PL→bb: octagonal acceleration, eventual-monotonicity guards, full exponential-polynomial sums (replacing the k≤3 Faulhaber ceiling). bb→PL: the unbounded-tower operating regime as a new benchmark class.

**Collatz application.** This *is* the acceleration tower formalized: level-1 = single steps on run coordinates; level-2 = maximal-run closed forms x↦(3^k x+c)/2^j; level-3+ = repeated run-patterns. Adopt rule levels plus the two PL soundness conditions (guard monotonicity, eventual applicability) as our certificate format.

#### 2C.6 ExpInt: residue-computable tower arithmetic

**Implicit theorem.** E_b = closure of Z under (Σ a_i·b^{t_i}+c)/d with nested exponents; every residue map Z→Z/m extends computably to E_b via b^e ≡ b^{((e−k₀) mod λ(M))+k₀} with recursion down the iterated-Carmichael chain; order decided by (height, top) tower valuation — a computable Hardy-field-style ranking.

**Nearest theory and gap.** The core trick is iterated-totient folklore (last digits of Graham's number); Semenov arithmetic (Presburger + 2^x, decidable) is the logical home. Gap: no CAS provides towers as a closed arithmetic *type*; nobody exploits Semenov decidability for rule-guard entailment.

**Fusion.** Package as a "residue-computable tower arithmetic" library wired to Semenov decision procedures; guards and parity branches become decidable queries.

**Collatz application.** Essential at tower scale: verifying accelerated trajectories of n = 2↑↑k + c requires exactly these operations; it is the natural substrate for Michel's "exponential Collatz-like functions" (Def 1.5, michel2015), which he notes have never been studied.

---

### 2D. Skelet 17: The Odometer Trilogy

#### 2D.1 Gray-code decoding (odometer factor)

**Implicit theorem.** φ(S) = (n,l,σ) — Gray-decoded parity word, list length, sum sign — is a semiconjugacy from the counter-list system onto a 3-variable machine: Increment = n→n+σ (dyadic adding machine in Gray coordinates), Halve = n→⌊n/2⌋ with sign flip, plus Zero/Overflow resets; the fiber magnitudes evolve as Birkhoff sums of cylinder indicators along the odometer orbit (divpow2r(n,i) = ⌊(n+2^i)/2^{i+1}⌋). The full factor is an odometer interleaved with halving — a binary counter automaton; the rule-trace is plausibly Toeplitz (unstated, unproven by anyone).

**Nearest theory and gap.** Gray code classical (Knuth 7.2.1.1); odometers/Toeplitz systems (Downarowicz, Contemp. Math. 385) supply exactly the right vocabulary, never applied to busy beavers (calibration searches: zero hits); SMART (Cassaigne–Ollinger–Torres-Avilés, JCSS 2017) is the same phenomenon *by design* — Skelet 17 is the found-in-the-wild instance. Every side condition is definable in Büchi arithmetic (N,+,V₂) even though the tape language is irregular — the recoding is exactly what defeats regular deciders.

**Fusion.** Prove the compactified theorem: the rule-trace orbit closure is an almost-1:1 extension of Z₂. Payoff (1): converts the community's informal "irregularity" of Skelet 17 into a theorem. Payoff (2): poses the classification "which small TMs have zero-entropy blank-tape orbit closures?" — plausibly all machines that survive regular deciders without being Collatz-like: a structural theorem about the halting problem's hard instances.

**Collatz application.** Two-sided. Negative: the 2-adic Collatz extension is conjugate to the full shift (Lagarias 1985; Bernstein–Lagarias 1996), positive entropy, so no global odometer factor — factor-detection cannot touch Syracuse as a whole. Positive: individual orbits can be structured; log the "which run-length coordinate changed" index sequence along accelerated Syracuse orbits and test for 2-automaticity/ruler structure (Walnut, automata learning); any hit yields a recoding under which orbit statements become Büchi-arithmetic sentences — decidable, hence certifiable. This is the precise sense in which "find odometer factors" is well-posed: it certifies exactly the structured exceptional orbits a divergence certificate must be.

#### 2D.2 Embanked invariant + interleaved ruler sequences

**Implicit theorem.** On the empty-state section restricted to the embanked family V (two inequalities: a₀ < 2^{2k+1}−1, a₁ < 3·2^{2k}), the return map N is conjugate to a skew product over a rank-one zero-entropy base: (h₁,h₂) counters with parity-driven switching, fiber adds 2e_{i(h)} with i read from the ruler sequence v₂(m+1) — a hand-rolled Vershik adic map on a two-vertex-per-level Bratteli diagram (0-rooted/1-rooted = the two vertices). V is closed only under the *accelerated composite* N′ (k-induction), certified by a digit-distance monotonicity inequality; epoch totals are Legendre digit-counting sums.

**Nearest theory and gap.** Bratteli–Vershik (Herman–Putnam–Skau 1992) is developed for compact minimal systems, not one non-compact orbit with growing counters; k-induction + acceleration is standard in model checking but effects here need v₂ and powers of 2 (Büchi arithmetic), outside FAST-class accelerators; WSTS explicitly does not apply (zero-tests, no monotonicity).

**Fusion.** Recast as a parametric Bratteli–Vershik library theorem: any counter-list system whose return itinerary is generated by finitely many ctzS-driven lines with dyadic synchronization admits a closed-form epoch map — mechanizing the hardest ~2,000 Coq lines and pre-building the tool BB6's Antihydra-class will need.

**Collatz application.** Import as certificate *format*: invariants k-inductive only relative to an accelerated composite, closure certified by digit-distance inequalities, all side conditions in (N,+,V₂) so a decision procedure discharges them. For accelerated Syracuse, the (h₁,h₂) analogue is tracking v₂(3n+1); ruler-structured v₂-itineraries on residue-class sections would give closed-form epoch maps. Realistic first target: Michel's Collatz-like functions from BB champions.

#### 2D.3 Epoch renormalization: Base_k →* Base_{k+1}

**Implicit theorem.** ∀k: R^{t_k}(S_k) = S_{k+1} avoiding Halt, S_k = (0,2,4,…,2^{2k},0), with exactly one Overflow (ZIHIO) per epoch — the blank-tape orbit is *self-induced*: its first-return map to {Base k} is conjugate, after dilation, to the original system one scale up. Renormalization fixed point with period-doubling combinatorics; epoch lengths ~4^k. Halting excluded because the countdown variable provably exhausts first (Savask's identified crux).

**Nearest theory and gap.** Durand's "self-induced ⟺ substitutive" characterization (ETDS 2000) is the phenomenon, for compact minimal systems; the Feigenbaum attractor conjugate to the dyadic odometer (Bruin–Keller–Nowicki–van Strien) is the same architecture in another category. Nobody has drawn either analogy for busy beavers. Michel's Collatz-like phylum does *not* cover Skelet 17 — the holdout ecology contains a second, rigid phylum.

**Fusion.** The public conjecture: every 5-state machine surviving regular deciders without being Collatz-like has an eventually substitutive rule-trace — the regular-decider sieve *selects for* infinitely renormalizable zero-entropy orbits. If true, nonhalting certificates have a universal format: (renormalization operator, seed family, closure proof).

**Collatz application.** Adopt "renormalization certificates" (parametric family C_k, verified C_k →* C_{k+1}, distinctness) as a first-class certificate type (Sk_closed/Base_ne is the reference implementation). Honest scope: for 3x+1 such a certificate would *disprove* Collatz (Tao/Terras equidistribution says S_k-like orbits shouldn't exist); the real habitat is divergence proofs for engineered maps and BB6-era machines — plus the selection principle: renormalizable holdouts are the solvable ones; random-like ones are where certificate effort dies.

---

### 2E. Epistemic Machinery

#### 2E.1 The probvious calculus

**Implicit theorem.** Two-part object: (1) exact, provable — under any Markov measure μ respecting the *proven* congruence constraints of the verified rule set, P_μ(hit halting set | counter at n) = h(n), the gambler's-ruin solution (Hydra: (1/φ)^{n+1}); (2) the single unproven hypothesis, always the same — the actual itinerary is μ-generic. "Probviously nonhalting with confidence 1−ε" = the conditional theorem "genericity ⟹ halting lies in a set of μ-measure ≤ h(N)" for certified burn-in level N. The curated failure case (the mod-6 machine, BB5 paper footnote 23: naive model predicts halting w.p. 1, reachable set provably avoids halting residues) identifies the exact failure mode: not quotienting by the provable invariant congruence lattice before randomizing.

**Nearest theory and gap.** Lagarias–Weiss (Ann. Appl. Prob. 1992, projecteuclid.org/euclid.aoap/1177005779) is the mechanism, reinvented per machine; Terras 1976 / Tao 2019 (arXiv:1909.03562) are its rigorous shadows; the burn-in bound is a supermartingale value = Martin-Löf test level (Downey–Hirschfeldt), unrecognized. Gap: no formal object "heuristic certificate" exists in any literature.

**Fusion.** Define it: (Coq-verified rule set R, model class M = all Markov measures consistent with R's provable congruence lattice, bound sup_{μ∈M} P_μ(halt | certified prefix) ≤ ε). Machine-checkable end-to-end; the lattice computation makes M algorithmic — Tao's structure-vs-randomness as executable preprocessing.

**Collatz application.** (a) Emit two-part certificates (verified reduction + worst-case-over-model-class bound) for undecided instances; (b) adopt the debugging discipline: compute the exact 2-adic/3-adic invariant congruence lattice *before* any drift computation, or critical-drift-gap statistics are garbage.

#### 2E.2 Champion forecasts

**Implicit theorem.** Under μ = ∏ μ_M over holdouts, Σ(6) is a random variable; P_μ(Σ(6) ≥ 10↑↑16) ≈ 0.055 from geometric reset laws composed with tetrational output maps (https://www.sligocki.com/2025/04/21/lucys-moonlight.html). Randomness matters only through an integer tetration-height variable. **Gap:** Lagarias–Weiss predicted extremal constants for ensembles; nobody in EVT handles tetration-scale tails, and nothing prior assigns dynamics-based (not Chaitin length-based) probabilities to individual halting events. **Fusion:** since ruin excursions scale like exp(c/|drift|), the record tail of BB_μ is governed by the empirical density of holdouts near zero drift — a testable link between a population statistic and the forecast of one uncomputable integer. **Collatz:** a quantitative null hypothesis for our critical-drift-gap experiment: stopping-time records among near-critical bred maps scale like exp(Θ(1/|drift|)); publish model classes alongside any confidence numbers.

#### 2E.3 Wall arguments

**Implicit theorem.** (i) exact: halting basin contains a certified interval I of width L = 3,403,055 below H; (ii) exact: orbits increase monotonically between renewals; (iii) model: geometric jump domination ⟹ P(leap over I forever) ≤ exp(−pL(1−o(1))) (https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA). Exact backward pruning (Wirsching-style preimage tree: 58 of 64 halting values proven unreachable) composed with a forward renewal estimate — Lagarias–Weiss's two models fused into one argument about one orbit. **Gap:** neither community composes certified finite basin computations with domination lemmas. **Fusion:** package as a reusable certified lemma — basin interval (finite computation) + jump-law domination (sometimes provable from rule structure) ⟹ quantitative bound; the first probvious arguments where every probability input is a theorem. **Collatz:** the verified range n ≤ 2^68 *is* a wall; certify wall-width vs jump-law inequalities as lemmas; the natural certificate for the probviously-halting side of a drift gap.

#### 2E.4 Cryptid breeding (Mother of Giants)

**Implicit theorem.** A breeding family {f_θ} agrees outside one congruence-defined cylinder; all children share a proven rule skeleton; the single exceptional rule selects excursion scale, sweeping quasihalting times through >10^10000 range (10^4079 → 10^14006 among siblings; https://wiki.bbchallenge.org/wiki/Mother_of_Giants). **Gap:** Kurtz–Simon explains why one-rule perturbations can do anything (universality); Kontorovich–Lagarias (arXiv:0910.1944) covers only the coarse qx+1 axis; stopping-time statistics across one-cylinder families exist nowhere (searched). **Fusion:** fit T(f_θ) ~ exp(c/|drift(θ)|) across the family — the data already exists, nobody has plotted it. **Collatz:** a ready-made protocol for the critical-drift-gap experiment: freeze skeleton, vary one congruence class, measure (a) stopping-time distribution vs drift, (b) certificate-size growth as drift→0, (c) gap vs crossover between probviously-halting and -nonhalting siblings. The community has the specimens and has never drawn the phase diagram.

#### 2E.5 N-gram entropy barometer

**Implicit theorem.** Necessary direction (provable): an n-state regular certificate puts the reachable orbit closure inside a sofic shift with an n-state cover, so entropy of any factor process ≤ log n. The community uses the converse empirically: measured h5 predicts certificate size ≥ exp(h·window); threshold near h ~ 0.1–0.3 (https://discuss.bbchallenge.org/t/n-gram-frequencies/119). **Gap:** TM entropy is established (Kůrka TCS 1997; Jeandel STACS 2014); its link to certificate existence is not. The converse is probably false in general — Skelet 17 should be the counterexample (low entropy, no small regular certificate). **Fusion:** characterizing which low-entropy machines defeat regular methods = the boundary between sofic-approximable and inherently non-regular TM dynamics; symbolic dynamics has the tools and has never asked. **Collatz:** one-line consequence: no subexponential regular certificate can decide behavior of maps with positive itinerary entropy — explaining why FAR-class methods kill bouncers/counters and never cryptids. Use block-entropy triage across bred families; the drift gap should manifest as an entropy jump.

---

## 3. The Three Sharpest Fusion Plays

**Ranked by expected yield for the Collatz certificate program.**

### #1. Dimension-2 WFAR × path-complete barriers / LP certificates (their WFAR × AJPR + Farkas)
The highest-leverage single step: bbchallenge shipped the two degenerate corners (Boolean matrices; one scalar counter with ±1 weights) of a ladder whose LP-level middle rung is exactly what Collatz needs. Weights in Z² tracking (odd steps, halvings) make 3^a/2^b additive; accept sets become rational polyhedra; closure = polyhedral inclusion certified by stored Farkas multipliers; log₂3 enters only through Stern–Brocot rational slopes, keeping everything in integer linear arithmetic. Joint synthesis is SAT-modulo-difference-logic — one solver call replaces mitmwfar's blind enumerate-perturb-close loop and searches all integer weightings at once.
**First move:** encode accelerated Syracuse as LSB-side string rewriting; implement the SMT search over (DWFA pair structure Booleans, Z² edge weights, polyhedral bounds) with BFS-canonical symmetry-breaking clauses ported from mitm_dfa.rs; target lemmas of the form "no n in regular family S re-enters S / reaches 1 under T," verified by a Coq checker that recomputes the accept set by widening closure from the seed.

### #2. Rule mining × congruence domains + complete acceleration (their Proof_System/validator × Granger congruences, porous invariants, octagonal acceleration, LoAT)
The two literatures are provably disjoint (both reports searched; zero cross-citations) and solve the same problem with complementary failure modes: the bb stack has coordinate discovery, exactness, and unbounded tower height but fails on UNPROVEN_PARITY and multiple decreasing counters; the PL stack has congruence/porous domains (Ouaknine et al. CAV 2021, explicitly motivated by Collatz-like loops) and complete octagonal acceleration (Bozga–Iosif–Konečný CAV 2010) but no coordinate discovery and fixed-theory ceilings. Composing them converts today's heuristic give-ups into certificates and cleanly fences off the genuinely residue-equidistributed hard core.
**First move:** take the machine-checked Hydra/Antihydra/Bigfoot rule tables out of validator.rs, run porous-invariant synthesis on them, and count how many sub-cryptid UNPROVEN_PARITY machines fall; simultaneously port octagonal acceleration into Proof_System to remove the "multiple negative diffs — we fail" branch.

### #3. Odometer/Toeplitz factor theory × the holdout ecology (Skelet 17's Gray-code structure × Downarowicz/Durand/S-adic machinery)
Lower certainty, highest ceiling: prove the rule-trace of Skelet 17 is Toeplitz, converting the community's informal irregularity claim into a theorem (the wiki's "proven irregular Aug 2024" is overstated — the BB5 paper claims only informal arguments); then attack the conjecture that the regular-decider sieve selects for zero-entropy, infinitely renormalizable orbits — a structural theorem about hard halting instances, and a universal certificate format (renormalization operator + seed family + closure).
**First move:** along accelerated Syracuse orbits of structured seeds, log the "which run-length coordinate changed" index sequence and test it for 2-automaticity/ruler structure with Walnut; in parallel, write the Toeplitz-trace irregularity proof for Skelet 17 using the ctzS palindrome lemmas already sitting in BB5_Skelet17.v:4218–4274.

---

## 4. Weird-Unnoticed Items Deserving Attention

1. **Cache-eviction policies as abstract domains, scheduled by a bandit.** mxdys's 2026 holdout killer is a UCB bandit over LRU/FIFO/move-to-front/random-replacement folds used as finite-index congruence generators, with an undocumented bi-level exploration hack (`double c = mt()%2 ? 1 : 0.01`). The dictionary "eviction policy = parameterized basis for right congruences of word streams, empirically ordered by certificate yield" is written down nowhere in abstract interpretation or automata theory. Documentation: an 8-line README; 113/1534 BB6 holdouts fell to it.
2. **The mitmwfar `-m` flag is a De Bruijn path-complete expansion.** addWFAMemory (decider.go:343–383) is the line-graph/memory construction that is *the* canonical power-increase in path-complete Lyapunov theory, with ordering theorems the community could use to schedule refinements — described in the README as an empirical knob.
3. **The Skelet 1 proof is number-free.** Period 8,468,569,863 and preperiod 5.42e51 occur zero times in either Skelet1.v; the celebrated constants are uncertified journalism computed afterwards. Also: the acceleration exponent is chosen by a deliberately unverified oracle inside a certified procedure; strict progress rests on one head-direction bit; and uni_T = 4·uni_P − 5 sits in the source as an exact affine identity — the tower's self-similarity is exact.
4. **The ruler-sequence palindrome at the heart of Skelet 17.** The endgame rests on ctzS_add/ctzS_sub (v₂(2^i−x) = v₂(x)): two odometers launched from opposite ends of a dyadic block tick in unison — the machine physically implements the time-reversal symmetry of the dyadic adding machine. Mentioned in no summary, wiki page, or the BB5 paper. Runner-up: Xu's nearest-integer Gray-code closed form (⟨n/2^i⟩ mod 2) appears to be unpublished.
5. **Probvious confidence is compute-indexed.** Every quoted probability is a hitting bound conditioned on a simulated prefix — an anytime certificate that strengthens monotonically with compute, structurally a supermartingale value placing the halting event inside an effective null cover: algorithmic randomness reinvented, with −log P used informally as a "distance-to-proof" metric, alongside a curated calibration counterexample (the mod-6 machine).
6. **The prover instruments its own number-theoretic-hardness detector.** UNPROVEN_PARITY fires exactly when halting hinges on an unknowable residue of a symbolic count; "cryptid" is operationally defined by a telemetry counter in Proof_System.py. Likewise the coordinate system of every celebrated "high-level rule" is chosen by an MDL heuristic applied at the dynamics' *worst-compression* moment (Block_Finder).
7. **The two "equivalent" WFAR verifiers check different certificate classes** (Go: one convex interval per tuple; Coq: nonconvex unions of points and half-lines), and the paper's Bellman-Ford layer exists in no implementation — deployed "weighted" FAR is one tropical unit deep.
8. **The most refined artifacts are unpublished test code.** The machine-checked Hydra/Antihydra/Bigfoot rule tables live inside test functions of validator.rs; Discord holds the methods threads (mxdys's 2467→1691 holdout equivalence grouping is documented only by its input/output sizes).

---

## 5. Honest Deflation: Reinventions, with the Originals Named

| Community belief / practice | Actually is | Original |
|---|---|---|
| CTL as a decider concept | Inductive safety invariants; regular model checking | Cousot–Cousot POPL 1977; Bouajjani–Jonsson–Nilsson–Touili CAV 2000 |
| FAR's saturation completion | pre* pushdown saturation (knowingly — README cites it) | Bouajjani–Esparza–Maler CONCUR 1997; Finkel–Willems–Wolper 1997 |
| MitM-DFA SAT search with first-use state ordering | Exact DFA identification with BFS symmetry breaking | Heule–Verwer ICGI 2010; Ulyantsev–Zakirzyanov–Shalyto 2016 (code credits community members instead) |
| Macro machines / block simulation / counted repeats | Original within BB — but 1990, not new | Marxen–Buntrock, "Attacking the Busy Beaver 5" (1990); higher-block recoding: Lind–Marcus |
| Savask's sweep-section trick | Poincaré first-return / induced maps, Kakutani skyscrapers | Standard ergodic theory (Petersen) |
| RepWL's exponent abstraction | (0..T−1, ∞) counter abstraction; simple regular expressions | Pnueli–Xu–Zuck 2002; Abdulla–Bouajjani–Jonsson 1998 |
| Seed + verified closure, in-kernel replay | Proof by reflection / certifying algorithms | Boutin 1997; Grégoire–Leroy vm_compute 2002; Gonthier 4CT 2005; CeTA (Thiemann–Sternagel 2009) |
| The rule-DSL validator's proof system | Rewriting induction on compressed words + procedure summaries | Reddy CADE 1990; Lohrey's power-word algorithmics |
| "Cryptids reduce to Collatz-like maps" | Published 30+ years ago | Michel 1993 (Arch. Math. Logic 32:351–367) and 2015 (LMCS 11(4:10)); existence guaranteed by Conway 1972 / Kurtz–Simon 2007 |
| Random-walk drift heuristics for cryptids | The 3x+1 stochastic-model program, per machine | Terras 1976; Lagarias–Weiss 1992 |
| ExpInt's mod-of-tower core | Iterated-Carmichael/totient folklore (Graham's-number last digits) | Folklore; logical home Semenov 1984 |
| UCB over decider configurations | Algorithm portfolios with bandit selection | SATzilla lineage |
| WFAR's sign sets / feasibility pruning | Difference constraints, node potentials, interval widening | Bellman-Ford potential theory (Cormen et al.); Cousot–Cousot widening |
| Affine conjugacy of cryptids across substrates; TNF | Classification of generalized 3x+1 maps up to linear conjugacy | Wirsching LNM 1681; Matthews's generalized Collatz surveys |
| BMO verified-reduction exports | Mechanized many-one reductions between undecidable problems | Coq Library of Undecidability Proofs (Forster et al., ITP 2019+) |
| The 7-level Coq tower | Forward-simulation composition from verified compilation | Leroy, CompCert (CACM 2009) |

**The honest bottom line.** Almost every load-bearing *component* has an established home; the community's genuine contributions are (a) two certificate objects with no clean prior analogue — context-universal shift-templates certifying periodicity polylog in preperiod, and the measured certificate-rank census over program space; (b) several exact assemblies nobody on either side has built (acceleration towers of depth >1, congruence-template portfolios, weighted meet-in-the-middle synthesis of the state map itself); and (c) a real vocabulary gap — the reverse translations in this report (odometers, Bratteli–Vershik, path-complete barriers, Medvedev lifts, view abstraction, Martin-Löf tests) appear in print on neither side, which is precisely why the verdicts skew "new twist" rather than "reinvention": the pieces are classical, the bridges are unbuilt, and the bridges are where the yield is.