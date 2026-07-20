# Cryptid structure report

Agent-mined from bbchallenge wiki/blogs/Michel papers, 2026-07-20; recurrences verified numerically by the agent. Referenced from STRATEGY.md §3.6.

All recurrences verified numerically (champion orbit reproduces Michel's exactly; Space Needle matches the wiki's published orbit). Here is the full report.

---

# CRYPTID STRUCTURE REPORT: The arithmetic anatomy of Busy Beaver holdouts

**PDFs saved to /Users/simon/Desktop/COLLATZ/papers/ this session:** `michel1993_bb_collatz.pdf` (Michel, *Busy beaver competition and Collatz-like problems*, Arch. Math. Logic 32:351–367, 1993 — full Springer PDF, text-verified), `michel2015_number_theory_bb.pdf` (= arXiv:1311.1029, LMCS 11(4:10), 2015), `michel_bb_historical_survey.pdf` (arXiv:0906.3749), `erdos_conjecture_tm_2107.12475.pdf`, `xu-skelet17-chrisxu.pdf` (Chris Xu's Skelet 17 proof). Note: `docs.bbchallenge.org` does not resolve from this machine, so savask's Skelet 17 PDF and the Erdős/weak-Collatz machine .txt files could not be mirrored; URLs given below. The directory already contained the BB(5) determination paper (`bbchallenge-2025-bb5-determination.pdf` = arXiv:2509.12337) and Stérin–Woods BB(15) hardness (`sterin-woods-2021-bb15-hardness-collatz-like.pdf`).

**Terminology used below.** *Base map*: the extracted arithmetic recurrence. *Functional*: what the BB question evaluates on the orbit. *Drift class*: sign of the drift of the halting-relevant observable relative to the halting boundary, under the empirical "parities are a fair coin" model. "Probviously" = probabilistically obvious but unproven (bbchallenge term: https://wiki.bbchallenge.org/wiki/Probviously).

## PART I — WILD CRYPTIDS (found in the wild, minimal)

Master list: https://wiki.bbchallenge.org/wiki/Cryptids

### 1. ANTIHYDRA — BB(6), the canonical BB(6) blocker
- **Machine:** `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` (6 states, 2 symbols; unique undefined transition F0). Discovered by mxdys on Discord, 2024-06-28; high-level rules by Racheline.
- **Base map (exact, published):** a₀ = 8, a_{n+1} = a_n + ⌊a_n/2⌋. Equivalently: a even → 3a/2; a odd → (3a−1)/2 (i.e., ⌊3a/2⌋). Wiki tape-level rules: A(a,2b) → A(a+2, 3b+2) in 2a+3b²+12b+11 steps; A(a+1, 2b+1) → A(a, 3b+3); A(0, 2b+1) → halt configuration 0^∞ <F 1101 3b 0^∞. Ligocki's form uses E(a,b) = 0^∞ 1^b 0 1^a E> 0^∞ starting E(4,0) — parameterizations differ by offsets; the integer form above is canonical (BMO statement).
- **Observable/functional:** counter b integrating the parity history: b += 2 on even a, b −= 1 on odd a (b₀ = 0).
- **Halting predicate (exact):** halts iff a is odd while b = 0 — i.e., iff some prefix a₀..a_k contains **more than twice as many odd terms as even terms**. (Cryptids-page phrasing: termination condition O > 2E.)
- **Drift class:** value supercritical (×3/2 per step, a > 2^37 after 2^38 rule steps); counter walk (+2, −1) with fair coin has drift **+1/2 away from the boundary**. P(hit −1 from n) = ((√5−1)/2)^{n+1} = (1/φ)^{n+1} — golden-ratio decay; current halting-probability estimate ≈ 2.884×10^(−28,723,042,565).
- **Status:** open; the machine that made "BB(6) is Hard" official. Partial results: parity sequence proven **not Sturmian** (via Dubickas 2009, Glasgow Math. J. 51(2):243–252); explicit connection drawn to **Mahler's Z-number problem** (parities of ⌊ξ(3/2)^n⌋); basics formalized in Lean (https://github.com/rwst/Antihydra-Basics). OEIS: A385902 (b-values); A386792 (orbit values — wiki attribution). 
- **Sources:** https://wiki.bbchallenge.org/wiki/Antihydra ; https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html ; https://bbchallenge.org/antihydra ; popular account: https://benbrubaker.com/why-busy-beaver-hunters-fear-the-antihydra/

### 2. HYDRA — BB(2,5)
- **Machine:** `1RB3RB---3LA1RA_2LA3RA4LB0LB0LA` (2 states, 5 symbols; undefined A2). Found by Daniel Yuan, Discord, 2024-04-20; analyzed by Shawn Ligocki.
- **Base map (exact):** **identical to Antihydra**: a_{n+1} = a_n + ⌊a_n/2⌋, but a₀ = 3. Two-variable published form: Start → C(3,0); C(2n, b+1) → C(3n, b); C(2n+1, b) → C(3n+1, b+2); C(2n, 0) → Halt(9n−6). (Wiki uses a shifted parameterization C(2a,b+1)→C(3a+3,b) etc. — same dynamics.)
- **Observable/functional:** counter b: −1 on even step, +2 on odd step.
- **Halting predicate (exact):** halts iff an even step occurs with b = 0 — i.e., iff some prefix contains **more than twice as many even terms as odd terms** (mirror image of Antihydra).
- **Drift class:** identical to Antihydra: drift +1/2 away from boundary; P(halt from b=n) = (1/φ)^{n+1}; at b = 2,005,373 (after ~4M rule steps, value >10^700,000): (1/φ)^{2,005,374} < 2^{−1,000,000}.
- **Status:** open; blocks BB(2,5). **Sibling cryptid** found days later by Yuan: `1RB3RB---3LA1RA_2LA3RA4LB0LB1LB` (differs in one transition; probviously non-halting, same family). A compiled 9-state 2-symbol Hydra exists (BB(9) upper-bound coordinate): https://wiki.bbchallenge.org/wiki/File:Hydra_9_states.txt
- **Key structural fact:** Antihydra and Hydra are **the same base map with mirrored halting functional and different seed** (8 vs 3). Ligocki: "The only difference is that Antihydra starts at 8 instead of 3 and the halting condition is reversed."
- **Sources:** https://wiki.bbchallenge.org/wiki/Hydra ; https://www.sligocki.com/2024/05/10/bb-2-5-is-hard.html

### 3. BIGFOOT — BB(3,3), the first Cryptid (term coined here)
- **Machine:** `1RB2RA1LC_2LC1RB2RB_---2LA1LA` (3 states, 3 symbols; undefined C0). Found by savask, 2023-10-14; analyzed and named by Ligocki within two days.
- **Base map (exact, blog form):** config A(a,b,c) with c ∈ {2,3,5}; cases on b mod 6: A(a,6k,c)→A(a,8k+c−1,2); A(a,6k+1,c)→A(a+1,8k+c−1,3); A(a,6k+2,c)→A(a−1,8k+c+3,2); A(a,6k+3,c)→A(a,8k+c+1,5); A(a,6k+4,c)→A(a+1,8k+c+3,2); A(a,6k+5,c)→A(a,8k+c+5,3). So b → (4/3)b + O(1): a **×4/3 mod-6 map**. Start: A(2,1,2) at step 69.
- **Observable/functional:** counter a: +1 on b ≡ 1,4 (mod 6); −1 on b ≡ 2 (mod 6); unchanged otherwise. Effective walk: ±1 with P(+1)=2/3, P(−1)=1/3.
- **Halting predicate (exact):** A(0, 6k+2, c) → Halt(16k+2c+7) — i.e., the walk hits −1: **a = 0 exactly when b ≡ 2 (mod 6)**.
- **Drift class:** counter drift +1/3 away from boundary; P(hit −1 from n) = 2^{−(n+1)}; with a ≈ 4×10^6 after 24M iterations: ≈ 2.697×10^(−1,204,087).
- **Status:** open; blocks BB(3,3). Compiled 7-state 2-symbol version exists (BB(7) coordinate): https://github.com/sligocki/sligocki.github.io/issues/8#issuecomment-2140887228
- **Sources:** https://wiki.bbchallenge.org/wiki/Bigfoot ; https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html

### 4. SPACE NEEDLE — BB(6), a *different* hard functional (no counter)
- **Machine:** `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`. Found by mxdys, 2025-01-09. Sibling: `1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC` (mxdys, Aug 2024).
- **Base map (exact):** b₀ = 6; write b = (2a+1)·2^k (k = v₂(b)); then f(b) = b + k + 3a. Verified orbit: 6→10→17→41→101→251→626→1095→2736→2995→... Average growth ×1.92006 per step (log-factor 0.652355). Low-level form (Ducharme): start (3,1); (1,c)→halt; (2b,c)→(2+5b+c,1); (2b+1,c)→(b−1, 3+b+c).
- **Observable/functional:** the **2-adic valuation of the value itself** — no auxiliary counter.
- **Halting predicate (exact):** halts iff some iterate is an **exact power of 2** (odd part = 1).
- **Drift class:** value supercritical (×1.92); halting set exponentially thin in value space; per-step hit probability ~ b^{−1}-ish and summable; simulated 17M+ terms, b now > 10^4,800,000, max v₂ observed = 24. Probviously non-halting. Proving it "requires proving that a highly chaotically growing sequence never intersects a value equal to 2^n" — a 2-adic-valuation-under-addition problem.
- **Status:** open; Beaver Math Olympiad problem 6.
- **Sources:** https://wiki.bbchallenge.org/wiki/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD ; https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad

### 5. BMO Problem 1 machine — BB(6), coupled subtractive pair
- **Machine:** `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE`.
- **Base map (exact):** (a₁,b₁)=(1,2); if a ≥ b: (a,b) → (a−b, 4b+2); if a < b: (a,b) → (2a+1, b−a).
- **Halting predicate:** halts iff **a_i = b_i** ever (exact coincidence of two coupled sequences).
- **Drift class / status:** mutual-subtraction dynamics (Euclidean-like) with ×4 / ×2 growth branches; halting = codimension-1 exact hit; undecided, listed among "chaotic" cryptids. Source: https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad (Problem 1).

### 6. BMO Problem 5 machine — BB(6), exponential threshold
- **Machine:** `1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE`.
- **Base map (exact):** (a₁,b₁)=(0,5); f(x) = 10·2^x − 1; if b ≥ f(a): (a,b) → (a+1, b − f(a)); if b < f(a): (a,b) → (a, 3b + a + 5).
- **Halting predicate:** halts iff **b_i = f(a_i) − 1** exactly. Multiplicative-3 growth racing an exponential staircase; halting = exact hit of exponentially spaced points. This is the wild instance of Michel's "exponential Collatz-like" class. Undecided. Source: BMO Problem 5 (URL above).

### 7. BMO Problem 8 machine — BB(6)
- **Machine:** `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`.
- **Base map (exact):** (a₁,b₁)=(10,12); if a > ⌊b/2⌋: (a,b) → (a − ⌊b/2⌋ − 3, 3⌊(b+1)/2⌋ + 6); else (a,b) → (3a+5, b − 2a).
- **Halting predicate:** halts iff **a_i = ⌊b_i/2⌋ + 1** exactly. Undecided. Source: BMO Problem 8.

### 8. LUCY'S MOONLIGHT — BB(6), the *probviously-halting* archetype
- **Machine:** `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`. Found by Racheline, 2025-03-01; analyzed by Ligocki (Apr 2025); Lean formalization: https://github.com/rwst/bbchallenge/blob/main/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA/machine.lean
- **Base map (exact):** C(a,b,c) = 0^∞ 1011^a 1^b 10^c C> 0^∞; rules on b mod 3: C(a+1, 3k) → C(a, 8k+6); C(a+2, 3k+1) → C(a, 8k+16); C(0, 3k+1) → C(0, 8k+5); **C(1, 3k+1) → Halt(6k+14)**. So b → (8/3)b + O(1) while a **decreases** by 1 or 2 per step, with epoch resets a ← (value of order b).
- **Halting predicate (exact):** a = 1 exactly when b ≡ 1 (mod 3).
- **Drift class:** counter drifts **toward** the halting boundary → halting is a.s. (recurrent event, constant hit probability per descent epoch). But epoch lengths tower: c₀ = 14, c₁ = 11,292, c₂ ≈ 10^2901.92. Probviously **halting**, with "a 5% chance of beating the former BB(6) champion". Hardness lives in the *value of the halting-time functional*, which is pseudorandom and unreachable by simulation.
- **Source:** https://wiki.bbchallenge.org/wiki/Lucy%27s_Moonlight

### 9. Remaining wild BB(6) cryptids (from the Cryptids table, verbatim notes)
- `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA` — "Variant of Hydra and Antihydra. Probviously non-halting."
- `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC` — "Similar random walk mechanism to Hydra, Antihydra. Probviously non-halting."
- `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---` (Daniel Yuan, Sep 2024) — same note.
- `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB` (Racheline, Nov 2024) — same note.
- `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC` (mxdys, Jul 2024) — "Has near-identical behavior to **16 related BB(6) holdouts**. Probviously halting." (A whole *family* of one arithmetic problem.)
- Six further "probviously halting" machines (Racheline Jul 2024 ×3, Nov 2024 ×2, Feb 2025; mxdys Jul 2025) and one "probviously decidable" machine `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE` — "Estimated to have a 3/5 chance of becoming a translated cycler and a 2/5 chance of halting."
- `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` (sheep, Apr 2026) — probviously non-halting.
- Machine codes + statuses all at https://wiki.bbchallenge.org/wiki/Cryptids (with per-machine bbchallenge.org links).
- **Global status:** BB(6) ≥ 2↑↑↑5 (mxdys champion, Jun 2025); ~1,094 holdout machines up to equivalence as of June 2026 (2,320 raw); partial Rocq proof at https://github.com/ccz181078/busycoq/tree/BB6; annotated holdout spreadsheet: https://docs.google.com/spreadsheets/d/1mMp8bAcTFT91j7azn72liX8NSTwc2E_ozKnOGTfRCfw/ ; https://wiki.bbchallenge.org/wiki/BB(6)

### 10. FENRIR — Fractran, BBf(22): the family reproduces in another substrate
- **Programs (exact):** `[1/15, 27/77, 49/3, 10/49, 33/2]`, `[1/15, 49/3, 27/77, 10/49, 33/2]`, `[27/35, 1/33, 25/3, 22/25, 21/2]`. Found 2026-03-22 by Jason Yuen and Claude Opus 4.6 (of 2003 BBf(22) holdouts, 1997 proven non-halting and 3 halting; these 3 remain).
- **Base map (exact):** S(x,2y) → S(x−1, 5y+2); S(x,2y+1) → S(x+2, 5y); start S(0,1); **halt iff S(0, even y)**. I.e., value y → (5/2)y + O(1) by parity; counter x: −1 on even, +2 on odd — **the Hydra functional verbatim, with multiplier 5/2 instead of 3/2**.
- **Other Fractran cryptids:** Frankenstein's Monster (size 23) `[1/12, 9/10, 14/3, 121/2, 5/7, 3/11]` — biased walk, steps {+1,+3,−1}; an Antihydra-like size 23 `[9/10, 1/6, 1331/2, 14/3, 5/7, 3/11]`; a size-25 program simulating Hydra `[363/14, 125/2, 22/21, 1/3, 7/11, 14/5]`.
- **Source:** https://wiki.bbchallenge.org/wiki/Fractran#Fenrir

## PART II — THE SOLVED CONTRAST SET (same family, tractable)

### 11. BB(5) champion (Marxen–Buntrock 1990) — halts; fully proven; the anchor of Coq-BB5
- **Machine:** `1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA`; s = 47,176,870 = S(5), σ = 4098 = Σ(5).
- **Base map (exact, Michel 1993/2009):** C(n) = 0^∞ (A0) 1^n 0^∞; C(3k) → C(5k+6) in 5k²+19k+15 steps; C(3k+1) → C(5k+9) in 5k²+25k+27 steps; **C(3k+2) → HALT** in 6k+12 steps. Michel taxonomy: *pure Collatz-like, type 3 → 5, without parameter*.
- **Orbit (verified this session):** 0→6→16→34→64→114→196→334→564→946→1584→2646→4416→7366→12284 → halt (15 transitions; 12284 ≡ 2 mod 3). Quadratic per-transition cost gives the 4.7×10^7 total.
- **WHY TRACTABLE:** the halting set is a **full residue class mod 3** — positive density ≈ 1/3 per iterate under the random model, so halting is the measure-one outcome, expected within O(1) iterates; and the actual blank-tape orbit hits it at step 15. The certificate is a finite computation. Michel explicitly notes the *general* problem (behavior of g on all n) is open — the BB instance is easy only because it evaluates the functional at a single point that happens to sit on the halting (measure-1) side. Sources: `michel1993_bb_collatz.pdf`; https://wiki.bbchallenge.org/wiki/1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA ; arXiv:2509.12337.

### 12. Skelet 1 — BB(5) holdout, proven non-halting (rigidity type: exact periodicity)
- `1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC`. **Translated cycler**: period 8,468,569,863, preperiod ≈ 5.42×10^51 steps. Proven by Pavel Kropitz & Shawn Ligocki (2023); individually proven in Coq-BB5. Tractable because behavior is **eventually exactly periodic** — a rigid invariant exists despite astronomical constants. https://wiki.bbchallenge.org/wiki/Skelet_1

### 13. Skelet 17 — BB(5) holdout, proven non-halting (rigidity type: structured counter)
- `1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA`. Behavior = **Gray-code counter** over lists 0^{n₁}11 0^{n₂}…; approx-periodic, visiting milestone configs near powers of 16. Proven by savask (structure) → Chris Xu (full bisimulation proof, https://chrisxudoesmath.com/papers/skelet17.pdf, saved as `xu-skelet17-chrisxu.pdf`; arXiv version already in papers dir) → formalized by mxdys in Coq-BB5 (Aug 2024, https://github.com/ccz181078/Coq-BB5/blob/main/CoqBB5/Skelet17.md). Tractable because the observable is a **counter with a provable invariant**, not a mixing arithmetic map. https://wiki.bbchallenge.org/wiki/Skelet_17

### 14. Solved Beaver Math Olympiad problems (proven non-halting) — the sharpest intra-family contrast
- **BMO 3** (BB(2,5) pair `1RB0RB3LA4LA2RA_2LB3RA---3RA4RB`, `1RB1RB3LA4LA2RA_2LB3RA---3RA4RB`): a₀ = 2, a_n = a_{n−1} + 2^{v₂(a_{n−1})+2} − 1; halt iff a_n = 4^k. **Answer: never.** Same "hit an exact power" predicate as Space Needle — but here the valuation dynamics are rigid enough for an invariant/closed form.
- **BMO 4** (`1RB3RB---1LB0LA_2LA4RA3LA4RB1LB`): a₀ = 2; a ≡ 0 (mod 3): a → a/3 + 2^{n+1}; a ≡ 2 (mod 3): a → (a−2)/3 + 2^{n−1}; halt iff a ≡ 1 (mod 3) ever. **Answer: never** — closed form a_n = (3/5)·{2^{n+7}/3, 2^{n−2}, 2^{n+1}, 2^{n+2}} by n mod 4, giving the **eventually periodic residue pattern** a_{4k} ≡ 2, a_{4k+j} ≡ 0 (mod 3). This is the textbook case of "provable because orbits are eventually periodic mod something".
- **BMO 7** (BB(6) `1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---`): f(n) = n + 1 + (v₂(n+1) mod 2); a₀ = 1, a_{n+1} = f^{n+2}(⌊a_n/2⌋); halt iff a_k even. **Answer: never** — a parity invariant.
- Source: https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad

## PART III — TAXONOMIES / TABULATIONS FOUND (task item 6)

1. **Michel 1993** (saved: `michel1993_bb_collatz.pdf`): proves the halting problems of six ex-champion 5-state machines are Collatz-like iterations; poses their all-input problems as open number theory. Original URL: https://link.springer.com/content/pdf/10.1007/BF01409968.pdf
2. **Michel 2015, LMCS 11(4:10)** (saved: `michel2015_number_theory_bb.pdf` = arXiv:1311.1029) — the explicit tabulation. **Taxonomy (Defs 1.2–1.5):** *pure Collatz-like of type d → a* (d residue cases, all slopes a; "without parameter" = map on Z; "with parameter" = map on Z × S, S a finite parameter set — a finite automaton riding on the arithmetic); *exponential Collatz-like* (f(dn+i) = (a_i p^n + b_i)/c_i); *R(bin(p))* (an apparently infinite rule family indexed by binary strings); *unclassifiable* (Kropitz's 2010 6×2 machine, g₅(n,p)). **Tables 1–5** classify all analyzed champions: all 5×2 record holders are pure Collatz-like (types 4→9, 3→8, 8→15, 3→5); 6×2 champions are pure 4→10, R(bin(p)) 2→3 / 2→5 / 4→6, exponential Collatz-like, and unclassifiable; 3×3 machine M1 is type 8→14; 2×4 machine M2 type 3→5 with parameter (g₂, halts because g₂¹³(1,2) undefined); 2×5 machine M3 type **2→3 with parameter** (g₃(2k,s) ≈ (3k+c_s, s′) — parity-cases ×3/2 plus an 8-state parameter automaton: literally the same base map as Hydra/Antihydra, 17 years earlier, on the halting side).
3. **Michel's historical survey** (saved: `michel_bb_historical_survey.pdf`, arXiv:0906.3749; maintained page version): per-machine behavior theorems including the champion's (Section 5.2.1, verified above).
4. **Community successors to Michel:** the Cryptids page (https://wiki.bbchallenge.org/wiki/Cryptids), the **Beaver Math Olympiad** page (https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad — pure math restatements, solved/unsolved status), and the Collatz-like page (https://wiki.bbchallenge.org/wiki/Collatz-like — defines Generalized Collatz Functions, notes their halting problem is Turing-complete per Kurtz–Simon, distinguishes "consistent Collatz" with shared linear coefficient).
5. **Constructed cryptids** (calibration ceiling for the hardness scale): Goldbach = BB(25); Erdős's 2^n-base-3 conjecture = BB(5,4) and BB(15) (arXiv:2107.12475, saved); **weak Collatz conjecture = BB(43,4) and BB(124)** (Stérin–Woods, saved); Riemann Hypothesis = BB(744); PA-consistency = BB(372) (Feb 2026); ZF-consistency = BB(432) (Wade); Fermat's Last Theorem was a BB(~400) cryptid until 1994. URLs on the Cryptids page.

## PART IV — SYNTHESIS: what the hard ones share that the solved ones lack

**Universality of the base map.** Every wild cryptid's base map is drawn from the same tiny family: multiply by a small rational, with the branch chosen by a residue (usually parity) of the current value — ×3/2 (Hydra, Antihydra, and at least five more BB(6) machines described as "variant of / similar random-walk mechanism to Hydra, Antihydra"), ×4/3 mod 6 (Bigfoot), ×5/2 (Fenrir, in Fractran), ×8/3 mod 3 (Lucy's Moonlight), ×~1.92 with a 2-adic additive term (Space Needle). The solved champions live in the *same* family (Michel types 3→5, 8→14, 2→3-with-parameter…). Independent minimal machines in three different substrates (2-symbol TMs, 5-symbol TMs, Fractran) converge on ⌊3n/2⌋-type parity dynamics — strong empirical support for treating "the symbolic/parity dynamics of ×3, ÷2" as one underlying object on which all these problems are functionals.

**The discriminating axis is the functional, not the map.** Precisely:

- **Solved-halting (champions):** halting predicate = *current value lies in a fixed residue class* (positive density per iterate). Measure-1 event; finite orbit is the certificate. (BB(5) champion: class 2 mod 3, hit at iterate 15.)
- **Hard, probviously non-halting (Antihydra, Hydra + sibling, Bigfoot, Fenrir, several BB(6)):** halting predicate = *a counter that integrates the residue history hits an exact boundary against positive drift*. The functional is a cumulative parity-balance crossing a linear boundary (O > 2E; E > 2O; a = 0 at b ≡ 2 mod 6; x = 0 at even y). Halting probability decays geometrically in the counter — (1/φ)^{n+1} for step-set {+2,−1}, 2^{−(n+1)} for {+1,+1,−1} — so non-halting is "true with probability 1" but a proof must control the deviation of a deterministic parity sequence from equidistribution for all time. This is exactly the open core of Mahler's Z-numbers / normality of (3/2)^n orbits; the only partial result on Antihydra is negative-structure (parities not Sturmian, via Dubickas 2009).
- **Hard, probviously non-halting, valueless variant (Space Needle, BMO 1/5/8):** predicate = *exact hit of an exponentially thin set in value space* (powers of 2; b = f(a)−1; a = b). Same measure-0-target shape without an auxiliary counter; the obstruction is 2-adic valuation behavior under addition rather than parity balance.
- **Hard, probviously halting (Lucy's Moonlight + the 16-machine family + ~6 more):** the counter drifts *toward* the boundary; halting is a.s.; the hardness migrates into the *value of the halting-time functional* (c₂ ≈ 10^2901.92 rule steps of pseudorandom trajectory — no feasible certificate on either side).
- **Solved-non-halting (Skelet 1, Skelet 17, BMO 3/4/7):** superficially in the hard class, but rescued by discovered **rigidity**: eventual exact periodicity of configurations (Skelet 1: period 8.47×10^9 after ~10^51 steps); a structured counter with a provable invariant (Skelet 17: Gray code); a closed form making residues/valuations eventually periodic (BMO 4: a_n mod 3 has period 4 in n; BMO 3, BMO 7: valuation/parity invariants). In each case the "pseudorandom" observable was in fact eventually deterministic modulo something.

**Precise family axes** for coordinating Collatz-like problem space, as instantiated by this sample: (1) **multiplier** p/q of the base map (3/2, 4/3, 5/2, 8/3, 5/3, …); (2) **branch alphabet and measure** — which residues drive which affine branch; (3) **functional type** — per-step residue membership / integrated-counter boundary crossing / exact thin-set hit / halting-time value; (4) **drift sign of the halting observable** (repelling = probviously-non-halting hard; attracting = probviously-halting hard; the sample contains *no critical/zero-drift wild cryptid* — a conspicuous gap); (5) **counter step-set**, which fixes the hitting-probability constant ((+2,−1) → golden ratio; ±1 biased 2:1 → powers of 2); (6) **presence/absence of algebraic rigidity** (conjugacy to a counter, eventual periodicity, closed form) — the only property that has ever moved a machine from the hard column to the solved column.

**Placement of Collatz itself on these axes:** Collatz's accelerated map (3n+1)/2, n/2 has *negative* log-drift (subcritical, orbits a.s. contract), and the conjecture is a measure-1 statement over *all* seeds; the cryptids are supercritical single-seed maps whose BB-question is a measure-0 statement. Both are bounded functionals of the same object — the deviation-from-equidistribution of the ×3,÷2 parity symbolic dynamics — evaluated at opposite corners of (drift sign) × (quantifier over seeds). The machine-derived sample also pins an empirical hardness frontier in machine-size coordinates: hard at (3,3), (2,5), (6,2), Fractran-22; solved at (2,4) (=3,932,964), (5,2), (4,2) — note the states/symbols asymmetry: (5,2) solved but (2,5) hard. Full Collatz itself sits no higher than BB(124) / BB(43,4), and the smallest *natural* hard point is 6 states, 2 symbols (Antihydra) — "the smallest open problem in mathematics on the Busy Beaver scale."

**Complete source URL list:** https://wiki.bbchallenge.org/wiki/Cryptids ; https://wiki.bbchallenge.org/wiki/Antihydra ; https://wiki.bbchallenge.org/wiki/Hydra ; https://wiki.bbchallenge.org/wiki/Bigfoot ; https://wiki.bbchallenge.org/wiki/Lucy%27s_Moonlight ; https://wiki.bbchallenge.org/wiki/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD ; https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad ; https://wiki.bbchallenge.org/wiki/Fractran ; https://wiki.bbchallenge.org/wiki/Collatz-like ; https://wiki.bbchallenge.org/wiki/Skelet_1 ; https://wiki.bbchallenge.org/wiki/Skelet_17 ; https://wiki.bbchallenge.org/wiki/BB(6) ; https://wiki.bbchallenge.org/wiki/1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA ; https://wiki.bbchallenge.org/wiki/Probviously ; https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html ; https://www.sligocki.com/2024/05/10/bb-2-5-is-hard.html ; https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html ; https://arxiv.org/abs/1311.1029 ; https://arxiv.org/abs/0906.3749 ; https://arxiv.org/abs/2107.12475 ; https://arxiv.org/abs/2509.12337 ; https://link.springer.com/content/pdf/10.1007/BF01409968.pdf ; https://chrisxudoesmath.com/papers/skelet17.pdf ; https://github.com/ccz181078/Coq-BB5/blob/main/CoqBB5/Skelet17.md ; https://github.com/ccz181078/busycoq/tree/BB6 ; https://github.com/rwst/Antihydra-Basics ; https://oeis.org/A385902 ; https://benbrubaker.com/why-busy-beaver-hunters-fear-the-antihydra/ ; https://bbchallenge.org/antihydra ; holdout spreadsheet https://docs.google.com/spreadsheets/d/1mMp8bAcTFT91j7azn72liX8NSTwc2E_ozKnOGTfRCfw/

**Caveats:** (a) Hydra/Antihydra two-variable rule coefficients differ across wiki vs. blog parameterizations (offset conventions); the single-integer forms given here are the canonical BMO statements and were verified numerically this session, as were the champion orbit and Space Needle orbit. (b) Wiki-reported simulation depths (b-values, step counts) are moving targets; figures above are as published at the cited revisions. (c) `docs.bbchallenge.org` (savask's Skelet 17 PDF, Erdős/weak-Collatz machine files) was unresolvable from this network; those artifacts are cited but not mirrored.