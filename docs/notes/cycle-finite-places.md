# Collatz cycles at the finite places: does the sporadic-prime structure exclude anything?

2026-07-20. Status: **structural + computational note; verdict NEGATIVE-with-nuance.**
Tags: **[PROVED]**, **[VERIFIED]** (by the computation in `experiments/cycles/`),
**[HEURISTIC]**, **[CONJECTURAL]**, **[OPEN]**. Consulted gpt-5.6-sol (its
counterexample corrected a false lemma below and supplied the sharp conjecture
in §8; verified independently). Context: `docs/notes/dynamical-hasse.md`
(monodromy reformulation, Q1/Q2), `docs/LANDSCAPE.md` cycle row,
`experiments/expsum/` (the exponential sum `S_{K,L}(ξ)` machinery this reuses).

**One-line verdict.** The finite places `p | Λ = 2^K − 3^L` — untouched by the
Steiner→Hercher archimedean literature — carry genuine, computable obstructions,
but they give **no exclusion that is both orthogonal to Baker and feasible in the
archimedean-relevant regime**. Every finite-place obstruction is *infeasible
where it would be new* (needs a giant prime factor of a ~2^K-bit `Λ` and a DP over
~2^{0.95K} states) and *redundant where it is feasible* (small `K`, already
excluded by Barina's `n < 2^71`). It collapses onto the same equidistribution
heuristic `N_Λ ≈ C/Λ ≈ 2^{−0.05K}` that already underlies belief in the
conjecture. The one clean rigorous witness of the collapse is the m=1 (Steiner)
stratum (§7).

---

## 1. Setup and the object of study

A length-`(K,L)` integer cycle exists ⟹ `Λ := 2^K − 3^L` divides the
Böhm–Sontacchi weight `W(v) = Σ_{i=0}^{L−1} 3^{L−1−i} 2^{b_i}` for some parity
word `v` of shape `(K,L)` (`b_0<…<b_{L−1}` = one-positions), with cycle element
`W(v)/Λ` (`docs/notes/dynamical-hasse.md` Thm 2/3). Number of admissible words
`C(K,L) = C(K,L) ≈ 2^{H(L/K)K}`; in the positive window `L/K ≈ log_2 3` this is
`≈ 2^{0.94992K}`.

**Definition.** For a modulus `m`, `N_m(K,L) := #{words of shape (K,L) : W(v) ≡ 0
(mod m)}`. A **finite-place obstruction** at a prime power `p^e ‖ Λ` is
`N_{p^e}(K,L) = 0`: no word is divisible, so no cycle of that shape — an
exclusion located purely at finite places, **with no linear-forms-in-logs input**.

`N_m` is computed exactly by the transfer-matrix DP (right-to-left over
positions, state = #ones-so-far, weight accumulated mod `m`), the mod-`m`
restriction of `expsum`'s `S_{K,L}(ξ)`; cost `O(K·L·m)`. Code + self-test:
`experiments/cycles/local_count.py` (reproduces the `(11,7)/139` necklace:
`N_139(11,7)=11`, exactly the eleven rotations of the −17 cycle).

## 2. What an obstruction would have to look like

Heuristically (and on the `expsum` minor-arc square-root-cancellation data)
`N_{p^e}(K,L) ≈ C(K,L)/p^e`. So:

- if `p^e ≪ C`, then `N_{p^e} ≫ 1` and there is **no** obstruction;
- an obstruction needs `p^e ≳ C ≈ Λ^{0.95}` — a **single giant prime power**
  carrying almost all of `Λ`. **[HEURISTIC]**

In the positive window `Λ = 2^K − 3^L ≈ 2^K / poly(K) ≈ 2^{0.99K} > C ≈ 2^{0.95K}`
(the near-convergent quality of `log_2 3`), so the *product* condition `N_Λ ≈
C/Λ ≈ 2^{−0.05K} < 1` already "predicts no cycle" — but that is the global
divisibility, not a single-place fact.

## 3. Small primes: obstruction is possible only at small L (correction)

A tempting lemma — "slide-connectivity of shape-`(K,L)` words + single-slide
increments `±3^c2^j` additively generate `ℤ/p`, hence `v↦W(v) mod p` is
surjective, hence `N_p>0`" — is **FALSE**. Edge increments generating `ℤ/p` do
not make vertex labels cover `ℤ/p` (gpt-5.6-sol). Concretely `(K,L)=(7,1)`:
`Λ = 2^7−3 = 125 = 5^3`, and `W = 2^{b_0}` is a power of two, so `N_5 = 0` — a
real obstruction. More generally **small `L` (few ones) can miss 0 mod `p`**:
for `L=1`, `W` is a single power of two, so `N_p = 0` for every odd `p`.

What *is* true, and verified, is the equidistribution statement in the regime
that matters: **[VERIFIED]** for every near-convergent `(K,L)`
(`L = ⌊K log_2/log_3⌋`), `K ≤ 160`, and every small prime factor `p | Λ`, the
exact count `N_p > 0` with normalised density `N_p·p / C ∈ [0.968, 1.000]`
(`experiments/cycles/local_density.py`, `local_density.csv`, 204 rows). The large
number of ones (`L ≈ 0.63K`) washes out the small-`L` obstruction. So along
near-convergents, **any obstruction must sit at a single giant prime power** (§2).

## 4. Availability of a giant-prime obstruction

Full factorization of `Λ` at near-convergents, `20 ≤ K ≤ 100`
(`factor_lambda.py pplus`, `lambda_pplus.csv`): **9–11%** carry a prime power
`> C` (the Dickman prediction `P⁺(n) > n^{0.95}` is ~5%, same order); mean
`log_Λ P⁺(Λ) = 0.60`. So a single-prime obstruction is **heuristically available
at positive density** among near-convergents. **[VERIFIED]**

**Computable witness. [PROVED by computation]** At `(K,L) = (21,13)`,
`Λ = 502829` is **prime** and `< C = 203490`, and `N_Λ = 0` (confirmed mod two
64-bit primes). Shape `(21,13)` is thereby excluded by a pure mod-`Λ` count with
**zero archimedean input** — a concrete instance of a finite-place cycle
exclusion. But `Λ` is tiny and Barina's `n < 2^71` already covers it.

## 5. The feasibility wall

At the genuine CF convergents — the archimedean method's actual targets —
`Λ ≈ 2^K` is a several-hundred-bit composite. E.g. `(485,306)`: `Λ` is 476-bit
with a 466-bit composite cofactor after trial division; `P⁺(Λ)` is
**unknowable**, and even given a giant `p ≈ 2^{0.95K}` the DP/exp-sum for
`N_p=0` needs ~`2^{0.95K}` states/frequencies (meet-in-the-middle only halves the
exponent, `2^{K/2}` — irrelevant at Hercher's `K ≥ 2.18×10^{11}`)
(`lambda_feas.csv`). **[VERIFIED / OPEN]**

## 6. The valuation-lifting loophole is (empirically) closed

`N_p > 0` does not a priori imply `N_{p^e} > 0`: a structural failure to lift
`W ≡ 0 mod p` to `mod p^e` would be a **cheap** obstruction at a *modest* prime
power. Tested (`lifting_test.py`, `lifting_test.csv`): all 37 near-convergent
cases `K < 400` with `p^e ‖ Λ`, `e ≥ 2`, `p^e ≤ 2·10^5` lift perfectly —
`N_{p^k}·p^k/C = 1.000` at every level `k ≤ e`. No cheap lifting obstruction
exists in range. **[VERIFIED]** (Not a theorem; the loophole remains logically
open for large `p^e`.)

## 7. The m=1 (Steiner) stratum: a clean witness of the collapse

The m=1 cycle (all `L` odd steps contiguous, word `1^L 0^{K−L}`) has
`W = 3^L − 2^L`. Since `3^L ≡ 2^K (mod Λ)` and `Λ` is odd:

> **[PROVED]**  `Λ | (3^L − 2^L)  ⟺  Λ | (2^K − 2^L) = 2^L(2^{K−L} − 1)
>  ⟺  Λ | (2^{K−L} − 1).`

So the m=1 cycle is **excluded at finite places whenever `0 < 2^{K−L} − 1 < Λ`**
— a pure size comparison, *no linear forms in logs*. Verified for every
near-convergent `(K,L)` with `Λ > 1`, `K ≤ 4000`: only the unit-stratum trivial
cycle `(2,1)/Λ=1` divides `W`; everywhere else excluded, and `(∗)` holds with
slack growing like `0.62K` bits (`m1_steiner.py`, `m1_steiner.csv`). **[VERIFIED]**

**The collapse, exactly.** `(∗)` is `2^{K−L} < 2^K − 3^L`, i.e. a **lower bound
`|2^K − 3^L| > 2^{0.37K}`** — a Baker-type statement. For fixed `K` it is a
finite integer check (unconditional). A *uniform*-in-`K` guarantee is exactly the
archimedean linear-forms bound: were `log_2 3` Liouville, `Λ` could be tiny and
`(∗)` could fail. Historically Steiner 1977 proved m=1 via Baker; the finite-place
reduction repackages it but **inherits the same archimedean lower bound as its
load-bearing input**. This is the cleanest concrete answer to Task 2/3: on the
one stratum where the finite-place computation is fully explicit, it collapses to
Baker.

## 8. Honest verdict and the sharpest falsifiable statement

**Verdict (Task 3).** The finite-place angle gives **no exclusion orthogonal to
and feasible beyond Baker**. It is genuine (§4 witness), heuristically available
at positive density (§4), but (i) uncomputable in the archimedean-relevant range
(§5), (ii) redundant where computable, and (iii) on the explicit m=1 stratum
provably reduces to the archimedean lower bound (§7). "At least as hard as Baker"
is *not* a proven reduction (gpt-5.6-sol); it is the observed behaviour plus the
fact that the required input — uniform square-root cancellation of
`S_Λ(ξ) = Σ_v e(ξW(v)/Λ)` over near-convergent `Λ`, i.e. Q2 of
`dynamical-hasse.md` — is itself open. Logical escape routes not killed here:
structural non-lifting at large `p^e` (§6 loophole), compressed/automata
certificates, and a *hybrid* argument where Baker shrinks the size window enough
that a modest congruence closes it.

**Sharpest falsifiable conjecture (finite-place, quantitative, not Baker).**

> **[CONJECTURAL]** Conditional on `Λ = 2^K − 3^L` having a prime factor `p`, the
> counts `N_p(K,L)`, binned by `λ := C(K,L)/p`, obey a **Poisson law of mean
> `λ`**; in particular `Pr(N_p = 0) ≈ e^{−C/p}`.

For small `p` (`λ ≫ 1`) this forces `N_p > 0` (§3); for a giant `p` (`λ < 1`) it
predicts obstruction with probability `≈ 1 − C/p`. **The one computation that
confirms or kills it:** exact `N_p` via meet-in-the-middle (`2^{K/2}`) at
near-convergents with a DP-reachable large `p | Λ` (feasible to `K ≈ 90–100`,
`p` up to ~`2^{45}`), histogrammed against `Poisson(C/p)`. Confirmation would
give a rigorous *density* heuristic for cycle-freeness located at finite places —
new, but supporting a heuristic, **not** an all-shapes proof. Failure (a
non-Poisson excess of `N_p = 0`, or a `p^e` non-lifting anomaly) would be the
first sign of genuine finite-place rigidity and would reopen the lane.

## 9. Claim ledger

| # | Claim | Tag |
|---|---|---|
| 1 | `N_m` = mod-`m` transfer DP = `(1/m)Σ_ξ S_m(ξ)`; `N_139(11,7)=11` | PROVED / VERIFIED |
| 2 | Obstruction needs `p^e ≳ C ≈ Λ^{0.95}` (single giant prime power) | HEURISTIC |
| 3 | "Slide-connectivity ⟹ surjective `W mod p`" is FALSE; `(7,1)`: `N_5=0` | PROVED (counterexample) |
| 4 | Near-convergent, `K≤160`: every small `p\|Λ` has `N_p>0`, density `∈[0.968,1]` | VERIFIED |
| 5 | ~9–11% of near-convergent `Λ` (`K≤100`) have a prime power `>C` (Dickman ~5%) | VERIFIED |
| 6 | `(21,13)`: `Λ=502829` prime, `N_Λ=0` — computable finite-place exclusion, no Baker | PROVED (computation) |
| 7 | Feasibility wall: `Λ≈2^K` unfactorable at convergents; `N_p=0` check is `≥2^{K/2}` | VERIFIED / OPEN |
| 8 | Valuation lifting `N_p>0 ⟹ N_{p^e}>0` holds in all 37 tested `e≥2` cases | VERIFIED |
| 9 | m=1: `Λ\|W ⟺ Λ\|(2^{K−L}−1)`; excluded when `2^{K−L}<Λ` | PROVED |
| 10 | m=1 finite-place exclusion collapses to the Baker lower bound `\|2^K−3^L\|>2^{0.37K}` | PROVED + analysis |
| 11 | Verdict: no orthogonal-AND-feasible exclusion; collapses to `C/Λ≈2^{−0.05K}` | HEURISTIC/assessment |
| 12 | Poisson conjecture `Pr(N_p=0)≈e^{−C/p}`; kill/confirm by meet-in-middle counts | CONJECTURAL |

## 10. Files (`experiments/cycles/`)

- `local_count.py` — mod-`m` transfer DP (exact + mod-`Q`); self-test incl. `(11,7)/139`, `(21,13)`.
- `local_density.py` / `local_density.csv` — exact small-prime densities (§3).
- `factor_lambda.py` / `lambda_pplus.csv`, `lambda_feas.csv` — factor structure, availability, wall (§4–5).
- `lifting_test.py` / `lifting_test.csv` — `p^e` lifting (§6).
- `m1_steiner.py` / `m1_steiner.csv` — the m=1 reduction and collapse (§7).
