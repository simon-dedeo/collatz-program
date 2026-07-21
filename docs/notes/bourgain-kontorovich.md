# Bourgain–Kontorovich thermodynamic CF machinery, the Diophantine type of log₂3, and why the cycle-length bound stalls

2026-07-20. Status: **scout / assessment note; verdict NEGATIVE-for-new-bound,
POSITIVE-for-explanation.** Tags: **[PROVED]**, **[VERIFIED]** (own CF
computation), **[LIT]** (cited), **[HEURISTIC]**, **[SPECULATIVE]**. Consulted
gpt-5.6-sol (stress-test of the two load-bearing claims; verified independently).
Context: `docs/LANDSCAPE.md` cycle rows (Rhin constant 13.3), `docs/notes/
cycle-finite-places.md` (the `(485,306)` shape), `docs/notes/adversarial-operator.md`
(KL = min-plus transfer operator on ℤ₃).

**One-line verdict.** Bourgain–Kontorovich gives **no new cycle bound** — it is a
category mismatch (an *ensemble* density statement; a single number's type is
invisible to it). Ouaknine–Worrell gives **no bound either, but the right
explanation**: the cycle-length lower bound sits on the *same* Diophantine-type
hardness barrier they isolated for Positivity, and both, plus Zaremba, reduce to
**effective equidistribution of one Gauss-map orbit** — capped only by Baker.
Nothing here beats Baker; it explains *why* nothing does.

## 1. The CF of log₂3 IS the cycle-shape enumerator [VERIFIED]

`log₂3 = 1.5849625007…`, CF `[1;1,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4,3,1,1,15,…]`.
Convergents `p_n/q_n`: `1/1, 2/1, 3/2, 8/5, 19/12, 65/41, 84/53, 485/306,
1054/665, 24727/15601, …, 301994/190537, 17087915/10781274, 85137581/53715833, …`.
A cycle of shape (K halvings, L odd steps) needs `2^K ≈ 3^L`, i.e. `L/K ≈ 1/log₂3`
— so **the admissible shapes are exactly the CF convergents** `(K,L)=(p_n,q_n)`.
The `(485,306)` shape of `cycle-finite-places.md` is the 8th convergent; and
Eliahou's (1993) lattice generators `301994, 17087915, 85137581` are precisely
convergent numerators `p_n` (verified in my run). This is not new — it is the
classical reason the cycle side is a continued-fraction problem — but it fixes
the dictionary: **partial quotient `a_n` large ⟺ convergent `(K,L)` with
`|2^K−3^L|` anomalously small ⟺ a cycle shape where `X_min` could sink into the
verified range.** Baker (μ finite) is exactly what forbids a giant `a_n`.

**Type of log₂3.** Partial quotients look Gauss–Kuzmin-generic (max in first 120
is 55); **not proven bounded, not proven unbounded** — the Zaremba/Lévy dichotomy
is open for it. Effective irrationality measure: `μ(log₂3) ≲ 11` via Wu's linear
independence measure of `{1,log2,log3}` (Math. Comp. 2003); the *two-log form*
`|K log2 − L log3| > C·K^{−κ}` with `κ ≈ 13.3` (Rhin 1987, packaged as
Simons–de Weger Lemma 12) is the shape actually used for cycles.

## 2. Bourgain–Kontorovich: a category mismatch [LIT + SPECULATIVE]

BK (Annals 2014, arXiv:1107.3776; sharpened to alphabet `A=5,4` by Kan–Frolenkov)
proves a **density-one** set of integers `q` are Zaremba denominators, via the
Ruelle transfer operator of the Gauss map restricted to a finite digit alphabet
`A` (pressure `P_A(s)=log λ_A(s)`; the restricted-CF Cantor set has dimension the
`s` with `λ_A(s)=1`) plus a circle method on thin-group orbits. **This counts an
ensemble of numbers; it says nothing about the digits or type of one fixed
irrational.** gpt-5.6-sol's nuance (verified): thermodynamic formalism *can*
describe periodic orbits and give a.e.-orbit metric statements, but pinning them
to a *named* number needs an independent genericity/extreme-digit input — exactly
the arithmetic fact unknown for log₂3. **No transfer-operator route delivers an
effective irrationality measure of log₂3.** So BK cannot sharpen the cycle bound.

## 3. Ouaknine–Worrell: the stall, named [LIT]

Positivity of linear-recurrence sequences is **decidable at order ≤ 5**;
extending to **order 6 would compute the homogeneous approximation type (Lagrange
constant) of certain transcendentals** — a Diophantine-approximation advance
beyond current reach (Ouaknine–Worrell, SODA/ICALP 2014). This is *structurally
the Collatz cycle stall*: the cycle-length bound bottlenecks on the effective
type of log₂3, which we cannot push past Baker. OW does not bound cycles, but it
is the honest diagnosis — **the obstruction is a Diophantine-type hardness
barrier, not a missing combinatorial idea.**

## 4. Scaling: where κ=13.3 binds, and where it does not [PROVED + LIT]

Cycle inequality `0 < K log2 − L log3 ≤ L/(3X_min)` with Rhin `> C K^{−κ}` gives
`X_min < (log2/3C log3)·K^{κ+1}`, i.e. **cycle length `K ≫ X_min^{1/(κ+1)}`** —
a *power* of the verification bound, exponent set by the irrationality measure
(`μ ≈ κ+1`). BUT (sol, verified): the **m-cycle** refinement replaces `L/(3X_min)`
by `≪ m/X_min` (m = local minima / increasing runs), giving `K ≫ (X_min/m)^{1/κ}`;
and Steiner/Simons–de Weger/Hercher use **exact convergent gaps over a finite
height range**, which are *far* stronger than the uniform `K^{−13.3}`. So the
LANDSCAPE lever is real but narrower than billed: **κ=13.3 binds only the coarse
uniform argument; the actual best cycle bounds run on exact CF gaps + block
combinatorics, where improving Rhin's constant helps sub-linearly.**

## 5. The unification (the one genuinely new framing) [SPECULATIVE]

Zaremba/BK, the Collatz cycle side, and Ouaknine–Worrell all reduce to **one
Gauss-map orbit's effective equidistribution**. The Gauss map is the
**archimedean transfer operator** — the real-place twin of the repo's proven
ℤ₃-odometer min-plus transfer operator (`adversarial-operator.md`) driving
predecessor density. Predecessor side: profinite transfer operator, spectral gap
⇒ `π_a(x) ≥ x^{0.9033}`. Cycle side: archimedean transfer operator, whose
**spectral gap answers ensemble questions (BK's density-one) but is blind to the
single orbit `{a_n(log₂3)}`** — that single orbit is the Diophantine type, i.e.
Baker. Same wall as OW at order 6. Collatz's "two multiplicatively independent
primes" difficulty is, on the cycle side, precisely *one Gauss-map orbit we cannot
see*.

## 6. Honest verdict & ledger

New cycle result: **no.** It re-derives / re-frames Baker. Value delivered:
(i) the dictionary `a_n large ⟺ dangerous cycle shape`; (ii) the correct scaling
`K ≫ X_min^{1/(κ+1)}` and the correction that κ binds only the coarse bound;
(iii) the OW hardness-barrier diagnosis of the stall; (iv) the transfer-operator
unification with the predecessor side.

| # | Claim | Tag |
|---|---|---|
| 1 | Cycle shapes (K,L) = CF convergents of log₂3; Eliahou generators = convergent numerators | VERIFIED |
| 2 | log₂3 partial quotients Gauss–Kuzmin-generic; bounded/unbounded OPEN; μ≲11 (Wu), two-log κ≈13.3 (Rhin) | LIT/VERIFIED |
| 3 | BK is ensemble/density; no transfer-operator route to a single number's effective type | LIT + confirmed |
| 4 | OW order-6 Positivity ⟺ Diophantine-type advance; same barrier as cycle stall | LIT |
| 5 | K ≫ X_min^{1/(κ+1)}; m-cycle gives 1/κ; exact CF gaps beat uniform 13.3 | PROVED + LIT |
| 6 | Gauss map = archimedean twin of ℤ₃ odometer operator; single-orbit blindness = the wall | SPECULATIVE |

**Kill/keep.** Dead as a bound source. Keep as the framing that the cycle stall
= single-Gauss-orbit-type = Baker, so effort belongs on **exact finite-range CF
gaps + block combinatorics** (Hercher's bootstrap at X₀=2^71), NOT on importing
Zaremba machinery. Sources: BK arXiv:1107.3776; Kan–Frolenkov arXiv:1210.4204;
Ouaknine–Worrell pos12 (cs.ox.ac.uk/james.worrell/pos12.pdf); Wu, Math. Comp. 72
(2003) 901; Rhin 1987; Simons–de Weger 2010; Eliahou 1993; Hercher arXiv:2201.00406.
