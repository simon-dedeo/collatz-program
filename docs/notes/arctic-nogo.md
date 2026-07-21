# Arctic (max-plus) no-go for Zantema's Collatz SRS Z

**Status.** A successor audit repaired a real gap in the original cyclicity
argument and produced an elementary candidate all-dimension weighted-walk proof
for both Theorems A and B. It gives the arctic analogue of Yolcu–Aaronson–
Heule's unary-`Z` natural-matrix no-go; their explicit future challenge concerns
the mixed-base system `T`, not this theorem. Kernel formalization has been
requested from CLEAN_LEAN. Under this repo's verification rule, the general
theorem remains provisional until that check lands; the bounded z3 diagnostics
and dimension-one witnesses are separate machine-checked facts.

The honest answer remains more interesting than the pre-think predicted. Its
blanket claim ("no rule of Z can even be strictly top-oriented by an arctic
interpretation of any dimension") is **false**; five hand-checkable
dimension-one witnesses refute it.
The correct no-go is a sharp two-part statement mirroring YAH's natural-number
Theorems 3.8/3.10.

---

## 0. The exact system Z (verified against YAH Example 3.1)

Five symbols `{1, B, h, s, t}` where **B is the blank** — the blank is genuinely part of
four rules. (The pre-think worked with a blank-free 4-symbol simplification and even
"corrected" rule R2 to `1h->1s`; that system is *not* Z. All results below use the real Z.)

```
R1: h 1 1      -> 1 h
R2: 1 1 h B    -> 1 1 s B
R3: 1 s        -> s 1
R4: B s        -> B h
R5: h 1 B      -> t 1 1 B
R6: 1 t        -> t 1 1 1
R7: B t        -> B h
```

States are `B h 1^n B`. Macro-steps (Zantema Thm 16 / YAH Thm 3.2):
`B h 1^{2n} B ->* B h 1^n B` (even) and `B h 1^{2n+1} B ->* B h 1^{3n+2} B` (odd).
Even macro-step uses **R1,R2,R3,R4** (R4 = "turn s back to h at the left blank"); odd
macro-step uses **R1,R5,R6,R7** (R7 = "turn t back to h at the left blank"). Confirmed by
direct simulation (`experiments/arctic/verify.py`).

## 1. Arctic setup (KW09 / YAH §2.3.2)

Semiring `A = Z ∪ {−∞}` (arctic integers `AZ`) or `N ∪ {−∞}` (arctic naturals `AN`), with
`x ⊕ y = max(x,y)`, `x ⊗ y = x+y`. Each symbol σ: `[σ](x) = M_σ ⊗ x ⊕ v_σ`.
Domain restricted to `N × A^{d-1}` (well-foundedness). Orders: `a ≥ b` iff `a ≥_Z b`;
`a ⊐ b` iff `a >_Z b` or `a = b = −∞`.
- **Weakly monotone** (top/relative termination — the only setting arctic *integers* support):
  each σ has `(M_σ)_{1,1} ≥ 0` **or** `(v_σ)_1 ≥ 0`.
- **Extended monotone** (direct rule removal): `A = AN`, `v_σ = −∞`, `(M_σ)_{1,1} ≥ 0`.
- Compatibility (the sufficient coefficient tests used by KW Lemma 6.5):
  `M_ℓ≥M_r ∧ v_ℓ≥v_r` implies weak orientation, while
  `M_ℓ⊐M_r ∧ v_ℓ⊐v_r` implies strict orientation (elementwise).

## 2. Key empirical finding — the blanket claim is false

With **arctic integers** (weakly monotone), **5 of the 7 rules are strictly
top-oriented already at dimension 1** (strict on that rule, weak on all others).
Example strictly orienting **R3** (`d=1`):
`[1]x = 1+x`, `[h] = id`, `[B]=[s]=[t] = const 0`. Then `[1s] = 1 ⊐ 0 = [s1]`, and every
other rule is weakly oriented. Verified by hand and by an independent (non-z3) max-plus
checker: R1,R2,R3,R5,R6 all admit valid `d=1` witnesses (`experiments/arctic/FOUND_*`).

Only **R4 and R7** — the two blank-turnaround rules — resist in the completed
dimension-one search (UNSAT). These are *exactly*
YAH's dependency-pair bottleneck `I = {B#s → B#h, B#t → B#h}` (their Thm 3.10). So arctic
integers are more expressive for this weak/top orientation than the natural
interpretations of YAH Thm 3.8, yet the candidate general obstruction still
localises to `I`.

## 3. Theorem B (arctic naturals, extended monotone) — clean no-go

**Theorem B.** No arctic-natural matrix interpretation (`AN`, extended monotone, any
dimension d) removes any single rule of Z: there is no interpretation with `[ℓ]⊐[r]` for
one rule and `[ℓ']≥[r']` for the rest.

*Proof.* Homogenize the affine symbol maps to `(d+1)×(d+1)` max-plus
matrices and fix any input `x_0` in the interpretation domain. Then

`f(n):=[B h 1^n B](x_0)_1 = u⊗A^n⊗v ∈ N`.

Let `D=d+1` and `P=lcm(1,...,D)`. The weighted-walk pumping lemma (Lemma 2)
says that, for all sufficiently large `m` and every `q≥0`,
`f(m+qP)≥f(m)`. On the other hand the exact odd-even-odd derivation

`B h 1^(8N+1) B ->* B h 1^(9N+2) B`

uses every rule. Extended monotonicity preserves any selected strict rule in
all contexts, so `f(8N+1)>f(9N+2)`. Put `N=qP−1` with `q` large. The two
arguments are `8qP−7` and `9qP−7`, whose difference is `qP`; pumping gives
the reverse weak inequality, a contradiction. ∎

This is the candidate arctic analogue of YAH Thm 3.8; the repaired argument
uses weighted-walk pumping rather than their Berstel lemma or max-plus
cyclicity. Empirics: UNSAT for all seven rules at `d≤2`, entry bounds `K≤3`.
Higher-dimensional rows include timeouts and are not claimed.

## 4. Theorem A (arctic integers, weakly monotone / DP) — the real closure

**Theorem A.** No arctic-integer interpretation (`AZ`, weakly monotone, any
dimension) can orient all rules of `Z` and **both** dependency-pair rules

`I_s: B# s -> B# h`,  `I_t: B# t -> B# h`

weakly while making either selected `I`-rule strict. Thus arctic integers
cannot discharge `SN(I_top/Z)`.

*Proof.* As above, homogenization gives
`f(n):=[B# h 1^n B](x_0)_1=u⊗A^n⊗v∈N`, so Lemma 2 applies. The exact marked
macros are

`B# h 1^(2r+1) B ->* B# h 1^(3r+2) B`  (one root `I_t`),

and, for `r≥2`,

`B# h 1^(2r) B ->* B# h 1^r B`  (one root `I_s`).

Consequently, for `N≥1`,

`8N+1 -> 12N+2 -> 6N+1 -> 9N+2`.

This composite uses `I_t` twice and `I_s` once, always at the root. All other
steps are weak and context-closed; whichever `I`-rule is selected strict occurs
at least once with no left context, so

`f(8N+1)>f(9N+2)`.

Let `P=lcm(1,...,d+1)` and take `N=qP−1` large enough for Lemma 2. The endpoint
lengths differ by `qP`, hence pumping gives
`f(9qP−7)≥f(8qP−7)`, a contradiction. ∎

The hypothesis that **both** `I`-rules are weak is load-bearing. If only the
seven `Z`-rules are required weak while `I_s` is strict, a dimension-one AZ
witness exists with `I_t` unoriented. `dp_search.py` uses the correct stronger
dependency-pair hypothesis. Bounded diagnostics find UNSAT for both selected
rules at `d≤2`, `K≤2`; they are falsification checks, not the all-dimension proof.

## 5. Numbered lemmas (Lean-able)

- **Lemma 1 (affine homogenization).** Replace `[σ](x)=M_σ⊗x⊕v_σ` by
  `Mhat_σ=[[M_σ,v_σ],[-∞,...,-∞,0]]` and `xhat=(x,0)`. Then every word
  interpretation is the upper block of the corresponding homogeneous product.
  In particular the displayed `f(n)` has the form `u⊗A^n⊗v`, and domain
  preservation makes its first coordinate a finite natural number.
- **Lemma 2 (nonnegative-walk pumping).** Let `A` be a finite `D×D` arctic-
  integer matrix and suppose `f(n)=u⊗A^n⊗v` is finite and nonnegative for every
  `n`. With `P=lcm(1,...,D)`, for all sufficiently large `n` and every `q≥0`,
  `f(n+qP)≥f(n)`. Choose a maximizing length-`n` walk. If it contained no
  nonnegative simple cycle, delete simple cycles until a simple path remains.
  The path and endpoint weights have a fixed upper bound, while each removed
  integer-weight cycle contributes at most `−1` and has length at most `D`;
  the maximizing weight would therefore become negative for large `n`, a
  contradiction. Repeat a nonnegative simple cycle of length `ell|P` exactly
  `qP/ell` times.
- **Lemma 3 (extended-monotone strict is context-closed).** `AN`, extended monotone ⇒ for
  `ℓ→r` strict, `s→_{ℓ→r} t ⇒ [s]⊐[t]` in all contexts (KW; standard). Hence a derivation
  using the strict rule ≥1× has `f` strictly dropping.
- **Lemma 3' (top-rewrite strictness, weak monotone).** If `ℓ→r` is strict and fires at the
  ROOT (no left context) inside `s = ℓ w -> r w = t`, then `[s](x)⊐[t](x)` for all x
  (composition absorbs right context `w`; `⊐` needs no left-monotonicity). With domain
  `N×A^{d-1}` the first coordinate is finite, so the drop is `≥ 1` per firing.
- **Lemma 4 (macro-step rule counts).** The marked odd-even-odd composite uses
  `I_t` twice, `I_s` once, `R1` `13N+1` times, `R2` once, `R3` `6N+1`
  times, `R5` twice, and `R6` `7N` times. `experiments/arctic/verify.py`
  independently asserts both marked and unmarked literal instances and these
  count formulas for `N=1..12`; the displayed symbolic derivation is the
  all-`N` argument pending Lean.

## 6. What this corrects in `arctic-prethink-gpt.md`

- Wrong system: pre-think dropped the blank and rewrote R2; used unconditional `s->h`,`t->h`.
- Overclaim: "no rule can be strictly top-oriented by arctic interpretations"
  is false (R1,R2,R3,R5,R6 have dimension-one weak/top witnesses). The correct
  AZ dependency-pair target is `I={R4,R7}`.
- The original single-slope cyclicity lemma is false for reducible max-plus
  matrices: different residue classes can have different eventual slopes. The
  elementary weighted-walk pumping lemma replaces it and removes the need for
  the even-step `λ≥0` argument entirely.
- The `Θ(m)`-accumulation families (B),(C) are not needed. Strictness in a
  weakly monotone algebra is not context-closed under left context; it survives
  here only because the `I`-rules are root rewrites.

## 7. Experiments

`experiments/arctic/` — `arctic_search.py` (z3 rule-removal search, AN & AZ), `dp_search.py`
(faithful DP/top encoding with marked blank), `verify.py` (independent non-z3 max-plus
checker + rewrite simulator). Result CSVs: `sweep_d6_K3.csv`, `an_K1.csv`, `an_K2.csv`,
`dp_K1.csv`, `dp_K2.csv`; witnesses `FOUND_AZ_d1_K2_R{1,2,3,5,6}.txt` (all independently
verified VALID). See `RESULTS.md`.
