# Arctic (max-plus) no-go for Zantema's Collatz SRS Z

**Status.** Closes Yolcu–Aaronson–Heule's explicitly-stated open problem (CADE 2021,
arXiv:2105.14697) for arctic matrix interpretations — but the honest answer is **more
interesting than the pre-think predicted**. The pre-think's blanket claim ("no rule of Z
is removable by an arctic interpretation of any dimension") is **FALSE**, and I refute it
with hand-verified dimension-1 witnesses. The *correct* arctic no-go is a sharp two-part
statement that exactly mirrors YAH's natural-number Theorems 3.8 / 3.10.

Calibration: **Theorem B — proved.** **Theorem A — provable-looking** (one standard
citation: max-plus cyclicity; the reduction to a single eventual slope and the top-rewrite
strictness are checked below). Empirics: **certified** by z3 + an independent pure-Python
max-plus checker.

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
- Compatibility (KW Lemma 6.5): weak `ℓ→r` iff `M_ℓ ≥ M_r ∧ v_ℓ ≥ v_r`; strict iff
  `M_ℓ ⊐ M_r ∧ v_ℓ ⊐ v_r` (elementwise).

## 2. Key empirical finding — the blanket claim is false

With **arctic integers** (weakly monotone), **5 of the 7 rules are removable already at
dimension 1** (strict on that rule, weak on all others). Example removing **R3** (`d=1`):
`[1]x = 1+x`, `[h] = id`, `[B]=[s]=[t] = const 0`. Then `[1s] = 1 ⊐ 0 = [s1]`, and every
other rule is weakly oriented. Verified by hand and by an independent (non-z3) max-plus
checker: R1,R2,R3,R5,R6 all admit valid `d=1` witnesses (`experiments/arctic/FOUND_*`).

Only **R4 and R7** — the two blank-turnaround rules — resist (UNSAT). These are *exactly*
YAH's dependency-pair bottleneck `I = {B#s → B#h, B#t → B#h}` (their Thm 3.10). So arctic
integers are **strictly more powerful** than natural interpretations (which remove *nothing*,
YAH Thm 3.8) yet **still cannot finish**: the obstruction localises to `I`.

## 3. Theorem B (arctic naturals, extended monotone) — clean no-go

**Theorem B.** No arctic-natural matrix interpretation (`AN`, extended monotone, any
dimension d) removes any single rule of Z: there is no interpretation with `[ℓ]⊐[r]` for
one rule and `[ℓ']≥[r']` for the rest.

*Proof.* Let `f(n) := [B h 1^n B](x_0)_1` (first coordinate, `x_0∈N×A^{d-1}` fixed);
`f(n) = u^T ⊗ M_1^{⊗n} ⊗ w` up to the fixed affine ends. All entries are `≥ 0`, so every
cycle mean of `M_1` is `≥ 0`, hence the eventual slope `λ ≥ 0` (Lemma 1). A strict rule is
used in `B h 1^{8n+1} B ->* B h 1^{9n+2} B` (this derivation uses **every** rule); extended
monotonicity makes `⊐` context-closed, so `f(8n+1) > f(9n+2)` for all n (Lemma 3). By
cyclicity `f(n)=nλ+π(n)`, π p-periodic (Lemma 1); on `n=qp−1`, `8n+1` and `9n+2` differ by
`qp`, so `f(8n+1)−f(9n+2) = −(qp)λ ≤ 0` (Lemma 2), contradicting `> 0`. ∎

This is the arctic analogue of YAH Thm 3.8 (they used Berstel; we use max-plus cyclicity).
Empirics: UNSAT for all 7 rules, `d ≤ 3`, entry bound `K ≤ 3` (`experiments/arctic/`).

## 4. Theorem A (arctic integers, weakly monotone / DP) — the real closure

**Theorem A.** No arctic-integer interpretation (`AZ`, weakly monotone, any dimension)
removes an `I`-rule at the root while orienting all of Z weakly — i.e. arctic integers
cannot discharge `SN(I_top / Z)`. Equivalently, R4 and R7 are not removable.

*Proof.* Let `f(n) := [B# h 1^n B](x_0)_1`, `B#` the DP root marker. Cyclicity: `f(n)=nλ+π(n)`
eventually, π p-periodic, λ the top eventual slope (Lemma 1).
1. `B# h 1^{2n} B ->* B# h 1^n B` — all steps weak (weak monotonicity ⇒ `≥` context-closed),
   so `f(2n) ≥ f(n)`; on `p | n`, `π(2n)=π(n)`, giving `nλ ≥ 0`, hence **λ ≥ 0** (Lemma 2a).
2. `B# h 1^{8n+1} B ->* B# h 1^{9n+2} B` uses the strict `I`-rule **at the root** (odd–even–odd:
   R7 fires 2×, R4 1×; whichever is strict fires ≥1×, and always at the leftmost position, so
   there is **no left context** to erase strictness). Right context is absorbed by composition,
   and the first coordinate stays in `N`, so `f(8n+1) ≥ f(9n+2) + 1` (Lemma 3').
   On `n=qp−1`: `f(8n+1)−f(9n+2) = −(qp)λ ≥ 1 > 0`, forcing **λ < 0**.

`λ ≥ 0` and `λ < 0` contradict. ∎

The single extra ingredient beyond YAH's Thm 3.10 is step 1 (**λ ≥ 0**), which is *needed*
precisely because arctic integers, unlike naturals, permit negative cycle means — this is
why YAH left arctic open. Empirics (faithful DP encoding with a marked blank `B#`): UNSAT
for both `I`-rules, `d ≤ 2`, `K ≤ 3`.

## 5. Numbered lemmas (Lean-able)

- **Lemma 1 (cyclicity, cite BCOQ 1992 Ch.3 / Butkovič 2010 Thm 3.101).** For arctic
  `M ∈ A^{d×d}` and fixed `u,w`, `f(n)=u^T⊗M^{⊗n}⊗w` is eventually `nλ+π(n)` with `π`
  p-periodic and `λ = max{ cycle means of M reachable u→w }` a single rational slope; for
  reducible M, `f = max_{i,j}(u_i+(M^n)_{ij}+w_j)`, a max of finitely many affine-periodic
  functions, so the *eventual* slope is well-defined and equals the largest contributing `λ_{ij}`.
- **Lemma 2 (slope extraction).** (a) `f(2n)≥f(n) ∀n ⇒ λ≥0` (evaluate on `p|n`).
  (b) `f(an+b)≥f(cn+d)+ε` with `ε>0`, `a<c` ⇒ `λ<0` is forced when the two arguments share a
  residue mod p (here `a=8,c=9`, on `n=qp−1`, difference `qp`); combined with (a): impossible.
- **Lemma 3 (extended-monotone strict is context-closed).** `AN`, extended monotone ⇒ for
  `ℓ→r` strict, `s→_{ℓ→r} t ⇒ [s]⊐[t]` in all contexts (KW; standard). Hence a derivation
  using the strict rule ≥1× has `f` strictly dropping.
- **Lemma 3' (top-rewrite strictness, weak monotone).** If `ℓ→r` is strict and fires at the
  ROOT (no left context) inside `s = ℓ w -> r w = t`, then `[s](x)⊐[t](x)` for all x
  (composition absorbs right context `w`; `⊐` needs no left-monotonicity). With domain
  `N×A^{d-1}` the first coordinate is finite, so the drop is `≥ 1` per firing.
- **Lemma 4 (macro-step rule counts).** Even step uses R4 once at root; odd step uses R7
  once at root. `8n+1 ->* 9n+2` = odd,even,odd ⇒ R7 2×, R4 1×, all others `O(n)` but weak.
  (Simulation-checked.)

## 6. What this corrects in `arctic-prethink-gpt.md`

- Wrong system: pre-think dropped the blank and rewrote R2; used unconditional `s->h`,`t->h`.
- Overclaim: "no rule removable by arctic of any dimension" is false (R1,R2,R3,R5,R6 are
  removable at d=1). The correct target is `I = {R4,R7}` only.
- The `Θ(m)`-accumulation families (B),(C) are *not needed*; the single `8n+1→9n+2` family
  plus `λ≥0` suffices, and it sidesteps the genuine hole in the pre-think (strictness in a
  *weakly* monotone algebra is **not** context-closed under left context — it survives only
  because `I`-rules are root rewrites).

## 7. Experiments

`experiments/arctic/` — `arctic_search.py` (z3 rule-removal search, AN & AZ), `dp_search.py`
(faithful DP/top encoding with marked blank), `verify.py` (independent non-z3 max-plus
checker + rewrite simulator). Result CSVs: `sweep_d6_K3.csv`, `an_K1.csv`, `an_K2.csv`,
`dp_K1.csv`, `dp_K2.csv`; witnesses `FOUND_AZ_d1_K2_R{1,2,3,5,6}.txt` (all independently
verified VALID). See `RESULTS.md`.
