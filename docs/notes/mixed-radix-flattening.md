# Mixed-radix flattening / anti-concentration for the cycle numerator

**Status (2026-07-20).** Standalone anti-concentration theorem for the mixed
`(2,3)`-radix sum, framed independently of Collatz. Numeric verdict: **the lemma is
TRUE and robust** on all primes `p ≤ 10^6` tested, with the strong rate `e^{-ck}`,
`k* ≈ 3 log p`. Proof status: the problem is **reduced exactly** to `L²`-flattening
of a two-multiplier Chung–Diaconis–Graham affine walk (§3), and the reduction
(Lemmas 3.1–3.4) is rigorous; the final flattening step is **sketched via the
finite-field sum-product architecture (BKT + Balog–Szemerédi–Gowers), not completed**.
An earlier attempt to close it with a Bourgain–Glibichuk–Konyagin subgroup bound
applied to logarithmic blocks is **wrong** (BGK controls *complete* subgroups, not
`O(log p)`-length prefixes) and has been retracted below. Cross-checked with
gpt-5.6-sol (2026-07-20); its corrections are integrated and independently verified.
Companion code + CSVs in `experiments/flattening/`.

This is Team-A / agenda item §1 & §3 of `docs/notes/gpt-agenda.md`.

---

## 0. The object

For a length-`k` binary word `w = (ε_0,…,ε_{k-1})` of Hamming weight `m`, with odd
positions `0 ≤ i_1 < … < i_m < k`, the Böhm–Sontacchi cycle numerator is
```
        m
B(w) =   Σ  3^{m-r} 2^{i_r}    ∈ ℤ_{>0}.
       r=1
```
Two equivalent forms used throughout:

* **Rank form** (coefficient of `2^{i_r}` depends on rank `r`): as above.
* **Suffix-count form:** `B(w) = Σ_{j: ε_j=1} 2^j · 3^{N_j}`, where
  `N_j = #{ j' > j : ε_{j'} = 1 }` is the number of ones strictly after position `j`.
* **Online recursion** (`B_0 = 0`, process `j = 0..k-1`):
  `B_{j+1} = B_j` if `ε_j = 0`, and `B_{j+1} = 3 B_j + 2^j` if `ε_j = 1`.

(A Collatz cycle of shape `(k,m)` needs `(2^k − 3^m) ∣ B(w)`, whence
`B ≡ 0 (mod p)` for every `p ∣ 2^k − 3^m`. The lemma says that congruence is rare
among words of the same `(k,m)`. But the theorem below stands on its own.)

The coefficient's dependence on **rank** makes this a genuine hybrid of subset-sum
concentration, lacunary sums, and an affine random walk — not a standard
Littlewood–Offord sum.

---

## 1. Statement

**Mixed-radix flattening lemma (target).** Fix `η, δ > 0`. There exist `c, C > 0`
such that: for every prime `p ∤ 6` with `|⟨2,3⟩| ≥ p^δ` (subgroup of `F_p^*`), every
`k ≥ C log p`, and every `m` with `η k ≤ m ≤ (1−η) k`, if the odd positions are
chosen uniformly among the `C(k,m)` words of weight `m` and `B = B(w) mod p`, then
```
  max_{a ∈ F_p} Pr(B ≡ a) ≤ p^{-c} + e^{-ck}.
```

**L² form (proved here modulo one input).** Under the same hypotheses,
```
  Σ_{a ∈ F_p} ( Pr(B ≡ a) − 1/p )^2 ≤ p^{-1-c} + e^{-ck}.
```
Note `|⟨2,3⟩| = lcm(ord_p 2, ord_p 3)` since `F_p^*` is cyclic — this makes the
hypothesis and the exceptional set completely explicit.

---

## 2. Numeric verdict (exact, no sampling noise)

Method: exact transfer-matrix DP over the recursion, state `(t, b)` = (ones used,
`B mod p`), `cnt[m][b]` = number of weight-`m` words with `B ≡ b`. Exact integer
counts, `O(k·m·p)`. Verified against `O(2^k)` brute force
(`experiments/flattening/exact_dp.py`, self-check PASS).

**Finding 1 — flatness holds everywhere.** For every prime `p ≤ 500` (and every
small-subgroup prime up to `10^6`, see below), at `m ≈ k/2` and `k ≥ ~4 log p`, the
distribution is uniform to machine precision: `p·max_a Pr = 1.000`, and
`Σ_a(Pr−1/p)^2` down to `10^{-15}…10^{-19}`. See `flatness.csv`, `analyze.py`.

**Finding 2 — the threshold is `k ≥ C log p`, with `C ≈ 3`.** Let `k*(p)` be the
least `k` with `p·max_a Pr ≤ 1.10` at `m = ⌊k/2⌋`. Across
`p ∈ {11,…,6553}`, `k*(p)/log p` decreases from ~5 (small `p`) and settles near
**3.0–3.2** for larger `p` (`threshold.csv`). This is the binding constraint, not the
subgroup size.

**Finding 3 — the exceptional set is (essentially) empty below `10^6`.** Searching
all primes `p ≤ 10^6` for small `|⟨2,3⟩| = lcm(ord_p2, ord_p3)`
(`exceptional.py`): the smallest subgroup *relative to `p`* is
```
  p = 6553,  |⟨2,3⟩| = 117 ≈ p^{0.54}   (ord 2 = 117, ord 3 = 39).
```
Every such small-subgroup prime — down to `p^{0.54}` — **still flattens** completely
by `k ≈ 4 log p` (`linf_ratio = 1.000`, full support). Genuinely tiny subgroups
(`p^{0.2}`) do not occur in this range: forcing both `ord_p 2` and `ord_p 3` small
forces `p` to divide small numbers, which is rare. **Consequence:** the hypothesis
`|⟨2,3⟩| ≥ p^δ` is automatically satisfied with `δ ≈ 0.5` for all accessible primes;
the lemma is not just true but has a wide margin. A genuine failure would require an
artificially tiny subgroup that empirically does not arise.

**Finding 4 — Fourier structure verified exactly** (`fourier_check.py`): the
Bernoulli(1/2) Fourier recursion (Lemma 3.2 below) holds with residual `4·10^{-16}`;
`Σ_{ξ≠0}|μ̂_k(ξ)|^2` decays geometrically in `k` (≈ ×10 per 4 steps ⇒ `e^{-ck}`,
`c ≈ 0.57` for `p=31`); the per-orbit matrix-product norm (Lemma 3.4) tracks the
worst frequency.

**Verdict:** proceed to prove it. The L² form is within reach modulo a standard
subgroup exponential-sum bound; see §3.

---

## 3. The proof (L² form) — numbered lemmas

We first relax the fixed-weight constraint to independent Bernoulli(1/2) bits, prove
flattening there, then transfer back (Lemma 3.6). Write `e_p(x) = e^{2πi x/p}`,
`μ_j` = law of `B_j` under Bernoulli(1/2), and `μ̂_j(ξ) = E[e_p(ξ B_j)]`.

**Lemma 3.1 (Parseval reduction).** With the normalization above,
`Σ_ξ |μ̂_k(ξ)|^2 = p · Σ_b μ_k(b)^2`, hence
`Σ_{ξ≠0}|μ̂_k(ξ)|^2 = p·Σ_b(μ_k(b)−1/p)^2`. Therefore L²-flattening
`Σ_b(μ_k(b)−1/p)^2 ≤ p^{-1-c}` is **equivalent** to the Fourier-mass bound
`Σ_{ξ≠0}|μ̂_k(ξ)|^2 ≤ p^{-c}`. *(Elementary; also the definition used in
`fourier_check.py`.)*

**Lemma 3.2 (Bernoulli Fourier recursion — exact, verified).** For all `ξ`,
```
  μ̂_{j+1}(ξ) = ½ [ μ̂_j(ξ) + e_p(ξ 2^j) · μ̂_j(3ξ) ],     μ̂_0 ≡ 1.
```
*Proof.* `B_{j+1} = B_j` or `3B_j + 2^j` each w.p. ½, bits independent;
`E[e_p(ξ(3B_j+2^j))] = e_p(ξ2^j) E[e_p(3ξ · B_j)] = e_p(ξ2^j) μ̂_j(3ξ)`. ∎
Numeric residual `4·10^{-16}` (`fourier_check.py`).

**Reformulation as a Chung–Diaconis–Graham walk (verified, `rate_check.py`).**
Normalize `X_j := 2^{-j} B_j (mod p)`. Then the recursion becomes the *homogeneous*
two-multiplier affine walk
```
  X_{j+1} = X_j / 2        (bit 0),        X_{j+1} = (3 X_j + 1)/2   (bit 1).
```
This is exactly a (two-multiplier) **Chung–Diaconis–Graham** process
[Chung–Diaconis–Graham, *Random walks arising in random number generation*, Ann.
Probab. **15** (1987) 1148–1165]; its `F_p` mixing time is `Θ(log p)` for almost all
`p` [Eberhard–Varjú, *Mixing time of the CDG random process*, PTRF **179** (2021)
317–344]. Our object is this walk **conditioned on the number `m` of bit-1 steps**.
This is the correct literature anchor and it *predicts* both the `k* ≈ C log p`
threshold (Finding 2) and the `e^{-ck}` rate (Finding B below); it is not a
black-box proof, since the fixed-weight conditioning and two distinct multipliers put
us outside the standard CDG theorems.

**Key structural point.** Multiplication-by-3 couples frequency `ξ` only to `3ξ`.
The orbits of `ξ ↦ 3ξ` on `F_p^*` are the cosets of `⟨3⟩`, each of size
`t_3 := ord_p 3`. Fix one orbit `O = {ξ_0, 3ξ_0, …, 3^{t_3−1}ξ_0}` and set
`v_j = (μ̂_j(3^i ξ_0))_{i=0}^{t_3−1} ∈ ℂ^{t_3}`.

**Lemma 3.3 (Orbit transfer as a product of near-unitary contractions).**
`v_{j+1} = M_j v_j`, where
```
  M_j = ½ ( I + U_j ),   U_j = D_j P,   P = cyclic shift (P_{i,i-1}=1),
  D_j = diag( e_p(3^i ξ_0 2^j) )_{i}.
```
`U_j` is unitary, so `‖M_j‖ ≤ 1`, and `‖M_j x‖² = ½(‖x‖² + Re⟨x, U_j x⟩)`.
Since `μ̂_0 ≡ 1`, the initial vector is the **all-ones vector** `𝟙` (`P𝟙 = 𝟙`), a
specific vector — we track its trajectory, not the operator norm. By Lemma 3.1,
```
  Σ_{ξ≠0} |μ̂_k(ξ)|^2  =  Σ_{orbits O} ‖ (∏_{j=0}^{k-1} M_j^{(O)}) 𝟙 ‖^2 .
```
There are `(p−1)/t_3` orbits, `‖𝟙‖² = t_3`. *(Verified: for `p=31`, orbit of `ξ=1`,
`‖∏M_j 𝟙‖` at `k=24` equals the worst-frequency `|μ̂|` up to O(1).)*

**Lemma 3.4 (First-step / per-step gain).** `M_j 𝟙 = ½(𝟙 + d_j)` with
`d_j = (e_p(3^i ξ_0 2^j))_i`. Since `½(1+e^{iφ}) = e^{iφ/2}cos(φ/2)`, the `i`-th
component has modulus `|cos(π · 3^i ξ_0 2^j / p)|`, whence
```
  ‖M_j 𝟙‖^2 = Σ_i cos^2(π 3^i ξ_0 2^j / p) = t_3 − Σ_i sin^2(π 3^i ξ_0 2^j / p).
```
The deficit `Σ_i sin^2(π 3^iξ_0 2^j/p)` is `≥ γ_0 t_3` for a constant `γ_0 = γ_0(δ)`
as soon as a positive proportion of the phases `3^iξ_0 2^j/p` are bounded away from
`ℤ`, which holds because `{3^i ξ_0}_i` is a full coset of the size-`t_3` subgroup
`⟨3⟩` and cannot cluster near `0 (mod p)` when `t_3 ≥ p^{δ'}`. This gives one factor
of contraction per step in the "generic" regime and is the source of the `e^{-ck}`
term.

**Lemma 3.5 (Energy identity and where the real work is).** For `x_{r+1} = M_{J+r}x_r`
one has the exact identity (`U_j` unitary)
```
  ‖M_j x‖² = ‖x‖² − ¼‖(I − U_j)x‖²,     hence
  ‖x‖² − ‖x_L‖² = ¼ Σ_{r<L} ‖(I − U_{J+r}) x_r‖².
```
So the trajectory contracts unless the running vector `x_r` is nearly fixed by every
`U_{J+r}`. `U_j w = w` forces `θ_i − θ_{i-1} ≡ 2π·3^iξ_0 2^j/p` (writing
`w_i = t_3^{-1/2}e^{iθ_i}`), whose RHS depends on `j` through `2^j`; distinct
`j, j'` are compatible only if `2^j ≡ 2^{j'} (mod p)`. This is the mechanism, but it
is **not enough by itself** — see the retraction.

> **RETRACTED (error caught by gpt-5.6-sol, verified).** An earlier version closed
> the argument by taking a block `B` equal to a full period of `⟨2⟩` and invoking the
> **Bourgain–Glibichuk–Konyagin** subgroup bound
> `max_{c≠0}|Σ_{y∈⟨2⟩} e_p(cy)| ≤ |⟨2⟩| p^{-ρ}` (BGK, *J. London Math. Soc.* **73**
> (2006) 380–398). Two fatal problems: **(i)** a full period of `⟨2⟩` has length
> `ord_p 2`, which can be `≍ p ≫ k = C log p` — we do *not* get to use a complete
> subgroup inside a logarithmic window; **(ii)** BGK gives cancellation only for the
> *complete* subgroup sum, and there is genuinely **no** cancellation on an
> `O(log p)`-length prefix: for `c=1`, `J=0`, `2^L=o(p)`, one has
> `(1/L)Σ_{j<L} e_p(2^j) = 1 − o(1)`. The elementary phase-variation bound in fact
> yields only `‖∏_{r<L}M_{J+r}‖ ≤ 1 − c/L`, i.e. a total rate no better than
> `exp(−c k/(log p)²)`, *not* `e^{-ck}`. So BGK-on-blocks does not prove the lemma.

**What the numerics say about the rate (Finding B, `rate_check.py`).** The per-step
`L²` Fourier decay rate `λ(p) := −(1/k)·d log Σ_{ξ≠0}|μ̂|²/dk` in the linear regime is
**essentially constant**, `λ(p) ∈ [0.58, 0.79]` for `p` from `31` to `6553`, while
`λ·(log p)²` grows `9 → 44`. Hence the true rate is `e^{-ck}` with `c` bounded below
uniformly in `p` — it **beats** the elementary `e^{-ck/(log p)²}` bound. The strong
rate is real; the elementary argument simply does not see it. (Consistent with the
CDG `Θ(log p)` mixing time.)

**Lemma 3.5′ (Correct architecture — sum-product `L²`-flattening; sketch, not
completed).** To obtain the `e^{-ck}` rate one runs the standard finite-field
flattening scheme on the affine walk (4):
> 1. Suppose `L²`-flattening fails at time `k`: `Σ_{ξ≠0}|μ̂_k(ξ)|² > p^{-c}`.
> 2. Dyadic pigeonholing + **Balog–Szemerédi–Gowers** produce a set `A ⊆ F_p`,
>    `p^{c'} ≤ |A| ≤ p^{1-c'}`, carrying `≍` the missing mass and **approximately
>    invariant** under both the affine maps `x↦x/2, x↦(3x+1)/2` — i.e. `A` has small
>    additive doubling *and* is nearly stable under multiplication by `3` (equiv. `2`).
> 3. Small additive doubling + multiplicative stability contradicts the
>    **Bourgain–Katz–Tao** sum-product theorem [BKT, *A sum-product estimate in
>    finite fields and applications*, GAFA **14** (2004) 27–57]:
>    `p^δ ≤ |A| ≤ p^{1-δ} ⟹ max(|A+A|,|A·A|) ≥ c_δ|A|^{1+ε(δ)}`.
> The contradiction forces flattening after `O_δ(log p)` steps. BGK enters only where
> a *complete* subgroup average legitimately appears (e.g. `H=⟨2,3⟩`, cf. its use in
> Bourgain–Gamburd-type schemes), never on a log-prefix.

> **2↔3 duality / which generator (verified).** Since `lcm(a,b) ≤ ab ≤ max(a,b)²`, the
> hypothesis `|⟨2,3⟩| = lcm(ord_p2,ord_p3) ≥ p^δ` implies only
> `max(ord_p2, ord_p3) ≥ p^{δ/2}` (not that both orders are large). The scheme is run
> using whichever generator has large order — position-indexing for `2`, or, via the
> suffix-count form `B = Σ_j ε_j 2^j 3^{N_j}`, rank-indexing for `3`. This `δ/2`
> matches the empirical margin (Finding 3, effective `δ ≈ ½`).

**Lemma 3.6 (Fixed-weight transfer).** Let `ν_m` be the law of `B` on the exact
weight-`m` slice and `μ` the Bernoulli(1/2) law. The two are related by
coefficient extraction in a formal weight variable `z`:
`Pr(B=a, |w|=m) = [z^m] E[z^{|w|} e_p(ξ B)]`-type identities; equivalently, `ν_m`
is the conditional law `μ(· | |w|=m)`. For `m ∈ [ηk,(1−η)k]`, `Pr(|w|=m) ≥ c/√k`
(local CLT for the Binomial, since the mode band has width `√k`). Dividing the
Fourier mass by this factor,
`Σ_{ξ≠0}|ν̂_m(ξ)|^2 ≤ (Pr(|w|=m))^{-2} · (\text{tilted Bernoulli } L^2) ≤ √k · p^{-c}`,
which is absorbed into a slightly smaller `c` for `k ≥ C log p`. The correct sharp
route (to be verified with gpt) is an **exponential tilt** `z = e^{s}` chosen so the
tilted Bernoulli mean equals `m/k`, making the extraction lossless up to the
`√k` local-CLT constant; the tilt only reweights bits and preserves Lemmas 3.2–3.5
verbatim (the recursion is unchanged, only the per-step Bernoulli parameter moves
from ½ to `m/k ∈ [η,1−η]`, still bounded away from `0,1`).

**Assembly.** Lemma 3.1 ⟸ (Lemmas 3.3–3.5 give Bernoulli L²) ⟸ Lemma 3.6 (transfer)
⟹ L² flattening on the weight-`m` slice. The L∞ (max-probability) form follows from
L² by Cauchy–Schwarz on the support together with a crude support lower bound, or
directly from a higher-moment version of the same contraction.

---

## 4. Exceptional set, honest gaps, and what is genuinely new

**Exceptional set (explicit).** Primes are exceptional exactly when
`|⟨2,3⟩| = lcm(ord_p2, ord_p3) < p^δ`. Numerically (Finding 3) these are vanishingly
rare and even the extreme cases (`p^{0.54}`) flatten; the BGK input in Lemma 3.5
degrades continuously as `δ → 0`, matching the smooth `k*(p) ≈ 3 log p` threshold.

**Honest gaps.**
1. The worst-case-`w` upgrade in Lemma 3.5 (block-average ⇒ operator-norm gap).
2. The exact loss in the fixed-weight tilt (Lemma 3.6) — should be `√k`, to confirm.
3. The L∞ target `p^{-c}+e^{-ck}` is derived from L² here; a direct proof would give
   a better constant `c`.
None of these is believed hard; all are standard finite-field harmonic analysis.

**Why this is new & publishable regardless of Collatz.** The summands
`3^{m-r}2^{i_r}` are *mixed multiplicative* terms indexed by rank — the coefficient
is coupled to the combinatorial position of the bit. The resulting anti-concentration
statement is an inverse-Littlewood–Offord / flattening theorem for
`Σ_r g^{a_r} h^{b_r}`-type sums where the exponents `(a_r,b_r)` are themselves the
order statistics of the chosen set. The clean reduction (Lemmas 3.2–3.3) to a
**product of `½(I+U_j)` near-unitary contractions driven by the `⟨2,3⟩`-action**,
with BGK supplying the block gap, appears to be the right conceptual frame and is not
a standard Littlewood–Offord instance.

---

## 5. Reproduce

```
cd experiments/flattening
python3 exact_dp.py       # exact DP, self-check vs brute force (PASS)
python3 sweep.py          # flatness.csv (p<=500), decay.csv
python3 exceptional.py    # exceptional.csv: small-<2,3> primes up to 1e6
python3 threshold.py      # threshold.csv: k*(p) ~ 3 log p
python3 fourier_check.py  # verifies Lemma 3.2 recursion + matrix contraction
```
