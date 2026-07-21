# Mixed-radix flattening for the cycle numerator — numerical evidence + proof program

**Status (2026-07-20). This is a numerical-evidence + proof-program note, NOT a
completed proof.** Standalone anti-concentration question for the mixed `(2,3)`-radix
sum, framed independently of Collatz.

**What is established (exact computation, the actual object):** the fixed-weight
distribution of `B mod p` flattens at the advertised scale `k ≈ 3 log p`, uniformly
over primes `p ≤ 10^6` and over the mass band `η k ≤ m ≤ (1−η) k`, with a strong
`e^{-ck}` rate. The true threshold constant is `C ≈ 3` (at `k = 2 log p` the
distribution is **not** flat; see §2, Finding S). No exceptional prime appears below
`10^6` (smallest `|⟨2,3⟩| ≈ p^{0.54}` still flattens).

**What is NOT proved — three load-bearing gaps (§3):**
1. **Scale/mechanism.** At `k ≈ C log p` the walk contains *not even one* full `⟨2⟩`
   period, and the single-generator short-orbit sum `max_{c≠0}|Σ_{j<k} e_p(c 2^j)|/k`
   does **not** decay (measured ≈ 0.3–0.8, Finding S). So BGK / short-geometric-sum
   cancellation is **useless** here; flattening is driven by the **2–3 coupling**. A
   proof needs an `e^{-ck}` gap for the *coupled* transfer, not a single-generator sum.
2. **Fixed-weight conditioning is not automatic.** Small Fourier mass of the
   unconditioned Bernoulli mixture does not bound the weight-`m` slice (weights cancel
   in `μ̂`); dividing by `Pr(|w|=m)` is invalid. A genuine bivariate `(weight,residue)`
   estimate is required.
3. **Operator-norm / running-vector upgrade** of the per-block gap.

An earlier draft claimed "proved modulo one BGK input"; that is **wrong and
retracted** (§3.5). Cross-checked twice with gpt-5.6-sol (2026-07-20); its
corrections are integrated and independently verified by exact computation.
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

**L² form (target; NOT proved — see §3 gaps).** Under the same hypotheses,
```
  Σ_{a ∈ F_p} ( Pr(B ≡ a) − 1/p )^2 ≤ p^{-1-c} + e^{-ck}.
```
By Cauchy–Schwarz the L∞ form follows from the L² form with **no** support argument:
`max_a |Pr(B=a) − 1/p| ≤ (Σ_a(Pr−1/p)²)^{1/2}`. Note
`|⟨2,3⟩| = lcm(ord_p 2, ord_p 3)` since `F_p^*` is cyclic — this makes the hypothesis
and the exceptional set completely explicit.

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

**Finding S — the decisive scale test (`scale_test.py`, `scale_test.csv`).** At
`k = C log p` we compare three quantities (worst `m ∈ [0.3k, 0.7k]` for the last):

| `C` | single-generator `max_c|Σ_{j<k}e_p(c2^j)|/k` | walk `max_{ξ≠0}|μ̂_k(ξ)|` | fixed-weight `p·max_a|Pr−1/p|` |
|----|----|----|----|
| 2 | 0.5–0.8 | `~4·10^{-2}` | **2–5 (NOT flat)** |
| 3 | 0.5–0.7 | `~5·10^{-3}` | `<1` (flat) |
| 4 | 0.3–0.6 | `~3·10^{-4}` | `~0.05` |
| 5 | 0.3–0.5 | `~3·10^{-5}` | `~0.01` |

Two conclusions. **(i) The theorem is TRUE at `k ≈ 3 log p`** and the constant is
sharp-ish: `C = 2` fails, `C = 3` flattens. This is measured on the **actual
fixed-weight object**, exactly. **(ii) The single-generator short-orbit sum does NOT
decay** (stays `≈ 0.3–0.8`, no `p`-trend) — so cancellation of `Σ_{j<k} e_p(c 2^j)`
is *not* the mechanism, and no BGK/short-progression bound can prove the lemma.
Flattening comes from the **2–3 coupling**: mult-by-3 mixes the `⟨3⟩`-orbit while the
per-step `2`-phases act (§3). This is the single most important finding of the note.

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
the per-orbit matrix-product norm (Lemma 3.4) tracks the worst frequency.

**Finding B — the `e^{-ck}` rate is genuine and `p`-uniform** (`rate_check.py`). The
per-step `L²` Fourier decay rate `λ(p) = −(1/k) d log Σ_{ξ≠0}|μ̂|²/dk` is essentially
constant, `λ(p) ∈ [0.58, 0.79]` for `p ∈ [31, 6553]`, while `λ·(log p)²` grows
`9 → 44`. So the true rate is `e^{-ck}` with `c` bounded below uniformly in `p` — it
**beats** the crude `e^{-ck/(log p)²}` any elementary phase-variation argument gives
(§3.5). Also verified: the normalization `X_j = 2^{-j}B_j` turns the recursion exactly
into the CDG walk `X↦X/2 | (3X+1)/2`.

**Verdict:** the *statement* is true at `k ≈ 3 log p` with a wide margin. A *proof*
must use the 2–3 coupling (single-generator bounds provably cannot work, Finding S);
see §3 and its three explicit gaps.

---

## 3. Proof program — numbered lemmas, with the three gaps marked

Lemmas 3.1–3.4 are rigorous and reduce the problem to a clean matrix-contraction
statement; Lemmas 3.5–3.6 are the **open** steps (Gaps 1–3). We first relax the
fixed-weight constraint to Bernoulli bits (Gap 2 is exactly the cost of returning).
Write `e_p(x) = e^{2πi x/p}`, `μ_j` = law of `B_j` under Bernoulli(1/2),
`μ̂_j(ξ) = E[e_p(ξ B_j)]`.

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
because `{3^i ξ_0}_i` is a full coset of `⟨3⟩` and (for `t_3 ≥ p^{δ'}`) cannot cluster
near `0 (mod p)`. This gives one factor of contraction *at the first step from `𝟙`*.
It does **not** by itself give `e^{-ck}` over many steps: the running vector `x_r`
generally leaves the flat direction, and sustaining contraction is exactly GAP 1
below (the deficit must be recreated each step by the 2–3 coupling, not by either
generator alone — Finding S).

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

**GAP 1 (scale/mechanism). The single-generator route is provably dead.** Finding S
shows `max_{c≠0}|Σ_{j<k} e_p(c 2^j)|/k ≈ 0.3–0.8` at `k = C log p` with no `p`-decay;
and the elementary energy identity yields at best `‖∏_{r<L}M_{J+r}‖ ≤ 1 − c/L`, i.e.
`exp(−c k/(log p)²)`, *not* `e^{-ck}`. Yet Finding B shows the true rate is `e^{-ck}`,
`p`-uniform. The gap between these is exactly the **2–3 coupling**: the shift `P`
(mult-by-3) rotates the running vector between the diagonal `D_j` (the 2-phases) so
that no vector can stay near-fixed, even though each generator alone gives no
cancellation. Proving `e^{-ck}` requires quantifying this coupling — the open core,
made precise as:

> **Proposition (P) — uniform 2–3 matrix-product contraction (the substantive missing
> theorem).** There exist absolute `C₀, c₀ > 0` s.t. for every prime `p ∤ 6`, every
> `ξ ≠ 0`, every `n ≥ C₀ log p`,
> ```
>   ‖ M_{n-1}(ξ) ⋯ M_0(ξ) 𝟙 ‖₂ ≤ e^{-c₀ n} √{t₃},   M_j(ξ)=½(I + D_j(ξ)P),
> ```
> `t₃=ord_p3`, `P` cyclic shift on `ℓ²(ℤ/t₃)`, `D_j(ξ)=diag(e_p(ξ 2^j 3^s))_s`.
> (A polynomial `p^{-A}√{t₃}`, `A` large after enlarging `C₀`, also suffices.) Per
> gpt-5.6-sol this is genuinely *rank-two* arithmetic — an energy / S-unit /
> Fourier-decoupling statement for `{2^j 3^s mod p}` — and because `W₂` does not decay
> (Finding S) it does **not** reduce to a single-orbit CDG mechanism. No cited result
> yields it (§6).

**Lemma 3.5′ (Correct architecture — sum-product `L²`-flattening; SKETCH, GAP 1
open).** To obtain the `e^{-ck}` rate one runs the standard finite-field flattening
scheme on the affine walk (4):
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

**Lemma 3.6 (Fixed-weight transfer — GAP 2, and why the naive step is WRONG).** Let
`ν_m` be the law of `B` on the exact weight-`m` slice. **The naive reduction is
invalid:** one cannot bound `ν_m` by dividing the unconditioned Bernoulli Fourier
mass by `Pr(|w|=m)`, because `μ̂(ξ) = Σ_{m'} Pr(|w|=m') ν̂_{m'}(ξ)` and the different
weights `m'` can **cancel** — small `|μ̂(ξ)|` does not imply small `|ν̂_m(ξ)|`. The
correct object is the **bivariate** character sum in a weight phase `θ`:
```
  E[ e_p(ξ B) · e^{iθ|w|} ]  =  the (ξ,θ)-Fourier coefficient of the joint law of (B,|w|),
  ν̂_m(ξ) = (1/2π) ∫_{-π}^{π} e^{-imθ} · E_{q=1/2}[ e_p(ξB) e^{iθ|w|} ] · 2^k dθ.
```
Under an exponential tilt to Bernoulli(`q`), `q = m/k ∈ [η,1−η]`, the per-orbit
transfer becomes `M_{j,q,θ} = (1−q)I + q e^{iθ} U_j`, with the exact identity
`‖M_{j,q,θ}x‖² = ‖x‖² − q(1−q)‖x − e^{iθ}U_j x‖²`. Writing
`H_{q,k}(ξ,θ) = E_q[e_p(ξB) e^{iθ|w|}]` and `ρ_{q,m} = Pr_q(|w|=m)`, coefficient
extraction gives `ν̂_m(ξ) = ρ_{q,m}^{-1} (2π)^{-1}∫_{-π}^{π} H_{q,k}(ξ,θ) e^{-imθ}dθ`,
and by Cauchy–Schwarz the **precise sufficient statement** (gpt-5.6-sol) is:
```
  (FW)   (1/2π)∫_{-π}^{π} Σ_{ξ≠0} |H_{q,k}(ξ,θ)|² dθ  ≤  ρ_{q,m}² · ε_k² / p,
```
uniformly for `q ∈ [η,1−η]`, whence `p‖ν_m − u_p‖_∞ ≤ (p Σ_{ξ≠0}|ν̂_m|²)^{1/2} ≤ ε_k`.
*Honest costs:* (i) prove flattening uniformly in `q∈[η,1−η]` (Lemmas 3.2–3.5′ survive
with `U_j → e^{iθ}U_j`, `M_j → M_{j,q,θ}`); (ii) the squared-`L²` extraction cost is
`ρ_{q,m}^{-2} ≍ k` at `q=m/k` (i.e. `√k` at norm level) — keeping `q=½` instead costs
`ρ_{1/2,m}^{-2} ≍ k·e^{2k D(m/k‖1/2)}`, exponentially bad near the band edges, so the
tilt is mandatory; (iii) a sup in `θ` then divide is the invalid move — the
`θ`-integral is required. **This bivariate `(ξ,θ,q)` estimate is not supplied here.**

**Assembly (conditional).** *If* Gap 1 (coupled `e^{-ck}` flattening, uniformly in
`q∈[η,1−η]`) *and* Gap 2 (the `θ`-integrated bivariate transfer) *and* Gap 3
(worst-case operator-norm / running-vector upgrade of the per-block gap) are closed,
then Lemma 3.1 gives L² flattening on the weight-`m` slice, and the L∞ form follows by
Cauchy–Schwarz alone: `max_a|ν_m(a)−1/p| ≤ (Σ_a(ν_m(a)−1/p)²)^{1/2}` (no support
lower bound needed). All three gaps are currently open.

---

## 4. Exceptional set, the three gaps, and what is genuinely new

**Exceptional set (explicit).** Primes would be exceptional when
`|⟨2,3⟩| = lcm(ord_p2, ord_p3) < p^δ`. Numerically (Finding 3) these are vanishingly
rare and even the extreme cases (`p^{0.54}`) flatten by `k≈4 log p`. The hypothesis
`|⟨2,3⟩| ≥ p^δ` gives only `max(ord_p2,ord_p3) ≥ p^{δ/2}`, so a proof must run through
whichever generator is large (2↔3 duality, §3.5′).

**The three open gaps (restated).**
1. **Coupled `e^{-ck}` flattening (GAP 1).** Prove `‖∏_{j<k} M_{j,q} 𝟙‖ ≤ e^{-ck}`,
   `k ≍ log p`, uniformly in `q∈[η,1−η]`, via the 2–3 coupling. Single-generator /
   short-orbit exponential sums provably cannot do this (Finding S). Candidate tools:
   the CDG spectral-gap analysis of Eberhard–Varjú, or a bivariate `⟨2⟩×⟨3⟩`
   sum-product / decoupling. **Open.**
2. **Bivariate fixed-weight transfer (GAP 2).** The `θ`-integrated
   `(ξ,θ)`-transfer of Lemma 3.6; division by `Pr(|w|=m)` is invalid. **Open.**
3. **Worst-case operator-norm upgrade (GAP 3).** Upgrade the energy/running-vector
   estimate (Lemma 3.5) to a uniform block gap `‖∏_{j∈B}M_j‖ ≤ 1−γ`. **Open.**

**References for the program.** BGK (subgroup sums), *J. London Math. Soc.* **73**
(2006) 380–398; Bourgain–Katz–Tao (sum-product), *GAFA* **14** (2004) 27–57;
Chung–Diaconis–Graham, *Ann. Probab.* **15** (1987) 1148–1165; Eberhard–Varjú (CDG
mixing), *PTRF* **179** (2021) 317–344. (See §6 for the open literature question of
whether Eberhard–Varjú already covers the *unconditioned* two-multiplier walk.)

**Why this is new & interesting regardless of Collatz.** The summands
`3^{m-r}2^{i_r}` are *mixed multiplicative* terms indexed by **rank** — the exponents
`(a_r,b_r)` in `Σ_r g^{a_r}h^{b_r}` are the order statistics of the chosen set. The
clean reduction (Lemmas 3.1–3.4) to a **product of `½(I+U_j)` near-unitary
contractions driven by the `⟨2,3⟩`-action**, together with the exact identification
with a *conditioned two-multiplier Chung–Diaconis–Graham walk*, is the right frame and
is not a standard Littlewood–Offord instance. The decisive empirical separation
(Finding S: theorem true at `k≈3 log p`, single-generator cancellation false) is the
substantive contribution pending the proof.

---

## 5. Reproduce

```
cd experiments/flattening
python3 exact_dp.py       # exact DP, self-check vs brute force (PASS)
python3 sweep.py          # flatness.csv (p<=500), decay.csv
python3 exceptional.py    # exceptional.csv: small-<2,3> primes up to 1e6
python3 threshold.py      # threshold.csv: k*(p) ~ 3 log p
python3 fourier_check.py  # verifies Lemma 3.2 recursion + matrix contraction
python3 rate_check.py     # Finding B: e^{-ck} rate p-uniform; CDG normalization
python3 scale_test.py     # scale_test.csv, Finding S: THE decisive experiment
```

---

## 6. Does existing literature already prove the unconditioned walk?

**No.** (gpt-5.6-sol, cross-checked.)

* **Eberhard–Varjú** (*PTRF* **179** (2021) 317–344, Thm 1.1) prove `O(log p)` mixing
  for the standard CDG process `X_{n+1} = a X_n + ε_{n+1} (mod p)` with a **fixed**
  multiplier `a` (`a=2`) and randomness in the **additive** digit. Our walk has **two
  distinct multipliers** `1/2` and `3/2` and a deterministic step-type sequence; it is
  not an instance of their theorem. Concretely, our Fourier evolution transports modes
  around the `⟨3⟩`-orbit (the shift `P`), whereas theirs is scalar per mode — and the
  nondecay of `W₂` (Finding S) shows the difference is essential.
* **Bourgain–Gamburd** expansion (*Ann. of Math.* **167** (2008), Thm 1) does not
  apply: the generating affine matrices `[[1/2,0],[0,1]]`, `[[3/2,1/2],[0,1]]` lie in a
  **solvable upper-triangular** group, violating the Zariski-density / non-elementarity
  hypotheses. Lindenstrauss–Varjú / BFLM likewise need irreducible non-solvable linear
  dynamics.

So even the *unconditioned* `O(log p)` flattening is **not** a corollary of known
theorems; **Proposition (P)** is the substantive missing input, and the fixed-weight
statement **(FW)** is a separate, additional uniform `(ξ,θ,q)` estimate. Both are
open. The numerics (Findings S, B) make a strong case that (P) is *true*.
