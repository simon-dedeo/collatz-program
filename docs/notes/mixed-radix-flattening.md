# Mixed-radix flattening for the cycle numerator — numerical evidence + proof program

**Status (2026-07-20). This is a numerical-evidence + proof-program note, NOT a
completed proof.** Standalone anti-concentration question for the mixed `(2,3)`-radix
sum, framed independently of Collatz.

**What is established (exact computation, the actual object):** fixed-weight
distributions approach flatness on logarithmic scales on specified finite test
sets: the 93 primes `5≤p≤499`, `p∤6`, at central weight; seven selected
scale-test primes across the
mass band; and fourteen capped-small-subgroup candidates drawn from primes
`p ≤ 10^6`. This is **not** a uniform sweep over all primes below `10^6`,
and it does not establish a `p`-uniform `e^{-ck}` rate. Within the tested scope,
`k = 2 log p` is not flat and no exceptional candidate was found.

**What is NOT proved — three load-bearing gaps (§3):**
1. **Scale/mechanism.** At `k ≈ C log p` one cannot assume that the walk window
   contains a full `⟨2⟩` period: `ord_p(2)` can be much larger than `log p`.
   The single-generator short-orbit sum `max_{c≠0}|Σ_{j<k} e_p(c 2^j)|/k`
   does **not** decay (measured ≈ 0.3–0.8, Finding S). So BGK / short-geometric-sum
   does **not** supply the needed cancellation here. The data suggest that the
   **2–3 coupling** is the missing mechanism, but do not prove causation. A proof
   needs an `e^{-ck}` gap for the *coupled* transfer, not the tested single-
   generator estimate.
2. **Fixed-weight conditioning is not automatic.** Small Fourier mass of the
   unconditioned Bernoulli mixture does not bound the weight-`m` slice (weights cancel
   in `μ̂`); dividing by `Pr(|w|=m)` is invalid. A genuine bivariate `(weight,residue)`
   estimate is required.
3. **Running-vector propagation.** Upgrade one-step or averaged energy loss to
   uniform contraction along the actual `(q,θ)`-dependent trajectories. A
   worst-case operator-norm block gap would suffice but is not required.

An earlier draft claimed "proved modulo one BGK input"; that is **wrong and
retracted** (§3.5). Cross-checked twice with gpt-5.6-sol (2026-07-20); its
corrections are integrated. Exact identities are checked with integer DP, while
the corrected Fourier orientation is checked componentwise to floating-point
tolerance rather than by exact arithmetic.
The successor audit additionally corrected the Fourier matrix orientation, a
fixed-slice normalization, and the definition of the reported fitted decay
rate; all three corrections are called out at their use sites below.
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
`B ≡ 0 (mod p)` for every `p ∣ 2^k − 3^m`. The target lemma would say that
congruence is rare among words of the same `(k,m)`. The target below stands on
its own.)

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

**Finding 1 — near-flatness on the tested grids.** For the 93 primes
`5≤p≤499`, `p∤6`, at
central weight and the first sampled grid point `k∈{12,16,20,24,30,40,50}`
with `k≥4 log p`, the exact-DP value of `p·max_a Pr` lies between `1.0019` and
`1.2175`; thus “machine precision by `4 log p`” was an overstatement. At
`k=40` and `k=50`, across all five sampled weights `0.3k,…,0.7k`, the worst
ratios are `1.0050` and `1.0003`, while the largest recorded L² errors are
`8.32·10^{-7}` and `3.21·10^{-8}`. Some rows reach machine scale, but not every
row does. See `flatness.csv`, `analyze.py`.

**Finding 2 — selected-prime threshold statistic.** Let `k*(p)` be the
least `k` with `p·max_a Pr ≤ 1.10` at `m = ⌊k/2⌋`. Across
the 18 primes listed in `threshold.csv`, `k*(p)/log p` ranges from `3.04` to
`5.10`; the three entries at `p≥2003` are `3.16,3.13,3.19`. This finite sample
suggests logarithmic scaling but establishes neither an asymptotic constant nor
independence from subgroup size.

**Finding S — the decisive selected-prime scale test (`scale_test.py`, `scale_test.csv`).** At
`k = C log p` we compare three quantities (worst `m ∈ [0.3k, 0.7k]` for the last):

| `C` | single-generator `max_c|Σ_{j<k}e_p(c2^j)|/k` | walk `max_{ξ≠0}|μ̂_k(ξ)|` | fixed-weight `p·max_a|Pr−1/p|` |
|----|----|----|----|
| 2 | 0.5175–0.8030 | 0.03556–0.09061 | 2.1770–4.8839 |
| 3 | 0.4626–0.6546 | 0.001821–0.02130 | 0.2235–1.0000 |
| 4 | 0.3027–0.6295 | 0.0001259–0.006636 | 0.0306–0.4886 |
| 5 | 0.3357–0.5120 | 0.000007783–0.001032 | 0.0022–0.0714 |

Two conclusions within these seven primes. **(i) The data support flattening at
`k ≈ 3 log p`** and a sharp-ish constant: `C = 2` fails while `C = 3`
substantially reduces the exact fixed-weight deviation on this sample.
This is measured on the **actual fixed-weight object**, exactly, but is not a
theorem uniform in `p`. **(ii) The single-generator short-orbit sum does NOT
decay on this sample** (stays in the displayed finite range), so the specific complete-subgroup
and tested short-prefix route does not prove the lemma. The data suggest a
**2–3 coupling** explanation: multiplication by 3 moves among frequencies while
the per-step 2-phases act (§3). Establishing that explanation uniformly is Gap 1.

**Finding 3 — no exception among the capped-small-subgroup candidates.**
`exceptional.py` scans primes `p ≤ 10^6` but retains only those for which
`lcm(ord_p(2),ord_p(3))≤400` (and therefore both individual orders are at most
`400`). It finds 105 of the 78,496 eligible primes and then exact-DP tests the fourteen
most extreme retained candidates. Among that filtered list, the smallest
subgroup *relative to `p`* is
```
  p = 6553,  |⟨2,3⟩| = 117 ≈ p^{0.54}   (ord 2 = 117, ord 3 = 39).
```
Every tested small-subgroup candidate — down to `p^{0.54}` — has full support
and is near-flat around `4 log p`, but not identically flat. At the sampled
point nearest `4 log p`, `linf_ratio` ranges from `1.0015` to `1.1054`; at the
first sampled point at or above `4 log p`, it ranges from `1.0005` to `1.0377`.
For the most extreme candidate `p=6553`, the values at `k=36,48,60` are
`1.0138,1.0004,1.0000`. Genuinely tiny subgroups
(`p^{0.2}`) do not occur in this filtered sample. The scan does **not** prove
that `p=6553` is extremal among all primes below `10^6`: a prime with an order
above the cap can have a smaller relative exponent. Accordingly no uniform
lower bound `|⟨2,3⟩| ≥ p^δ` follows from this computation.

**Finding 4 — Fourier structure verified numerically** (`fourier_check.py`):
the Bernoulli(1/2) Fourier recursion (Lemma 3.2 below) holds to floating-point
residual, and the correctly oriented per-orbit matrix product reproduces the
Fourier vector from the all-ones initial state componentwise. A successor audit
fixed the former reversed cyclic shift. The top singular value is printed only
as an operator-norm diagnostic; it is not claimed to equal the trajectory or
the worst Fourier coefficient.

**Finding B — selected-prime evidence for an `e^{-ck}` rate** (`rate_check.py`). The
fitted per-step `L²` Fourier decay rate
`λ(p)=−d[log Σ_{ξ≠0}|μ̂_k(ξ)|²]/dk` ranges from `0.575` to `0.791`
on the eight selected primes, while `λ(log p)²` ranges from `9.33` to `47.63`
and is not monotone. (An earlier formula incorrectly inserted an extra factor
`1/k`; the code fits the negative least-squares slope.) On this finite sample
the observed rate is compatible with
`e^{-ck}` with `c` bounded away from zero, and is substantially faster than
the crude `e^{-ck/(log p)²}` elementary phase-variation proxy
(§3.5). Also verified: the normalization `X_j = 2^{-j}B_j` turns the recursion exactly
into a two-multiplier CDG-type affine walk `X↦X/2 | (3X+1)/2`.

**Verdict:** the finite exact data strongly support the statement at
`k ≈ 3 log p`, but do not prove it uniformly in `p`. A proof must control the
coupled transfer; the data suggest, but do not establish, a genuinely 2–3
mechanism. The tested single-generator estimate does not explain the data.
See §3 and its three explicit gaps.

---

## 3. Proof program — numbered lemmas, with the three gaps marked

Lemmas 3.1–3.3 and the displayed identity in Lemma 3.4 are elementary. The
uniform deficit asserted after that identity requires a large `⟨3⟩` orbit and a
complete-subgroup exponential-sum input; sustained contraction under the
original combined-subgroup hypothesis remains open. Lemmas 3.5–3.6 are proof
architecture, not completed implications (Gaps 1–3). We first relax the
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

**Reformulation as a CDG-type affine walk (verified algebraically, `rate_check.py`).**
Normalize `X_j := 2^{-j} B_j (mod p)`. Then the recursion becomes the *homogeneous*
two-multiplier affine walk
```
  X_{j+1} = X_j / 2        (bit 0),        X_{j+1} = (3 X_j + 1)/2   (bit 1).
```
This is a two-multiplier **Chung–Diaconis–Graham-type** process
[Chung–Diaconis–Graham, *Random walks arising in random number generation*, Ann.
Probab. **15** (1987) 1148–1165]; its `F_p` mixing time is `Θ(log p)` for almost all
`p` [Eberhard–Varjú, *Mixing time of the CDG random process*, PTRF **179** (2021)
317–344]. Our object is this walk **conditioned on the number `m` of bit-1 steps**.
This is the relevant literature anchor and motivates a logarithmic-scale
comparison, but it is not a black-box proof: the two distinct multipliers lie
outside the standard fixed-multiplier CDG theorem, and fixed weight constrains
the total number (not the order) of bit-1 steps.

**Key structural point.** Multiplication-by-3 couples frequency `ξ` only to `3ξ`.
The orbits of `ξ ↦ 3ξ` on `F_p^*` are the cosets of `⟨3⟩`, each of size
`t_3 := ord_p 3`. Fix one orbit `O = {ξ_0, 3ξ_0, …, 3^{t_3−1}ξ_0}` and set
`v_j = (μ̂_j(3^i ξ_0))_{i=0}^{t_3−1} ∈ ℂ^{t_3}`.

**Lemma 3.3 (Orbit transfer as a product of near-unitary contractions).**
`v_{j+1} = M_j v_j`, where
```
  M_j = ½ ( I + U_j ),   U_j = D_j P,   P = cyclic shift (P_{i,i+1}=1),
  D_j = diag( e_p(3^i ξ_0 2^j) )_{i}.
```
`U_j` is unitary, so `‖M_j‖ ≤ 1`, and `‖M_j x‖² = ½(‖x‖² + Re⟨x, U_j x⟩)`.
Since `μ̂_0 ≡ 1`, the initial vector is the **all-ones vector** `𝟙` (`P𝟙 = 𝟙`), a
specific vector — we track its trajectory, not the operator norm. By Lemma 3.1,
```
  Σ_{ξ≠0} |μ̂_k(ξ)|^2  =  Σ_{orbits O} ‖ (∏_{j=0}^{k-1} M_j^{(O)}) 𝟙 ‖^2 .
```
There are `(p−1)/t_3` orbits, `‖𝟙‖² = t_3`. For `p=31`, the checker verifies
componentwise that `∏M_j 𝟙` at `k=24` equals the Fourier vector restricted to
the orbit of `ξ=1`, to floating-point tolerance.

**Lemma 3.4 (First-step gain from the all-ones vector).** `M_j 𝟙 = ½(𝟙 + d_j)` with
`d_j = (e_p(3^i ξ_0 2^j))_i`. Since `½(1+e^{iφ}) = e^{iφ/2}cos(φ/2)`, the `i`-th
component has modulus `|cos(π · 3^i ξ_0 2^j / p)|`, whence
```
  ‖M_j 𝟙‖^2 = Σ_i cos^2(π 3^i ξ_0 2^j / p) = t_3 − Σ_i sin^2(π 3^i ξ_0 2^j / p).
```
Conditional on `t_3≥p^{δ'}`, a complete-subgroup exponential-sum estimate gives
a bound `Σ_i sin^2(π 3^iξ_0 2^j/p)≥γ_0(δ')t_3`; the original hypothesis on
`|⟨2,3⟩|` does not itself imply this lower bound for `t_3`. Under that extra
hypothesis this gives one factor of contraction *at the first step from `𝟙`*.
It does **not** by itself give `e^{-ck}` over many steps: the running vector `x_r`
generally leaves the flat direction, and sustaining contraction is exactly GAP 1
below. The complete-period BGK argument and the tested `W₂` prefix proxy do not
supply sustained contraction; the finite data suggest coupled dynamics without
excluding every possible one-generator method.

**Lemma 3.5 (Energy identity and where the real work is).** For `x_{r+1} = M_{J+r}x_r`
one has the exact identity (`U_j` unitary)
```
  ‖M_j x‖² = ‖x‖² − ¼‖(I − U_j)x‖²,     hence
  ‖x‖² − ‖x_L‖² = ¼ Σ_{r<L} ‖(I − U_{J+r}) x_r‖².
```
So the trajectory contracts unless the running vector `x_r` is nearly fixed by every
`U_{J+r}`. `U_j w = w` forces `θ_i − θ_{i+1} ≡ 2π·3^iξ_0 2^j/p` (writing
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

**GAP 1 (scale/mechanism). The complete-subgroup / short-prefix route is unavailable.**
On the seven scale-test primes, Finding S shows
`max_{c≠0}|Σ_{j<k} e_p(c 2^j)|/k ≈ 0.3–0.8` at `k = C log p`; moreover the explicit
`c=1`, `2^k=o(p)` regime rules out any universal short-prefix cancellation statement
of the proposed form. The elementary energy identity yields at best
`exp(−c k/(log p)²)`, not `e^{-ck}`. Finding B observes faster decay only on a finite
selected-prime sample. A proposed explanation is the **2–3 coupling** between the
shift `P` and diagonal `D_j`. The finite data do not prove that mechanism or
exclude all one-generator approaches. Proving `e^{-ck}` for the coupled product
is the open core,
made precise as:

> **Proposition (P) — uniform 2–3 matrix-product contraction (the substantive missing
> theorem).** For every `δ>0`, there should exist `C₀(δ),c₀(δ)>0` such that for
> every prime `p∤6` with `|⟨2,3⟩|≥p^δ`, every
> `ξ ≠ 0`, every `n ≥ C₀ log p`,
> ```
>   ‖ M_{n-1}(ξ) ⋯ M_0(ξ) 𝟙 ‖₂ ≤ e^{-c₀ n} √{t₃},   M_j(ξ)=½(I + D_j(ξ)P),
> ```
> `t₃=ord_p3`, `P` cyclic shift on `ℓ²(ℤ/t₃)`, `D_j(ξ)=diag(e_p(ξ 2^j 3^s))_s`.
> (A polynomial `p^{-A}√{t₃}`, `A` large after enlarging `C₀`, also suffices.) Per
> gpt-5.6-sol this is genuinely *rank-two* arithmetic — an energy / S-unit /
> Fourier-decoupling statement for `{2^j 3^s mod p}` — and because `W₂` does not decay
> (Finding S) the tested prefix estimate does **not** supply the result. No cited theorem
> yields it (§6).

**Lemma 3.5′ (Proposed sum-product `L²` architecture; SKETCH, GAP 1 open).**
One possible route to the `e^{-ck}` rate is a finite-field flattening scheme on
the affine walk:
> 1. Suppose `L²`-flattening fails at time `k`: `Σ_{ξ≠0}|μ̂_k(ξ)|² > p^{-c}`.
> 2. One would need dyadic pigeonholing + **Balog–Szemerédi–Gowers** to produce a set `A ⊆ F_p`,
>    `p^{c'} ≤ |A| ≤ p^{1-c'}`, carrying `≍` the missing mass and **approximately
>    invariant** under both the affine maps `x↦x/2, x↦(3x+1)/2` — i.e. `A` has small
>    additive doubling *and* is nearly stable under multiplication by `3` (equiv. `2`).
> 3. One would then need small additive doubling + multiplicative stability to contradict the
>    **Bourgain–Katz–Tao** sum-product theorem [BKT, *A sum-product estimate in
>    finite fields and applications*, GAFA **14** (2004) 27–57]:
>    `p^δ ≤ |A| ≤ p^{1-δ} ⟹ max(|A+A|,|A·A|) ≥ c_δ|A|^{1+ε(δ)}`.
> If both implications are quantified for this affine walk, the contradiction
> would force flattening after `O_δ(log p)` steps. BGK enters only where
> a *complete* subgroup average legitimately appears (e.g. `H=⟨2,3⟩`, cf. its use in
> Bourgain–Gamburd-type schemes), never on a log-prefix.

> **Order-size observation and proposed dual route.** Since `lcm(a,b) ≤ ab ≤ max(a,b)²`, the
> hypothesis `|⟨2,3⟩| = lcm(ord_p2,ord_p3) ≥ p^δ` implies only
> `max(ord_p2, ord_p3) ≥ p^{δ/2}` (not that both orders are large). The scheme is run
> A proof might try whichever generator has large order — position-indexing for `2`, or, via the
> suffix-count form `B = Σ_j ε_j 2^j 3^{N_j}`, rank-indexing for `3`. This `δ/2`
> is exact; the alternate rank-indexed transfer for `3` is only proposed here,
> not derived.

**Lemma 3.6 (Fixed-weight transfer — GAP 2, and why the naive step is WRONG).** Let
`ν_m` be the law of `B` on the exact weight-`m` slice. **The naive reduction is
invalid:** one cannot bound `ν_m` by dividing the unconditioned Bernoulli Fourier
mass by `Pr(|w|=m)`, because `μ̂(ξ) = Σ_{m'} Pr(|w|=m') ν̂_{m'}(ξ)` and the different
weights `m'` can **cancel** — small `|μ̂(ξ)|` does not imply small `|ν̂_m(ξ)|`. The
correct object is the **bivariate** character sum in a weight phase `θ`:
```
  E[ e_p(ξ B) · e^{iθ|w|} ]  =  the (ξ,θ)-Fourier coefficient of the joint law of (B,|w|),
  ν̂_m(ξ) = [2^k / binom(k,m)] · (1/2π) ∫_{-π}^{π} e^{-imθ}
             · E_{q=1/2}[ e_p(ξB) e^{iθ|w|} ] dθ.
```
The factor `binom(k,m)^{-1}` is essential because `ν_m` is the *normalized*
uniform law on the weight-`m` slice. An earlier displayed formula omitted it;
the tilted formula below, with normalization `ρ_{q,m}^{-1}`, is the same
identity in the correct general form.
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
tilt is mandatory for this coefficient-extraction route; (iii) a sup in `θ` then divide is the invalid move — the
`θ`-integral is required. **This bivariate `(ξ,θ,q)` estimate is not supplied here.**

**Assembly (conditional).** *If* Gap 1 (coupled `e^{-ck}` flattening, uniformly in
`q∈[η,1−η]`) *and* Gap 2 (the `θ`-integrated bivariate transfer) *and* Gap 3
(running-vector propagation along the actual tilted trajectories) are closed,
then Lemma 3.1 gives L² flattening on the weight-`m` slice, and the L∞ form follows by
Cauchy–Schwarz alone: `max_a|ν_m(a)−1/p| ≤ (Σ_a(ν_m(a)−1/p)²)^{1/2}` (no support
lower bound needed). All three gaps are currently open.

---

## 4. Exceptional set, the three gaps, and the proposed new ingredient

**Exceptional set (explicit).** Primes would be exceptional when
`|⟨2,3⟩| = lcm(ord_p2, ord_p3) < p^δ`. The capped scan found 105
primes with `|⟨2,3⟩|≤400` among the 78,496 eligible primes below `10^6` and
exact-DP tested fourteen. This does not estimate the frequency excluded by a
fixed-`δ` hypothesis. The hypothesis
`|⟨2,3⟩| ≥ p^δ` gives only `max(ord_p2,ord_p3) ≥ p^{δ/2}`, so a proof must run through
whichever generator is large (2↔3 duality, §3.5′).

**The three open gaps (restated).**
1. **Coupled `e^{-ck}` flattening (GAP 1).** Prove `‖∏_{j<k} M_{j,q} 𝟙‖ ≤ e^{-ck}`,
   `k ≍ log p`, uniformly in `q∈[η,1−η]`. The complete-period BGK argument and
   tested `W₂` prefix proxy do not supply this estimate. Candidate tools:
   the CDG spectral-gap analysis of Eberhard–Varjú, or a bivariate `⟨2⟩×⟨3⟩`
   sum-product / decoupling. **Open.**
2. **Bivariate fixed-weight transfer (GAP 2).** The `θ`-integrated
   `(ξ,θ)`-transfer of Lemma 3.6; division by `Pr(|w|=m)` is invalid. **Open.**
3. **Running-vector propagation (GAP 3).** Upgrade the one-step/averaged energy
   loss to uniform contraction along the actual `(q,θ)`-dependent trajectories.
   A worst-case block operator-norm gap would suffice but is not required. **Open.**

**References for the program.** BGK (subgroup sums), *J. London Math. Soc.* **73**
(2006) 380–398; Bourgain–Katz–Tao (sum-product), *GAFA* **14** (2004) 27–57;
Chung–Diaconis–Graham, *Ann. Probab.* **15** (1987) 1148–1165; Eberhard–Varjú (CDG
mixing), *PTRF* **179** (2021) 317–344. (See §6 for the open literature question of
whether Eberhard–Varjú already covers the *unconditioned* two-multiplier walk.)

**Candidate contribution, independently interesting if completed.** The summands
`3^{m-r}2^{i_r}` are *mixed multiplicative* terms indexed by **rank** — the exponents
`(a_r,b_r)` in `Σ_r g^{a_r}h^{b_r}` are the order statistics of the chosen set. The
clean reduction (Lemmas 3.1–3.3) to a **product of `½(I+U_j)` near-unitary
contractions driven by the `⟨2,3⟩`-action**, together with the exact identification
with a *conditioned two-multiplier Chung–Diaconis–Graham walk*, is the right frame and
appears not to be a standard Littlewood–Offord instance. The empirical separation
(Finding S: selected-prime flattening at `k≈3 log p`, with the tested
single-generator mechanism failing) is the
substantive contribution pending the proof.

---

## 5. Reproduce

```
cd experiments/flattening
python3 exact_dp.py       # exact DP, self-check vs brute force (PASS)
python3 sweep.py          # flatness.csv (p<=500), decay.csv
python3 exceptional.py    # exceptional.csv: small-<2,3> primes up to 1e6
python3 threshold.py      # selected-prime first-crossing statistic
python3 fourier_check.py  # recursion + corrected orbit-product identity
python3 rate_check.py     # Finding B: selected-prime decay; CDG normalization
python3 scale_test.py     # scale_test.csv, finite selected-prime diagnostic
```

---

## 6. Does existing literature already prove the unconditioned walk?

**No cited theorem in the present audit supplies this result.**

* **Eberhard–Varjú** (*PTRF* **179** (2021) 317–344, Thm 1.1) prove `O(log p)` mixing
  for the standard CDG process `X_{n+1} = a X_n + ε_{n+1} (mod p)` with a **fixed**
  multiplier `a` (`a=2`) and randomness in the **additive** digit. Our walk has **two
  distinct multipliers** `1/2` and `3/2`, chosen randomly at each unconditioned
  step; under fixed weight only the total count of type-1 steps is fixed, not
  their order. It is
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
open. The finite numerics support only a suitably `δ`-dependent version of (P)
on the tested primes.
