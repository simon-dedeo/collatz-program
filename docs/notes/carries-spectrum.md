# The exact spectrum of the Diaconis–Fulman multiplication-carries chain

2026-07-20. Status: **complete proof** (every step below is self-contained), answering
the spectral question Diaconis–Fulman left open in §5.2 of arXiv:0806.3583 for the
coprime case. Verified numerically (numpy, machine precision, 12 multipliers up to
m = 243 plus general-base spot checks) and symbolically (sympy, exact rationals /
exact cyclotomic arithmetic). Scripts:
`experiments/carries/verify_carries_spectrum.py`, `experiments/carries/verify_carries_exact.py`.
Context: docs/CRACKS.md, Crack 4. Lean-ability: high (finite linear algebra +
one telescoping identity over cyclotomics).

---

## 1. The chain, and what was open

Fix a base b ≥ 2 and a multiplier m ≥ 2 (Diaconis–Fulman write k for the
multiplier). Multiply a b-ary "random number" — digits d₀, d₁, d₂, … i.i.d.
uniform on {0,…,b−1}, processed least-significant first — by m, by long
multiplication. The pending carry evolves as

  c₀ = 0,  sᵢ = m·dᵢ + cᵢ,  output digit uᵢ = sᵢ mod b,  cᵢ₊₁ = ⌊sᵢ/b⌋.

Since cᵢ ≤ m−1 implies cᵢ₊₁ = ⌊(m·dᵢ + cᵢ)/b⌋ ≤ ⌊(m(b−1)+m−1)/b⌋ = m−1, the
carries stay in {0,…,m−1}, and because the dᵢ are i.i.d., (cᵢ) is a Markov chain
on {0,…,m−1} with kernel

  K_{m,b}(c, c′) = (1/b) · #{ d ∈ {0,…,b−1} : ⌊(m·d + c)/b⌋ = c′ }.

This is exactly the "carries for multiplication" chain of Diaconis–Fulman
(§5.2 of arXiv:0806.3583; their worked example is m = 26, b = 10). They prove:
K is doubly stochastic (so uniform is stationary), K is a generalized circulant
(each column is the previous column shifted down by b mod m), the base
multiplicativity K_{m,a}·K_{m,b} = K_{m,ab}, and the total-variation upper bound
d_TV(K₀ʳ, π) ≤ m/(2bʳ) (their Proposition 5.1). About the spectrum they say only
that the example matrix (b = 10, m = 7) "does not have all eigenvalues real", and:

> "Convergence rate lower bounds depend on the number theoretic relation of k
> and b in a complicated way."

This note computes the spectrum exactly when gcd(m, b) = 1 and shows the
"number theoretic relation" is precisely the orbit structure of multiplication
by b on ℤ/m. (Contrast Holte's addition-carries "amazing matrix", whose spectrum
is 1, 1/b, 1/b², …: here **all** nontrivial eigenvalues sit on the circle of
radius exactly 1/b, with cyclotomic phases.)

## 2. Main theorem

**Theorem 1.** Let gcd(m, b) = 1, and let K = K_{m,b} be the chain above. Then

  det(xI − K) = (x − 1) · ∏_O ( x^{|O|} − b^{−|O|} ),

the product running over the orbits O of the map x ↦ b·x mod m on (ℤ/m)∖{0}.
Consequently the spectrum of K is

  {1} ∪ { b⁻¹·ζ : O an orbit, ζ^{|O|} = 1 },

with multiplicities read off from the orbit sizes; every eigenvalue other than
the Perron eigenvalue 1 has modulus **exactly 1/b**. Moreover K is
diagonalizable over ℂ.

(Orbit convention: the proof below produces the permutation x ↦ b⁻¹x on
character indices; a permutation and its inverse have identical orbits, so
stating the product over orbits of x ↦ bx, as above, is equivalent. Either
reading of Crack 4's formula is correct.)

For b = 2 and odd m this is the claim recorded in CRACKS.md Crack 4:
det(xI − K_m) = (x−1)·∏_O (x^{|O|} − 2^{−|O|}) over ⟨2⟩-orbits O on (ℤ/m)∖{0}.

## 3. Proof

Throughout, gcd(m,b) = 1, ω := e^{2πi/m}, and b⁻¹ denotes the inverse of b
mod m. Characters of ℤ/m: χ_x(c) := ω^{xc} for x ∈ ℤ/m. We let K act on
functions, (Kf)(c) = E[f(c₁) | c₀ = c]; the matrix of this operator in the
delta basis is the transition matrix, so they have the same characteristic
polynomial.

### Step 1: the chain is exactly affine mod m

**Lemma 1 (exact linearization).** Identify the state space {0,…,m−1} with ℤ/m.
Then the chain is

  c′ ≡ b⁻¹·(c − u)  (mod m),  u uniform on {0,…,b−1}, i.i.d. over steps,

where u is the **output digit** of the current step; in particular, given the
entire past, the output digit is exactly uniform on {0,…,b−1}.

*Proof.* From s = m·d + c, u = s mod b, c′ = (s−u)/b we get the exact integer
identity

  b·c′ = c + m·d − u,

so c′ ≡ b⁻¹(c − u) (mod m); since 0 ≤ c′ ≤ m−1, the residue determines c′.
It remains to identify the conditional law of u. Given c, the map
d ↦ u = (m·d + c) mod b is a bijection of {0,…,b−1} (m is invertible mod b
because gcd(m,b) = 1). Since d is uniform and independent of the past, u is
uniform on {0,…,b−1} and independent of the past. Conversely (c,u) determines
d, so driving the chain by u loses nothing. ∎

Two remarks. (i) This is where the non-linear ⌊·/b⌋ is dissolved: division by b
becomes multiplication by b⁻¹ mod m *after subtracting the output digit* — the
change of variables hinted at in the crack brief, made exact. (ii) Lemma 1
re-proves that the output digit stream of m × (uniform b-adic input) is i.i.d.
uniform, as it must be: m is a unit in ℤ_b-adic arithmetic, so multiplication
by m preserves Haar measure. The time reversal of the chain, c = b·c′ + u mod m,
is the "append a digit" map.

### Step 2: Fourier transform makes K monomial

**Lemma 2.** For all x ∈ ℤ/m: K χ_x = w_x · χ_{b⁻¹x}, with

  w₀ = 1,  and  w_x = (1/b) · (1 − ω^{−x}) / (1 − ω^{−b⁻¹x})  for x ≠ 0.

*Proof.* By Lemma 1,
(Kχ_x)(c) = (1/b) Σ_{u=0}^{b−1} ω^{x·b⁻¹(c−u)} = ω^{(b⁻¹x)c} · (1/b) Σ_{u=0}^{b−1} ω^{−(b⁻¹x)u}.
If x = 0 the sum is b. If x ≠ 0 then b⁻¹x ≢ 0 (mod m), so ω^{−b⁻¹x} ≠ 1 and the
geometric sum gives (1/b)·(1 − ω^{−b·b⁻¹x})/(1 − ω^{−b⁻¹x}) =
(1/b)·(1 − ω^{−x})/(1 − ω^{−b⁻¹x}). ∎

So in the character basis {χ_x}_{x∈ℤ/m} (a basis of ℂ^{ℤ/m}: the DFT), K is a
**monomial matrix**: a weighted permutation, the permutation being
σ: x ↦ b⁻¹x, which fixes 0 and permutes (ℤ/m)∖{0} with cycles equal to the
⟨b⟩-orbits.

*Cross-check with DF's properties:* the g-circulant structure DF observe is
exactly monomiality in the Fourier basis (Davis, "Circulant Matrices", ch. 5);
and their base multiplicativity K_{m,a}K_{m,b} = K_{m,ab} is transparent here —
the weights compose telescopically:
w_x^{(b)} · w_{b⁻¹x}^{(a)} = (1/ab)·(1−ω^{−x})/(1−ω^{−(ab)⁻¹x}) = w_x^{(ab)}.

### Step 3: the weight product around each orbit telescopes to b^{−|O|}

**Lemma 3.** For every ⟨b⟩-orbit O ⊆ (ℤ/m)∖{0}:  ∏_{x∈O} w_x = b^{−|O|}.

*Proof.* ∏_{x∈O} w_x = b^{−|O|} · ∏_{x∈O}(1 − ω^{−x}) / ∏_{x∈O}(1 − ω^{−b⁻¹x}).
The map x ↦ b⁻¹x is a bijection of O onto itself, so the two products run over
the same nonzero factors and cancel exactly. ∎

### Step 4: characteristic polynomial of a weighted cycle

**Lemma 4.** Let C be the ρ×ρ matrix of a weighted cyclic shift,
C e_j = w_j e_{j+1 (mod ρ)}. Then det(xI − C) = x^ρ − w₁w₂⋯w_ρ. If moreover all
w_j ≠ 0, C is diagonalizable with eigenvalues the ρ-th roots of w₁⋯w_ρ.

*Proof.* In the Leibniz expansion of det(xI − C), a permutation contributes
only if it uses entries from the support: the diagonal (x's) and the single
ρ-cycle graph j → j+1 (entries −w_j). Any nontrivial cycle of a contributing
permutation must consist entirely of edges j → j+1 and hence be the full
ρ-cycle. So exactly two permutations contribute: the identity, giving x^ρ; and
the full cycle, giving sgn = (−1)^{ρ−1} times ∏(−w_j) = (−1)^ρ ∏w_j, i.e.
−∏w_j. Hence det(xI − C) = x^ρ − ∏w_j.
If all w_j ≠ 0, then for each ρ-th root λ of ∏w_j the recursion
α_{j+1} = α_j w_j / λ (indices mod ρ, consistent around the cycle since
∏ w_j/λ^ρ = 1) produces a nonzero eigenvector Σ_j α_j e_j; these are ρ distinct
eigenvalues, so C is diagonalizable. ∎

### Assembly

The matrix of K in the character basis is block-diagonal along the cycles of σ.
The fixed point x = 0 contributes the factor (x − 1) (w₀ = 1: stationarity of
uniform). Each ⟨b⟩-orbit O contributes, by Lemmas 3–4, the factor
x^{|O|} − b^{−|O|}. This proves the determinant formula. Each w_x ≠ 0 (the
numerator 1 − ω^{−x} vanishes only at x = 0), so by Lemma 4 every block is
diagonalizable, with eigenvalues {b⁻¹ζ : ζ^{|O|} = 1}, all of modulus exactly
1/b. **Theorem 1 is proved.** ∎

Explicitly, for eigenvalue λ = b⁻¹ζ (ζ^{|O|} = 1) in block O with base point
x₀, an eigenvector is Σ_{j=0}^{|O|−1} α_j χ_{x_j}, x_j = b^{−j}x₀,
α_j = ζ^{−j} (1−ω^{−x₀})/(1−ω^{−x_j}) — used again in §6.

## 4. Exact non-asymptotic consequences

Let Π := uniform-averaging projector (all entries 1/m), L := ord_m(b) the
multiplicative order of b mod m, π the uniform distribution.

**Proposition 2 (exact powers).** For x ≠ 0,

  Kʳ χ_x = b^{−r} · (1 − ω^{−x})/(1 − ω^{−b^{−r}x}) · χ_{b^{−r}x}.

Consequently:

(i) ‖Kʳ − Π‖_{L²(π)→L²(π)} = b^{−r} · max_{x≠0} |1−ω^{−x}|/|1−ω^{−b^{−r}x}|, and

  b^{−r} ≤ ‖Kʳ − Π‖_{L²(π)} ≤ b^{−r}/sin(π/m).

(ii) bʳ(Kʳ − Π) is **periodic in r with period L**.

(iii) At multiples of the order, exactly: K^{jL} = Π + b^{−jL}(I − Π).

*Proof.* The power formula is Lemma 2 iterated; the weight telescopes as in
Lemma 3: ∏_{i=0}^{r−1} w_{b^{−i}x} = b^{−r}(1−ω^{−x})/(1−ω^{−b^{−r}x}).
(i): the characters are orthonormal in L²(π), and Kʳ − Π kills χ₀ and maps the
remaining orthonormal vectors χ_x to scalars times the distinct orthonormal
vectors χ_{b^{−r}x}; the operator norm of such a map is the largest scalar
modulus. Upper bound: |1−ω^{−x}| ≤ 2 and |1−ω^{−y}| = 2 sin(π‖y/m‖) ≥ 2 sin(π/m)
for y ≠ 0. Lower bound: choose x maximizing |1−ω^{−x}| over (ℤ/m)∖{0}; then the
ratio is ≥ 1. (ii): both the scalar bʳ·b^{−r}(1−ω^{−x})/(1−ω^{−b^{−r}x}) and
the target index b^{−r}x depend on r only through r mod |O| (which divides L;
and the orbit of 1 has size exactly L, so the period is exactly L).
(iii): when L | r, b^{−r}x = x, so the scalar is b^{−r} for every x ≠ 0, i.e.
Kʳ − Π = b^{−r}(I − Π). ∎

**Proposition 3 (exact total-variation distance from the start state).** For the
chain started at c₀ = 0 (as in DF), with t_r := bʳ mod m,

  d_TV(K₀ʳ, π) = t_r (m − t_r) / (m·bʳ).

*Proof.* As in DF's proof of their Proposition 5.1: after r steps the carry is
c_r = ⌊m·x/bʳ⌋ with x uniform on {0,…,bʳ−1} (the low r output digits satisfy
m·x = (output mod bʳ) + bʳ c_r). So K₀ʳ(j) = N_j/bʳ with
N_j = #{x < bʳ : ⌊mx/bʳ⌋ = j} = ⌈(j+1)bʳ/m⌉ − ⌈j bʳ/m⌉ ∈ {⌊bʳ/m⌋, ⌊bʳ/m⌋+1},
and Σ_j N_j = bʳ forces exactly t_r of the m values of j to take the larger
value (t_r ≠ 0 since gcd(m,b)=1, m > 1). Each larger-value j contributes
(m−t_r)/(m bʳ) to Σ|K₀ʳ(j) − 1/m| and each smaller-value j contributes
t_r/(m bʳ); summing and halving gives the claim. ∎

This pins down DF's "complicated number-theoretic relation" in closed form: the
TV profile is literally the ⟨b⟩-orbit of 1 in ℤ/m, oscillating between
(m−1)/(m bʳ) (when bʳ ≡ ±1 mod m) and ≈ m/(4bʳ) (when bʳ mod m ≈ m/2). It
sharpens DF's upper bound m/(2bʳ) to m/(4bʳ) and provides the matching lower
bound: the mixing rate is exactly 1/b per step.

**Proposition 4 (correlation decay for the carry process).** Drive the chain by
Lemma 1 (u₀, u₁, … i.i.d. uniform digits). Fix t, r ≥ 0. Let f be bounded and
measurable w.r.t. the past σ(c₀, u_j : j < t), and g bounded measurable w.r.t.
the future σ(c_{t+r}, u_j : j ≥ t+r). Then:

(a) (any initial law of c₀)  |Cov(f, g)| ≤ (2√m / sin(π/m)) · b^{−r} · ‖f‖_∞‖g‖_∞
  ≤ m^{3/2} · b^{−r} · ‖f‖_∞‖g‖_∞.

(b) (stationary chain, c₀ ~ π)  |Cov(f, g)| ≤ (b^{−r}/sin(π/m)) · ‖f−Ef‖₂ ‖g−Eg‖₂.

(c) (exactness) If L | r then for any functions φ, ψ on the state space and
  **any** law of c₀:  Cov(φ(c_t), ψ(c_{t+r})) = b^{−r} · Cov(φ(c_t), ψ(c_t)).

*Proof.* Set h(y) := E[g | c_{t+r} = y]; since the digits u_{≥t+r} are
independent of everything up to time t+r, E[g | 𝔉_{t+r}] = h(c_{t+r}), and
‖h‖_∞ ≤ ‖g‖_∞. Markov property: E[h(c_{t+r}) | 𝔉_t] = (Kʳh)(c_t). Write
v := (Kʳ − Π)h, so (Kʳh)(c_t) = π(h) + v(c_t). Constants drop out of
covariances, hence

  Cov(f, g) = Cov(f, h(c_{t+r})) = Cov(f, v(c_t)).

(a): |Cov(f, v(c_t))| ≤ 2‖f‖_∞‖v‖_∞, and since π is uniform,
‖v‖_∞ ≤ √m ‖v‖_{L²(π)} ≤ √m · (b^{−r}/sin(π/m)) · ‖h‖_∞ by Prop. 2(i); finally
sin(π/m) ≥ 2/m gives the m^{3/2} form.
(b): under stationarity E[v(c_t)] = π(v) = 0, so
Cov(f, v(c_t)) = E[(f−Ef)·v(c_t)] ≤ ‖f−Ef‖₂ ‖v(c_t)‖₂ = ‖f−Ef‖₂ ‖v‖_{L²(π)},
and ‖v‖_{L²(π)} = ‖(Kʳ−Π)(h−πh)‖_{L²(π)} ≤ (b^{−r}/sin(π/m))·‖h−πh‖_{L²(π)}
≤ (b^{−r}/sin(π/m))·‖g−Eg‖₂ (conditional expectation contracts L²).
(c): by Prop. 2(iii), E[ψ(c_{t+r}) | c_t] = π(ψ) + b^{−r}(ψ(c_t) − π(ψ)), so
ψ's conditional expectation is an affine function of ψ(c_t) with slope b^{−r},
whatever the law of c_t. ∎

Part (c) with (b) shows the rate b^{−r} in these statements is exact, not an
upper bound artifact — every subdominant eigenvalue has modulus exactly 1/b —
and by Prop. 2(ii) the b^r-rescaled correlation profile r ↦ bʳ·Cov is
(exactly) periodic in r with period L: the oscillation frequencies are
2πj/L, j = 0, …, L−1.

## 5. The Collatz tower m = 3^a, b = 2

**Corollary 5.** Let a ≥ 1, m = 3^a, b = 2, L := ord_{3^a}(2) = 2·3^{a−1}. The
⟨2⟩-orbits on (ℤ/3^a)∖{0} are exactly the a "3-adic layers"
{x : v₃(x) = a−i}, i = 1,…,a, of sizes φ(3^i) = 2·3^{i−1}. Hence

  det(xI − K_{3^a,2}) = (x − 1) · ∏_{i=1}^{a} ( x^{2·3^{i−1}} − 2^{−2·3^{i−1}} ),

the spectrum is {1} ∪ { ½·e^{2πi j / (2·3^{i−1})} : 1 ≤ i ≤ a, 0 ≤ j < 2·3^{i−1} },
all subdominant moduli are exactly ½, all phases lie in (2π/L)·ℤ, and

  K^{jL} = Π + 2^{−jL}(I − Π)  exactly, with L = 2·3^{a−1}.

*Proof.* 2 is a primitive root mod 3 (ord = 2 = φ(3)) and mod 9 (powers of 2
mod 9: 2, 4, 8, 7, 5, 1 — order 6 = φ(9)); by the standard lifting theorem
for odd prime powers, 2 is a primitive root mod 3^i for every i ≥ 1, so
ord_{3^i}(2) = φ(3^i) = 2·3^{i−1}. A nonzero x ∈ ℤ/3^a with v₃(x) = a−i is
3^{a−i}·y with y a unit mod 3^i; multiplication by 2 preserves the layer, and
since ⟨2⟩ = (ℤ/3^i)^×, each layer is a single orbit, of size 2·3^{i−1}. Sizes
sum to Σᵢ 2·3^{i−1} = 3^a − 1. ✓. Apply Theorem 1 and Prop. 2(iii); orbit sizes
divide L, and the unit layer has size exactly L. ∎

Example spectra: m = 3: {1, ½, −½}. m = 9: {1} ∪ {½ζ : ζ⁶=1} ∪ {±½}.
m = 27: adds {½ζ : ζ¹⁸ = 1}. The eigenvalue ½ itself has multiplicity = number
of orbits = a. This is the same ⟨2⟩ mod 3^a arithmetic that appears in Hercher's
cycle bounds and in Tao's characteristic-function decay at 3-power moduli —
here it appears as the exact oscillation spectrum of the carry process.

## 6. Syracuse digit windows under Haar measure

One Syracuse/Terras step on the odd branch is "multiply by 3, add 1, divide by
2": base-2 long multiplication plus an increment. We now make exact the sense
in which k such steps decorrelate digit windows at rate 2^{−r} per bit of
separation. Work on ℤ₂ with the Terras map T(n) = n/2 (n even),
T(n) = (3n+1)/2 (n odd) — continuous on ℤ₂, parity = first digit.

**Lemma 6 (Terras coset structure; self-contained).** For j ≥ 1 and t ∈ ℤ₂,
T(n + 2^j t) = T(n) + 3^{ε(n)} 2^{j−1} t, where ε(n) = n mod 2. Consequently:
(i) the parity word w(n) = (n mod 2, Tn mod 2, …, T^{k−1}n mod 2) depends only
on n mod 2^k and gives a bijection ℤ/2^k → {0,1}^k; (ii) on the coset
C_w = n_w + 2^k ℤ₂ of a word w with a ones (n_w ∈ {0,…,2^k−1}),

  T^k(n_w + 2^k n′) = Q_w + 3^a n′,  Q_w := T^k(n_w) ∈ ℤ_{≥0}.

*Proof.* The displacement identity is immediate on each branch (n + 2^j t has
the parity of n since j ≥ 1). (ii) follows by iterating it: each of the k steps
halves the displacement's power of 2 and multiplies by 3 exactly on odd steps.
(i): dependence on n mod 2^k is (ii) read mod 2 at each step; injectivity: if
n ≢ n̂ (mod 2^k) write n − n̂ = 2^s u, u odd (unit of ℤ₂), s < k; if s = 0 the
first letters differ; else the displacement identity gives
v₂(T^i n − T^i n̂) = s − i for i ≤ s, so T^s n and T^s n̂ differ in parity: the
words differ within the first s+1 ≤ k letters. A bijection follows by counting.
∎

So: if n is Haar-random on ℤ₂ conditioned on C_w (an event of Haar measure
2^{−k}), then n′ is Haar on ℤ₂ — i.e. its digits b₀, b₁, … are i.i.d. fair bits
— and T^k(n) = m·n′ + Q with m = 3^a and the fixed constant Q = Q_w ≥ 0.

**The affine transducer.** Let q_j ∈ {0,1} be the binary digits of Q, ℓ := the
number of binary digits of Q (ℓ = 0 if Q = 0). Long multiplication with
increment computes the digits (d_j) of m n′ + Q by

  c₀ = 0,  s_j = m b_j + q_j + c_j,  d_j = s_j mod 2,  c_{j+1} = ⌊s_j/2⌋.

*Correctness:* by induction, m·(n′ mod 2^j) + (Q mod 2^j) = Σ_{i<j} d_i 2^i + 2^j c_j
(exact integer identity: adding the j-th column m b_j 2^j + q_j 2^j + 2^j c_j
= d_j 2^j + 2^{j+1} c_{j+1} is the recursion), so m n′ + Q ≡ Σ_{i<j} d_i 2^i
(mod 2^j) for all j: (d_j) is the 2-adic digit stream of T^k(n). *State space:*
by induction c_j ∈ {0,…,m}: c ≤ m ⟹ ⌊(m+1+c)/2⌋ ≤ m. For j ≥ ℓ (past the bits
of Q) the transition is time-homogeneous with kernel K̃ on {0,…,m}:
rows 0,…,m−1 are those of K = K_{m,2} (states ≤ m−1 cannot reach m since
s ≤ 2m−1), and from state m: b = 0 gives s = m, c′ = (m−1)/2; b = 1 gives
s = 2m, c′ = m. So, ordering state m last,

  K̃ = [ K   0 ]
      [ v   ½ ],   v = ½·δ_{(m−1)/2}.

**Proposition 7 (affine chain spectrum).** For odd m ≥ 3:
det(xI − K̃) = (x − ½)·det(xI − K), so spec(K̃) = spec(K) ∪ {½} and every
nontrivial eigenvalue again has modulus exactly ½. Moreover K̃ is
**diagonalizable**, its top eigenvalue 1 is simple with stationary law π =
uniform on {0,…,m−1} (mass 0 at the transient state m), and with
Π̃ := 𝟙 πᵀ and L = ord_m(2):

  K̃^{jL} = Π̃ + 2^{−jL}(I − Π̃)  exactly;  2^r(K̃^r − Π̃) is periodic in r, period L.

The only nontrivial point is diagonalizability at the doubled eigenvalue ½; it
rests on:

**Lemma 8 (orbit sum vanishing).** For every ⟨2⟩-orbit O ⊆ (ℤ/m)∖{0} (m odd):

  T_O := Σ_{x∈O} ω^{−2⁻¹x} / (1 − ω^{−x}) = 0.

*Proof.* All denominators are nonzero, and also 1 + ω^{−x} ≠ 0 (−1 is not an
m-th root of unity for odd m). Put S₁ := Σ_{x∈O} 1/(1−ω^{−x}) and
S₂ := Σ_{x∈O} 1/(1+ω^{−x}). Two evaluations of T_O:
(i) with z = ω^{−2⁻¹x} (so z² = ω^{−x}), each term is z/(1−z²) =
½[1/(1−z) − 1/(1+z)]; as x runs over O so does 2⁻¹x, hence T_O = ½(S₁ − S₂).
(ii) 1/(1+ω^{−y}) = (1−ω^{−y})/(1−ω^{−2y}); substituting y = 2⁻¹x (a bijection
of O) gives S₂ = Σ_{x∈O} (1 − ω^{−2⁻¹x})/(1−ω^{−x}) = S₁ − T_O.
Substituting (ii) into (i): T_O = ½ T_O, so T_O = 0. ∎

*Proof of Proposition 7.* The characteristic polynomial is the block-triangular
determinant. Simplicity of 1: the other roots have modulus ½. Stationarity of π
was checked by column sums (πK̃ = π since K is doubly stochastic and column m
of K̃ receives mass only from row m). Diagonalizability: for an eigenvalue
λ ≠ ½ of K with eigenvector u, the extension (u; β) with β = u((m−1)/2)/(2λ−1)
satisfies the last row ½u((m−1)/2) + ½β = λβ; since K is diagonalizable
(Theorem 1) this preserves all geometric multiplicities at λ ≠ ½. At λ = ½ the
algebraic multiplicity in K̃ is (#orbits) + 1. The ½-eigenspace of K is spanned
by the orbit vectors u_O := Σ_{x∈O} (1−ω^{−x})^{−1} χ_x (check:
K u_O = Σ_x (1−ω^{−x})^{−1} w_x χ_{2⁻¹x} = ½ Σ_x (1−ω^{−2⁻¹x})^{−1} χ_{2⁻¹x} = ½u_O).
Now evaluate at the entrance state: (m−1)/2 ≡ −2⁻¹ (mod m), so
u_O((m−1)/2) = Σ_{x∈O} ω^{−2⁻¹x}/(1−ω^{−x}) = T_O = 0 by Lemma 8. Hence each
(u_O; 0) satisfies the last row (½·0 + ½·0 = ½·0 ✓) and is a ½-eigenvector of
K̃; together with δ_m (column m of K̃ equals ½δ_m, so K̃δ_m = ½δ_m) this gives
(#orbits) + 1 independent eigenvectors: geometric = algebraic. So K̃ is
diagonalizable, K̃^r − Π̃ = Σ_{λ≠1} λ^r P_λ over its spectral projectors, and
since every nontrivial λ satisfies (2λ)^{L} = 1, the last two displays follow
(for jL both sides have every λ^{jL} = 2^{−jL}). ∎

Define D(m) := Σ_{λ∈spec(K̃)∖{1}} ‖P_λ‖_{∞→∞} < ∞ — an explicitly computable
constant (finite by Prop. 7) with ‖K̃^r − Π̃‖_{∞→∞} ≤ D(m)·2^{−r}.

**Corollary 9 (exact decorrelation of Syracuse digit windows under Haar).**
Fix a ≥ 1, m = 3^a, L = 2·3^{a−1}. Fix k and a parity word w ∈ {0,1}^k with a
ones; let n ~ Haar(ℤ₂ | C_w), and let (b_j) be the digits of n′ (equivalently,
digits k, k+1, … of n), (c_j) the carries, (d_j) the digits of T^k(n), and
ℓ = ℓ(w) the bit length of Q_w. Then for all t ≥ ℓ and r ≥ 0, all bounded f
measurable w.r.t. σ(b_j : j < t) — in particular any functional of the digit
window (d_j)_{j<t} — and all bounded g measurable w.r.t.
σ(c_{t+r}; b_j : j ≥ t+r) — in particular any functional of (d_j)_{j≥t+r}:

  |Cov(f, g)| ≤ 2·D(3^a) · 2^{−r} · ‖f‖_∞ ‖g‖_∞ ,

the rescaled profile r ↦ 2^r·Cov is governed by 2^r(K̃^r − Π̃), which is exactly
periodic in r with period L = 2·3^{a−1} — i.e. all correlation phases lie in
{2πj/ord₂(3^a)} — and at separations r ≡ 0 (mod L) the contraction is exact:
for any φ, ψ on the carry space, Cov(φ(c_t), ψ(c_{t+r})) = 2^{−r} Cov(φ(c_t), ψ(c_t)).
In particular every subdominant correlation modulus is exactly ½ per bit: the
2^{−r} rate can not be improved, and carries no slowly-varying prefactor other
than the stated constants.

*Proof.* d_j for j < t is a function of b_0,…,b_j (via the carries), so such f
qualify; d_j for j ≥ t+r is a function of c_{t+r}, b_{t+r},…,b_j and the fixed
bits of Q, so such g qualify. For t ≥ ℓ the carry transitions on [t, t+r) are
homogeneous with kernel K̃, so with h(y) := E[g | c_{t+r} = y]:
E[g | σ(b_j : j<t)] = (K̃^r h)(c_t) = π̃(h) + v(c_t), v := (K̃^r − Π̃)h. Constants
cancel in covariances: Cov(f,g) = Cov(f, v(c_t)), so |Cov| ≤ 2‖f‖_∞‖v‖_∞ ≤
2D(m)2^{−r}‖f‖_∞‖g‖_∞ — valid for the actual (non-stationary, inhomogeneously
started) carry process, since no assumption on the law of c_t was used. The
periodicity and exactness statements are Prop. 7 (the exactness argument is
Prop. 4(c) verbatim with K̃, again with no assumption on the law of c_t). ∎

Since ℤ₂ = ⨆_w C_w with each coset of measure 2^{−k}, Corollary 9 covers
Haar-almost-every n and every k: k-step Syracuse digit windows at bit
separation r decorrelate at exactly (½)^r with phase spectrum
(2π/2·3^{a−1})·ℤ, where a is the number of odd steps taken.

**Honest scope.** Everything in this section is a statement about Haar measure
on ℤ₂. The positive integers are a Haar-null subset; nothing here constrains
any individual Collatz orbit, and no individual-orbit statement (divergence,
cycles, Antihydra, s₂(3^n) lower bounds) is touched. What the corollary does
give: a rigorous, fully explicit finite-window surrogate for Syracuse digit
statistics with error bars 2^{−r} and computable oscillation phases — strictly
finer information than parity-level (Terras) equidistribution, which is the
marginal of the present statement at window size 1.

## 7. What remains open

1. **gcd(m, b) > 1.** Lemma 1 fails (b is not invertible mod m; the output
   digit is no longer conditionally uniform). DF's own example m = b (uniform
   after one step, spectrum {1, 0, …, 0}) shows genuinely different behavior:
   eigenvalue 0 appears. The mixed case presumably interpolates
   (nilpotent-times-monomial structure); not pursued here.
2. **Joint spectra of composed Syracuse transducers** (the "persistence
   conjecture" of Crack 4: spectra of k-fold letter-transducer compositions
   remaining inside {2^{−r}ζ : ζ^{ord₂(3^a)} = 1}) — not addressed here; the
   present note is the single-multiplication building block.
3. Whether Lemma 8 / semisimplicity of K̃ has a conceptual (representation-
   theoretic) home — it looks like a shadow of a general fact about
   g-circulants bordered by an absorbing digit state.

## 8. Verification

Scripts (both rerun today, all checks pass):

- `experiments/carries/verify_carries_spectrum.py` (numpy):
  - **A.** b = 2, m ∈ {3,5,7,9,11,13,15,21,27,33,81,243}: eigenvalue multiset of
    K_{m,2} vs. Theorem 1 (greedy matching) and det(zI − K) vs. the product
    formula at 20 random points on |z| = 2. Max eigenvalue-match error
    7.98e−15 (at m = 243); max det relative error 2.76e−13 (m = 243, degree-243
    polynomial); typical values ≤ 1e−15.

    | m | orbit sizes | eig err | det rel err |
    |---|---|---|---|
    | 3 | 2 | 1.3e−16 | 5.6e−16 |
    | 5 | 4 | 5.6e−16 | 6.0e−16 |
    | 7 | 3,3 | 4.0e−16 | 1.0e−15 |
    | 9 | 6,2 | 1.4e−15 | 1.1e−15 |
    | 11 | 10 | 8.3e−16 | 1.7e−15 |
    | 13 | 12 | 9.8e−16 | 2.4e−15 |
    | 15 | 4,4,4,2 | 8.3e−16 | 3.7e−15 |
    | 21 | 6,6,3,3,2 | 7.4e−16 | 3.4e−15 |
    | 27 | 18,6,2 | 1.2e−15 | 5.4e−15 |
    | 33 | 10,10,10,2 | 2.1e−15 | 6.3e−15 |
    | 81 | 54,18,6,2 | 2.1e−15 | 3.4e−14 |
    | 243 | 162,54,18,6,2 | 8.0e−15 | 2.8e−13 |

  - **B.** General base: DF's printed matrix (b = 10, m = 7) reproduced
    entry-for-entry from the digit definition; spectrum checks for
    (b, m) ∈ {(10,7), (3,5), (10,9), (4,7), (6,35), (3,8), (5,12)} — composite
    bases, even multipliers, orbit fixed points all covered; all pass at
    ≤ 1.6e−15 / 1.1e−14.
  - **C.** K^L = Π + b^{−L}(I−Π) for (2,3), (2,5), (2,9), (2,27), (2,15),
    (10,7), (3,8): deviation 0.0 (exact in floating point) except 8.3e−17 for
    (10,7). Also verified for the extended chain K̃, m ∈ {3, 9, 27}: deviation
    exactly 0.0.
  - **D.** Exact TV formula (Prop. 3) vs. matrix powers, (b,m) ∈
    {(2,7), (2,27), (10,7)}, r = 1..6: all agree to 1e−12 (printout matches the
    closed form digit-for-digit).
  - **E.** Extended chain: spec(K̃) = spec(K) ∪ {½} for m = 3, 9, and eigenvalue
    ½ is semisimple (numerical rank).

- `experiments/carries/verify_carries_exact.py` (sympy, exact — no floats):
  1. m ∈ {3,5,7,9,15}: charpoly(K_{m,2}) **equals** (x−1)∏_O(x^{|O|} − 2^{−|O|})
     as polynomials over ℚ. All True.
  2. m ∈ {3,5,9,15}: K^L = Π + 2^{−L}(I−Π) exactly over ℚ. All True.
  3. m ∈ {3,5,7,9}: charpoly(K̃) = (x−½)·charpoly(K) exactly, and eigenvalue ½
     of K̃ is semisimple (exact rank over ℚ: rank(K̃ − ½I) = (m+1) − (1 + #orbits)).
     All True.
  4. Lemma 8: T_O = 0 verified in exact cyclotomic arithmetic (numerator ≡ 0
     mod Φ_m) for every orbit, m ∈ {3,5,7,9,15}. All True.

## References

- P. Diaconis, J. Fulman, *Carries, shuffling, and an amazing matrix*,
  Amer. Math. Monthly 116 (2009); arXiv:0806.3583. §5.2 (multiplication
  carries: definition, doubly stochastic, g-circulant, K_aK_b = K_{ab},
  Prop. 5.1 upper bound, open remark on lower bounds/spectrum). Local copy:
  `papers/diaconis-fulman-carries-shuffling-0806.3583.pdf`.
- J. M. Holte, *Carries, combinatorics, and an amazing matrix*, Amer. Math.
  Monthly 104 (1997) 138–149 (addition carries; spectrum 1, 1/b, …, 1/b^{n−1}).
- P. J. Davis, *Circulant Matrices*, Wiley 1979, ch. 5 (g-circulants; DF's
  reference [13]).
- A. Izsak, *Carry propagation in multiplication by constants* (single
  multiplication, not the stationary chain), arXiv:0801.4040.
- R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30
  (1976) 241–252 (parity-vector bijection; re-proved self-contained in Lemma 6).
- J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math.
  Monthly 92 (1985) (survey; coset/parity formalism).
- Context and the original conjectured formula: `docs/CRACKS.md`, Crack 4
  (brief's numerics for m ∈ {3,5,7,9,11,15,27,81}, here extended and proved).
