# Wildcard bridges: Collatz-dynamics ↔ fields not yet in the program

2026-07-20. Deliverable of the re-widening pass. Goal: genuine *structural* bridges
from fields untouched by this program to the ×3/÷2 parity dynamics, the transfer
operator on ℤ₃, the −1 co-spine NO-GO, and cycles as 2^K−3^L points. Two bridges are
backed by fresh computations (`experiments/wildcard/`, results in `results.csv`); the
rest are honest reaches with a real theorem attached. gpt-5.6-sol pressure-tested
Bridges 1–2 and caught two over-claims, corrected below.

Calibration: **[PROVED]** / **[COMPUTED]** (verified numerically here) /
**[PROVABLE-LOOKING]** / **[SPECULATIVE]**.

---

## Bridge 1 — Open quantum systems: the transfer operator IS a quantum channel, and the −1 NO-GO is its peripheral spectrum. **[COMPUTED; WARM]**

Field: quantum information / open quantum systems (CPTP maps, peripheral spectrum,
decoherence). Not operator-algebra Cuntz (which is in-program) — this is the
finite-dimensional channel/Perron theory.

**The tool (real theorem).** (i) *Stinespring/Arveson:* a positive linear map with
commutative domain **or** codomain is automatically completely positive. The
annealed KL operator L acts on the commutative algebra C([3^k]); with its strictly
positive Perron eigenfunction h (guaranteed by Gaubert–Gunawardena, Thm 2.1 of
`adversarial-operator.md`), the Doob transform P(f)=ρ⁻¹h⁻¹L(hf) is a **unital CP
map — a genuine quantum channel** (here a stochastic matrix). (ii) *Evans–Høegh-Krohn
(JLMS 17, 1978):* the peripheral spectrum (|μ|=1) of an irreducible positive map is a
cyclic subgroup of U(1); primitivity ⇔ that group is trivial. For a **reducible**
map (deterministic functional graph) the peripheral eigenvalues are exactly the roots
of unity contributed by its cycles (Frobenius/Markov cyclic classes, Seneta).

**The bridge, sharpened by computation** (`channel_and_dolangrady.py`):
- The **odometer alone** (m↦4m) is a pure 3^{k−1}-cycle permutation → its peripheral
  spectrum is the *full* cyclic group of 3^{k−1} roots of unity (verified: 9, 27 at
  k=3,4). Maximally non-mixing.
- The **annealed channel at λ=2 is PRIMITIVE**: peripheral spectrum = {1} only, and
  the subdominant eigenvalue is exactly λ⁻²=¼, i.e. **spectral gap = ¾**, stable
  across k=3..6 [COMPUTED, not yet a uniform-in-k theorem — sol's caveat]. So the
  chords *destroy* the odometer's peripheral group and turn a non-mixing permutation
  into a fast-mixing channel. **The annealed dynamics has no obstruction.**
- The obstruction lives on the **adversarial (min) side**. The global min-operator is
  nonlinear (not a channel); but where the argmin is unique its Fréchet derivative is
  a deterministic 0/1 stochastic matrix — the argmin-**selection channel** — which is
  the opposite extreme: maximally *reducible*, spectrum {0,1}
  (`renormalization-at-minus-one.md` §6.1). Its eigenvalue-1 eigenspace is
  **peripheral**, hence *not contracted* — the marginal co-spine mode.
- The **−1 "charge"** is organized by the order-2 relabeling U: q↦2q on Prüfer
  offsets, swapping 1/3↔2/3 (ord(2 mod 3)=2). U has eigenvalues {+1 (symmetric mode
  a), −1 (antisymmetric mode b−a)} — verified: a −1 eigenvalue appears at every depth
  (`charge_and_geometry.py`). The pinned mode a sits in the trivial rep; the
  **undamped charge b−a sits in the sign rep**.

**Honest statement of the NO-GO (corrected).** A charged-Lyapunov certificate needs to
manufacture a spectral gap at the charge. It cannot, because the charge is a
**peripheral/marginal eigenvector** of the selection operator (Evans–Høegh-Krohn
/Frobenius: peripheral modes are permuted with |μ|=1, never strictly contracted).
The Z/2 relabeling does **not** by itself forbid damping (G-covariance only keeps
isotypic sectors invariant — a depolarizing channel contracts within a sector; sol's
correction, so "decoherence-free subspace" is *not* the operative theorem). What the
symmetry does is *label* which combination is protected: the sign-rep (b−a) is the
marginal one, the trivial-rep (a) is pinned. **Falsifiable prediction:** any working
charge-damping certificate must act asymmetrically across the U-swap (break the
sign-rep/trivial-rep decoupling) — a concrete constraint on certificate design.

First lemma to prove next: uniform-in-k primitivity + gap≥¾−o(1) of the annealed
channel (exact-arithmetic Perron bound), which would give annealed mixing rigorously.

---

## Bridge 2 — Ising / free-fermion integrability: the transfer matrix is NOT Onsager-solvable. **[COMPUTED; COLD but a genuine NO]**

Field: exactly solvable statistical mechanics (Ising transfer matrix, Onsager
algebra, free fermions).

**The tool (real theorem).** *Dolan–Grady (Phys. Rev. D 25, 1982, 1587; Davies,
J. Phys. A 23, 1990):* a Hamiltonian/transfer matrix built from two generators
A₀,A₁ is Onsager-integrable (free-fermion, closed-form spectrum) **iff** the
reciprocal triple-commutator relations [A₀,[A₀,[A₀,A₁]]]=β²[A₀,A₁] and
[A₁,[A₁,[A₁,A₀]]]=β²[A₁,A₀] hold.

**The bridge / computation** (`channel_and_dolangrady.py`). Natural split of the KL
transfer matrix: A₀ = odometer (kinetic) term λ⁻²·permutation, A₁ = chord (field)
terms. Best-fit residual of the DG relation (0 = integrable, 1 = maximally not):

  k=3: 0.994 / 0.992  k=4: 0.9995 / 0.999  k=5: 0.9999 / 0.9999  (β²→0)

**Verdict.** The natural kinetic/potential split does **not** realize the
Onsager/Dolan–Grady mechanism, and the failure *sharpens* with k. This is strong
evidence the operator is not free-fermion solvable — a structural reason the
λ∞-threshold has resisted closed form. **Honest caveat (sol):** this is not a
nonintegrability *theorem*; a different generator split, a Majorana/quadratic-fermion
closure, or a Yang–Baxter R-matrix could still exist. So "no closed form expected" is
heuristic, not proved. Next test: scan A₀=cos θ·odo + sin θ·chord splits for any θ
with DG residual → 0; a null result across θ would upgrade the evidence.

---

## Bridge 3 — Geometry of numbers: why lattice methods are *mis-signed* for cycles. **[COMPUTED + honest negative; MODERATE]**

Field: geometry of numbers (Minkowski, successive minima, Ehrhart/Barvinok,
flatness).

**Setup.** Shape-(K,L) cycle candidates = words b₀<…<b_{L−1}∈[0,K) with
W(b)=Σ 3^{L−1−i}2^{b_i} ≡ 0 (mod Λ), Λ=2^K−3^L; count C(K,L)=binom(K,L)≈2^{0.95K}
on near-convergents (`cycle-finite-places.md`).

**What geometry of numbers *does* give.** (i) *Covolume/Gaussian heuristic
(Minkowski):* when W is surjective mod Λ, {W≡0} is a coset of a covolume-Λ subgroup,
so the Gaussian heuristic predicts #points ≈ vol/covol = C/Λ ≈ 2^{−0.05K} — the whole
cycle-freeness numeric on a lattice footing rather than an equidistribution vibe (the
program's own verified densities N_p·p/C∈[0.968,1.000] are exactly this).
(ii) The (7,1) obstruction reproduced (`charge_and_geometry.py`): Λ=125=5³, W a pure
power of 2, so residue 0 is unhit → N_5=0. A single-place lattice-miss.

**The honest negative (the genuinely new structural point).** W is *exponential* in
b_i, so {b : W(b)≡0} is **not** a linear congruence: the b-simplex + divisibility is
**not** an Ehrhart/Barvinok lattice-point problem, so those exact-count tools do not
apply. Worse, the classical existence engine — the **flatness theorem** (Khinchin;
Banaszczyk): a lattice-point-free convex body has bounded lattice width — is
*existence*-directed (wide body ⇒ contains a point), whereas cycle-rarity is
*non*-existence-directed. **Geometry of numbers is mis-signed for Collatz cycles**,
which is a clean explanation of the program's finding that finite-place/geometric
attacks "collapse to Baker." The only correctly-signed lattice object is the rank-2
log-lattice ℤlog2+ℤlog3 whose height |2^K−3^L| *is* the archimedean Baker input.

---

## Bridge 4 — three shorter reaches (each with a theorem; SPECULATIVE)

- **Random matrix / free probability.** *Furstenberg (1963):* products of random
  matrices under strong irreducibility + noncompactness have a positive top Lyapunov
  exponent. Bridge: the accelerated map's affine branches are upper-triangular, so the
  1-D Lyapunov exponent is *degenerate* (just the diagonal average log(3/4)) — free
  probability adds nothing there. It becomes live for the **twisted transfer-matrix
  ensemble** {T_ξ} of the exp-sum S_{K,L}(ξ): the "square-root cancellation" (Q2 of
  `dynamical-hasse.md`) ⇔ a *uniform spectral gap* ρ(T_ξ)<1, and free multiplicative
  convolution (Benaych-Georges; Kargin) predicts the limiting singular-value law. First
  computation: empirical ESD of T_ξ vs a free-convolution prediction. TEMP: moderate.
- **Markov categories / categorical probability.** *Fritz (2020) Markov categories;
  Maslov dequantization.* The annealed operator is a morphism in the Kleisli category
  of the probability monad; the adversarial min-operator is the same diagram in the
  Kleisli category of the **possibility (tropical/Viterbi) monad**, and the λ-tower's
  β→∞ limit is the semiring homomorphism between them. Gives a clean functorial account
  of "annealed vs adversarial" — but it is formalism, not a theorem with teeth. TEMP:
  cold.
- **Quantum walks.** *Szegedy walk + spectral mapping (Segawa–Suzuki):* the walk's
  eigenphases are ±arccos(singular values of the underlying stochastic matrix). Unitarize
  the Doob channel of Bridge 1 → a quantum walk whose phase gap is √(gap) (quadratic
  speedup to the fixed state). The 2⊥3 incommensurability (log₂3 irrational) suggests
  the discriminant is quasi-periodic → possible Cantor spectrum (almost-Mathieu /
  Ten-Martini, Avila–Jitomirskaya 2009). TEMP: speculative, but a real famous theorem
  at the end of the road.

---

## Files & reproduction
- `experiments/wildcard/channel_and_dolangrady.py` — Bridge 1 peripheral spectra +
  Bridge 2 Dolan–Grady residuals.
- `experiments/wildcard/charge_and_geometry.py` — the −1 charge as a sign-rep mode +
  Bridge 3 covolume/(7,1)-obstruction check.
- `experiments/wildcard/results.csv` — key numbers.

## References
Stinespring, *Proc. AMS* 6 (1955); Arveson (commutative ⇒ CP). D. E. Evans, R.
Høegh-Krohn, *J. London Math. Soc.* 17 (1978) 345. E. Seneta, *Non-negative Matrices
and Markov Chains*. L. Dolan, M. Grady, *Phys. Rev. D* 25 (1982) 1587; B. Davies,
*J. Phys. A* 23 (1990) 2245. H. Furstenberg (1963). F. Benaych-Georges;
V. Kargin (free-probability matrix products). T. Fritz, *Adv. Math.* 370 (2020). E.
Segawa, A. Suzuki (quantum-walk spectral mapping). A. Avila, S. Jitomirskaya, *Ann.
Math.* 170 (2009) 303 (Ten Martini).
