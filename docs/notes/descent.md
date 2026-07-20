# Descent of equilibrium statements to arithmetic sections

2026-07-20. Companion to `docs/notes/carries-spectrum.md` (exact Haar-side window
laws). Question addressed: the Syracuse/Terras system on ℤ₂ is exactly solved
for Haar measure; the conjecture lives on the Haar-null section ℕ ⊂ ℤ₂. Which
Haar-a.e. / Haar-quantitative statements **descend** to ℕ, what structural
properties of ℕ support descent, and what is the minimal non-trivial descent
statement worth proving first?

**Calibration summary.**

- **Proved (here or assembled from the literature):** the Bit-Budget Dictionary
  (§2): every finite-2-adic-depth Haar statement descends to density-one integer
  statements *with exact error bars* — including the joint digit-window
  decorrelation of the carries note — and this is Terras-style counting, nothing
  more (honesty box §2.4). The Refresh Lemma (§2.5). The ±sign no-go (§3): no
  finite-level structural property of ℕ (Büchi definability, scalewise
  equidistribution, closure under 2x, 3x+1) can support descent of orbit-fate
  statements, because ℕ and −ℕ share all of them and provably differ in cycle
  structure.
- **Provable-looking:** the in-budget optimality of Korec's exponent (§2.6);
  window statistics of *primes* (§2.7); WD1-min at logarithmic density via Tao's
  renewal method (§5.2); the transfer-operator reformulation of Tao's
  Proposition 1.17 with exact small-modulus spectra (§6, target T1).
- **Conjectural:** WD1 (persistence of Bernoulli window statistics to the
  collapse horizon ≈ 4.82·log₂n, §5.2); WD2 (geometric mixing of Syracuse
  random variables at growing 3-adic modulus — Tao's "plausible, not pursued"
  exp(−cn), §5.3); WD2′ (fine-scale mixing of the full random affine map =
  Tao's named gate from logarithmic to natural density, §5.4).
- **Speculative:** zero-entropy exclusions for divergent parity sequences
  beyond eventual periodicity (§4.3); any use of ×2×3 measure rigidity on
  growing-height rationals (§4.2).

---

## 1. Setting: the solved ambient system and its arithmetic section

Terras map T(n) = n/2 (n even), (3n+1)/2 (n odd), continuous on ℤ₂. The parity
map Φ(x) = (x mod 2, Tx mod 2, T²x mod 2, …) is a homeomorphism ℤ₂ → {0,1}^ω
conjugating T to the one-sided shift and pushing Haar to Bernoulli(½,½)
(finite-level version: Lemma 6 of `carries-spectrum.md`, i.e. Terras 1976 /
Everett 1977; 2-adic version: Lagarias 1985 §2, Bernstein–Lagarias 1996). So
(ℤ₂, T, Haar) is *exactly solved*: Bernoulli, hence ergodic, mixing of all
orders; and by the carries note the solution is now *quantitatively exact at
the digit level*: k-step digit windows at bit-separation r decorrelate at
exactly 2^{−r}, with oscillation phases in (2π/ord_{3^a}(2))·ℤ and explicit
constants (Corollary 9 there).

The section: ℕ ⊂ ℤ₂, countable, dense, Haar-null. Its structural inventory —
the candidate "descent supports" named in the brief:

- **(S1) Büchi definability.** ℕ = {eventually-0 digit streams}: recognized by
  a nondeterministic Büchi automaton (guess the last 1); a Σ₂ Borel set. −ℕ =
  {eventually-1 streams}: same complexity. (Role assessed in §3: none, for
  descent.)
- **(S2) Perfect scalewise equidistribution.** #{n ≤ x : n ≡ a mod 2^D} =
  x·2^{−D} + O(1) for every a, D. Equivalently: the counting measure on [1,x]
  pushed to ℤ/2^D is uniform up to TV error ≤ 2^D/x. This is the strongest
  possible pseudorandomness at 2-adic depth ≤ log₂x, and it is *completely
  degenerate* beyond that depth (atoms).
- **(S3) Closure.** 2ℕ ⊂ ℕ, 3ℕ+1 ⊂ ℕ, T(ℕ) ⊆ ℕ; the backward tree of any
  integer stays in ℕ (source of the Krasikov–Lagarias x^{0.84} bound for the
  1-basin — pure backward counting).
- **(S4) Positive relative density at every dyadic scale**, and
  quasi-invariance of the *logarithmic* counting measure under n ↦ n/2, the
  only known workable surrogate for an invariant measure on ℕ (this is why Tao
  2019 and Kontorovich–Lagarias 2009 both live at logarithmic density).

**The bit-budget principle** (used throughout): one Terras step consumes
exactly one bit. The parity word of length k is a bijection with residues
mod 2^k, and every digit of T^k(n) up to position p is a function of
n mod 2^{k+p+1} (Lemma 6 of the carries note). An integer n ≤ x carries
log₂x usable bits; hence depth-D window functionals are "free" for
D ≤ (1−ε)log₂x and *undefined by counting* beyond.

---

## 2. Free descent: what transfers with no new mathematics (proved)

### 2.1 Finite-level descent lemma

**Lemma 2.1.** Let F: ℤ₂ → ℂ, |F| ≤ 1, be measurable at depth D (F(x) depends
only on x mod 2^D). Then for all x ≥ 1,

  | (1/x) Σ_{n≤x} F(n) − ∫_{ℤ₂} F dHaar | ≤ 2^D / x.

*Proof.* Haar at depth D is uniform on ℤ/2^D; each residue class meets [1,x]
in ⌊x/2^D⌋ or ⌈x/2^D⌉ integers. ∎

Trivial — but it is the entire content of "descent" below the budget line, and
it is sharp in both directions (no statement of depth > log₂x has any counting
meaning). Everything in §2 is an instance.

### 2.2 The descended carries theorem (the integer-side statement requested)

**Corollary 2.2 (integer form of exact window decorrelation).** Fix k ≥ 1, a
parity word w ∈ {0,1}^k with a ones, t ≥ ℓ(w), r ≥ 0, D′ ≥ 1, and set
D := k + t + r + D′ + 1. Let f be any functional of the binary digits of
T^k(n) in positions < t, and g any functional of the digits in positions
[t+r, t+r+D′), both bounded by 1. Then for x ≥ 2^{D+k}:

  Cov_{n ≤ x, n≡n_w mod 2^k}(f, g) = Cov_Haar(f, g) + O(2^{D+k}/x),
  and |Cov_Haar(f,g)| ≤ 2·D(3^a)·2^{−r},

with the exact rate, phase spectrum (2π/ord_{3^a}(2))·ℤ, and constant D(3^a)
of Corollary 9 of `carries-spectrum.md`. Unconditionally on the word:
for all n ≤ x jointly, the empirical two-window joint laws of the digit field

  F(k, t) := t-th binary digit of T^k(n)

match the exactly-computed Haar laws with TV error ≤ 2^{−r}·(2D(3^a)) + x^{−ε}
whenever the total depth k + t + r + D′ ≤ (1−ε)log₂x. ∎ (Lemma 2.1 + Cor. 9.)

### 2.3 What this adds beyond Terras

Terras 1976 / Everett 1977 give the *parity marginal*: exact equidistribution
of length-k parity words for n < 2^k. Corollary 2.2 gives the *full joint
window laws of the output digits along the orbit*, with the spectrally exact
decorrelation rate ½ per bit and computable oscillation phases — strictly finer
information (Terras is the window-size-1 marginal). Novel content: the sharp
constant, the phase group, the two-parameter field formulation.

### 2.4 Honesty box: is Corollary 2.2 "already provable by Terras-style counting"?

**Yes — definitionally.** Haar measure at depth D *is* the uniform distribution
on ℤ/2^D; the Haar statement at depth D *is* a statement about all integers
below 2^D. Descent through Lemma 2.1 adds no mathematics: the entire novelty
of Corollary 2.2 resides in the finite-level spectral theorem already proved in
`carries-spectrum.md`, not in the transfer. There is no intermediate regime
where the Haar theory says something at finite depth that counting does not:
**for this system, "Haar-quantitative at depth D" and "density-statement for
integers ≤ 2^D" are the same category of assertion.** The interesting notion
of descent therefore begins strictly past the budget line — §5.

Two further free consequences worth recording (both counting + Cor. 9):

- **Effective Birkhoff in the free zone.** The depth-D window at orbit time j
  is exactly the parity-word block [j, j+D) (Lemma 6(i)), so the window process
  along the orbit is a sliding D-block of an i.i.d. sequence; Chernoff gives:
  for density-one n, the empirical depth-D window distribution over the first
  J = (1−ε)log₂n steps is within O(√(2^D·log J / J)) of uniform. No ergodic
  theorem is invoked — and none could be (§4.4): the quantitative decay *is*
  the substitute.
- **DFA-certificate pressure.** Any automaton computing a window functional to
  accuracy better than the decorrelation floor must resolve carry states at
  scale 2^{−r}; this is the state-count lower-bound mechanism flagged in
  CRACKS Crack 4, now with descended (integer-side) meaning in the free zone.

### 2.5 The Refresh Lemma (exact, and the skeleton of every renewal argument)

**Lemma 2.5.** Let n be uniform on [1, 2^{k+D}]. Then conditionally on the
parity word w(n) ∈ {0,1}^k — *any* word, hence also conditionally on any
word-measurable event such as {σ(n) = k} (first descent at time k) —
T^k(n) mod 2^D is uniform on ℤ/2^D up to TV error O(2^{−D}) from interval
edges; exactly uniform if n is uniform on the full coset intersected with
[1, 2^{k+D}].

*Proof.* T^k(n_w + 2^k n′) = Q_w + 3^a n′ (Lemma 6(ii) of the carries note);
n′ is uniform mod 2^D; 3^a is a unit mod 2^D. ∎

So the 2-adic residue data *refreshes exactly* at each first-passage renewal;
what does **not** refresh is the coupling between the word and the Archimedean
size of T^k(n) (the size is a deterministic function of (n, w)). All difficulty
of descent past the budget concentrates in that coupling — made precise in §5.

### 2.6 The budget wall is exactly Korec's exponent

**Proposition 2.6.** Let θ = log₄3 = 0.79248…
(i) (Korec 1994) For every ε > 0, density-one n have min_k T^k(n) ≤ n^{θ+ε}.
(ii) (matching in-budget lower bound; elementary, apparently folklore — the
stochastic-model analogues are in Lagarias–Weiss 1992 and Borovkov–Pfeifer
2000) For every ε > 0, density-one n satisfy

  min_{k ≤ log₂n} T^k(n) ≥ n^{θ−ε}.

*Proof sketch of (ii).* T^k(n) = (3^{a_k}n + β_k)/2^k ≥ 3^{a_k}2^{−k}n with
β_k ≥ 0. For uniform n ≤ x the parity word of length log₂n is uniform;
Chernoff + a union bound over k give a_k ≥ k/2 − √k·ω(n) simultaneously for
all k ≤ log₂n, ω(n) = 2√(log log n), off a vanishing-density set. Then
log₂T^k(n) ≥ log₂n − k(1 − log₂3/2) − o(log n), minimized at k = log₂n with
value θ·log₂n − o(log n). ∎

**Reading.** Korec's density-one result is *exactly* the optimum of the free
zone: the deepest point a depth-≤log₂n counting statement can certify is
n^{log₄3+o(1)}. Any density-one bound below n^{θ} (Tao 2019 reaches n^ε and
below) is *genuine* descent — mathematics beyond counting. Conversely, no
orbit-time k > D is even measurable at depth D, so the free zone cannot
mention the orbit past one budget of steps at all.

### 2.7 Free descent to thinner sections (the honest Green–Tao-shaped product)

Lemma 2.1 quantifies over the section only through (S2). Hence it applies
verbatim to any S ⊆ ℕ with known equidistribution in residues mod 2^D:

**Corollary 2.7 (window statistics of primes; provable today).** For every A,
uniformly for D ≤ A log log x, the depth-D Collatz window statistics of primes
p ≤ x match Haar with error o(1) (Siegel–Walfisz for modulus 2^D); under GRH
the range extends to D ≤ (½−ε)log₂x. In particular parity-word
equidistribution ("Terras along primes") holds at these depths. Similar
statements hold for Beatty sequences, Piatetski-Shapiro sequences, sums of two
squares, etc., with each set's known level of distribution in dyadic moduli.

This is where transference machinery points, honestly deployed: not deeper
into the orbit, but across thinner sections; the currency is classical
equidistribution in progressions, nothing dynamical.

---

## 3. No-go: finite-level structure cannot support descent of orbit fates (proved)

**Proposition 3.1 (±sign no-go).** The map ι(x) = −x is a Haar-preserving,
Büchi-definable homeomorphism of ℤ₂ commuting with x ↦ 2x and conjugating T to
the Terras form of the 3x−1 map. The sections ℕ and −ℕ therefore have
*identical* finite-level inventories: both dense, Haar-null, Büchi-recognizable
(S1), perfectly scalewise equidistributed (S2), T-forward-closed with the same
closure algebra (S3), positive log-density at all scales (S4); and the ambient
Haar theories are isomorphic (the carries analysis of `carries-spectrum.md`
applies verbatim to 3x−1: same kernels K̃, same spectra). Yet:

- on ℕ, exactly one T-cycle exists with minimum ≤ 2^71 (the {1,2} cycle;
  Barina's verification);
- on −ℕ, at least three T-cycles exist below 100 in absolute value:
  {−1}, {−5,−7,−10}, and the 11-cycle through −17.

Hence **no meta-principle of the form "[ambient system exactly solved] +
[(S1)–(S4)-type properties of the section] ⟹ [orbit-fate statement]" is
valid**: any such principle would be ι-equivariant and assign 3x+1 and 3x−1
the same cycle structure. ∎

**Sharper conditional contrast.** The 5x+1 Terras map has the *same* solved
ambient theory (conjugate to the same Bernoulli shift via its parity map, same
(S1)–(S4) for ℕ), yet conjecturally (and empirically: repo census, 99.94%)
almost every integer orbit diverges, while 3x+1 orbits conjecturally all
converge. Even the *direction* of the a.e. integer fate is invisible to the
solved 2-adic layer. What breaks the symmetry is the **Archimedean cocycle**
log|T(x)|/|x| — a function of the multiplier through |·|_∞, not through any
finite 2-adic window. (The undecidability ceiling — Conway 1972, Kurtz–Simon
2007 — says the same thing uniformly: no effective descent meta-theorem can
cover all such maps.)

**Consequence for the program.** Descent past the budget line is necessarily a
statement *coupling* 2-adic window data to Archimedean size. (S1) supports no
descent (both signs have it); its real role is on the disproof side —
certificate exclusions (two-bases note, Mahler note). (S2) supports exactly
the free zone. (S3)–(S4) supply the renewal skeleton and the correct (log)
density — the raw material of §5.

Two small facts sharpening "divergence is 2-adically atypical forever," both
elementary; proofs included for self-containedness (folklore; cf. Lagarias
1985 §2):

**Lemma 3.2.** If the T-orbit of n ∈ ℕ diverges, then liminf_k a_k/k ≥
log2/log3 = 0.6309…, where a_k counts odd steps among the first k. *Proof.*
T^k(n) = 3^{a_k}2^{−k}n·∏_{odd steps i}(1+1/(3x_i)); divergence sends the
odd iterates x_i → ∞, so the product is e^{o(k)}, forcing
a_k log3 − k log2 ≥ −log n − o(k). ∎ So a divergent orbit's empirical parity
measure stays bounded away from the Haar value ½ for all time: **divergent
points are permanently non-generic** for (ℤ₂, T, Haar).

**Lemma 3.3.** No divergent integer orbit has an eventually periodic parity
sequence. *Proof.* If the parity word is eventually periodic with period p and
a odd letters per period, the orbit tail satisfies y_{j+1} = (3^a y_j + c)/2^p;
2-adically |y_j − y*|₂ = 2^{pj}|y_0 − y*|₂ for the rational fixed point
y* = c/(2^p−3^a), which exits ℤ₂ unless y_0 = y*; so the tail is exactly the
cycle through y*, an integer cycle — contradicting divergence. ∎
(The converse — every rational in ℤ₂ has eventually periodic parity — is
Lagarias's Periodicity Conjecture Φ(ℚ∩ℤ₂) = ℚ∩ℤ₂, *open* and stronger than
"no divergent orbits".)

---

## 4. Theory hunt: the commissioned families, one verdict each

### 4.1 Transference: Green–Tao, dense models (Tao–Ziegler, RTTV, Gowers), relative Szemerédi (Conlon–Fox–Zhao)

**What they are.** Green–Tao 2008: a set of positive relative density inside a
*pseudorandom majorant* inherits Szemerédi-type conclusions. The dense model
theorem (Tao–Ziegler 2008; Reingold–Trevisan–Tulsiani–Vadhan 2008; Gowers
2010): if ν is a measure indistinguishable from uniform by a test family 𝔉,
then any A of positive density relative to ν has a *dense model* A′
indistinguishable from A by 𝔉. Conlon–Fox–Zhao 2015: relative Szemerédi under
a linear-forms condition alone.

**Verdict for descent.** The direction of transference fits, the regime does
not — and this is illuminating rather than disappointing. Take 𝔉 = 𝔉_D =
depth-D clopen functionals. Then the counting measure on [1,x] is a *perfect
dense model of Haar* for 𝔉_D whenever D ≤ (1−ε)log₂x (indistinguishability
error 2^D/x): Lemma 2.1 is a degenerate dense-model theorem, and the entire
free zone of §2 is its output. Past the budget the framework locates the exact
failure: a measure on ≤ x atoms cannot be 𝔉_D-indistinguishable from Haar once
2^D ≫ x (a single cylinder of Haar mass 2^{−D} carries counting mass 0 or
≥ 1/x). **The pseudorandomness hypothesis is not a tool that might be clever
enough; it is provably equivalent to the budget constraint.** The genuinely
available Green–Tao-shaped theorem is Corollary 2.7 (thin sections via their
level of distribution), which we mark provable-today.

### 4.2 ×2×3 rigidity: Furstenberg, Rudolph–Johnson, Host, Lindenstrauss, Hochman–Shmerkin, BLMV

**What they are, precisely, for integer points.** Furstenberg 1967: for
*irrational* α, {2^m 3^n α mod 1} is dense (topological; equidistribution open).
Rudolph 1990 / Johnson 1992: an ergodic measure on the circle invariant under
×2 and ×3 with positive entropy is Lebesgue. Host 1995: if μ is ×p-invariant,
ergodic, of positive entropy, gcd(q,p)=1, then μ-a.e. x is *normal in base q*
— the model "equilibrium ⟹ pointwise for a.e. point of a structured measure"
theorem; extended by Lindenstrauss 2001 (p-adic foliation) and in full
multiplicative-independence generality by Hochman–Shmerkin 2012.
Bourgain–Lindenstrauss–Michel–Venkatesh 2009: effective versions, with
iterated-logarithmic rates under Diophantine conditions.

**For orbits of integer points the answer is: nothing, structurally.** For
x ∈ ℤ the orbit {2^m 3^n x mod 1} is {0}; for rationals it is finite and
periodic — these are exactly the zero-entropy atomic invariant measures that
every theorem above excludes by hypothesis. Since every positive-entropy
invariant μ is non-atomic, μ(ℕ) = 0: **the rigidity family cannot see the
section ℕ even in principle.** The Collatz-relevant avatar — equidistribution
of rationals of *growing height* (e.g. the cycle-equation fractions
W(v)/(2^K−3^L), or 3-smooth orbits mod growing moduli) — falls outside the
family and lands in exponential sums (CRACKS Crack 3). Note the finite-modulus
sanity check: at the Collatz-relevant moduli 3^n the plain orbit
equidistribution question is *trivial* (2 is a primitive root mod 3^n, the
⟨2⟩-orbit is the whole unit group; Bourgain–Glibichuk–Konyagin-type subgroup
bounds are not even needed); the difficulty in §5 is entirely in the *weighted*
sums along that orbit. What the family does export: (i) the worldview — ×2×3
disjointness as the source of hardness (our two-bases/Cobham and Mahler notes
are its automata-theoretic and functional-equation shadows); (ii) Host's
theorem as the *shape* to aim for: a pointwise theorem on a rigid class of
reference measures. The only reference measure available on ℕ is logarithmic
counting (S4) — and the Host-analogue for it is precisely the open WD1.

### 4.3 Sarnak program: the parity sequence as a "deterministic sequence"

**What it is.** Sarnak 2011: Möbius is conjecturally orthogonal to every
sequence sampled from a zero-topological-entropy system; proved in many cases;
logarithmically-averaged versions from Matomäki–Radziwiłł 2016, Tao's entropy
decrement, Frantzikinakis–Host 2018 (log-Sarnak for systems with countably
many ergodic invariant measures).

**Verdict.** No Sarnak-program tool applies to Collatz parity sequences, for
three structural reasons worth recording. (i) The family of all integer parity
sequences generates the *full shift* (Terras surjectivity onto cylinders):
collectively they are maximally non-deterministic — entropy log 2, the opposite
of Sarnak's hypothesis. (ii) The tools bound correlations of a deterministic
sequence *against multiplicative randomness* (Möbius); the parity sequence of
an integer orbit is neither multiplicative nor paired with any μ-like partner
here. (iii) The one transferable device — logarithmic averaging to couple
scales (entropy decrement) — has already been cashed in this subject: it is,
in spirit, Tao 2019's use of logarithmic density. What survives as a question
is a *Sarnak-style complexity ladder for a single hypothetical divergent
orbit*: its parity sequence is aperiodic (Lemma 3.3) and ballistic
(Lemma 3.2, density ≥ 0.6309 > ½); rung 2 would be "not Sturmian", rung 3 "not
k-automatic / morphic" — zero-entropy exclusions that would complement the
set-level certificate exclusions of the two-bases and Mahler notes.
[SPECULATIVE; plausibly attackable for automatic sequences via the 3-adic
Mahler machinery of `mahler-cartier-lemma0.md`, since an automatic parity
sequence makes the orbit generating series a Mahler-like object.]

### 4.4 Bourgain: pointwise ergodic theorems along arithmetic sets; return times; the {2^n} question

**What they are.** Bourgain 1988–89 (Publ. IHES 69): pointwise ergodic theorems
in L^p (p>1) along squares, polynomials, primes — hard Fourier analysis on ℤ
(major/minor arcs, maximal-function transference); appendix with Furstenberg–
Katznelson–Ornstein: the return times theorem (orbit-sampled universal
weights). Negative side: Bourgain's entropy criterion (Israel J. Math 1988)
and Akcoglu–Bellow–del Junco–Jones–Losert–Reinhold-Larsson–Wierdl 1996:
averages along *lacunary* sequences — in particular along {2^j} — are **strong
sweeping out**: a.e. convergence fails as badly as possible.

**What the {2^n} machinery actually gives here.** Three answers.
(i) *Directly: nothing for ℕ.* All conclusions are μ-a.e. for the invariant μ
of an abstract system; on (ℤ₂,T,Haar) they produce Haar-a.e. statements, which
are ℕ-blind (ℕ is null), and there is no invariant measure on ℕ to run them
on (the log-counting measure is only quasi-invariant under the renewal — §5).
(ii) *Negatively and usefully:* the strong-sweeping-out theorems are a sharp
warning that "sample the orbit/digit statistics along the scales 2^k" is
precisely the geometry where *soft* pointwise ergodic theory fails; any
along-2^k-scales statement must be powered by summable quantitative
decorrelation. We possess it exactly (rate ½ per bit): effective
Borel–Cantelli/Chebyshev replaces ergodic maximal inequalities throughout the
free zone (§2.4), and that is not a convenience but a necessity.
(iii) *As a template:* Bourgain's Fourier-side proof architecture (weighted
exponential sums over arithmetically structured index sets, ℓ²-transference)
is the natural proof shape for WD2 below — weighted sums along the ⟨2⟩-orbit
of a frequency mod 3^n with geometric weights. The return times theorem is
the right *shape* for "orbit-sampled statistics of a second system", but again
requires an invariant measure on the sampling side; its role here is
inspirational only.

---

## 5. The descent conjectures

### 5.1 The two-parameter digit field and what is at stake

Let F(k,t) = t-th binary digit of T^k(n). Under Haar, the carries note computes
the full joint law of F over finite windows exactly (decay ½ per bit of
t-separation; k-direction handled by the word/window dictionary). The free
zone (§2) descends this to density-one integer statements on
{(k,t): k+t ≤ (1−ε)log₂n}. Conjecturally, orbits collapse at the horizon

  J*(n) = log n / ((1/2)log(4/3)) = (6.952…)·ln n = (4.8188…)·log₂n

(Lagarias–Weiss constant), after which F is trivial (cycle). The descent gap is
the strip

  log₂n < k < (1−ε)·J*(n),

where the orbit is conjecturally alive and Bernoulli-looking but the bit budget
is spent. Nothing at density one is known there beyond Tao 2019.

### 5.2 WD1: persistence of window statistics to the collapse horizon

**Conjecture WD1.** For every fixed depth D and ε > 0, for logarithmic-density-
one n: uniformly in J ≤ (1−ε)J*(n),

  d_TV( (1/J)Σ_{j<J} δ_{T^j(n) mod 2^D} , Unif(ℤ/2^D) ) = o(1),

and more generally the empirical joint law of the digit field F on windows of
depth D along the first J steps matches the exact Haar law of
`carries-spectrum.md` to o(1). Equivalent packaging: the orbit of n is
"finite-window generic" for Haar until it collapses.

**Status and honest placement.**
- For J ≤ (1−ε)log₂n: theorem (free zone, §2). Not a conjecture.
- **WD1-min** (minimal nontrivial instance): *there exists δ > 0 such that for
  logarithmic-density-one n, the parity of T^{⌈(1+δ)log₂n⌉}(n) is 0 with
  frequency ½+o(1).* Even this single just-past-budget bit is not in the
  literature. We assess it **provable-looking** by Tao's renewal method: his
  first-passage analysis re-randomizes after each descent below a threshold,
  and the Refresh Lemma 2.5 supplies the exact 2-adic component; what must be
  imported from Tao 2019 is control of the size/word coupling at logarithmic
  density (his Propositions 1.9–1.14 machinery). Extracting WD1-min as a
  standalone corollary of that machinery is a well-defined exercise with real
  expository value — it would be the first explicitly stated *past-budget
  window* theorem.
- Full WD1 at logarithmic density: plausibly within a strengthened Tao
  framework but requires propagating window laws (not just minima) through
  the renewal; open. At *natural* density: gated by WD2′ below.
- Consequences of WD1: total stopping time ∼ 6.952 ln n for log-density-one n
  (currently open; Lagarias–Weiss prediction), Korec-type bounds with any
  exponent > 0, and the full "Bernoulli until collapse" picture.

### 5.3 WD2: the quantitative kernel — geometric mixing at growing 3-adic modulus

Where does the difficulty concentrate after the refresh? Conditionally on the
parity word w (a odd steps among k), T^k(n) = Q_w + 3^a n′: the residue mod 2^D
refreshes exactly (Lemma 2.5), while the residue mod 3^m is *deterministic
given the word*: it is carried entirely by Q_w. Quantitative equidistribution
of Q_w mod 3^m under (near-)uniform words is exactly Tao's object:

- **Tao, Proposition 1.17** (verified against the local PDF): for ξ ∈ ℤ/3^nℤ
  not divisible by 3, |E e^{−2πiξ·Syrac(ℤ/3^n)/3^n}| ≪_A n^{−A}, uniformly in
  n, ξ. His Remark 1.15: the entropy heuristic predicts exp(−cm); end of his
  §1: improvement "perhaps to as far as O(exp(−cn))" is "possible … we will
  not need or pursue such a bound here". His reduction (his (6.1)) consumes
  this at scales 0.9n ≤ m ≤ n.

**Conjecture WD2 (geometric Syracuse mixing).** There is c > 0 with
|E e_{3^n}(−ξ·Syrac(ℤ/3^n))| ≤ C·e^{−cn} for all n and all 3∤ξ.

**Exact relation to our carries theorem — the sharp reframing.**
`carries-spectrum.md` proves the *fixed-modulus* analogue exactly: for fixed
3^a, the carry/window chain has every subdominant eigenvalue of modulus
exactly ½ — geometric mixing with the best possible constant and computed
phases. Tao's Proposition 1.17 is the *growing-modulus* statement (modulus 3^n
after n odd steps) with superpolynomial-only decay. The descent frontier is
literally "spectral persistence as the modulus grows with the step count":

  fixed 3^a: exact gap ½ (proved) → 3^{εn}: ??? → 3^{0.9n..n}: n^{−A} (Tao).

Structurally the two objects share one skeleton, and this is where our method
has purchase: both are weighted sums along the orbit of the monomial
permutation σ: ξ ↦ 2^{−1}ξ on ℤ/3^n (2 is a primitive root mod 3^n, so the
orbit of any unit is the full unit group). In the carries chain the weights
are the w_x of Lemma 2 (carries note), whose orbit product telescopes *exactly*
to 2^{−|O|} — modulus-independent gap. In the Syracuse characteristic function
the conditioning-on-a₁ recursion makes the frequency perform a *drifted*
monomial walk ξ ↦ 2^{−a}(ξ + drift), with geometric weights whose modulus
approaches 1 exactly when the orbit visits frequencies with small 3-adic
"height" — Tao's "wasted digits". **WD2 is a spectral-gap statement for a
drifted version of the operator we diagonalized exactly.** The obstruction to
exp(−cn) is quantifying how long the ⟨2⟩-orbit of ξ can linger near the
small-height set — an exponential-sum/Diophantine input (kinship with Crack 3
and with Stewart's s₂(3^n) ≫ log n/log log n wall, which is the deterministic
shadow of the same phenomenon). Risk: real; this is why WD2 is conjectural,
not provable-looking.

### 5.4 WD2′: the named gate from logarithmic to natural density

**Tao, Remark 1.16** (verbatim content, verified locally): to upgrade
logarithmic density to natural density in his results, "it seems necessary" to
strengthen Proposition 1.14 to fine-scale mixing of the **entire random affine
map** Aff_{Geom(2)ⁿ} (multiplier and offset jointly), not just the offset; he
adds that this "looks plausibly attainable from the methods in this paper".

**Conjecture WD2′.** Fine-scale joint mixing of (a_{[1,n]}, F_n(ā) mod 3^m) —
equivalently of the random affine map — at scales m ≍ n, with any rate
summable enough to run his §5 iteration at natural density.

WD2′ is, in our assessment, **the cleanest open "descent conjecture" in the
area with a certified payoff**: it is the precise missing lemma, named by the
strongest existing descent theorem, whose proof would convert logarithmic-
density conclusions (including WD1 once extracted) to natural-density ones.
Our exact-spectrum toolkit applies to it in the same way as to WD2 (the
multiplier data a_{[1,n]} is word data; the offset is the drifted walk).

---

## 6. Minimal non-trivial descent statement worth proving first

Ordered recommendation; effort estimates assume the current toolkit.

**T0 (days; assembly; Lean-friendly).** Write up the §2–§3 package as a short
paper/formalization target: Lemma 2.1, Corollary 2.2, Refresh Lemma 2.5,
Proposition 2.6(ii), Proposition 3.1, Lemmas 3.2–3.3, Corollary 2.7 (primes).
Value: pins the free zone and the wall *as theorems*, gives the program its
"what descent means" reference, and produces two publishable morsels (the
descended window laws; Terras-along-primes). Everything here is proved or
routine.

**T1 (weeks; the recommended first real target).** *Transfer-operator
reformulation of Tao's Proposition 1.17 with exact small-modulus spectra.*
Formulate the characteristic function E e_{3^n}(−ξ Syrac) as an n-step product
of a drifted monomial operator on frequency space (the σ-orbit structure of
`carries-spectrum.md` Lemma 2 plus a drift), then: (a) recompute the fixed-
modulus case and check it reproduces the exact gap ½ (consistency test — our
Corollary 9 is the m fixed, n → ∞ case); (b) compute exact spectra/decay for
n ≤ 12–15 by dynamic programming over ℤ/3^n (state space ≤ 14M at n = 15;
32-core feasible), fit the true decay rate of sup_{3∤ξ}|char fn|, and decide
empirically between n^{−A}-type and e^{−cn}-type behavior with explicit c;
(c) prove exp(−c·m) decay for the oscillation at fixed scale m uniformly in
n (the "m = O(1), n → ∞" strip — plausibly already implicit in our Prop. 7 /
Cor. 9 via the K̃-chain, i.e. provable-looking). Deliverable: a "drifted
carries chain" note that either locates the exact obstruction to WD2 or
produces the first explicit-constant strip of it. This is the minimal
statement that is (i) not counting, (ii) not already in Tao, (iii) squarely on
the WD2/WD2′ critical path, and (iv) matched to our proved machinery.

**T2 (weeks–months; extraction).** WD1-min at logarithmic density from Tao's
renewal machinery + Refresh Lemma (§5.2). Medium risk, high expository value:
the first stated past-budget window theorem.

**T3 (months; real risk; the prize).** WD2′ (affine-map mixing) and/or WD2
(geometric decay). Payoff: natural-density descent — the upgrade Tao names —
and effective constants throughout the strongest known almost-all result.

---

## 7. Structural-properties audit (answering the brief directly)

| Property of ℕ | Supports descent? | Precise role |
|---|---|---|
| (S1) Büchi definability | **No** (Prop. 3.1: −ℕ has it too) | Disproof side only: certificate exclusions (two-bases, Mahler notes) |
| (S2) scalewise equidistribution | **Yes — and only the free zone** | *Is* Lemma 2.1; equivalent to budget-limited pseudorandomness (§4.1) |
| (S3) closure under 2x, 3x+1, T | Partially | Backward-tree counting (Krasikov–Lagarias x^{0.84}); renewal skeleton for WD1 |
| (S4) positive log-density at 2^k-scales | **Yes — the correct density** | Log-counting is the unique quasi-invariant reference measure; why Tao/KL09 statements are logarithmic; natural density is gated by WD2′ |

**Sharpest single finding.** Descent splits cleanly at the bit-budget line
k = log₂n. Below it, descent is definitionally free and our exact Haar window
laws become integer theorems with exact constants (strictly finer than Terras,
but counting-provable — stated honestly). Above it, no finite-level property
of ℕ can help (±sign no-go), the known crossing (Tao 2019) pays for the
Archimedean coupling with mixing at the *other* prime, and the fixed-modulus
case of exactly that mixing is what `carries-spectrum.md` solved with gap
exactly ½. The frontier is spectral persistence under growing 3-adic modulus
(WD2/WD2′) — Tao's own named gate to natural density — and T1 above is its
minimal attackable instance.

---

## References (local copies in `papers/` where noted)

Ambient theory and counting regime:
- R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30
  (1976). `papers/terras-1976-stopping-time.pdf`
- C. J. Everett, *Iteration of the number-theoretic function f(2n)=n,
  f(2n+1)=3n+2*, Adv. Math. 25 (1977).
- J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math.
  Monthly 92 (1985). (Parity/coset formalism; Periodicity Conjecture.)
- D. J. Bernstein, J. C. Lagarias, *The 3x+1 conjugacy map*, Canad. J. Math 48
  (1996). https://cr.yp.to/papers/3x1conjmap-19960215-retypeset20220326.pdf
- I. Korec, *A density estimate for the 3x+1 problem*, Math. Slovaca 44 (1994).
  `papers/korec-1994-density-estimate-3x1.pdf`
- J. C. Lagarias, A. Weiss, *The 3x+1 problem: two stochastic models*, Ann.
  Appl. Probab. 2 (1992).
- A. Borovkov, D. Pfeifer, *Estimates for the Syracuse problem via a
  probabilistic model*, Theory Probab. Appl. 45 (2000).
- I. Krasikov, J. C. Lagarias, *Bounds for the 3x+1 problem using difference
  inequalities*, Acta Arith. 109 (2003). arXiv:math/0205002
- A. Kontorovich, J. C. Lagarias, *Stochastic models for the 3x+1 and 5x+1
  problems*, 2009. `papers/kontorovich-lagarias-2009-stochastic-models.pdf`
- T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*,
  Forum Math. Pi 10 (2022); arXiv:1909.03562. Props. 1.14, 1.17; Remarks
  1.15–1.18; (6.1). `papers/tao-2019-almost-all-collatz-orbits.pdf`

Transference / dense models:
- B. Green, T. Tao, *The primes contain arbitrarily long arithmetic
  progressions*, Ann. of Math. 167 (2008). `papers/green-tao-2008-primes-long-aps.pdf`
- T. Tao, T. Ziegler, *The primes contain arbitrarily long polynomial
  progressions*, Acta Math. 201 (2008). (Dense model theorem.)
- O. Reingold, L. Trevisan, M. Tulsiani, S. Vadhan, *Dense subsets of
  pseudorandom sets*, FOCS 2008. `papers/rttv-2008-dense-subsets-pseudorandom.pdf`
- W. T. Gowers, *Decompositions, approximate structure, transference, and the
  Hahn–Banach theorem*, Bull. LMS 42 (2010).
- D. Conlon, J. Fox, Y. Zhao, *A relative Szemerédi theorem*, GAFA 25 (2015).
  `papers/conlon-fox-zhao-2015-relative-szemeredi.pdf`

×2×3 rigidity:
- H. Furstenberg, *Disjointness in ergodic theory…*, Math. Systems Theory 1
  (1967).
- D. Rudolph, *×2 and ×3 invariant measures and entropy*, ETDS 10 (1990);
  A. Johnson, Israel J. Math. 77 (1992).
- B. Host, *Nombres normaux, entropie, translations*, Israel J. Math. 91
  (1995).
- E. Lindenstrauss, *p-adic foliation and equidistribution*, Israel J. Math.
  122 (2001).
- M. Hochman, P. Shmerkin, *Local entropy averages and projections of fractal
  measures*, Ann. of Math. 175 (2012).
  `papers/hochman-shmerkin-2012-local-entropy-averages.pdf`
- J. Bourgain, E. Lindenstrauss, P. Michel, A. Venkatesh, *Some effective
  results for ×a×b*, ETDS 29 (2009), doi:10.1017/S0143385708000898.
- C. L. Stewart, *On the representation of an integer in two different bases*,
  J. reine angew. Math. 319 (1980). (s₂(3^n) ≫ log n/log log n.)

Sarnak program:
- P. Sarnak, *Three lectures on the Möbius function, randomness and dynamics*,
  IAS 2011. `papers/sarnak-2011-mobius-lectures.pdf`
- K. Matomäki, M. Radziwiłł, *Multiplicative functions in short intervals*,
  Ann. of Math. 183 (2016).
- N. Frantzikinakis, B. Host, *The logarithmic Sarnak conjecture for ergodic
  weights*, Ann. of Math. 187 (2018).
  `papers/frantzikinakis-host-2018-logarithmic-sarnak.pdf`
- O. Rozier, *Parity sequences of the 3x+1 map on the 2-adic integers and
  Euclidean embedding*, Integers 19 (2019); arXiv:1805.00133. (Adjacent prior
  art on parity sequences of 2-adic points; no descent content.)

Pointwise ergodic theory along subsequences:
- J. Bourgain, *Pointwise ergodic theorems for arithmetic sets* (appendix with
  H. Furstenberg, Y. Katznelson, D. Ornstein: return times), Publ. Math. IHES
  69 (1989). `papers/bourgain-1989-pointwise-ergodic-arithmetic-sets.pdf`
- J. Bourgain, *Almost sure convergence and bounded entropy*, Israel J. Math.
  (1988). (Entropy criterion; negative results.)
- M. Akcoglu, A. Bellow, A. del Junco, R. Jones, V. Losert, K. Reinhold-
  Larsson, M. Wierdl, *The strong sweeping out property for lacunary
  sequences, Riemann sums, convolution powers, and related matters*, ETDS 16
  (1996). (Averages along {2^j} fail a.e., maximally.)

Ceiling:
- J. H. Conway, *Unpredictable iterations* (1972); S. Kurtz, J. Simon, *The
  undecidability of the generalized Collatz problem*, TAMC 2007.

In-repo context: `docs/notes/carries-spectrum.md` (exact window laws; Lemma 6,
Prop. 7, Cor. 9); `docs/notes/two-bases.md` and `docs/notes/mahler-cartier-lemma0.md`
(certificate-side role of (S1)); `docs/CRACKS.md` Cracks 3–4; README census
(5x+1 contrast, Barina verification frontier).
