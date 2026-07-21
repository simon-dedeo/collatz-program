# Thin-connection atlas: six objects reached from three directions

Status: **exploratory literature atlas, not a Collatz result**.  The purpose of
this note is not to rename familiar Collatz structures.  It asks for a much
harder kind of analogy: a technically specific object `B` which is reached by
at least three genuinely different chains

```text
Collatz object -> adjacent object A_i -> the same B.
```

The source search was run *outward* from the `A_i` literatures.  None of the
primary sources retained below was found by asking for Collatz.  A bounded
full-text audit of the twelve retained arXiv PDFs found zero case-insensitive
matches for `Collatz`, `3x + 1`, or `Syracuse`; see the source table.  This is
evidence of bibliographic separation, not proof that nobody has ever noticed
one of the connections.

Calibration used below:

- **D**: a possible mechanism for excluding a divergent positive-integer
  orbit;
- **C**: a possible mechanism for excluding a nontrivial positive cycle;
- **K**: a possible bridge from the predecessor/KL program to full Collatz;
- **exact seam**: an identity that should be turned into a checker before it
  is advertised as a result;
- **speculative seam**: the analogy is coherent but a load-bearing map is not
  known.

## Ranking

| rank | technically specific object `B` | independent entrances | best possible use | present verdict |
|---:|---|---:|---|---|
| 1 | Nontrivial-character Schur complement / Artin--Ihara factors of a **branched cyclic voltage tower** | 4 | **K**, then C | Strongest match.  The exact quotient/detail gate passes: transport is a sheet permutation and each branch is a rank-one reset, not an ordinary lift.  Soft-policy character leakage remains to be measured. |
| 2 | Product-of-places **Poisson boundary of `Aff(Q)`** and its zero-real-drift Cramer face | 4 | D and C, with a possible K bridge | Genuinely full-orbit and adelic.  The local drift vector is explicit, but all available boundary theorems are probabilistic and Collatz itineraries are feedback-selected.  Immediate theorem/experiment probe. |
| 3 | **Peierls barrier and Aubry set of a risk-sensitive Shapley operator** | 4 | K and C | The right replacement for a loose “weak KAM” analogy.  It separates critical policies from transient ones, but the KL min-of-sums is not a classical pathwise Lax--Oleinik operator. |
| 4 | Minimal **max-plus Martin boundary** / Busemann points of the weighted predecessor graph | 3 | D and K | A precise boundary object for rays to infinity.  It may merely expose that the predecessor tree has far too many ends unless arithmetic admissibility makes the boundary collapse. |
| 5 | Critical/torsion group and least-action odometer of a **nonhalting abelian network** | 4 | C and K | Very falsifiable.  Occurrence-sensitive deletion already predicts failure of abelianity, but the raw additive expansion may retain a useful abelian core. |
| 6 | **Maharam extension and Krieger ratio set** of the Collatz size cocycle | 3 | D and K | Mathematically natural but currently measure-only.  Its finite diagnostic may coincide with the zero-charge defect SCC already computed, which would make it a repackaging rather than a lane. |

The first two are selected for immediate work in the final section.  The other
four stay on the atlas until their stated kill tests pass.

---

## 1. Branched cyclic voltage towers and their nontrivial characters

### The object `B`

Take a finite directed graph with a cyclic sheet coordinate, allow some edges
to carry group voltages and some edges to merge or split sheets, and decompose
its weighted adjacency operator into the trivial and nontrivial
representations of the sheet group.  For an honest regular lift this is the
standard character decomposition of a voltage graph.  The KL refinement is
slightly stranger: branch averaging is a rank-one **sheet reset**, so the
natural object is a branched or factored lift, and the useful invariant is the
Schur complement seen by the two nontrivial characters of `Z/3Z`.

This distinction is load-bearing.  Calling the KL tower an ordinary graph
cover is false: for a fixed branch edge, all three lifted target digits can
merge at one lifted row.  The factored/branched-lift literature is relevant
precisely because ordinary local bijectivity fails.

### Four independent entrances

1. **Residue refinement -> three sheets -> factored lift.**  The map from
   level `k` to `k-1` groups coordinates into
   `(x_u,x_(u+n),x_(u+2n))`, `n=3^(k-2)`.  This is literally a three-sheet
   tower before any operator is applied.  Fine branch targets exchange a
   coarse target digit with the new sheet digit, giving the rank-one
   ramification rather than an arbitrary dense matrix.

2. **Carry cocycle -> voltage assignment -> holonomy character.**  The
   transport edge permutes the three children.  Around one coarse transport
   circuit, multiplication by `4^n` satisfies
   `4^n = 1+3^(k-1) (mod 3^k)`, so the omitted digit undergoes a nontrivial
   3-cycle.  This is exactly a `Z/3Z` voltage/holonomy observable, reached
   from the carry calculation rather than from spectral theory.

3. **Annealed transfer -> quotient/detail splitting -> twisted spectrum.**
   Let `P` be arithmetic averaging over each three-sheet fiber and
   `D=ker P`.  A direct index calculation gives the proposed exact seam

   ```text
   P A_k = A_(k-1) P,
   A_k(D) subset D,
   A_k restricted to D = tau times (the transport permutation).
   ```

   The branch average kills every zero-sum fiber, while transport merely
   permutes such fibers.  Thus the annealed “old spectrum plus detail
   spectrum” is a triangular, ramified analogue of the character
   factorization of a cyclic lift.  This route reaches `B` from the transfer
   operator, independently of the carry-holonomy route.

4. **Cycle word -> Frobenius voltage -> compatible prime in a tower.**  A
   closed residue walk lifts to a closed walk one level higher only when its
   accumulated sheet action fixes the chosen lift.  A genuine integer cycle
   gives a compatible closed walk at *every* precision.  Artin--Ihara theory
   packages exactly this splitting/lifting behavior of primitive cycles.
   The new difficulty is ramification: a base cycle can die, split, or merge
   at a branch reset rather than merely acquire a group-valued Frobenius
   element.

### Why the convergence is nontrivial

The annealed operator has the symmetry, but the object of interest does not.
A strict minimizing policy replaces each rank-one average by a one-hot edge;
a soft tangent policy gives three unequal coefficients.  Both couple the
trivial character to the two detail characters.  The same-policy audit found
that retaining those coefficients and sibling masses produces nearly full
state complexity.  Therefore an ordinary finite voltage quotient cannot be
silently substituted for the actual nonlinear policy.

This is nevertheless more than an analogy: “failure of the quotient” becomes
a matrix-valued measurable quantity--the four trivial/detail blocks of the
tangent matrix--rather than a verdict that representation theory is
irrelevant.

### Concrete mechanisms

- **K:** For the soft Perron vector, form its tangent-policy matrix `B_(k,p)`
  and decompose it into trivial/detail character blocks.  A dimension-free
  bound on the detail return operator after taking the appropriate Schur
  complement would exclude a persistent calibrated detail mode.  This is a
  representation-theoretic formulation of the missing fixed-temperature
  annealing theorem, and it explicitly retains policy weights and sibling
  masses.
- **C:** An integer cycle determines a nested prime/closed walk through every
  ramified level.  If the inverse limit of compatible primitive cycles can be
  shown to consist only of the known unit orbit, nontrivial cycles are
  excluded.  A count of cycles at each separate finite level is insufficient;
  compatibility is the essential extra datum.
- **D:** Expansion of the nontrivial characters could force most rays to
  equidistribute among sheets, but a single integer orbit is exceptional.
  This route has no divergence theorem until the compatible-ray exceptional
  set is controlled arithmetically.

### Decisive first test

Build the three-character block decomposition for the annealed matrix and the
soft tangent matrices at `k<=14`.

1. Verify the three displayed annealed identities exactly using separate
   integer edge-type matrices, not floating eigenvectors.
2. Determine whether the refinement is an instance of a published factored
   lift or requires a new “rank-one ramified voltage” definition.
3. For `p=-1,-8,-128`, report Perron-weighted norms and radii of all four
   trivial/detail blocks and of the detail Schur complement.  Euclidean norms
   alone are not dimension-free evidence.
4. Repeat for the hard selected policy.  If soft leakage decays while one-hot
   leakage stays large, the decomposition distinguishes a real finite-
   temperature mechanism from an annealed artifact.  If the weighted detail
   return tends to one at fixed `p`, this candidate is falsified as an endpoint
   route.

The exact part of this test is now complete.  Run

```bash
python3 experiments/kl/verify_branched_voltage_decomposition.py --max-level 12
```

It checks every edge type through level 12: `P_k A_k=A_(k-1)P_k`, branch
annihilation of `ker P_k`, transport preservation of detail, and the literal
three-by-three sheet blocks.  Transport blocks are permutation matrices;
branch blocks are rank-one rows proportional to `(1,1,1)`, and neither they
nor their transposes are scaled permutations.  Thus “rank-one sheet reset” is
an exact description and “ordinary weighted voltage lift” is false.  The
soft/hard Schur-complement stress test remains open.

**Current classification:** exact **ramified-lift structure result** plus an
open experiment/theorem interface.  The uniform soft-policy estimate is the
load-bearing part.

---

## 2. The adelic Poisson boundary of rational affine products

### The object `B`

An element `(a,b)` of `Aff(Q)` acts by `x -> ax+b` simultaneously on the real
line and every `Q_p`.  For a random product of rational affinities, the Poisson
boundary is built from the local fields in which the multiplicative cocycle is
contracting in mean.  This is a sharply classified object: it records all
bounded harmonic information of the random affine walk, not merely an analogy
to “random dynamics.”

### Four independent entrances

1. **Accelerated odd map -> affine product.**  One accelerated Collatz block is

   ```text
   H_e(x)=(3x+1)/2^e,  e>=1.
   ```

   A block word is therefore one element of `Aff(Q)` with multiplier
   `3^L/2^K` and an explicitly accumulated rational translation.

2. **Parity-word Diophantine formula -> local fixed point.**  A cycle word
   asks whether the affine product has a fixed point lying in the diagonal
   copy of the positive integers inside all completions.  The familiar
   denominator `2^K-3^L` is the real component of this simultaneous local
   fixed-point problem.

3. **Numen/solenoid coordinate -> contracting local boundary.**  Reading a
   parity sequence backwards makes the affine translation converge 3-adically;
   the `(2,3)`-solenoid already records the real, 2-adic, and 3-adic faces of
   the same rational affine product.  This reaches the local-field boundary
   from arithmetic coding, not from probability.

4. **KL renewal law -> random walk on `Aff(Q)`.**  The annealed block coding
   supplies a probability law on the exponents `e`; the selected/tangent KL
   eigenvectors supply non-iid Doob laws on affine blocks.  Their local
   Lyapunov vector determines which completions can appear in a boundary.  A
   theorem identifying this Doob boundary would turn predecessor mass into a
   forward affine harmonic measure.

### An exact drift calculation worth isolating

At the endpoint annealed law `q_e=2^-e`, `E[e]=2`.  For the multiplier
`a_e=3/2^e`, the three nonzero local drifts are

```text
chi_infinity = log 3 - 2 log 2 = log(3/4) < 0,
chi_2        = 2 log 2 > 0,
chi_3        = -log 3 < 0,
chi_infinity+chi_2+chi_3=0.
```

So the iid endpoint law contracts in the real and 3-adic fields and expands
in `Q_2`; Brofferio's boundary is correspondingly supported on the contracting
places.  By contrast, a divergent positive-integer orbit must asymptotically
live on the nonnegative-real-drift face, requiring mean exponent at most
`alpha=log_2 3` once the vanishing `+1/x` correction is removed.

The Cramer tilt of `2^-e` to zero real drift is explicit.  It is geometric
with ratio

```text
r_0=1-1/alpha = 0.3690702464...,
theta_0=-1-log_2(r_0) = 0.4380326593... .
```

This “adelic critical face” was reached independently from the divergence
log-walk and from the endpoint renewal law.  It is a concrete distribution to
compare with selected predecessor/Doob measures.

### Why the convergence is nontrivial

The primary boundary theorem assumes iid (or comparably stationary) random
affinities.  Collatz chooses `e=nu_2(3x+1)` by arithmetic feedback, and a
hypothetical divergent orbit is a single measure-zero path.  Even proving that
the KL-selected Doob chain has a particular Poisson boundary would say nothing
about that path unless one proves a support or absolute-continuity bridge.

The local fixed-point language can also merely repackage the standard cycle
equation: a product formula by itself does not add a lower bound at any place.
The candidate earns its rank because the *boundary classification and change
of measure* are extra structures, not because “adeles sound global.”

### Concrete mechanisms

- **D:** Show that any admissible stationary affine law on the zero-real-drift
  face has a non-atomic 3-adic boundary with quantitative cylinder decay, then
  prove that an integer divergent ray would create an atom.  The second arrow
  is completely open and is the decisive one.
- **C:** Bound simultaneous real/3-adic cancellation in the translation part
  of a zero-drift word.  A lower bound forcing its affine fixed point out of
  the positive diagonal would exclude that cycle word.  This must improve on,
  not restate, the existing Baker/continued-fraction denominator bounds.
- **K:** Identify the time reversal of the KL Doob chain with an affine random
  walk, or prove a controlled Markov version.  If its boundary measure charges
  every admissible integer cylinder at the predecessor lower-bound scale,
  predecessor abundance could become a statement about forward recurrence.

### Decisive first test

Compute, for the exact selected `k=12,...,19` records and the soft Perron
vectors, the induced block-exponent law, local Lyapunov vector, entropy, and
relative entropy to the explicit zero-drift geometric law.  Separate
one-cylinder marginals from correlations.  Then prove the finite-state theorem:
for a Markov affine law with rational transitions, identify its contracting
places and stationary boundary measures.  Kill the lane if the selected law
stays on the ordinary contracting-real face or if the only proposed integer
bridge is “the exceptional set has measure zero.”

**Current classification:** high-originality **program** with a cheap exact
drift theorem and a severe deterministic-exception gap.

---

## 3. Peierls barriers for a risk-sensitive Shapley operator

### The object `B`

For a discrete Lax--Oleinik operator, a critical additive eigenfunction is a
weak KAM solution.  The Aubry set is the recurrent minimizing core and the
Peierls barrier measures the asymptotic excess cost of returning between
states.  For a monotone additively homogeneous Shapley operator, the analogous
objects are critical classes, calibrated policies, dominions, and bias vectors.
The relevant `B` here is not “ergodic optimization” in general, but the
**Peierls/critical-class decomposition of the log-transformed, risk-sensitive
KL operator**.

### Four independent entrances

1. **KL nonlinear Perron equation -> additive eigenproblem.**  If `c=e^u`,
   then positive homogeneity becomes additive homogeneity:

   ```text
   log F(e^(u+a)) = a + log F(e^u).
   ```

   The soft dual-policy formula turns the operator into an infimum over
   entropy-penalized positive linear kernels.  In log coordinates this is a
   risk-sensitive dynamic-programming/Shapley operator with eigenvalue
   `log rho` and bias `u`.

2. **Parity log walk -> action functional.**  Along a forward Collatz word,
   `L log 3-K log 2` is an additive action, with a small positive correction
   from the affine `+1`.  One-sided nonnegative-drift tails and near-cycles are
   therefore calibrated-path candidates reached without mentioning KL.

3. **Cycle formula -> periodic Aubry class.**  A periodic parity word is a
   periodic orbit of the residue action.  If it realizes the critical average
   action, it belongs to a finite-level Aubry/critical class.  Requiring the
   class to lift compatibly through every modulus is an arithmetic refinement
   of the ordinary critical graph.

4. **Zero-temperature soft policy -> selected Mather measure.**  The Gibbs
   row policies in the softened KL operator concentrate on hard argmins as
   temperature falls.  Selection/nonselection among tied minimizing policies
   is exactly the kind of information encoded by zero-temperature Mather
   measures and Peierls barriers.

### Why the convergence is nontrivial

The KL row is a sum of a transport term and a minimized branch term.  It is not
a min-plus matrix and not a classical “one path, one additive cost”
Lax--Oleinik operator.  The risk-sensitive Shapley representation fixes this
formal mismatch, but published graph weak-KAM theorems do not automatically
apply to a growing 3-adic state tower with entropy-penalized continuous
actions.

More seriously, a divergent integer orbit need not optimize any action.  A
finite residue quotient admits many spurious periodic policies, so seeing a
small Aubry set at fixed `k` is not a cycle theorem either.

### Concrete mechanisms

- **K:** A level-uniform positive Peierls barrier separating the annealed
  critical class from every nonuniform calibrated class would be a nonlinear
  stability modulus for projection rigidity.  At finite temperature this
  would rule out a phase gap without requiring convergence of eigenvectors.
- **C:** If every compatible inverse-limit Aubry class is shown to be the
  trivial Collatz cycle class, then a nontrivial cycle is excluded.  The word
  “compatible” carries all of the arithmetic content.
- **D:** A divergent orbit would have to determine a Busemann-calibrated ray
  for the chosen action.  No theorem currently gives this calibration, so the
  divergence mechanism is speculative.

### Decisive first test

On levels small enough for exact policy iteration, compute the reduced costs
and Peierls barriers of the hard selected policy and several softened tangent
policies.  Track critical classes under refinement, not just their count.  A
promising signal is a unique compatible class with a barrier bounded away from
zero in the Perron weighting.  A proliferation of compatible near-critical
classes, or barriers falling like the inverse transport-cycle length, kills
the hoped-for stability theorem and confirms the slowly rotating defect
scenario.

**Current classification:** serious **K-oriented formulation**, not yet a new
theorem.  It must not be conflated with the closed max-plus matrix-
interpretation lane for the separate string-rewriting system.

---

## 4. The minimal max-plus Martin boundary

### The object `B`

The max-plus Martin compactification represents extremal harmonic functions of
an infinite weighted graph by limits of almost-geodesics.  Its minimal boundary
is simultaneously a set of Busemann-type functions, extremal eigenvectors, and
optimal ways of escaping to infinity.  This is much more specific than saying
that Collatz has “a boundary at infinity.”

### Three independent entrances

1. **Backward predecessor tree -> weighted almost-geodesic.**  Give inverse
   edges their logarithmic scale costs.  An infinite predecessor history whose
   normalized cost is extremal is an almost-geodesic and therefore proposes a
   Martin boundary point.

2. **Tropical policy value -> max-plus harmonic function.**  Once a branch
   policy is fixed, long-history value functions have tropical asymptotics.
   Normalized limits of those values are candidate max-plus eigenfunctions,
   reached from the certificate side rather than the orbit side.

3. **Divergent parity ray -> Busemann function.**  A forward orbit that escapes
   every compact set supplies nested suffix costs.  If the normalized suffix
   differences converge, they define the same kind of horofunction that the
   max-plus Martin theory identifies with an extremal boundary point.

### Why the convergence is nontrivial

The raw predecessor tree has an enormous end boundary, most of which consists
of formal residue histories not realized by one positive integer orbit.  The
KL operator is also min-of-sums rather than max-plus linear.  One must first
construct an arithmetic weighted graph whose almost-geodesics correspond both
to KL extremals and to actual Collatz histories.  Without that construction,
the boundary is guaranteed to be large and says nothing.

### Concrete mechanisms

- **D:** Prove that the arithmetic minimal boundary has no positive-integer
  Busemann point of nonnegative real slope.  A divergent orbit would create
  one.  This is logically clean, but the orbit-to-almost-geodesic implication
  is open.
- **K:** A finite or uniquely represented minimal boundary would give a
  low-complexity representation of all normalized hard-policy eigenvectors,
  even though no finite local defect quotient exists.
- **C:** Periodic critical nodes appear as recurrent Martin kernels, but this
  is weaker than the compatible-Aubry formulation above for excluding cycles.

### Kill test

Construct the boundary first on the exact occurrence-aware policy history
graph through small depth.  Minimize equivalent normalized kernels and measure
growth of extremal classes.  If the count grows at the same exponential rate
as admissible histories and no arithmetic quotient appears, this object is a
correct description with no compression power.

**Current classification:** useful **boundary language**, lower priority than
the Peierls formulation because the load-bearing arithmetic graph is missing.

---

## 5. Abelian-network odometers and critical groups

### The object `B`

An abelian network is a collection of finite processors whose message handling
commutes locally.  Legal executions obey a least-action principle; halting is
controlled by the production matrix; nonhalting networks have intrinsic
recurrent components and a torsion/critical group independent of update order.
The object proposed here is the **least-action odometer of the raw inverse-
Collatz expansion**, before nonlinear policy selection or deletion.

### Four independent entrances

1. **Raw predecessor expansion -> asynchronous firing.**  Expanding two
   already present predecessor occurrences in opposite orders gives the same
   multiset if every occurrence is retained.  This is the basic commutation
   pattern behind an abelian message network.

2. **Carry state -> finite processor.**  A residue/carry state receives a
   request, updates its finite carry, and emits transport and legal branch
   requests.  This is precisely the local syntax of a multi-letter processor,
   reached from the automaton side.

3. **KL feasible vector -> candidate toppling potential.**  The KL inequalities
   compare one state weight with the weights emitted along transport and
   branch expansions, the same formal role played by linear toppling
   potentials.  Whether the orientations and occurrence bookkeeping satisfy
   an abelian-network least-action hypothesis is part of the proposed test,
   not an imported fact.

4. **Termination rewrite system -> scheduling independence.**  Different
   rewrite orders are different legal executions.  A critical group or
   intrinsic recurrent component would separate genuine nonhalting from an
   artifact of schedule choice.

### Why the convergence is nontrivial

The occurrence-aware termination audit is already a major warning: deleting a
repeated label in one history cannot be justified from the same label in
another history.  Minimum selection and deletion are not abelian operations.
The value-dependent legality of `(2m-1)/3` also prevents a finite residue
processor from representing the full integer state without a proof of
congruence sufficiency.

There is a second obstruction.  The raw inverse tree intentionally branches
and contains the infinite doubling spine, so the usual “production spectral
radius below one implies halting” theorem cannot apply without sinks, weights,
or quotienting.  Any successful use must isolate an abelian core rather than
declare the whole Collatz map abelian.

### Concrete mechanisms

- **K:** If the complete occurrence-aware additive expansion is an abelian
  network, least action could replace history-by-history compilation with one
  canonical odometer.  KL potentials would then bound it, potentially turning
  predecessor abundance into a schedule-independent flow statement.
- **C:** In a nonhalting finite quotient, the torsion group acts on recurrent
  components.  A genuine cycle should yield a compatible recurrent class at
  every precision; a burning-style test might exclude all but the unit class.
- **D:** A stabilizing weighted network could exclude an infinite escaping
  execution.  At present the unavoidable doubling spine makes this mechanism
  unavailable.

### Decisive kill test

Define processors for the smallest occurrence-aware raw-history system and
exhaustively compare all legal firing orders on bounded inputs.  Test the two
local commutativity axioms, not merely equality of total output size.  If they
fail, compute the minimal extra occurrence state needed to restore them.  A
state count growing with depth closes the lane; a fixed restoration would be a
real new invariant.

**Current classification:** high-quality **negative/positive experiment**.
The expected result is a precise nonabelian obstruction, with a small chance
that the raw additive core survives and simplifies the KL construction.

---

## 6. Maharam extensions and ratio sets of the size cocycle

### The object `B`

For a nonsingular transformation with Radon--Nikodym cocycle `omega`, its
Maharam extension acts on `(x,t)` by shifting `t` by `omega(x)` and becomes
measure preserving.  The Krieger ratio set/essential-value group records which
cocycle displacements recur.  The proposed object is the Maharam extension of
the Collatz logarithmic size/holonomy cocycle under a selected conformal or
Doob measure.

### Three independent entrances

1. **Parity sequence -> additive size cocycle.**  Each accelerated block adds
   `log 3-e log 2`, plus a vanishing affine correction.  Appending this height
   is exactly a skew-product/Maharam-style extension of the symbolic base.

2. **Solenoid holonomy -> modular cocycle.**  The `(2,3)`-adic natural
   extension has transverse multipliers whose local modules are powers of two
   and three.  Their logarithm is a Radon--Nikodym cocycle reached from
   foliation holonomy rather than parity probability.

3. **KL Perron vector -> conformal/Doob measure.**  Left and right Perron data
   normalize the transfer operator to a Markov kernel.  Its path measure is
   nonsingular under shift, and its logarithmic Jacobian supplies the same
   cocycle under a different measure.

### Why the convergence is nontrivial

Maharam conservativity, type, and K-properties are almost-everywhere
statements.  Positive integers form a null section of the 2-adic symbolic
system.  Moreover, choosing the KL minimizing policy changes the path measure
with the level, so there is no established limiting nonsingular system.

The existing same-policy defect experiment already computes recurrent
zero-charge SCCs.  If “zero charge” is exactly the finite essential-value
condition for this cocycle, Maharam language adds no invariant.

### Concrete mechanisms

- **D:** Conservativity at zero real drift would force typical height returns,
  conflicting with monotone escape.  This excludes only typical rays until an
  arithmetic support theorem is supplied.
- **K:** A level-uniform essential-value estimate could prevent selected mass
  from remaining in one height sector, providing the dispersion input missing
  from the defect automaton.
- **C:** A zero-cocycle periodic point is visible in the ratio set, but the
  affine translation still decides whether it is an integer cycle.

### Kill test

Label every edge of the same-policy defect graph by its exact log-multiplier
pair `(Delta L,Delta K)` and compute the subgroup generated by charges of
closed SCC walks.  Compare this, state for state, with the existing zero-charge
SCC classification.  If the partitions agree through all feasible test
levels, record the equivalence and do not open a new lane.  Only a strictly
finer essential-value invariant, especially one carrying Perron mass, would
justify continuation.

**Current classification:** likely **repackaging**, retained because the
measure-preserving extension suggests quantitative recurrence tools not used
by the unweighted SCC diagnostic.

---

## Immediate probes selected from the atlas

### Probe A — exact character leakage in the ramified three-sheet tower

This is the highest expected-value probe because it begins with a finite exact
identity and touches the live fixed-temperature theorem.

**Artifact design.**  Represent the annealed operator as a sum of three
separate edge-type matrices: transport, type two, and type eight.  Work over a
rational function ring in formal weights if practical; otherwise verify each
integer incidence matrix separately.  Construct the fiber-sum projection `P`
and an explicit integer basis for `D=ker P`.

**Exact gates.**

1. Check `P A_k=A_(k-1)P` and invariance of `D` through at least `k=8`, then
   prove both formulas from the residue indices.
2. Check that both branch matrices vanish on `D` and that transport restricts
   to a permutation there.  This yields the triangular annealed spectrum
   without diagonalizing a floating matrix.
3. Test the defining axioms of ordinary voltage lifts, relative/factored
   lifts, and branched lifts.  Record the first axiom that fails rather than
   forcing terminology.

**Soft/hard stress.**  At a soft Perron vector, use the exact dual tangent
coefficients to build `B_(k,p)`.  In a Perron-weighted norm, measure the
trivial-to-detail, detail-to-trivial, and detail-return blocks.  Compute the
Schur complement at `rho_(k,p)`.  Compare `p=-1,-8,-128` and the one-hot hard
policy.

**Theorem target.**  For every fixed `lambda<2,p<0`, prove a strict bound on
the weighted detail return after eliminating the trivial block, uniform in
`k`.  Together with a quantitative bound on policy leakage, this would exclude
the slowly rotating calibrated mode and identify the soft spectral limit with
the annealed value.

**Stop rule.**  Stop as an endpoint lane if the Perron-weighted Schur radius
tends to one at fixed `p`, or if every norm making transport controlled makes
policy leakage grow comparably.  The exact annealed factorization remains a
valid structure result either way.

### Probe B — the zero-real-drift face of the affine adelic boundary

This is the full-Collatz moonshot probe.  Its first deliverable is modest and
exact; its jackpot bridge is explicitly separated.

**Exact theorem package.**

1. Derive the local Lyapunov vector for the complete annealed block law
   `q_e(lambda)` and verify the product-formula sum over all places.
2. Derive its Cramer tilt to `chi_infinity=0`; at `lambda=2` check the displayed
   geometric law and `theta_0` exactly up to the single transcendental constant
   `alpha=log_2 3`.
3. Extend Brofferio's elementary contracting-place construction to a finite-
   state Markov law on the rational affinities actually produced by a fixed
   KL policy.  Do not claim the full Poisson-boundary identification until its
   entropy/maximality step is proved.

**Experiment.**  From selected exact records and soft Perron vectors, extract
the stationary block law and transition law.  Report `(chi_infinity,chi_2,
chi_3)`, entropy rate, Cramer rate for the event `chi_infinity>=0`, and 3-adic
cylinder collision.  Compare these with exhaustive forward Collatz orbit
segments stratified by record minima; do not mix the two measures.

**Jackpot theorem target.**  Prove that a positive divergent integer orbit
would create an atom, or another forbidden singularity, in a 3-adic boundary
measure that predecessor/KL lower bounds force to be non-atomic.  This is the
only step that would turn the probabilistic boundary into divergence
exclusion.

**Stop rule.**  If the argument ends with “the divergent paths have measure
zero,” it has not advanced Collatz.  If the local cancellation bound reduces
algebraically to the known denominator/Baker estimates, keep the adelic
dictionary but close the cycle lane.

## What would count as big progress

- A uniform nontrivial-character Schur bound for the soft tangent tower would
  be genuine big progress on `lambda_infinity=2`, even before a full Collatz
  argument.
- A support theorem connecting KL harmonic measure to every positive integer
  affine ray would be bigger: it would be the missing bridge from predecessor
  abundance to forward behavior.
- A finite abelian restoration state or a finite arithmetic Martin boundary
  would be surprising new structure, but neither is currently evidenced.
- Merely proving an almost-everywhere Maharam/Poisson statement, counting
  finite-level critical classes, or renaming the defect SCC is not big
  progress.

---

## Primary-source table and blindness audit

The table lists only primary papers used for a specific theorem or definition.
For each arXiv PDF, the bounded audit was

```text
pdftotext paper.pdf paper.txt
rg -i 'collatz|3x\s*\+\s*1|syracuse' paper.txt
```

and returned zero matches.  The check is reproducible but lexical: it does not
establish priority or conceptual independence.

| id | primary source | fact imported here | lexical hits |
|---|---|---|---:|
| S1 | Iturriaga--Sanchez-Morgado, [*The Lax--Oleinik semigroup on graphs*](https://arxiv.org/abs/1601.03577) | Graph weak-KAM solutions as Lax--Oleinik fixed points; Aubry uniqueness set and long-time convergence | 0 |
| S2 | Akian--Gaubert--Hochart, [*A game theory approach to the existence and uniqueness of nonlinear Perron--Frobenius eigenvectors*](https://arxiv.org/abs/1812.09871) | Dominion/critical-game criteria for monotone homogeneous eigenvectors, including generalized means and Shapley operators | 0 |
| S3 | Akian--Gaubert--Walsh, [*The max-plus Martin boundary*](https://arxiv.org/abs/math/0412408) | Minimal Martin boundary, almost-geodesics, extremal harmonic functions, and Busemann points | 0 |
| S4 | Liu--Peyerimhoff--Vdovina, [*Signatures, lifts, and eigenvalues of graphs*](https://arxiv.org/abs/1412.6841) | Character-twisted spectra of cyclic signatures and towers of 3-cyclic lifts | 0 |
| S5 | Dalfo--Fiol--Siran, [*The spectra of lifted digraphs*](https://arxiv.org/abs/1707.04463) | Representation/character recovery of spectra from finite-group voltage assignments on digraphs | 0 |
| S6 | Dalfo--Fiol--Pavlikova--Siran, [*Combined voltage assignments, factored lifts, and their spectra*](https://arxiv.org/abs/2409.02463) | Factored lifts, group-ring matrices, and spectral recovery beyond ordinary covers | 0 |
| S7 | Gambheera--Vallieres, [*Iwasawa theory for branched `Z_p`-towers of finite graphs and Ihara zeta and L-functions*](https://arxiv.org/abs/2508.07373) | Artin--Ihara formalism and asymptotics in branched `p`-adic graph towers | 0 |
| S8 | Brofferio, [*The Poisson boundary of random rational affinities*](https://arxiv.org/abs/math/0403198) | Boundary as the product of real/`p`-adic fields contracting under the mean affine cocycle | 0 |
| S9 | Bond--Levine, [*Abelian networks I: Foundations and examples*](https://arxiv.org/abs/1309.3445) | Local commutativity axioms and least-action principle | 0 |
| S10 | Bond--Levine, [*Abelian networks II: Halting on all inputs*](https://arxiv.org/abs/1409.0169) | Finite irreducible network halts on all inputs iff its production spectrum lies in the open unit disk | 0 |
| S11 | Chan--Levine, [*Abelian networks IV: Dynamics of nonhalting networks*](https://arxiv.org/abs/1804.03322) | Intrinsic recurrent components and torsion group for update-order-independent nonhalting dynamics | 0 |
| S12 | Danilenko--Lemanczyk, [*K-property for Maharam extensions of nonsingular Bernoulli and Markov shifts*](https://arxiv.org/abs/1611.05173) | Type/conservativity structure and K-property of Maharam extensions | 0 |

## Bottom line

The atlas found six real multi-entrance junctions, not six claims of likely
proof.  The branched-voltage object is the clear winner because it converts a
known obstruction--loss of a finite defect quotient--into a quantitative
character-leakage calculation retaining the full soft policy.  The adelic
affine boundary is the most original full-orbit possibility, but its
deterministic exceptional-set bridge is currently a chasm.  The remaining
objects have explicit kill tests and should not consume a lane until they pass.
