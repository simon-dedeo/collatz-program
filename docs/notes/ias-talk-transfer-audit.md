# IAS talk-transfer audit for the Kontorovich challenge

Started 2026-07-23 21:40 EDT.  This is a literature/reverse-mining lane, not a
claim of a Collatz counterexample.  The source corpus is the local IAS release
in `/Users/simon/Desktop/DANIEL/release`: 1,025 talk JSON records, 7,628 proof
stages, 6,359 examples, and one word-timed raw Deepgram transcript per talk.

## Audit protocol

1. Give every talk a talk-level assessment from its proof-stage DAG and coded
   examples.  The assessment must name source stages/examples, translate the
   mathematical objects into Collatz objects, state one exact theorem or
   falsifiable bounded experiment, and state the principal mismatch.
2. Rank before reading transcripts.  Promote a talk only when it suggests an
   invariant, selector, symbolic encoding, compactness/coherence argument,
   obstruction, or exact search architecture rather than a verbal analogy.
3. For every promoted talk, reconstruct the cited spans from
   `release/transcripts/<key>.json` and check the noisy ASR against the
   structured summary.
4. Keep three statements separate: bounded survival, symbolic/invariant
   closure, and an ordinary positive Collatz counterexample.  The last remains
   `null` unless all unbounded and ordinary-seed obligations are proved.

One corpus-wide Batch-API pass was submitted as batch
`batch_6a62c709831481909b9b0066c2bdaaf9`: 1,025 requests and approximately
2,314,492 input tokens.  This is the only planned broad API call.  The output
cap is 4,000 tokens per talk, but the schema asks for short fields.  Actual
usage and estimated cost will be added after completion; no further API work
will be started if total projected spending approaches $1,000.

## Lead A: a mixed dyadic--triadic recursive valuation selector

**Source.** Rachel Greenfeld, *Einstein, P-adic Sudoku, Domino, and
Decidability*, IAS, 4 Dec. 2023,
[video](https://www.ias.edu/video/einstein-p-adic-sudoku-domino-and-decidability),
key `306cad1983df747b3cb7e38d2b9fea54`.  Raw transcript checked at S3--S5,
1,308--2,471 seconds.  The most relevant explanation is 1,520--1,880 seconds;
the hierarchical “remove the regular cells and rescale the remainder” proof
description occurs at approximately 1,760--1,910 seconds.

The construction begins with

```text
f_p(n) = n / p^v_p(n) mod p                      (n != 0),
```

with a convention at zero.  Away from the multiples of `p` it is periodic.
On the exceptional divisible coset, division by `p` reveals the same problem
at the next scale.  Consequently the function is a density limit of periodic
functions but is globally nonperiodic.  Line constraints and an additional
column constraint force the whole Sudoku solution to retain that hierarchy;
first-order constraints are then encoded as a finite system of tiling
equations and compressed to one equation.

For `p=3`, `f_p(H)` is precisely the first primitive ternary digit
`(H/3^v3(H)) mod 3`.  The key Collatz transfer is not “use Sudoku”; it is the
following architecture class:

```text
regular residue layers  -> finite dispatch table of legal recharge words
one divisible layer     -> divide an affine state coordinate by 3 and recurse
```

Equivalently, synthesize a finite recursive valuation transducer whose
effective modulus is unbounded.  It can inspect `v3(L_i(X))` and the primitive
residue of finitely many affine forms `L_i` in the full state
`X=(charge,address,carry,chart)`.  This architecture is outside the proved
open-hole theorem for any fixed finite congruence-cylinder selector only if
it also binds fresh dyadic data at each recursive layer.

There is now a kernel-checked obstruction to the pure ternary version.
`KontoroC.OutwardValuationSelectorNoGo` proves that every exact primitive
layer

```text
n = center + 3^depth*digit  (mod 3^(depth+1)),  digit in {1,2},
```

contains arbitrarily large ordinary members where any chart selected from
`(depth,digit)` is illegal.  Each layer is still a full ternary cylinder, and
CRT exposes the dyadic hole inside it.  A `Layer` node whose regular branch
leaves the dyadic coefficient free is therefore dead even when the chart
varies arbitrarily with depth and primitive digit.  A surviving transfer must
make the state genuinely mixed-base: the regular and exceptional branches
must both impose or update dyadic address/carry restrictions before selecting
the chart.  A local build of `KontoroC.OutwardValuationSelectorNoGo` passes.

**Exact CEGIS obligation.** Add mixed-base grammar nodes

```text
Layer(L,a,regular_table,exceptional_child)
```

with exact semantics: inspect `L(X) mod 3^a`; dispatch on nonexceptional
residues; bind a dyadic address/carry cylinder on every outgoing branch; on
the unique divisible class replace the designated coordinate by `L(X)/3^a`
and enter `exceptional_child`.  Enumerate only small finite graphs of these
nodes.  Reject a node immediately if any regular branch is a full ternary
layer with no dyadic binder.  For every remaining candidate, return the least
ordinary state where the selected first-passage word is illegal or invariant
closure fails.

A successful object must prove all of:

```text
I(X0)
I(X) -> selected word is exactly legal
I(X) -> I(R_selected(X))
the address/carry component represents the same ordinary positive seed
the resulting orbit never reaches 1
```

No such object is known.  In particular, an infinite recursive `3`-adic
selector without the address/carry clauses could still describe only a
profinite object.

## Lead B: weighted core entropy before recursive search

**Source.** Philipp Habegger, *The Dynamical Schinzel-Zassenhaus Conjecture
and the Transfinite Diameter of Trees*, IAS, 11 Mar. 2026,
[video](https://www.ias.edu/video/dynamical-schinzel-zassenhaus-conjecture-and-transfinite-diameter-trees),
key `4b080d81929fc490575d04cec24a3754`.  Raw transcript checked at S4--S7,
1,513--3,442 seconds, especially the comparison at 2,909--3,442 seconds.

The Hubbard-tree edge map has a finite nonnegative transition matrix.  Its
Perron root controls combinatorial growth, while inverse-image degree controls
geometric scaling.  The strict core-entropy gap—Perron root below degree—is
the leverage that keeps a capacity below its rigidity threshold.

For a finite exact Collatz macro grammar, give every Boolean first-passage edge
`e:i->j` its word length `D(e)` and define

```text
M_s(i,j) = sum_{e:i->j} 2^(-s D(e)).
```

This multi-state Kraft filter is now kernel-checked in
`KontoroC.OutwardFiniteStateKraftGap`.  The finite multigraph requires
first-passage labels and sourcewise label injectivity.  Instead of trusting a
floating spectral radius, it accepts the exact Collatz--Wielandt certificate

```text
v(i)>0,  0<=r<1,  Mv<=r*v.
```

Lean proves that some source state has outgoing Kraft mass below one and
constructs a literal Boolean word, at the maximum outgoing label length, for
which no outgoing edge label is a prefix.  Thus a rational subcritical
certificate produces an explicit finite-depth symbolic hole.  This prunes
impossible finite strongly connected components before valuation-recursive
CEGIS.  It does not identify the symbolic hole with an ordinary
writer--decoder parameter cylinder, and it does not cover infinite-state or
mixed recursively growing selectors.  A single exceptional atomic ray is
also outside any claim based only on missing complete coverage.

## Lead C: ordinary covering windows, not profinite shadowing

**Source.** Rafael de la Llave, *Some geometric mechanisms for Arnold
diffusion*, IAS, 10 Apr. 2018,
[video](https://www.ias.edu/video/emergingtopics/2018/0410-RafaeldelaLlave),
key `06c75558ea7a67c26523d60637d5f0af`.  Raw transcript checked at S4,
2,016--2,483 seconds, and S6, 3,033--3,267 seconds.  The speaker explicitly
allows a possibly infinite sequence of channel choices and distinguishes the
infinite case, where errors can accumulate, from a finite pseudo-orbit.

The useful translation is an exact integer covering-window lemma.  A verified
first-passage block is a channel between windows in
`(charge,dyadic tail,root carry,chart)`.  One should search for block relations
that cover a whole source subwindow onto a target window, rather than retain
one lucky canonical representative.  An infinite chain would imply one
ordinary orbit only if the theorem also carries compatible root projections
and certified zero ordinary-root carry at infinitely many endpoints.  Those
resets are the arithmetic substitute for the geometric transverse freedom in
Arnold diffusion.  Without them the shadow can again be merely `2`-adic.

## Lead D: clean catalytic macros for ordinary-seed coherence

**Source.** James Cook, *Borrowing memory that's being used: catalytic
approaches to the Tree Evaluation Problem*, IAS, 6 Apr. 2020,
[video](https://www.ias.edu/video/csdm/2020/0406-JamesCook), key
`62fe994bc97f7e36b22ecea9ea707a40`.  Raw transcript checked at S4--S5,
1,444--2,584 seconds, especially 1,500--2,550 seconds.

Cook's clean subroutines may use registers whose initial contents are
arbitrary, but must restore those contents after placing the answer in a
designated output register.  Compute--copy--uncompute makes this possible;
the product lemma composes recursive calls while reusing the same registers,
so recursion depth need not consume fresh workspace.

The exact Collatz transfer is a stronger macro specification than low carry.
Split a first-passage state into payload `P`, an ordinary-root/address
catalyst `C`, and bounded chart data `Z`.  Seek a forward-legal word family
with

```text
(P,C,Z) -> (F(P),C,Z')
```

on a recursively described invariant set, with `F(P)>P`.  The identity on
`C` is the clean-reset condition: an infinite recursive composition then
reuses one ordinary seed rather than consuming an infinite `2`-adic tape.
The first exact experiment should enumerate short legal block pairs whose
affine action on the root-address coordinate composes to the identity, then
ask CEGIS for a payload-dependent recursive rule that closes under those
pairs.

The mismatch is sharp.  Cook can explicitly run an inverse instruction
sequence; Collatz supplies only forward-legal words.  The proposed
"uncompute" must itself be compiled into another forward Collatz block on the
same invariant family.  Repeating one fixed clean block would also fall into
the existing eventual-periodicity no-go.  Any live version must therefore be
payload-dependent and recursively clean, not merely a zero-carry loop found
at one bounded depth.

## Lead E: turn anomalous carry concentration into algebraic structure

**Source.** Guy Moshkovitz, *Structure and Randomness for Finite-field
Polynomials are (almost) Equivalent*, IAS, 13 Jan. 2025,
[video](https://www.ias.edu/video/structure-and-randomness-finite-field-polynomials-are-almost-equivalent),
key `e71017370c27ed97e3367f54c6e3fc2b`.  Raw transcript checked across S1--S7,
especially 500--1,700 and 2,300--3,600 seconds.

The theorem says, quantitatively and uniformly over finite fields up to a
logarithmic loss, that a bounded-degree polynomial system whose solution
density deviates from the random benchmark has a low-rank algebraic
explanation.  Analytic rank measures bias; partition rank expresses the
multilinearized polynomial as few reducible pieces; local rank bridges the
two.

This suggests an inverse-search lane, not another trajectory predictor.
For a bounded block architecture, encode the exact carry/legality defect as a
finite-field polynomial or tensor in its block-choice variables.  If exact
counting finds far more zero/small-carry choices than the random baseline,
attempt to recover a low partition-rank decomposition and translate its
factors into a smaller recursive selector.  A successful bounded theorem
would have the form

```text
anomalous exact zero-carry density
    -> bounded-rank factorization
    -> explicit parametric macro family to replay by exact arithmetic.
```

This route has a decisive preliminary gate: dyadic valuations and carries are
discontinuous, and their exact polynomial representation over a fixed finite
field may have degree growing with block depth.  Unless one proves a
depth-uniform bounded-degree encoding (or a suitable replacement inverse
theorem), Moshkovitz's theorem cannot be applied.  It is nevertheless a
principled stopping rule for search: exceptional concentration should be
factorized and explained rather than merely used to extend a beam.

## Composite lead F: lift a clean local verifier, then amplify or expose its boundary

This architecture combines four transcript-checked talks.

- Madhu Sudan, *New Locally Decodable Codes from Lifting*, IAS, 25 Mar.
  2013, [video](https://www.ias.edu/video/csdm/1213/0325-MadhuSudan), key
  `3068276612d77bb8c917f3d60bce089b`, S6--S7 at 2,646--3,660 seconds (raw
  checked at 2,580--3,700).  The decisive reversal is to fix a local test and
  define the global code to be everything whose affine restrictions pass it.
  Local correction and testing are inherited from the base code; Lucas-type
  digit conditions and carry avoidance identify a large monomial basis.
- Emmanuel Abbe, *A Proof of the RM Code Capacity Conjecture*, IAS, 23 Oct.
  2023, [video](https://www.ias.edu/video/proof-rm-code-capacity-conjecture),
  key `f73def25cf4813d4304ad78e0fa763a1`, S6--S8 at 2,476--3,735 seconds
  (raw checked at 2,420--3,780).  A weak local advantage is amplified by
  recursively restricting to self-similar subspaces.  Many subspaces are
  packed as sunflower petals; their overlap is concentrated in one common
  kernel, and conditioning on that kernel makes the petals sufficiently
  independent for boosting.
- Jit Wu Yap, *Ultrafilters in Arithmetic Dynamics*, IAS, 7 Oct. 2025,
  [video](https://www.ias.edu/video/ultrafilters-arithmetic-dynamics), key
  `85dfdad85fdf0ab9bc2da969014af1c1`, S5--S7 at 2,236--3,581 seconds (raw
  checked at 2,180--3,620).  A pointwise positive energy separation over
  every characteristic-zero valued field becomes a uniform bound by taking
  a rescaled ultralimit of any putative sequence with vanishing normalized
  separation and deriving a contradiction at the nonarchimedean boundary.
- Peter Sarnak, *Pseudorandomness -- Substitution Sequences at Primes*, IAS,
  3 Dec. 2008,
  [video](https://www.ias.edu/video/pseudorandomness-substitution-sequences-primes),
  key `51ef6ccdfe811aca02e4380ca93f0867`, E1/S2 near 701 seconds (raw checked
  at 620--790).  His doubling-map example is the exact anti-cheating warning:
  an exceptional real starting point can preload any desired infinite word
  in its dyadic expansion, so apparent symbolic generation may be tautological.

The proposed Collatz object is a **lifted clean selector**.  Start with a
small exact base verifier `B` for policy tables on a bounded mixed residue
window.  Rather than guess one large table, define a level-`m` policy to be
admissible when every allowed low-dimensional affine slice restricts to an
element of `B`.  The domain should carry both dyadic and triadic coordinates;
a field-only lift is already inadequate after the pure ternary no-go.

Now concentrate all overlap between recursive slices in a common kernel `K`
containing the ordinary-root/address catalyst.  Every accepted petal macro
must be forward-legal and restore `K` exactly, in Cook's sense.  If an exact
count shows a weak surplus of good petals for each kernel value and symmetry
prevents the surplus from concentrating on one exceptional slice, a sunflower
argument can select a good compatible petal at the next scale.  Selection,
not majority voting, is the relevant conclusion; a deterministic least-good-
petal rule must then itself be exact-replayed.  Because the catalyst is
restored, recursive selection reuses state rather than reading fresh high bits
of a preloaded `2`-adic seed.

The bounded CEGIS pilot would therefore:

1. synthesize the smallest base verifier `B` from exact legal block tables;
2. enumerate its mixed affine slices and reject any slice leaving the dyadic
   coefficient unrestricted;
3. require identity action on the catalyst and positive payload progress;
4. count good petals conditional on every kernel value and test an exact
   sunflower dispersion inequality;
5. if concentration is anomalous, invoke the Moshkovitz/Nguyen structure lane
   to factor it into a smaller parametric verifier;
6. exact-replay the least selected petal and return the first semantic or
   closure failure.

Yap's mechanism supplies a separate completeness target for an architecture
class.  Compactify normalized base verifiers and define an exact nonnegative
failure energy.  If one can prove pointwise positive energy for every
ordinary and nonarchimedean boundary verifier, an ultralimit contradiction
would give a uniform finite failure bound.  If pointwise separation fails,
the boundary zero exposes the specific degeneration that the architecture
must represent rather than encouraging a larger blind search.

Every arrow above is conditional.  Sudan and Abbe work over affine finite-
field codes and probabilistic channels, whereas exact Collatz legality mixes
`2`- and `3`-adic divisibility and is not affine-invariant.  Yap's pointwise
boundary-separation theorem has not been proved for any Collatz selector
space.  Most importantly, a lifted policy without exact catalyst restoration
would reproduce Sarnak's preloaded-bit example in `2`-adic form and would not
define an ordinary counterexample.

## Lead G: extract an exact clean-macro factor before searching words

Three transcript-checked talks give complementary algebraic gates.

- Prahladh Harsha, *An Improved Line-Point Low-Degree Test*, IAS, 23 Sept.
  2024,
  [video](https://www.ias.edu/video/improved-line-point-low-degree-test), key
  `b5a7f9887daa1ac832aca5a35895482f`, S5--S7/E3--E4.  Raw spans checked at
  1,577--1,770, 1,880--2,010, 2,106--2,285, and 2,778--3,441 seconds.  Local
  polynomial roots on slices glue only after a simple-root/discriminant gate,
  uniqueness under Hensel lifting, and enough independent directions; the
  raw talk gives explicit one- and two-direction counterexamples to naive
  gluing.
- Rafael Oliveira, *Factors of polynomials of low individual degree*, IAS,
  12 Oct. 2015,
  [video](https://www.ias.edu/video/csdm/2015/1012-RafaelOliveira), key
  `5f48881ff6900ff31b1b09211f54361b`, S3--S5 at 1,077--2,482 seconds.
  Separated roots are recovered one homogeneous component at a time by
  Hensel/Newton lifting and exact interpolation; reversal moves a destructive
  recursive leading-coefficient blowup to a manageable constant interface.
- Michael Forbes, *Polynomial Identity Testing of Read-Once Oblivious
  Algebraic Branching Programs*, IAS, 26 Nov. 2012,
  [video](https://www.ias.edu/video/csdm/forbes), key
  `e94e440f44f7a0396ffcc58c9bcdd99c`, S3--S5/E6--E7 at 1,399--2,782
  seconds.  Recursive merging must preserve the full coefficient-matrix span;
  preserving nonzeroness of the two halves separately is not compositional.

For a fixed symbolic macro skeleton `T`, clear denominators and form the exact
returned-catalyst defect

```text
R_T(x_1,...,x_s,y).
```

The `x_i` are payload/interface parameters and `y` is the proposed returned
root/address coordinate.  A polynomial clean family `y=g(x)` requires the
exact factor relation

```text
y-g(x) divides R_T(x,y),
```

plus the separate valuation-legality and positive-payload identities.  The
pilot should derive `R_T` coefficientwise, test a simple root at a chosen
center, lift its homogeneous pieces only through an a priori degree bound,
and then verify `R_T(x,g(x))=0` as an integer polynomial identity.  The first
nonzero residual is an exact architecture counterexample, not a poor score.

For a recursively composed finite block library, encode each position by a
polynomial matrix `A_i(X_i)` whose coefficient matrices are the homogeneous
affine actions on `(payload,address,triadic quotient,root carry,1)`.  Compute
the exact coefficient-matrix span `S` of `prod_i A_i`, and let `C` be the
linear subspace satisfying the homogenized clean-catalyst equations.  Then

```text
S subset C       => every encoded word is clean,
S intersect C=0  => no encoded word is clean.
```

The intermediate case is honestly inconclusive because a clean linear
combination need not be an actual word.  These are useful universal/no-go
certificates before any word enumeration.

The main risk is bounded degree.  Collatz counters occur inside `2^D` and
`3^G`; unbounded templates may have growing degree, and high-valuation points
may be exactly where the derivative vanishes.  A formal or rational factor
also need not preserve integrality, forward legality, outward progress, or an
ordinary seed.  This lane is therefore restricted to fixed symbolic skeletons
with explicit degree and integrality bounds.

## Lead H: higher-congruence descent must begin with one genuine top lift

**Source.** Naomi Sweeting, *Kolyvagin's conjecture and higher congruences of
modular forms*, IAS, 22 Apr. 2021,
[video](https://www.ias.edu/video/kolyvagins-conjecture-and-higher-congruences-modular-forms),
key `2ec6065ba6553d6058a1b3551199f757`, S3--S4 and S6--S7; E3/E5.  Raw
transcript checked at 884--1,280, 1,470--1,952, 2,597--3,540, and
3,640--3,810 seconds.

The raw talk exhibits a map modulo `p^2` that mixes two genuine eigenvalues
but has no characteristic-zero lift.  Sweeting repairs this by adding an
auxiliary level index, constructing horizontal and vertical compatibility
relations with quantified loss of `p`-adic precision, producing a genuine
characteristic-zero object at the top, and descending only after budgeting
more precision than all losses.  She explicitly notes that `p=2` is harder.

The exact Collatz analogue uses two indices.  Let `C_m(n,q)` mean that one
specified canonical root makes a length-`n` macro prefix with repair level
`q` legal modulo `2^m`.  Horizontal relations extend or modify the prefix;
vertical relations remove repair levels while losing at most `e(q)` bits.
The certificate target is

```text
C_(m + sum e(q_i))(n_top,q_top) from one fixed ordinary seed
  + exact commuting horizontal/vertical relations
  -> C_m(n_base,1) for that same seed.
```

Enumerate commuting macro squares and compute their precision loss exactly.
Reject a square if its two routes yield different canonical ordinary roots.
Most importantly, separately optimized residue roots at each `m` are not a
top lift.  Unbounded depth must descend from the same explicit positive
ordinary seed, or the diagram is another profinite approximation.  Collatz
currently has no analogue of the cohomological relations and deformation
theory that manufacture Sweeting's top object, so this is a certificate
architecture and a false-lift detector, not evidence that it closes.

## Lead I: a mixed-base Toeplitz skeleton needs an internal clean clock

**Source.** Joana Kulaga-Przymus, *Thermodynamic Formalism for B-free
Dynamical Systems*, IAS, 1 Mar. 2023,
[video](https://www.ias.edu/video/thermodynamic-formalism-b-free-dynamical-systems),
key `d99bbc3ba5e7f41c084fc87c8fb505c5`, S1--S3 at 35--1,480 seconds and
S7 at 2,537--2,969 seconds.  Raw transcript checked at 430--1,510 and
2,537--2,750 seconds.

A `B`-admissible binary sequence omits at least one residue class modulo every
`b in B`.  In the Toeplitz regime every position is periodic, but the period
may depend on the position; regularity means that positions already fixed by
periods up to `K` have density tending to one.  Thus a globally nonperiodic
object can be specified by nested periodic skeletons with a shrinking set of
unresolved holes.  Periodic approximants then support exact transfer-matrix
and pressure calculations.

This is a natural language for the surviving part of Greenfeld's idea.  Build
periods `M_k | M_(k+1)` with both dyadic and triadic factors.  At level `k`,
assign clean macro types on some residue classes modulo `M_k`; unresolved
classes recurse to level `k+1`, and assignments never change.  The pure
ternary form is already closed by `OutwardValuationSelectorNoGo`, so every
assigned regular class must include the dyadic address/carry binder required
by its macro.

An external Toeplitz word is still a preloaded instruction tape.  A valid
Collatz certificate therefore needs an internal ordinary clock `tau(X)` with

```text
tau(X_0)=0,
selected clean macro sends X to X',
tau(X')=tau(X)+1,
the root/address catalyst is restored exactly.
```

Every clock value must be assigned at a finite skeleton level, and the macro
must prove exact legality, payload progress, and invariant closure on the
whole corresponding mixed residue class.  A bounded pilot should synthesize
nested skeletons, return the first uncovered clock or semantic counterexample,
and compute exact weighted pressure only after closure.  Density-one periodic
skeletons or nonempty `B`-free subshifts do not supply one Collatz orbit; the
internal clean clock and ordinary root remain the decisive obligations.

## Preflight filters J: resource cones, lattice support, and honest integral lifting

Three previously transcript-checked mechanisms should run before any costly
selector search.

**Exact rational resource cone.** Annie Raymond, *Graph Density Inequalities,
Sums of Squares and Tropicalization*, IAS, 1 Feb. 2021,
[video](https://www.ias.edu/video/graph-density-inequalities-sums-squares-and-tropicalization),
key `1046f78390fd05e12d05a3413a3ddf7b`, S3--S6; raw checked at
3,506--3,690 seconds.  Record for each exact macro its height margin, dyadic
precision consumed, triadic precision transported, counter-scale change, and
rigorous carry bounds.  Any recurrent grammar has a nonnegative conserved
edge flow satisfying the tropicalized resource inequalities.  The exact dual
preflight is now kernel-checked in `KontoroC.OutwardResourceConeNoGo`.

For a finite first-passage grammar, Lean defines nonnegative nonzero rational
circulations with flow conservation at every state.  Given a rational vertex
potential, or a vector of edge resources with nonnegative rational
multipliers, it proves that no resource-admissible nonzero circulation exists
when every edge has strictly negative reduced score

```text
potential(target e)-potential(source e)+combinedScore(e) < 0.
```

The proof is exact telescoping; an external LP may propose the rational
certificate, but no solver or floating optimization is trusted.  The semantic
layer must still prove that a proposed recurrent architecture has the assumed
coordinatewise nonnegative aggregate budgets.  A feasible ray is not an
ordered trajectory, bounded survival does not imply a circulation, and
tropicalization can discard the valuation cancellations that matter.
Commit `f0576d6` adds the ordered companion: `EdgeWalk` records a composable
edge list, vertex potentials telescope along it, and the same strict dual
excludes every nonempty closed macro walk with nonnegative total selected
resource score.  This rejects an actual returned graph-state candidate
without first replacing it by an averaged circulation.

Josephine Yu, *Tropicalizing Principal Minors of Positive Definite Matrices*,
IAS, 22 Oct. 2024,
[video](https://www.ias.edu/video/tropicalizing-principal-minors-positive-definite-matrices),
key `0eab2f1bcd5d53ef12cbbbd88b961671`, supplies the next gate after a
feasible resource ray.  S5--S8 at 2,181--3,758 seconds (raw checked at
2,150--3,780) distinguish the easy outer tropical cone from the smaller
representable tropicalization; slice-wise representability need not glue to
one global lift.  Positivity and Cauchy--Binet eliminate valuation
cancellation, and tropical equalities are explained by sharp algebraic
inequalities upstairs.  For a Collatz macro library, a feasible tropical
resource vector should therefore be promoted only after deriving an actual
positive-semiring macro representation or exact lifted inequalities which
certify realizability.  Returned-catalyst defects involve subtraction, so the
no-cancellation hypothesis may fail precisely where a reset occurs.  This is
a realizability filter, not a route from a cone ray to a trajectory.

**Local support before a local limit.** Swastik Kopparty, *A local central
limit theorem for triangles in a random graph*, IAS, 28 Mar. 2016,
[video](https://www.ias.edu/video/csdm/2016/0328-SwastikKopparty), key
`69956d38eef0339ec0f4207f78499dcd`, S1--S2/S4--S7 and E2; raw checked at
826--1,020 seconds.  A global CLT cannot detect even an odd/even support
obstruction.  For an exact block ensemble, compute the carry support modulo
powers of `2` and `3` and condition on every interface residue before using
Fourier decay or a Gaussian heuristic.  Only after zero is in the exact local
lattice should one seek a pointwise lower bound at zero.  Independent random
blocks and prefix-compatible Collatz blocks are very different, so even a
finite reset-block local limit would still need a clean recursive grammar.

**Finite-field connectivity is not an integral lift.** Alexander Gamburd,
*Varieties of Markoff Type: Arithmetic, Combinatorics, Dynamics*, IAS,
12 Dec. 2022,
[video](https://www.ias.edu/video/varieties-markoff-type-arithmetic-combinatorics-dynamics),
key `76f210c2e1fbd9df473b9ca8890f1e5a`, S4--S8/E3--E5, and Daniel Martin,
*Arithmetic on Markoff Surfaces*, IAS, 7 Apr. 2026,
[video](https://www.ias.edu/video/arithmetic-markoff-surfaces), key
`dfe6aa197a4b6c233c6312357c4670a6`, S2/S4--S6 and E4.  Martin's raw E4 span
at 2,045--2,158 seconds explicitly gives a parameter with many finite-field
Markoff triples but no integer triples.  Finite residue graphs of the recharge
map may still be useful for computing component-frequency vectors and their
exact orthogonal obstruction space, but edge lifting and positivity must be
proved separately.  The reversible Markoff group action has structural tools
that the one-way, changing-precision Collatz semigroup may not possess, and
compatible finite levels still need one eventually stable ordinary root.

## Lead K: a converse/bootstrap theorem must include Archimedean coercivity

Anshul Adve, *A Converse Theorem for Hyperbolic Surface Spectra and the
Conformal Bootstrap*, IAS, 15 Apr. 2026, key
`d76cbe86eae9244183aa6bd456d03039`, supplies a useful reconstruction pattern
which is stronger than another local-consistency test.  S4 and S6--S8 state
algebraic bootstrap identities for candidate structure constants, construct an
abstract representation and multiplication, use positivity identities to
bound all multiplication operators, and then apply Gelfand duality.  The
resulting compact `G`-space is forced to be homogeneous because every
`G`-smooth vector is bounded.  The raw transcript was checked at
2,268--3,064 seconds.  In the discussion at 3,341--3,489 seconds, inverse
limits of towers are given as explicit pathological solutions once the
discreteness condition is relaxed.

The exact Collatz analogue is now visible.  First-passage and cylinder
equations are the local bootstrap identities, but by themselves their inverse
limit may be only a `2`-adic seed.  The already-formalized ordinary-ray gate
says that the canonical root residues are nondecreasing and that any uniform
Archimedean bound forces eventual constancy, equivalently eventual zero
extension carry and one ordinary natural seed.  Therefore an invariant-CEGIS
candidate should not merely close under recharge.  It should export a
coercive exact certificate controlling the root residue uniformly along the
whole invariant.

A concrete next architecture is a polynomial/SOS extension of the current
linear resource dual.  Synthesize a low-description semialgebraic potential
`V(H,address,carry,chart)` together with exact identities showing that (i) its
sublevel set is closed under every selected legal macro, and (ii) membership
in that sublevel set bounds the canonical root residue by one fixed natural
`B`, while allowing the charge/counter coordinate to grow.  Clear all
denominators and check the resulting polynomial identities exactly; a first
negative point or nonzero residual is the CEGIS counterexample.  If such a
certificate exists, the existing bounded-residue theorem supplies the
ordinary seed and the writer--decoder invariant endpoint supplies the infinite
orbit.  This is a conditional proof architecture, not a current invariant.

The main risk is severe: the Collatz macro relation is piecewise exponential
in valuation parameters, not a fixed-degree commutative multiplication table.
A finite-degree SOS ansatz may cover only a fixed alphabet, where the Kraft and
resource no-go theorems already apply.  Unlike Adve's associativity equations,
no positive quadratic identity is presently known that bounds address while
permitting unbounded outward payload.  The transcript nevertheless changes
the search objective from “more compatible finite levels” to the exact missing
converse hypothesis: a globally verified Archimedean coercivity certificate.

Formalizer commit `af4c46f` now makes the local enumeration premise exact:
`heightAdmissibleSymbols H` is an executable finite set containing every
literal outward first-passage `(counter,drain)` at fixed source charge `H`.
The same module proves the counter budget and output envelope used by the
resource filters.  This permits exhaustive bounded synthesis of candidate
potentials on the complete local alphabet, but gives no uniform alphabet or
address bound as `H` grows.

Formalizer commit `acbcf84` kernel-checks the converse interface itself.
`CoerciveSublevelCertificate` requires a closed invariant sublevel of a
natural-valued potential and an inequality bounding every canonical initial
residue by that potential along the symbolic orbit.  Lean derives bounded
residues, eventual zero extension carry, and an ordinary nonnegative reset
chain.  Its final conditional endpoint deliberately requires a separate
`PositiveMacroRealization` theorem for every adjacent pair; abstract reset
equations alone do not prove positivity or literal first-passage execution.
Thus the remaining synthesis obligations are now formally separated:

1. construct and exactly verify the coercive residue-controlling invariant;
2. promote its reset chain to positive literal recharge macros.

Only their conjunction yields an infinite execution.  No candidate currently
satisfies either unbounded obligation.

Formalizer commit `b620786` separately kernel-checks the strict S-arithmetic
stabilization route suggested by Datta.  Congruence of two naturals modulo
`2^A*3^B` plus `abs(next-current)<2^A*3^B` forces equality.  On canonical
reset residues, an eventual increment strictly below the old dyadic width
forces every later carry digit to vanish and supplies an ordinary nonnegative
reset chain.  The theorem does not derive this pointwise bound; average or
metric estimates and a bound with an unspecified constant do not meet its
hypothesis.

The transcript re-audit sharpens Adve's missing hypothesis to **global uniform
properness**.  The actual converse uses a complete infinite multiplication
table, absolute convergence, a discrete spectrum with no finite accumulation,
and multiplier bounds uniform in both indices.  A bounded SOS/CEGIS fit is
therefore interpolation data only.  A faithful Collatz certificate must have
cutoff-independent degree/constants, a symbolic all-height identity over the
complete `heightAdmissibleSymbols H`, and proper address sublevels while charge
remains unbounded.

Lubotzky, Glebsky, and Petrov give three complementary reasons not to weaken
that clause.  Metric ultraproducts make asymptotic equations exact only in the
ultraproduct; stability is the additional lifting theorem back to genuine
maps.  Product/profinite compactness may solve equations only in a quotient or
overgroup, where a kernel can erase the seed error.  Even finite-coefficient
cohomology can survive completion while higher coherence changes: a
topological `K(pi,1)` may acquire profinite `pi_2`.  For a recursive macro
presentation, the exact audit is therefore to track relator two-cocycles,
prove a uniform correction/stability theorem if one exists, and check that its
kernel is trivial on the catalyst and ordinary root.  These are architecture
filters, not a path from finite shadows to an integer.

Formalizer commit `d8e789a` also kernel-checks the core of Kaveh's circuit
preflight.  An exact zero sum cannot have one supported term divisible by
`p^k` but not `p^(k+1)` while all other supported terms are divisible by
`p^(k+1)`.  Worker-facing theorems specialize this unique-minimum rejection to
`p=2` and `p=3`, including affine coefficient-times-value terms.  Passing the
paired tests supplies no lift or trajectory.

## Lead L: quotient min-plus states by exact aliases, but retain every boundary tie

Percy Deift, *Toeplitz Matrices and Determinants Under the Impetus of the
Ising Model*, IAS, 29 Jan. 2013, key
`e832f96f0127827a297b644c18151b91`, gives a surprisingly direct rule for the
triadic min-plus lane.  S4 and E2/E5 show that one Fisher--Hartwig symbol can
have many integer-shifted presentations.  Applying the one-representation
formula to an arbitrary presentation gives contradictory answers, including
decay for a symbol which is identically one.  The Basor--Tracy repair is to
minimize a quadratic cost over the whole zero-sum integer-shift orbit and sum
the contributions of every minimizing alias.  The raw transcript was checked
at 1,111--1,914 seconds.

S6--S7 solve the discrete alias problem by local exchanges.  Every orbit has a
representative of seminorm at most one.  Below the boundary the minimizer is
unique; at seminorm one all minimizers are connected by exchanges, and the
proof retains the entire tied family.  The transcript at 2,255--2,971 seconds
is explicit that strict convexity in the continuous problem does not prevent
multiple discrete minimizers.

The Collatz obligation is to decide first whether multiple first-passage
phase/carry records are presentations of the *same semantic cylinder*.  Define
an alias relation only from proved equality of their affine source set and
literal endpoint map.  Seek a finite collection of local integer carry
exchanges which generates every presentation of one semantic object.  Then
minimize the exact address/resource score over the complete alias orbit:

```text
strict interior minimum  -> one canonical normal form;
boundary minimum         -> retain every exchange-connected co-minimizer.
```

This changes the EM/CEGIS implementation in a falsifiable way.  Deduplicate
states only after an exact alias certificate, and never let beam width discard
a tied boundary face.  Feed the entire co-minimizer set to the clean-factor,
resource, coercivity, and literal semantic gates.  A disagreement between two
claimed aliases on one exact source is the smallest rejection witness.

The principal mismatch is also decisive.  Deift sums alias contributions to
one determinant asymptotic; a Collatz counterexample must select one executable
word, so co-minimizers may not be averaged or spliced.  Fisher--Hartwig has a
fixed finite singularity vector and a proved zero-sum shift action, whereas
Collatz's valuation dimension and exponent costs may grow.

Formalizer commit `af90376` now proves a stronger literal boundary than the
proposed exchange theorem.  Two positive `RechargeMacro`s with the same source
and target charges have exactly the same first-passage block list.  Determinism
makes their flattened words prefix-comparable, prefix-free decoding reflects
that comparison to block lists, and a proper suffix would be a forbidden
positive recharge from the target back to itself.  Therefore symbolic records
may be quotient aliases only after proving that they decode to the *identical*
literal macro.  A tie between distinct decoded words is a choice between
different executions, never one semantic alias orbit.  This closes the
distinct-executable-alias version of Lead L and leaves only record
normalization plus preservation of all genuinely different tied choices.

## Lead M: refine selector architectures by exact indistinguishability witnesses

Charanjit Jutla, *A Completeness Theorem for Pseudo-Linear Functions with
Applications to UC Security*, IAS, 28 Feb. 2010, key
`6e4ef815ee2322a047f36de5410f05f6`, gives a theorem-shaped outer loop for the
requested selector CEGIS.  The talk studies uniform finite branching programs
whose values are characteristic-two linear expressions and whose guards test
linear equalities.  The monolithic completeness theorem says that a
pseudo-linear target which is any function of pseudo-linear observations is
already pseudo-linearly expressible from them.  The raw transcript was checked
at 1,792--3,095 seconds.

The effective criterion is especially useful here.  Partition the exact
finite state space by every zero/nonzero guard signature.  On each row the
target must be a linear combination of the observed features, and isomorphic
rows must use the same coefficients.  If either requirement fails, the proof
constructs two points on which every observed input feature agrees but the
target differs.  The transcript states the row and isomorphic-row tests at
2,271--2,526 and 2,977--3,024 seconds, then states the two-point witness at
3,026--3,095 seconds.

For one bounded exact recharge problem, let `X_k` be the complete
height-admissible state set, let `F_k(x)` contain the chosen valuations,
residues, carry and memory features plus their guard signature, and let
`T_k(x)` be the exact next legal action or target.  Before fitting a selector,
test the necessary functionality condition

```text
F_k(x) = F_k(y)  ->  T_k(x) = T_k(y).
```

Under a proved pseudo-linear finite-field encoding, Jutla's criterion either
extracts the smallest row-coherent selector or returns an exact pair `(x,y)`
which the present architecture cannot separate.  That pair is a better CEGIS
counterexample than a late trajectory failure: add one carry bit, residue, or
memory feature specifically chosen to separate it, then rerun exact replay.
For iterated calls the talk introduces superguards and randomized/stateful
extensions; the raw discussion at 3,098--3,645 seconds also rejects exhaustive
field enumeration as a security-parameter-dependent, nonuniform program.

The mismatch sets the unbounded acceptance gate.  Collatz legality uses mixed
`2`- and `3`-adic valuations rather than characteristic-two linear guards, is
partial, and has precision that grows along the candidate orbit.  Separately
successful selectors for each `k` may therefore be another Frankenstein
inverse system.  A live result needs one fixed guard grammar and one fixed
coefficient rule, independent of `k`, followed by literal first-passage
replay, invariant closure, and the existing ordinary-seed stabilization gate.
The talk supplies an exact architecture-refinement principle, not that
uniform theorem and not a Collatz counterexample.

## Lead N: fixed-shape macro families face an S-unit finiteness gate

Lilian Matthiesen, *Linear equations in smooth numbers*, IAS, 18 Oct. 2022,
key `87c95bd0494bd525290bc695733fc58a`, separates dense additive heuristics from
the exponentially thin arithmetic relevant here.  The talk defines
`y`-smooth numbers and asks when systems of linear forms take smooth values.
At 775--969 seconds it uses `a+b=c` as the basic test: expected-order counts
are known only once `y` is at least a sufficiently large power of `log N`,
whereas for `y=(log N)^k`, `k<1`, ABC would leave only boundedly many
solutions.  At 985--1,205 seconds the speaker explicitly says the method does
not reach that super-sparse transition.

Collatz macro identities live further into the sparse regime: after removing
ordinary coefficients, their multiplicative terms are generated by the fixed
primes `2` and `3`.  The talk therefore does **not** justify a
Green--Tao/transference search for them.  Instead it points back to the
classical fixed-`S` unit-equation theorem already present in this project's
literature audit: for a fixed number of terms, the projective nondegenerate
solutions of

```text
u_1 + ... + u_t = 0,     u_i in Z[1/6]^times,
```

form a finite set.  This extra theorem is not proved in Matthiesen's talk, and
effective bounds beyond a few terms remain a known wall.

The resulting architecture gate is nonetheless exact.  Expand a proposed
fixed-shape returned-catalyst or recharge identity into its signed
`2^a 3^b` terms and remove the common projective scale.  First apply the
kernel-checked paired `v_2`/`v_3` unique-minimum rejection.  Then test every
proper subsum symbolically.  If no proper subsum vanishes, S-unit finiteness
allows only finitely many projective parameter tuples; it cannot support an
unbounded recurrence-parametrized macro family.  An infinite family must
therefore do at least one of three explicit things:

1. expose a persistent exact vanishing-subsum partition, which should be
   promoted to the clean compositional-factor lane;
2. grow the number of arithmetic terms/blocks with scale;
3. introduce genuinely unbounded coefficients, the already recorded wall in
   effective S-unit methods.

This is a principled way to reject fixed symbolic skeletons before trajectory
search.  It does not exclude growing recursive grammars, and finiteness without
an effective bound is not an executable exhaustive certificate.  The other
warning from the talk is parallel: small Gowers norms alone do not give the
correct four-term progression count without a pseudorandom majorant satisfying
the full linear-forms condition (2,792--3,267 seconds).  Likewise, entropy or
equidistribution of recharge features cannot replace exact lattice support,
closure, and ordinary-seed realization.

## Other promoted talks (transfer ledger)

| Status | Talk and raw spans | Concrete transfer | Principal mismatch |
|---|---|---|---|
| targeted | Rafael de la Llave, *Geometric and Numerical Approaches to KAM Theory*, key `e056004f8e81393a47abd4fb4dcce613`, S1--S4, 16--2,283 s | Parameterize the invariant itself and seek an a posteriori certificate from a small exact residual plus nondegeneracy, rather than accumulate orbit points. | Smooth/analytic Newton contraction and Diophantine rotation do not exist for the discontinuous integer map; a useful transfer likely needs a `3`-adic/Hensel replacement. |
| targeted | Bernard Chazelle, *The mathematics of natural algorithms*, key `5e0929aceb9d14462b6a9a4d3dd8d8ff`, S5--S7, 1,978--3,695 s | Treat exact recharge dynamics as cell decomposition with repeated orbit splitting; use a grammar/message-passing renormalization of changing transition graphs and quantify branch entropy versus address contraction. | The talk's generic periodicity is perturbative/almost-sure and cannot establish an exceptional ordinary orbit. |
| targeted | Jean Bourgain, *On Zaremba's Conjecture on Continued Fractions*, key `181d4aa312ac43061b3a703420b6a846`, S3--S8, 1,533--3,986 s | Factor a legal-word matrix semigroup into coherent blocks with controlled expanding direction; use renewal/local-to-global analysis to count prescribed residues. | Density-one denominators in an expanding `SL_2` semigroup do not imply a nested path whose canonical Collatz seed stabilizes to an ordinary integer. |
| targeted | Hoi H. Nguyen, *A New Approach to the Inverse Littlewood-Offord Problem*, key `b5044a0a3573537d667f9fcd9e06bae6`, S2--S7, 718--3,442 s | If exact search finds anomalously many small/equal address or carry sums, pose an inverse theorem: concentration should force the word coefficients into a bounded-rank generalized arithmetic progression, yielding a compact parametric family. | The Collatz coefficients are dependent powers of `2` and `3`, not iid signed coefficients; the needed inverse theorem is new. |
| background/warning | Umberto Zannier, *On a Problem of Polya and Some of its Evolutions*, key `8c6e7ea43c9de3b12a756caab4bc5ea0`, S2--S7, 711--3,601 s | Search for a finite-dimensional obstruction module in which closure modulo all `3^k` forces exact closure; require prime-power precision, not scattered mod-prime successes. | Pólya/Grothendieck--Katz use algebraic differential equations, integrality, and transcendence tools absent from the current recharge system. |
| background | Philipp Habegger, *The Dynamical Schinzel-Zassenhaus Conjecture and the Transfinite Diameter of Trees*, key `4b080d81929fc490575d04cec24a3754`, S2--S8, 443--3,600 s | A complexity-growth gap (core entropy below degree) plus a global capacity threshold converts many local near-solutions into a rigid preperiodic conclusion; look for an address-complexity versus branching gap. | Existing Collatz height/correspondence approaches degenerate, and this theorem concerns algebraic polynomial dynamics, not a piecewise-affine integer map. |
| targeted | Rafael de la Llave, *Some geometric mechanisms for Arnold diffusion*, key `06c75558ea7a67c26523d60637d5f0af`, S4/S6, 2,016--2,483 and 3,033--3,267 s | Replace lucky symbolic prefixes by exact covering relations between charge/address/carry windows; require recurring zero-root-carry endpoints in the shadowing theorem. | Collatz lacks the continuous transverse freedom and hyperbolicity that make geometric covering windows work. |
| targeted | James Cook, *Borrowing memory that's being used*, key `62fe994bc97f7e36b22ecea9ea707a40`, S4--S5, 1,444--2,584 s | Search for payload-dependent clean macros whose forward action restores the ordinary-root/address catalyst exactly, allowing recursive reuse without an infinite tape. | Collatz has no freely available inverse/uncompute instruction; it must be realized by another forward-legal word, and a fixed repeated macro is already excluded. |
| conditional | Guy Moshkovitz, *Structure and Randomness for Finite-field Polynomials are (almost) Equivalent*, key `e71017370c27ed97e3367f54c6e3fc2b`, S1--S7 | Treat anomalous exact zero-carry density as an inverse problem and factor a bounded-degree defect tensor into a small parametric architecture. | Exact valuation/carry predicates may require degree growing with depth, blocking direct use of the finite-field theorem. |
| composite/conditional | Madhu Sudan, *New Locally Decodable Codes from Lifting*, key `3068276612d77bb8c917f3d60bce089b`, S6--S7, 2,646--3,660 s | Define a growing policy language by one small exact local verifier on every mixed affine slice, rather than by a large residue lookup table. | The field-affine lifting theorem does not cover mixed dyadic--triadic valuation guards or dynamical closure. |
| composite/conditional | Emmanuel Abbe, *A Proof of the RM Code Capacity Conjecture*, key `f73def25cf4813d4304ad78e0fa763a1`, S6--S8, 2,476--3,735 s | Pack self-similar policy slices as sunflower petals around one clean address/carry kernel and amplify a weak exact surplus of good compatible extensions. | Channel decoders can vote; one Collatz orbit must select and replay one petal, and the needed independence/dispersion theorem is absent. |
| architecture filter | Jit Wu Yap, *Ultrafilters in Arithmetic Dynamics*, key `85dfdad85fdf0ab9bc2da969014af1c1`, S5--S7, 2,236--3,581 s | Turn pointwise positive failure energy on every valued-field boundary model into a uniform bounded failure depth for a compact selector class. | No Collatz compactification or boundary-separation theorem is known; an ultralimit alone produces another nonordinary object. |
| warning | Peter Sarnak, *Pseudorandomness -- Substitution Sequences at Primes*, key `51ef6ccdfe811aca02e4380ca93f0867`, E1/S2 near 701 s | Reject selectors that merely preload their instruction stream in the high dyadic bits of an exceptional starting point; require a finite ordinary root and clean reusable catalyst. | The doubling-map example is a warning, not a construction or no-go for a self-writing Collatz policy. |
| targeted | Prahladh Harsha, *An Improved Line-Point Low-Degree Test*, key `b5a7f9887daa1ac832aca5a35895482f`, S5--S7/E3--E4 | Glue slice-wise prefix selectors only after bounded-degree encoding, enough directions, and a uniform simple-root Hensel gate; then verify the global identity exactly. | Valuation gates may be singular, and a global formal root still need not be an ordinary seed. |
| targeted | Rafael Oliveira, *Factors of polynomials of low individual degree*, key `5f48881ff6900ff31b1b09211f54361b`, S3--S5, 1,077--2,482 s | Recover a clean returned-catalyst factor degree by degree and use its first nonzero residual as an exact macro-architecture obstruction. | Unbounded powers `2^D,3^G` generally destroy bounded degree and simple-root separation. |
| architecture filter | Michael Forbes, *Polynomial Identity Testing of Read-Once Oblivious Algebraic Branching Programs*, key `e94e440f44f7a0396ffcc58c9bcdd99c`, S3--S5/E6--E7, 1,399--2,782 s | Preserve the complete coefficient-matrix span of a recursive macro product; span containment proves universal cleanliness and trivial intersection proves a no-go. | A clean span element need not be an actual word, and width may grow with precision. |
| targeted/warning | Naomi Sweeting, *Kolyvagin's conjecture and higher congruences of modular forms*, key `2ec6065ba6553d6058a1b3551199f757`, S3--S4/S6--S7 | Use a two-index exact descent with quantified bit loss and require all finite congruence certificates to descend from one genuine ordinary top seed. | Collatz lacks the horizontal/vertical relations and deformation theory that produce the top lift. |
| warning | Andreas Wieser, *Local-Global Principles and Effective Rates of Equidistribution For Semisimple Orbits*, key `d6a6f21ab12a4e96856899c8b8d76b88`, S1--S4/S6 | Before invoking local-global lifting, test whether prefix varieties have a semisimple algebraic stabilizer and sufficient intermediate-orbit complexity to force an integral target hit. | Collatz macro actions are largely solvable/noninvertible; even integral lifts at each depth need not share one ordinary seed. |
| warning | Alan Reid, *Profinite rigidity and flexibility for compact 3-manifold groups*, key `752f9598c8fc447ea9edf6f2e2ffe372`, S1/S3/S5--S7 | Define the finite-portrait genus of a controller and seek quotient separation only inside a sharply restricted class. | Profinite rigidity gives uniqueness of an already existing discrete object, not existence of an ordinary realization. |
| conditional | Richard Ehrenborg, *Counting Pattern Avoiding Permutations Via Integral Operators*, key `e5d73aeba9471656ab49c2384cd0b4f3`, S2/S7 | Build an exact overlap graph of universally clean macros and certify primitivity, positive resource-cycle mean, and compatible unbounded-scale bonding maps. | Fixed-state graphs favor periodic paths and cannot absorb indefinitely fresh dyadic precision. |
| conditional | Elad Haramaty, *On the Structure of Cubic and Quartic Polynomials*, key `63ed799a0a626b68c9ed383b4c711805`, S5--S8/E3 | Refine the bias-to-structure lane: biased derivatives, a Bogolyubov subspace, and a shared low-rank linear basis can recover a compact carry grammar. | Carry degree may grow, modular structure may not lift, and the talk's quartic counterexample blocks naive inverse claims. |
| conditional | Joana Kulaga-Przymus, *Thermodynamic Formalism for B-free Dynamical Systems*, key `d99bbc3ba5e7f41c084fc87c8fb505c5`, S1--S3/S7 | Use nested mixed-base periodic skeletons with recursively resolved holes, and require a state-derived clean clock whose every value is eventually assigned. | An external Toeplitz schedule is a preloaded tape; density and pressure do not prove semantic closure or an ordinary seed. |
| preflight | Annie Raymond, *Graph Density Inequalities, Sums of Squares and Tropicalization*, key `1046f78390fd05e12d05a3413a3ddf7b`, S3--S6 | Solve the rational cone of height, dyadic/triadic precision, counter scale, and carry resources; export a Farkas no-go or a minimal feasible support. | Flow loses word order and tropicalization loses exact cancellation; a feasible ray is not a trajectory. |
| preflight | Josephine Yu, *Tropicalizing Principal Minors of Positive Definite Matrices*, key `0eab2f1bcd5d53ef12cbbbd88b961671`, S5--S8 | After cone feasibility, require membership in a realizable tropicalization via a positive-semiring representation or exact lifted inequalities. | Collatz clean-reset defects contain subtraction/cancellation, and slice-wise lifts need not glue globally. |
| preflight | Swastik Kopparty, *A local central limit theorem for triangles in a random graph*, key `69956d38eef0339ec0f4207f78499dcd`, S1--S2/S4--S7/E2 | Establish exact modular/lattice support of carry zero conditional on interfaces before any local-limit or entropy argument. | Collatz word contributions are dependent, and a finite zero-carry block does not supply a prefix-compatible infinite orbit. |
| warning | Alexander Gamburd, *Varieties of Markoff Type*, key `76f210c2e1fbd9df473b9ca8890f1e5a`, and Daniel Martin, *Arithmetic on Markoff Surfaces*, key `dfe6aa197a4b6c233c6312357c4670a6` | Use finite residue components and dual obstruction vectors as exact features, but demand a separate edge-lifting and ordinary-integral theorem. | Many finite-field points can have no integer lift; Markoff's reversible group action is unlike the Collatz semigroup. |
| conditional/converse | Anshul Adve, *A Converse Theorem for Hyperbolic Surface Spectra and the Conformal Bootstrap*, key `d76cbe86eae9244183aa6bd456d03039`, S4/S6--S8, 2,268--3,064 and 3,341--3,489 s | Pair exact local identities with a coercive global bound; synthesize an exact potential whose invariant sublevel set uniformly bounds canonical root residues, so the existing stabilization theorem reconstructs one ordinary seed. | No Collatz positivity identity is known that controls address while allowing unbounded charge, and fixed-degree/fixed-alphabet SOS may fall inside already-closed finite-state lanes. |
| warning/refinement | Danny Neftin, *Reducible Fibers and Monodromy of Polynomial Maps*, key `7eabb36b0c76b7dfc5ea3b5a15aa8aa9`, S2/S5--S7, 503--1,120 and 2,429--3,453 s | Strengthen the clean-factor gate by asking whether source, target, and reset maps share a genuine left compositional factor; infinite exceptional fiber families should come from such structure rather than isolated hits. | The large-monodromy theorem deliberately excludes the solvable power/Chebyshev cases, while Collatz macro matrices are upper triangular and built from powers of `2` and `3`; generic monodromy therefore misses the hard regime rather than solving it. |
| conditional finite existence | Jonathan Leake, *Polynomial Capacity and its Applications: To TSP and Beyond*, key `5aa2491ca875be21405d16cbf769efcd`, S1--S2/S4--S5/S7, 42--1,053 and 1,538--4,027 s | Encode exact resource vectors of a finite legal block library as exponents of a nonnegative generating polynomial; if homogeneity, real stability, positive target capacity, and support are proved, a coefficient lower bound certifies at least one finite clean macro. | Valuation/carry restrictions may destroy real stability or create lattice holes; approximate marginals do not imply a target coefficient, and one finite word gives neither recursive closure nor an infinite orbit. |
| architecture filter | Robert Robere, *Applications of Monotone Constraint Satisfaction*, key `7d3a4068c31f8f6add2e2191289f4896`, S4--S8/E4/E7, 988--3,922 s | Compile a bounded macro topology into exact local constraints and mine replayable refutations for small arithmetic separators that can be promoted independently as CEGIS features or no-go lemmas. | Exponential proof/circuit complexity is only hardness, not satisfiability or construction; Collatz is deterministic, unbounded, and not monotone under freely adding transitions. |
| preflight | Kiumars Kaveh, *Tropical Vector Bundles and Matroids*, key `6fbcec9c48581879e3e6864fff4761a1`, S2--S5/S8/E3, 1,055--3,739 s | Compute exact circuits of a candidate affine relation and reject it whenever the `v_2` or `v_3` weighted circuit has a unique minimum, which cannot cancel; survivors need an explicit representable lift over `Q` or `Z[1/6]`. | Abstract Bergman/matroid consistency can be nonrepresentable and tropicalization forgets units and signs; passing both valuation tests is necessary, never constructive by itself. |
| warning/exact target | Shreyasi Datta, *S-arithmetic Diophantine Approximation*, key `07617502569abfc23a09496b2fa3e3d7`, S1--S3/S7--S8/E1/E4, 15--3,972 s | Package dyadic/triadic divisibility and Archimedean address height together; the exact desired estimate is `abs(N_(k+1)-N_k) < 2^A_k*3^B_k`, which forces the integer extension carry to vanish and the ordinary representative to stabilize. | The talk proves metric/nondivergence statements for typical approximation, not the exceptional exact inequality needed here; measure zero neither constructs nor excludes a counterexample. |
| conditional architecture | Ana Rita Pires, *Symplectic Embeddings and Infinite Staircases*, key `5f0bc63953693792769f40cc44603678`, S4--S7/E3--E5/E7, 2,287--3,531 s | Seek a macro family whose integer parameters obey a proved second-order recurrence `A_n=K*A_(n-1)-A_(n-2)` and whose ratios converge to a quadratic resource-balance point; prove legality, clean reset, and invariant closure for all `n` by exact induction. | The talk's existence proof deliberately does not construct all staircase corners, and infinitely many active obstructions do not compose into one orbit; OEIS recognition or asymptotic accumulation is not an exact Collatz family. |
| closed literal alias / retained record normalization | Percy Deift, *Toeplitz Matrices and Determinants Under the Impetus of the Ising Model*, key `e832f96f0127827a297b644c18151b91`, S4/S6--S7/E2/E5, 1,111--1,914 and 2,255--2,971 s | Deduplicate symbolic records only after literal decoding; commit `af90376` proves that fixed positive recharge endpoints admit one unique first-passage block list.  Preserve every equal-cost distinct decoded word as a separate executable choice. | Determinant contributions may be summed, but Collatz choices cannot.  There is no nontrivial literal alias orbit at fixed endpoints; only redundant symbolic presentations of the identical word remain. |
| conditional stability filter | Alexander Lubotzky, *Stability, Non-approximated Groups and High-dimensional Expanders*, key `6b1b831e4b3dd5445ae97fcd580d1eb2`, S1/S3--S4/S6--S7/E4/E6, 52--610 and 1,587--3,440 s | Linearize controller relators, compute the degree-two defect cocycle, and require a uniform stability/correction theorem whose kernel is trivial on the seed coordinate before promoting asymptotically consistent tables. | The talk concerns total unitary group maps with metric error; Collatz macros are partial and valuation-discontinuous, and stability of a controller action still does not make its seed ordinary. |
| warning | Lev Glebsky, *Approximations of Groups, Subquotients of Infinite Direct Products and Equations over Groups*, key `02dcdc750c5e506010b7ccfae677d308`, S2--S3/S5--S8, 37--1,290 and 2,504--3,463 s | Measure the least finite quotient through which every selector function factors; a stable level plus kernel-triviality and bounded canonical representatives is the required discrete-lift gate. | Compactness deliberately produces a solution over an overgroup/product quotient, where growing finite dependence is exactly an infinite profinite tape. |
| warning/coherence audit | Alexander Petrov, *Galois Action on Higher Etale Homotopy Groups*, key `e76667fa26f053d772a9d6b48a8190ab`, S3--S6/E4--E5, 834--1,230 and 1,620--3,620 s | Attach a transition 2-complex to claimed commuting repair/descent squares and test comparison cocycles or `p`-good/`K(pi,1)` behavior before treating finite shadows as a discrete controller. | The arithmetic higher-homotopy obstruction need not occur in the Collatz graph, and detecting one only rejects gluing; it constructs neither a seed nor an orbit. |

## Negative lessons already extracted

- Greenfeld's hierarchy explains why a finite residue table is the wrong
  endpoint: a finite *recursive* table can have unbounded scale.  The new Lean
  obstruction shows that ternary scale alone is insufficient: every regular
  layer must also bind fresh dyadic address/carry information.
- Zannier's countercases show why infinitely many isolated modular successes
  are weaker than coherent success through all prime powers.
- Markoff-surface talks in the corpus include explicit finite-field solutions
  that do not lift to integer solutions.  Finite congruence connectivity must
  not be confused with ordinary-seed existence.
- Zaremba-type local-to-global counting may populate every finite modulus yet
  still converge only to a nonordinary `2`-adic address.  Canonical-address
  stabilization remains an independent obligation.

## Bibliography / talk provenance

- Rachel Greenfeld, *Einstein, P-adic Sudoku, Domino, and Decidability*, IAS
  School of Mathematics, 4 Dec. 2023, corpus key
  `306cad1983df747b3cb7e38d2b9fea54`.
- Rafael de la Llave, *Geometric and Numerical Approaches to KAM Theory*, IAS,
  8 Feb. 2012, key `e056004f8e81393a47abd4fb4dcce613`.
- Bernard Chazelle, *The mathematics of natural algorithms*, IAS, 14 Nov.
  2016, key `5e0929aceb9d14462b6a9a4d3dd8d8ff`.
- Jean Bourgain, *On Zaremba's Conjecture on Continued Fractions*, IAS,
  14 Feb. 2012, key `181d4aa312ac43061b3a703420b6a846`.
- Hoi H. Nguyen, *A New Approach to the Inverse Littlewood-Offord Problem*,
  IAS, 1 Feb. 2010, key `b5044a0a3573537d667f9fcd9e06bae6`.
- Umberto Zannier, *On a Problem of Polya and Some of its Evolutions*, IAS,
  8 Apr. 2026, key `8c6e7ea43c9de3b12a756caab4bc5ea0`.
- Philipp Habegger, *The Dynamical Schinzel-Zassenhaus Conjecture and the
  Transfinite Diameter of Trees*, IAS, 11 Mar. 2026, key
  `4b080d81929fc490575d04cec24a3754`.
- Rafael de la Llave, *Some geometric mechanisms for Arnold diffusion*, IAS,
  10 Apr. 2018, key `06c75558ea7a67c26523d60637d5f0af`.
- James Cook, *Borrowing memory that's being used: catalytic approaches to the
  Tree Evaluation Problem*, IAS, 6 Apr. 2020, key
  `62fe994bc97f7e36b22ecea9ea707a40`.
- Guy Moshkovitz, *Structure and Randomness for Finite-field Polynomials are
  (almost) Equivalent*, IAS, 13 Jan. 2025, key
  `e71017370c27ed97e3367f54c6e3fc2b`.
- Madhu Sudan, *New Locally Decodable Codes from Lifting*, IAS, 25 Mar. 2013,
  key `3068276612d77bb8c917f3d60bce089b`.
- Emmanuel Abbe, *A Proof of the RM Code Capacity Conjecture*, IAS, 23 Oct.
  2023, key `f73def25cf4813d4304ad78e0fa763a1`.
- Jit Wu Yap, *Ultrafilters in Arithmetic Dynamics*, IAS, 7 Oct. 2025, key
  `85dfdad85fdf0ab9bc2da969014af1c1`.
- Peter Sarnak, *Pseudorandomness -- Substitution Sequences at Primes*, IAS,
  3 Dec. 2008, key `51ef6ccdfe811aca02e4380ca93f0867`.
- Prahladh Harsha, *An Improved Line-Point Low-Degree Test*, IAS, 23 Sept.
  2024, key `b5a7f9887daa1ac832aca5a35895482f`.
- Rafael Oliveira, *Factors of polynomials of low individual degree*, IAS,
  12 Oct. 2015, key `5f48881ff6900ff31b1b09211f54361b`.
- Michael Forbes, *Polynomial Identity Testing of Read-Once Oblivious
  Algebraic Branching Programs*, IAS, 26 Nov. 2012, key
  `e94e440f44f7a0396ffcc58c9bcdd99c`.
- Naomi Sweeting, *Kolyvagin's conjecture and higher congruences of modular
  forms*, IAS, 22 Apr. 2021, key `2ec6065ba6553d6058a1b3551199f757`.
- Andreas Wieser, *Local-Global Principles and Effective Rates of
  Equidistribution For Semisimple Orbits*, IAS, 14 Nov. 2024, key
  `d6a6f21ab12a4e96856899c8b8d76b88`.
- Alan Reid, *Profinite rigidity and flexibility for compact 3-manifold
  groups*, IAS, 2 Feb. 2016, key `752f9598c8fc447ea9edf6f2e2ffe372`.
- Richard Ehrenborg, *Counting Pattern Avoiding Permutations Via Integral
  Operators*, IAS, 23 Nov. 2010, key `e5d73aeba9471656ab49c2384cd0b4f3`.
- Elad Haramaty, *On the Structure of Cubic and Quartic Polynomials*, IAS,
  1 Nov. 2010, key `63ed799a0a626b68c9ed383b4c711805`.
- Joana Kulaga-Przymus, *Thermodynamic Formalism for B-free Dynamical
  Systems*, IAS, 1 Mar. 2023, key `d99bbc3ba5e7f41c084fc87c8fb505c5`.
- Annie Raymond, *Graph Density Inequalities, Sums of Squares and
  Tropicalization*, IAS, 1 Feb. 2021, key
  `1046f78390fd05e12d05a3413a3ddf7b`.
- Josephine Yu, *Tropicalizing Principal Minors of Positive Definite
  Matrices*, IAS, 22 Oct. 2024, key `0eab2f1bcd5d53ef12cbbbd88b961671`.
- Swastik Kopparty, *A local central limit theorem for triangles in a random
  graph*, IAS, 28 Mar. 2016, key `69956d38eef0339ec0f4207f78499dcd`.
- Alexander Gamburd, *Varieties of Markoff Type: Arithmetic, Combinatorics,
  Dynamics*, IAS, 12 Dec. 2022, key `76f210c2e1fbd9df473b9ca8890f1e5a`.
- Daniel Martin, *Arithmetic on Markoff Surfaces*, IAS, 7 Apr. 2026, key
  `dfe6aa197a4b6c233c6312357c4670a6`.
- Anshul Adve, *A Converse Theorem for Hyperbolic Surface Spectra and the
  Conformal Bootstrap*, IAS, 15 Apr. 2026, key
  `d76cbe86eae9244183aa6bd456d03039`.
- Danny Neftin, *Reducible Fibers and Monodromy of Polynomial Maps*, IAS,
  28 Oct. 2021, key `7eabb36b0c76b7dfc5ea3b5a15aa8aa9`.
- Jonathan Leake, *Polynomial Capacity and its Applications: To TSP and
  Beyond*, IAS, 8 Apr. 2024, key `5aa2491ca875be21405d16cbf769efcd`.
- Robert Robere, *Applications of Monotone Constraint Satisfaction*, IAS,
  28 Mar. 2017, key `7d3a4068c31f8f6add2e2191289f4896`.
- Kiumars Kaveh, *Tropical Vector Bundles and Matroids*, IAS, 21 Oct. 2024,
  key `6fbcec9c48581879e3e6864fff4761a1`.
- Shreyasi Datta, *S-arithmetic Diophantine Approximation*, IAS, 2 Dec. 2022,
  key `07617502569abfc23a09496b2fa3e3d7`.
- Ana Rita Pires, *Symplectic Embeddings and Infinite Staircases*, IAS,
  15 Apr. 2016, key `5f0bc63953693792769f40cc44603678`.
- Percy Deift, *Toeplitz Matrices and Determinants Under the Impetus of the
  Ising Model*, IAS, 29 Jan. 2013, key
  `e832f96f0127827a297b644c18151b91`.
- Charanjit Jutla, *A Completeness Theorem for Pseudo-Linear Functions with
  Applications to UC Security*, IAS, 28 Feb. 2010, key
  `6e4ef815ee2322a047f36de5410f05f6`.
- Lilian Matthiesen, *Linear equations in smooth numbers*, IAS, 18 Oct. 2022,
  key `87c95bd0494bd525290bc695733fc58a`.
- Alexander Lubotzky, *Stability, Non-approximated Groups and
  High-dimensional Expanders*, IAS, 12 Oct. 2020, key
  `6b1b831e4b3dd5445ae97fcd580d1eb2`.
- Lev Glebsky, *Approximations of Groups, Subquotients of Infinite Direct
  Products and Equations over Groups*, IAS, 25 Nov. 2020, key
  `02dcdc750c5e506010b7ccfae677d308`.
- Alexander Petrov, *Galois Action on Higher Etale Homotopy Groups*, IAS,
  9 Mar. 2026, key `e76667fa26f053d772a9d6b48a8190ab`.

`counterexample: null`
