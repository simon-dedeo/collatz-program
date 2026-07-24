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

Formalizer commit `4b88221` kernel-checks the architecture-independent finite
core.  `witnessPairs` executablely enumerates every exact pair with equal
features and unequal required targets.  Lean proves that it is nonempty
exactly when the target is not functional on the complete finite state set,
and that an empty witness set is equivalent to existence of an actual decoder
on that set.  It also proves that feature refinement preserves functionality
and that an old witness survives every refinement which still fails to
separate its two states.  This certifies the bounded CEGIS logic, not the
pseudo-linear encoding or one precision-uniform Collatz selector.

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

Formalizer commit `cfaa1b2` checks the elementary implication without hiding
the deep number theory as an axiom.  Its explicit hypothesis
`NondegenerateNormalFormsFinite` says that the admissible projectively
normalized nondegenerate fixed-term zero sums have finite range.  Lean then
proves that an infinite normalized family has not merely one exceptional
degeneracy but infinitely many parameters with a nonempty proper vanishing
subsum, hence infinitely many exact two-factor zero-sum partitions.  Applying
this interface to Collatz still requires a concrete fixed-term expansion, a
proved normalization with infinite range, and an imported or independently
formalized fixed-`S` finiteness theorem.

## Lead O: holonomy bounds as a no-go for rational structured selectors

Vesselin Dimitrov, *Arithmetic holonomy bounds and Apéry limits*, IAS,
22 Sept. 2022, key `a7862ba15fb9251b3b0efb9ee64f9d71`, supplies a
four-gate contradiction template for bounded automatic or substitutive
selector schedules.  S3--S4 package rational-coefficient formal power series
with LCM denominator growth and analytic pullbacks at all places.  When total
conformal size strictly beats denominator and approximation cost, the
admissible space is finite-dimensional over `Q(x)`, hence holonomic, with an
explicit dimension bound.  The raw statement and formula were checked at
2,400--2,800 and 2,880--3,260 seconds.

S7 makes the method operational.  A modular overconvergent function contains
one conjecturally irrational 2-adic zeta-five constant.  If that constant were
rational, the function would have rational coefficients with LCM denominator
exponent five and sufficiently large analytic radius.  The bound permits at
most five independent functions, while the function and its derivatives give
six.  The transcript at 3,308--3,670 seconds gives the contradiction, and the
Q&A at 3,692--3,760 limits the claim to zeta five rather than a generic odd
zeta theorem.

For a fixed finite-kernel or constant-length substitution controller, first
construct its exact state-indexed generating system for the normalized
selector tail `r_infinity`.  Ordinary realization requires
`r_infinity=-3^C` in `Q_2`.  A Dimitrov-style exclusion is accepted only if all
four gates are proved:

1. rationality of `r_infinity` forces rational coefficients of one explicit
   auxiliary formal function;
2. its denominator-growth exponent and all-place analytic pullbacks are
   bounded exactly;
3. the explicit conformal-size inequality gives a finite `Q(x)`-dimension
   bound;
4. controller transforms or derivatives give more symbolically independent
   functions than that bound.

This is an architecture synthesizer for **no-go theorems**, not a trajectory
search: every failure names the missing property (non-D-finiteness, excessive
denominators, inadequate overconvergence, or insufficient independent
transforms).  The principal mismatch is severe.  Collatz tails use
symbol-dependent cumulative exponents and may satisfy only a Mahler or
noncommutative system, not a differential equation.  Rationality of one
`Q_2` value does not itself imply rational coefficients or complex
overconvergence; Dimitrov obtains that implication from special modular
structure.  Success would exclude a certified structured selector class, not
construct an escape.

## Lead P: canonical layered routing is matching plus a Hall witness

Stephen Fenner, *Bipartite perfect matching is in quasi-NC*, IAS, 8 Feb. 2016,
key `83398a9013343939af42951fafbfdaa1`, supplies a finite global-routing
dichotomy which is stronger than choosing each macro greedily.  The raw
transcript at 396--1,097 seconds identifies determinant terms with perfect
matchings and shows that two distinct minimum matchings differ on alternating
cycles of zero circulation.  The derived-graph argument and its bipartite
polytope proof occur at 1,249--1,530 and 2,759--3,036 seconds; the weighted
nonbipartite prism at 3,036--3,123 seconds is an explicit counterexample to
extending that lemma to general graphs.

At exact precision `K`, form a genuinely layered bipartite graph

```text
B_K = (source clean windows, target clean windows, certified macro edges).
```

Every edge must already be a literal whole-window-clean, positive-drift
first-passage macro.  A perfect matching is then a collision-free finite
router.  On failure, exact matching returns a Hall-deficient source set
`S` with `|N(S)|<|S|`; its residue/carry signature is a compact architecture
obstruction for CEGIS.  On success, Fenner's modular circulation weights and
lexicographic composition isolate one matching canonically, after which every
edge is replayed exactly.  Thus both outcomes are useful and certified.

Isolation does not create Hall coverage.  Formalizer commit `31b8466` proves
the exact Hall dichotomy and a stronger same-layer no-go: if one finite state
type carries one fixed positive ordinary charge per state, no total literal
recharge self-router exists at all, because every selected edge strictly
increases charge and a finite total function would create an impossible
cycle.  Hence a Hall-deficient source subset must exist; the same-layer lane
is empty before permutation analysis.  The live use is genuinely cross-layer,
with distinct source/target charge interpretations.  Such routers may still
be mutually incompatible or converge only profinitely, so explicit bonding
compatibility and one common zero-carry ordinary-root projection remain
mandatory.

## Lead Q: test binary repair capacity by an exact cokernel

Chao Li, *Level raising mod 2 and arbitrary 2-Selmer ranks*, IAS, 4 Dec. 2014,
key `c559fb878a66ef676aa3a21e64cc8fec`, gives a sharper model for simultaneous
binary repair with one global obstruction.  The raw transcript at
1,710--2,020 seconds shows that mod two erases the ordinary sign distinction
and that naive preservation of the old sign is false.  At 2,250--2,645
seconds the theorem prescribes all signs except one chosen prime of the old
level.  At 2,890--3,370 seconds an auxiliary ramified prime and quadratic
twist make the local choices available, while quadratic reciprocity leaves
exactly one uncontrolled global condition.  The base-change failure at
3,370--3,840 seconds warns that this rank behavior is not automatically
stable under adding a global constraint.

The exact Collatz experiment is purely finite linear algebra.  Index every
binary boundary obligation at one complete height-admissible state set and
replay each clean auxiliary macro to obtain a flip column `v(m)` in
`F_2^I`.  With these columns in `M`, a proposed repair is `Mx=t-b`.  Row
reduction must return either a solution or a cokernel vector proving the
requested target impossible.  The theorem-shaped target is one fixed macro
grammar satisfying

```text
rank(M_H) >= |I_H|-1
```

at every height, with the full cokernel generated by one explicit
mixed-base reciprocity functional and a literal later repair of the one
sacrificed bit.  Li obtains this phenomenon from deformation theory,
Chebotarev, twisting, and reciprocity; none is presently available for
Collatz.  Exact macro effects may also cease to add linearly once positivity,
first passage, and carry are imposed.  Consequently the matrix is a
theorem-driven architecture test, not evidence that its desired rank holds.

Formalizer commit `3e90286` now checks the finite additive alternative over
any field and supplies matrix adapters over `F_2`: either an exact coefficient
vector realizes the requested target, or a linear functional annihilates
every macro-effect column while detecting that target.  The latter is a
genuine obstruction for the supplied table.  The positive branch still does
not prove that the chosen macros compose literally, remain first-passage and
positive, or have zero ordinary carry; the all-height rank claim also remains
open.

## Lead R: compress a stationary controller to its exact boundary determinant

Charles Bordenave, *Random Perturbation of Toeplitz Matrices*, IAS, 20 Oct.
2025, key `7d917e77db1f51976d3253a965edd879`, separates a stable
translation-invariant bulk from a finite-rank boundary defect.  At
1,173--1,739 seconds the Laurent-symbol winding number distinguishes
well-conditioned and exponentially ill-conditioned Toeplitz regimes.  At
1,739--2,442 seconds a banded Toeplitz matrix is written as a circulant matrix
minus `PQ`, with `rank(PQ)` bounded by the band width; Sylvester's identity
then reduces the large characteristic determinant to

```text
det(S-z-PQ) = det(S-z) det(I-Q(S-z)^(-1)P).
```

The second determinant has only the boundary-defect dimension.  The
higher-adjugate analysis at 2,456--3,232 seconds explains why its first
nonzero term is controlled by the defect kernel dimension.

This gives an exact preflight for a genuinely stationary finite-memory
Collatz controller.  If its bounded transition equations can be proved to be
a banded translation-invariant bulk plus a fixed-rank initial/terminal carry
correction, compute the small Schur/Sylvester determinant exactly over the
chosen rational or finite coefficient ring.  A nonzero boundary minor is a
compact obstruction to the claimed global kernel; a zero with an extracted
kernel vector gives only a candidate controller, which must still be decoded
and replayed.  If the defect rank grows with precision, the architecture has
failed the promised finite-boundary compression rather than found a fixed
rule.

The numerical warning is more immediate.  At 153--490 seconds an exactly
nilpotent Toeplitz shift, whose true eigenvalues are all zero, produces an
apparently structured near-root-of-unity numerical spectrum after a basis
change.  Therefore floating eigenvalues or pseudospectra of a nonnormal
Collatz transfer matrix are discovery diagnostics only.  The talk's random
noise regularization, asymptotic outlier process, and winding theorem do not
transfer unless their full Toeplitz and analytic hypotheses are first proved.

## Lead S: pull every fine repair through the exact coarse cylinder

Scott Armstrong, *Renormalization Group and Homogenization*, IAS, 1 Dec.
2023, key `df980373a403d081ec128e7ac7fde48d`, identifies the main failure mode
of a naive multiscale sum.  At 1,487--1,977 seconds the proof renormalizes from
fine to coarse scale while controlling the product of finite errors.  At
2,515--3,050 seconds the scale recurrences require enough separation for each
homogenization step to finish.  Most importantly, at 3,457--3,909 seconds the
naive sum of fine shears fails because the coarse drift washes them out; the
repair is to compose every new fine shear with the inverse flow of the already
constructed coarse field.

The Collatz version is exact in kernel-checked theorem
`executes_iff_canonical_family` (`OutwardCylinderRenewal`), and formalizer
commit `9412825` now exposes the direct repair-veto interface.  For a parity
word `w`, with `S=|w|` and `O` odd steps, every literal execution is uniquely
parameterized by

```text
source = r_w + 2^S t,
target = b_w + 3^O t.
```

Thus deeper dyadic choices inside the same coarse cylinder cannot alter the
target modulo `3^O`.  Pulling a desired output correction `Delta` back through
the coarse affine map would require an input change
`2^S Delta / 3^O`, which is integral only if `3^O` divides `Delta`.  Unlike
Armstrong's flow, the Collatz semigroup supplies no free inverse coordinate
change.  Lean theorem `no_targetRepair_of_not_threePow_dvd` returns the exact
CEGIS rejection, and `targetIncrement_eq_zero_of_lt_threePow` proves that a
nonnegative correction below the frozen modulus must be zero.  Signed or
word-changing repairs remain outside this statement.

This is a direct search restriction.  A coherent nested-cylinder beam must
store the post-prefix ternary boundary residue and enforce its bonding law;
it may not choose a new low-`3`-adic optimum independently at greater dyadic
precision.  An outer CEGIS architecture is rejected at the first state where
it promises to repair a frozen low ternary digit using only deeper seed bits.
Conversely, a recurring compatible residue is a compact feature worth fitting.
The theorem gives cross-scale coherence, not positive drift, invariant
closure, bounded ordinary carry, or an infinite ordinary seed.

## Lead T: lift a selector by killing its exact carry-extension class

Vincent Pilloni, *Frobenius Lifting and a Geometric Theory of Companion
Forms*, IAS, 8 Dec. 2025, key `2b732a2bdb7cecc9e5a84fed018cce79`,
turns a lifting question into a finite obstruction class rather than a search
over all lifts.  At 645--1,210 seconds the filtered inverse-Cartier component
is identified with the obstruction to lifting Frobenius modulo `p^2`.  At
1,790--2,480 seconds the formula `f -> f^p+p*g(f)/Ha` makes `g mod Ha` the
derivation measuring failure to extend, and an extension complex retains the
integral data.  The Q&A at 3,410--3,580 seconds explicitly says iteration to
higher powers of `p` has not been worked out.

For a Collatz policy valid modulo `2^k`, fix a complete finite branch chart
and canonical lifts of its states to `2^(k+1)`.  Literal replay of each
selected edge gives a normalized new-bit defect `kappa_k(e)`.  Changing the
state lifts by bits `u(s)` changes that defect by a computable affine
coboundary

```text
(delta u)(e) = u(target(e)) - A_e u(source(e))  in F_2.
```

The one-level lift exists only if `delta u=kappa_k`, together with all literal
branch and positivity constraints.  Exact row reduction returns either the
correction cochain or a dual cocycle annihilating `im(delta)` and pairing
nontrivially with `kappa_k`; the latter is a compact carry obstruction for
CEGIS.  This specializes the Chao Li rank test to coherence between adjacent
precisions.  It is valid only on a certified branch chart, and solvability at
each level still needs compatible choices, an ordinary-root bound, and
positive outward growth.  Pilloni's own theorem supplies no unbounded
iteration.

## Lead U: exact tower completion is a capacitated Hall problem

Petr Naryshkin, *Topological Versions of the Rokhlin Lemma*, IAS, 27 Jan.
2026, key `e642e869e0f7b849949f65d2c14e605a`, distinguishes an almost-cover from
an exact decomposition.  At 800--1,360 seconds clopen Rokhlin castles leave a
remainder uniformly small for every invariant measure.  At 1,330--1,980
seconds comparison partitions and translates that remainder into available
tower space; in the zero-dimensional setting this is equivalent to empty
remainder.  At 1,940--2,570 seconds a nonempty remainder leaves the associated
finite-dimensional unit at norm distance one from the full unit, so
measure-small cannot be silently promoted to exact.

At one bounded Collatz precision, let the bases and literal intermediate
states of clean first-passage macros form disjoint finite towers.  Connect each
uncovered state to every capacity-limited clean top slot reachable by an
exactly replayed repair macro.  Maximum flow either absorbs the entire
remainder or returns a Hall/min-cut source set with insufficient legal target
capacity.  This is a compact carry/interface obstruction, not a trajectory
minimum.  Across precisions, every tower must refine its predecessor, old
levels must project literally, a nested base atom must persist, and some tower
height must tend to infinity.  This makes the user's counter-growth condition
precise: unbounded compatible heights are necessary, but even empty finite
remainders do not imply one ordinary orbit without canonical-root
stabilization.  The source concerns invertible amenable group actions, whereas
Collatz macros are partial noninvertible semigroup maps; the max-flow test is a
new exact finite substitute, not a consequence of the Rokhlin theorem.

## Lead V: patch the obstruction complex, not only its local solutions

George Boxer, *Modularity lifting theorems for non-regular symplectic
representations*, IAS, 7 Nov. 2017, key
`82d072493863a41d68666b415a295ec7`, isolates a lifting failure which is
invisible if one records only successful sections.  At 2,219--2,350 seconds,
the cokernel of reduction is exactly the torsion in `H^1`, so a mod-`p`
solution need not lift even though the visible `H^0` table looks correct.  At
2,922--2,976 seconds the Calegari--Geraghty response is to patch the whole
cohomology complex.  The full higher-degree strategy is unavailable for the
`GSp_4` problem (3,115--3,338 seconds), but Boxer explains at
3,374--3,790 seconds that two-degree complexes can be patched on restricted
local charts and then combined by a separate gluing argument.

The exact bounded Collatz transfer is a selector-architecture test.  Cover the
complete height-admissible state set by certified valuation/residue/carry
charts.  Let `C^0` contain the chartwise correction data and let `C^1` contain
all replayed overlap disagreements and edge carry defects.  Do not accept
nonempty local solution tables as evidence of a global policy: solve the
single exact equation

```text
delta u = kappa.
```

The general finite cokernel theorem in formalizer commit `3e90286`, and its
policy-lift specialization in `b4c5a7d`, already return either a correction or
a dual functional annihilating every coboundary while detecting `kappa`.
Thus the first cohomology obstruction is an exact CEGIS witness.  If a proposed
architecture needs higher overlap degrees, those degrees must be represented
rather than silently projected away; a useful architecture should have a
uniformly bounded complex and one literal gluing rule.

This imports no modularity theorem.  Boxer's positive result uses Galois
representations, big residual image, Taylor--Wiles patching, ordinary
projectors, and `p`-adic gluing.  In Collatz, every local cochain entry must
already decode to a positive first-passage macro, and overlap equality must
include the word, ternary boundary residue, and ordinary-root carry.  Exact
solvability at one finite bound, or even independently at every bound, still
does not supply compatible bonding maps or one ordinary integer seed.

## Lead Y: consume a finite rank, then prove a literal counter reset

Ilya Volkovich, *Upper and Lower Bounds for the Linear Ordering Principle*,
IAS, 9 Feb. 2026, key `558421665a5af3c98104e05ef9732e36`,
starts from the exact total-search dichotomy: a succinct alleged strict order
must yield either its minimum or an order-law violation (139--824 seconds).
At 3,560--3,898 seconds, once violations are excluded, order rank can be
halved by adaptively restricting a bit to the subcube of smaller average
rank; after at most `n+1` rounds the rank is zero.  The implementation uses
approximate counting through a PromiseSBP oracle, and the Q&A explicitly
leaves a nonadaptive version open (3,898--4,263 seconds).

For Collatz, let `S_(K,c)` be the complete finite set of exact reset states at
precision `K` and counter layer `c`.  A proposed architecture supplies a fixed
finite-description comparison relation and literal macros which send every
nonminimum state to a strictly smaller one.  Exact enumeration or checkable
SAT certificates must return either the first irreflexivity,
incomparability/asymmetry, or transitivity witness, or the genuine minimum.
The crucial additional obligation is

```text
minimum in S_(K,c)  --clean literal reset-->  S_(K,c+1).
```

With all hypotheses checked, descent reaches the minimum in at most
`|S_(K,c)|-1` selected steps and the reset makes the counter grow.  A missing
minimum reset is the architecture's smallest closure failure; search effort
should be concentrated there rather than on already ranked interior states.

This is still bounded rank-or-refute, not an escape theorem.  The source's
approximate ranks are not exact arithmetic certificates.  One fixed order and
reset law must work for every counter, commute with precision projections,
replay positive first-passage words with zero carry, and share one ordinary
positive seed.  Without those unbounded obligations, the construction is only
a family of finite rankings.

## Lead W: demand integral principality before trusting a valuation potential

Renzo Cavalieri, *Tropical Psi Classes and Tropicalizations of Psi Classes*,
IAS, 4 Feb. 2025, key `68250a0dd2074dd65c33b744c55b11a4`,
distinguishes a coherent-looking piecewise-linear class from one which
actually lifts.  At 1,336--1,730 seconds a tropical family carries an
integral-affine sheaf and the combinatorial psi class detects slope changes,
but no algebraic identification has yet been proved.  At 1,793--2,299 seconds
principal boundary divisors define affine functions, and a line bundle is
visible near a boundary stratum only under the stronger
``combinatorially-principal'' condition.  The conormal/psi comparison at
2,303--2,585 seconds holds precisely after that condition; the Q&A at
2,780--2,985 seconds stresses that non-boundary algebraic information can be
missed.

For a synthesized Collatz potential, build the finite face complex of its
fixed valuation, branch, and carry charts.  On every face `tau`, put the
primitive normal rays in an integer matrix `A_tau` and the claimed slope jumps
in `b_tau`.  The proposed chart formulas can be restrictions of one integral
affine correction only if

```text
A_tau * a_tau = b_tau  over Z.
```

Smith normal form gives an exact synthesis gate: either produce `a_tau`, or
return a left-kernel or invariant-factor congruence which proves nonprincipal
holonomy.  Corrections on overlapping stars must then pass the two-term
integer gluing test from Lead V.  This rejects a false valuation invariant
without extending any trajectory.

Formalizer commit `64af217` kernel-checks the algebraic boundary over the
integers: principality is equivalent to vanishing of the cokernel class, and
either a mapped left obstruction or a modular obstruction refutes an integer
solution.  The modular certificate may use a composite modulus, so it detects
torsion failures such as `2*a=1` which a rational left kernel misses.  Lean
does not yet generate Smith normal form executably; a search worker must emit
the proof-carrying witness for verification.

Passing principality is only a preflight.  The resulting literal potential
must include affine translation and ordinary carry, prove the macro inequality
on the full first-passage alphabet, and have sublevel sets which bound the
canonical root address while allowing charge to diverge.  Cavalieri begins
with a toroidal algebraic scheme and an actual line bundle; no theorem says
the Collatz chart complex has such a lift.  The search target is therefore an
integer-principal **and coercive** mixed-valuation potential, not another fit
of branchwise slopes.

## Lead X: enumerate motif grammars for locally consistent coarse states

Facundo Mémoli, *Hierarchical clustering on asymmetric networks*, IAS, 7 Nov.
2015, key `d2d50ba64aefb3df34cc2d9d058a8742`, replaces an arbitrary hierarchy by
an axiomatized architecture.  At 1,372--1,685 seconds weight-nonincreasing
maps make networks into a category and a clustering rule is required to be
functorial.  With the prescribed two-node behavior, every such rule lies
between two explicit asymmetric extremal methods (1,685--1,799 seconds).
Excision means that rerunning the method on one dendrogram block reproduces
the restricted hierarchy (2,124--2,299 seconds).  Finally, at
2,442--3,221 seconds, factoring through symmetric single linkage by a family
of finite directed motifs is equivalent to excision plus linear scale
invariance.

This suggests an exact outer loop for bounded selector CEGIS.  Give the
complete state table an asymmetric integer or rational dissimilarity, such as
the least certified resource threshold at which one cross-layer interface can
simulate another.  Propose a finite motif family `Q`, compute exactly the
minimum expansion factor of every motif map covering each state pair, and
apply single linkage to the resulting symmetric weights.  Rank `Q` by number
and size of motifs.  The architecture must satisfy:

```text
weight-decreasing maps preserve clusters;
positive rescaling only reparametrizes the hierarchy;
every extracted block reclusters to its restriction.
```

Failure returns a smallest exact morphism or block violating functoriality or
excision; passing extracts a compact motif grammar rather than a residue
lookup table.  The characterization theorem justifies this search only for
architectures satisfying the stated axioms; nonexcisive rules lie outside it.

The hierarchy is a compression device, not dynamics.  Motif occurrence need
not decode to a legal macro, and a cluster need not contain any compatible
nested ray.  Moreover, finite same-layer literal recharge is acyclic by
commit `31b8466`, so Mémoli's loop-based lower method has no nontrivial literal
same-layer component.  Use motifs only on cross-layer interfaces or exact
feature relations, then replay every chosen transition and separately prove
unbounded counter growth and ordinary-root stabilization.

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
| warning / finite-shadow kernel audit | Hélène Esnault, *Integrality Properties of Topological Fundamental Groups*, key `d3a6c2def4c89952472373e2cb74937b`, S3/S8 and the singular-surface example, 1,330--1,577, 3,109--3,230, and 3,665--3,778 s | Require every residue-, representation-, or spectrum-based controller certificate to be accompanied by literal word/carry replay and an injectivity or kernel-triviality proof for the ordinary-seed coordinate.  The talk gives two precise failure models: linear representations factor through a profinite completion and can miss its kernel, while Frobenius characteristic polynomials can miss discrete monodromy around a singular exceptional cycle. | The positive integrality theorem assumes a smooth quasiprojective variety and uses companions, arithmetic/geometric Langlands, and compact `l`-adic groups.  A stabilized `l`-adic lattice is not one ordinary integer seed, and the talk supplies no Collatz kernel theorem. |
| reject entropy-only persistence / conditional continuation test | Matthias Meiwes, *C0 Stability of Topological Entropy for 3-Dimensional Reeb Flows*, key `38037e3d560c09b82b6c2c0beae915f0`, S3--S8/E1--E4, 1,760--3,640 s | Before transferring exponential clean-macro growth from precision `k` to `k+1`, certify a finite-state lift transducer whose outputs project literally to their inputs, preserve positivity/first passage and distinct route classes, and increase length by at most one uniform affine bound.  Failure returns the first collision, illegal edge, or carry merger. | The Reeb theorem uses exact symplectic cobordisms, hypertightness, nondegeneracy, holomorphic-curve compactness, and isotopy.  The new link may change components and unique classes may cease to be unique.  Increasing Collatz precision is not a `C0` perturbation; entropy without a uniform compatible transducer proves no nested ordinary ray. |
| exact finite directed-search certificate | Michael Krivelevich, *Paths and cycles in expanders*, key `234d35e01cff3446271f60df1cf2d860`, S2--S7/E2--E3/E5--E6, 563--3,376 s | Formalizer commit `c17eb6f` proves the sound directed specialization: minimum retained out-degree at least `d` in a loopless exact reset graph gives a replayable vertex-simple path of exactly `d` edges; failure returns an exact vertex with out-degree below `d`. | The initially proposed arbitrary `k`-set out-neighborhood/minimum-cut implication omitted a directed separator/active-stack term and is withdrawn.  Even the corrected one-scale paths need not bond across scales or share an ordinary seed. |
| conditional finite balancing | Nikhil Bansal, *On Beck-Fiala and Komlós Conjectures*, key `d676051521258c7e0c738f0c67a82327`, S2--S7/E4--E6, 923--3,528 s | For an independently proved library of paired macros with identical exact boundary action, put resource differences on dyadic interval rows and use exact sign/MILP replay to bound every prefix; SDP is discovery only. | Collatz legality is adaptive and exact, while discrepancy rounds a fixed real matrix.  Commit `af90376` makes the identical-fixed-endpoint pair gate empty for distinct literal macros; only a genuinely parametric/coarser interface could remain. |
| tropical realizability gate | Felipe Rincón, *Tropical Ideals*, key `3fed4a408fef28d0dd296c03734f33e6`, S2--S6, 606--3,272 s | Treat support/circuit constraints across growing term degree as a matroid tower, but require coefficient-level multiplication closure.  Multiply every forced low-degree Collatz relation by the allowed monomials and use the first forbidden support, rank, or tensor-product obstruction as an exact architecture witness. | The talk constructs compatible elimination-closed matroid towers with Hilbert polynomial and balanced tropical variety which still come from no classical ideal.  Genuine Collatz identities are realizable automatically; this gate rejects only tropical/valuation relaxations. |
| exact finite path certificate | Yuval Wigderson, *Color-avoiding Paths*, key `a153fe90d9b0b97f818aadc105403504`, S3/S6--S7, 911--1,442 and 3,004--4,109 s | In any exact oriented clean-macro graph, take an inclusion-maximal acyclic subgraph.  Longest-path labels properly color the full underlying graph, so an exact certificate `chi(U)>=r` yields a replayable directed path on at least `r` vertices. | The headline color theorem needs a tournament or near-complete digraph and explicitly fails for sparse forward bipartite examples.  Chromatic complexity gives only a finite path and no cross-scale or ordinary-seed compatibility. |
| warning / mixed-place preflight | Matthew Emerton, *Local-Global Compatibility in the p-Adic Langlands Program for GL(2) over Q*, key `054ae194a1654549d78821a8534db66b`, S3--S7/E4--E5, 1,650--3,740 s | Before multiplying separate dyadic, triadic, and Archimedean route counts, build the exact joint compatibility tensor and exhibit a nonzero flattening minor whenever local choices do not recombine into literal macros. | Emerton's positive factorization uses linear completed cohomology, commuting group actions, and `p>2`, excluding the controlling dyadic place.  It is rejected as a construction analogy; vanishing bounded minors would still not prove an unbounded factorization or ordinary seed. |
| conditional routing certificate | Julia Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*, key `d9f6f01263bfc6a0d0fc3a35eccb90ae`, S1--S7/E6--E7, 15--3,658 s | Use exact tree-decomposition bags as compact interface bottlenecks, or require an explicitly oriented path-of-sets: ordered disjoint clean clusters, disjoint forward bundles, and an exact ledger proving a positive route reservoir survives every stitch. | The theorem is undirected; minors and well-linkedness erase direction, word order, drift, and carry.  High finite treewidth is not infinity, low treewidth does not exclude long paths, and systems at successive precisions may be incompatible. |
| incremental implementation of the Hall lane | Vijay Vazirani, *Matching: A New Proof for an Ancient Algorithm*, key `f72f878a92a697521442ae7e19a1e359`, S1--S7/E1--E8, 192--4,135 s | Maintain a cross-layer bipartite clean router by exact alternating-path flips; one augmentation covers one more source while preserving slot capacities.  If none exists, verify the reachable Hall-deficient source set.  Record every flip as a replayable router-repair certificate. | This refines the already formalized Hall alternative but creates no legal macro edge.  Merging source and target roles invalidates naive BFS: the talk requires even/odd levels, tenacity, bases, blossoms, and a lower-tenacity-first schedule, after which Collatz direction must still be restored.  Finite routers need compatible bonding and an ordinary root. |
| reject average equidistribution as construction / support-sensitive Fourier audit | Adam Harper, *A Zero-Density Approach to Smooth Numbers*, key `5a39422d011500985ebd93d55b08b76c`, S2--S8/E1/E3--E4, 429--3,337 s | For each complete finite macro family, compute exact character sums of its canonical address/carry outputs and retain any large low-conductor coefficient as a selector feature or residue obstruction.  If a uniform distribution claim is pursued, split the conductor range and prove support-sensitive bounds; use the exact saddle-point minimizer of the sparse generating function instead of a dense entropy surrogate. | The theorem counts all `y`-smooth integers on average over moduli.  Collatz coefficients are selected affine combinations of powers of `2` and `3`, not an Euler-product set, and one exceptional compatible path is the target.  The talk explicitly shows that the generic large sieve ignores sparse support.  Even perfect average equidistribution supplies neither nested bonding nor an ordinary seed. |
| closed executable word quotient / retained exact kernel diagnostic | Oliver Schlotterer, *Combinatorics on Words in String Amplitudes*, key `95d596e29fb322de3617a3b08d0c55a2`, S2--S8/E1--E6, 321--4,193 s | For a finite linearized macro evaluator `E : Z<words> -> M`, admit a proposed shuffle, bracket, or Jacobi relation module `Q` only after exact arithmetic proves `Q <= ker(E)`.  Store the relation and kernel certificate as aggregate compression, but keep every supported literal word for legality and seed/carry replay.  A failed relation returns its least nonzero evaluated combination. | In the talk, pure shuffles vanish under the Parke--Taylor evaluator and the `s`-bracket becomes a total derivative whose boundary terms vanish; those are the theorems that justify the quotient.  Ordered Collatz words are deterministic programs and have no analogous linear evaluator theorem.  At fixed positive recharge endpoints, commit `af90376` already proves that two literal first-passage macros have identical block lists, so the quotient cannot create a new executable alias.  The auxiliary-point KZ recursion is only an analogy until an exact flat compatible depth-lift is proved. |
| selector-architecture CEGIS / symmetry-fiber gap | Jan Vondrák, *Hardness of Randomized Truthful Mechanisms for Combinatorial Auctions*, key `c9b176433a3ce4d2c4a2c7732ca36f6a`, S1--S8/E1/E3, 53--3,889 s | On the complete bounded exact state set, group states by the proposed feature map `phi`.  Compute every state's legal positive-margin macro set.  If all sets are nonempty but their intersection on one `phi`-fiber is empty, return that fiber as an exact proof that the architecture erased a necessary residue/carry coordinate.  A rational robust-policy LP and dual witness quantify the same gap. | The source lower bound also requires strategic truthfulness, submodular valuations, random-relabeling oracle indistinguishability, taxation, and coding; none transfers.  The retained finite intersection test is elementary and rejects only `phi`, not richer selectors.  A randomized positive expected margin is not a literal path, and per-layer success supplies neither compatible counter growth nor an ordinary root. |
| recursive-architecture CEGIS / one-sided certificate gate | Mika Göös, *Lower Bounds for Clique vs. Independent Set*, key `afefbda709ba39acd2b7a84f4f022589`, S1--S7/E2/E4/E6, 14--3,214 s | Treat every nonzero grammar symbol as a particular replayed forward macro and `0` as absence of a certified lift.  SAT-check unambiguous positive certificates, compute exact weighted hitting-set certificates for zero, and reject already at depth two if a positive parent certificate invokes any zero child.  Increase recursion depth only after this one-sided composition gate passes. | The talk's three-bit example proves that ordinary self-composition need not amplify a positive/zero certificate gap; the repair uses a multivalued projective-plane pointer function.  Its later communication lifting uses a specific inner-product gadget and cannot be imported.  A large cost to certify failure is not evidence that a legal macro exists, and finite positive certificate trees may still be incompatible or merely profinite. |
| exact linear conjugacy diagnostic / reject non-atomic path transfer | Wilhelm Schlag, *On Structure Results for Intertwining Operators*, key `46182cb7217bb70e1c90e2f8e7ae016b`, S4--S8/E5--E7, 1,120--3,570 s | For a complete bounded transition matrix and a declared finite algebra of literal state symmetries, solve `T W = W T0` over the rationals, verify it entrywise, prove exact invertibility, and check algebra closure under every recursive contraction.  Transfer a deterministic path only when both `W` and `W^-1` are positive monomial state maps preserving literal directed edges. | Schlag's wave operator is an average of translations/reflections and its Wiener theorem depends on analytic decay, regular zero energy, and a larger contraction algebra.  A signed or dense invertible intertwiner sends a seed atom to a superposition, so it can transfer spectra or linear inequalities but not an integer execution.  Compatible atomic intertwiners at all heights and an ordinary root remain separate. |
| rejected direct transfer / conditional filtered-complex omission certificate | Viktor Ginzburg, *Invariant Sets and Hyperbolic Periodic Orbits*, key `3007cd718c9c9bfa85f714e21232adbf`, S2/S4--S8/E6--E9, 420--3,490 s | Only after an independently defined finite literal route complex has a machine-checked differential with `d^2=0` and a certified contracting homotopy, combine exact boundary depth, crossing-filtration gap, and grading separation to prove that a proposed finite route grammar omitted a homology class. | The source differential, vanishing homology, crossing energy, and index recurrence are Floer-theoretic theorems; the present Collatz graph has no analogue.  Relabeling an adjacency matrix as a differential would be invalid.  Even a valid finite contradiction would force refinement of a grammar, not an infinite orbit; compatible classes, counter growth, carry bonding, and an ordinary root would still be missing. |

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
- Vesselin Dimitrov, *Arithmetic holonomy bounds and Apéry limits*, IAS,
  22 Sept. 2022, key `a7862ba15fb9251b3b0efb9ee64f9d71`.
- Michael Krivelevich, *Paths and cycles in expanders*, IAS, 10 Feb. 2020,
  key `234d35e01cff3446271f60df1cf2d860`.
- Nikhil Bansal, *On Beck-Fiala and Komlós Conjectures*, IAS, 10 Nov. 2025,
  key `d676051521258c7e0c738f0c67a82327`.
- Felipe Rincón, *Tropical Ideals*, IAS, 30 Jan. 2025, key
  `3fed4a408fef28d0dd296c03734f33e6`.
- Stephen Fenner, *Bipartite perfect matching is in quasi-NC*, IAS, 8 Feb.
  2016, key `83398a9013343939af42951fafbfdaa1`,
  https://www.ias.edu/video/csdm/2016/0208-Fenner.
- Yuval Wigderson, *Color-avoiding Paths*, IAS, 2 Mar. 2026, key
  `a153fe90d9b0b97f818aadc105403504`,
  https://www.ias.edu/video/color-avoiding-paths.
- Chao Li, *Level raising mod 2 and arbitrary 2-Selmer ranks*, IAS, 4 Dec.
  2014, key `c559fb878a66ef676aa3a21e64cc8fec`,
  https://www.ias.edu/video/puiasnts/2014/1204-ChaoLi.
- Matthew Emerton, *Local-Global Compatibility in the p-Adic Langlands
  Program for GL(2) over Q*, IAS, 3 Nov. 2010, key
  `054ae194a1654549d78821a8534db66b`,
  https://www.ias.edu/video/galois/emerton2.
- Charles Bordenave, *Random Perturbation of Toeplitz Matrices*, IAS, 20 Oct.
  2025, key `7d917e77db1f51976d3253a965edd879`,
  https://www.ias.edu/video/random-perturbation-toeplitz-matrices.
- Scott Armstrong, *Renormalization Group and Homogenization*, IAS, 1 Dec.
  2023, key `df980373a403d081ec128e7ac7fde48d`,
  https://www.ias.edu/video/renormalization-group-and-homogenization.
- Vincent Pilloni, *Frobenius Lifting and a Geometric Theory of Companion
  Forms*, IAS, 8 Dec. 2025, key `2b732a2bdb7cecc9e5a84fed018cce79`,
  https://www.ias.edu/video/frobenius-lifting-and-geometric-theory-companion-forms.
- Petr Naryshkin, *Topological Versions of the Rokhlin Lemma*, IAS, 27 Jan.
  2026, key `e642e869e0f7b849949f65d2c14e605a`,
  https://www.ias.edu/video/topological-versions-rokhlin-lemma.
- Julia Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*, IAS, 10 Feb.
  2014, key `d9f6f01263bfc6a0d0fc3a35eccb90ae`,
  https://www.ias.edu/video/csdm/2014/0210-JuliaChuzhoy.
- Alexander Lubotzky, *Stability, Non-approximated Groups and
  High-dimensional Expanders*, IAS, 12 Oct. 2020, key
  `6b1b831e4b3dd5445ae97fcd580d1eb2`.
- Lev Glebsky, *Approximations of Groups, Subquotients of Infinite Direct
  Products and Equations over Groups*, IAS, 25 Nov. 2020, key
  `02dcdc750c5e506010b7ccfae677d308`.
- Alexander Petrov, *Galois Action on Higher Etale Homotopy Groups*, IAS,
  9 Mar. 2026, key `e76667fa26f053d772a9d6b48a8190ab`.
- Hélène Esnault, *Integrality Properties of Topological Fundamental
  Groups*, IAS, 19 June 2023, key `d3a6c2def4c89952472373e2cb74937b`,
  https://www.ias.edu/video/integrality-properties-topological-fundamental-groups.
- George Boxer, *Modularity lifting theorems for non-regular symplectic
  representations*, IAS, 7 Nov. 2017, key
  `82d072493863a41d68666b415a295ec7`,
  https://www.ias.edu/video/MotivesGaloisRepsandCohomology/2017/1107-GeorgeBoxer.
- Renzo Cavalieri, *Tropical Psi Classes and Tropicalizations of Psi Classes*,
  IAS, 4 Feb. 2025, key `68250a0dd2074dd65c33b744c55b11a4`,
  https://www.ias.edu/video/tropical-psi-classes-and-tropicalizations-psi-classes.
- Matthias Meiwes, *C0 Stability of Topological Entropy for 3-Dimensional
  Reeb Flows*, IAS, 24 Nov. 2023, key
  `38037e3d560c09b82b6c2c0beae915f0`,
  https://www.ias.edu/video/c0-stability-topological-entropy-3-dimensional-reeb-flows.
- Facundo Mémoli, *Hierarchical clustering on asymmetric networks*, IAS,
  7 Nov. 2015, key `d2d50ba64aefb3df34cc2d9d058a8742`,
  https://www.ias.edu/video/wtiocs-M%C3%A9moli.
- Vijay Vazirani, *Matching: A New Proof for an Ancient Algorithm*, IAS,
  10 Dec. 2012, key `f72f878a92a697521442ae7e19a1e359`,
  https://www.ias.edu/video/1213/csdm/VijayVazirani1210.
- Ilya Volkovich, *Upper and Lower Bounds for the Linear Ordering Principle*,
  IAS, 9 Feb. 2026, key `558421665a5af3c98104e05ef9732e36`,
  https://www.ias.edu/video/upper-and-lower-bounds-linear-ordering-principle.
- Adam Harper, *A Zero-Density Approach to Smooth Numbers*, IAS, 27 Mar.
  2013, key `5a39422d011500985ebd93d55b08b76c`,
  https://www.ias.edu/video/ANtheory/1213/0327-AdamHarper.
- Oliver Schlotterer, *Combinatorics on Words in String Amplitudes*, IAS,
  21 Nov. 2024, key `95d596e29fb322de3617a3b08d0c55a2`,
  https://www.ias.edu/video/combinatorics-words-string-amplitudes.
- Jan Vondrák, *Hardness of Randomized Truthful Mechanisms for Combinatorial
  Auctions*, IAS, 26 Mar. 2012, key `c9b176433a3ce4d2c4a2c7732ca36f6a`,
  https://www.ias.edu/video/csdm/vondrak.
- Mika Göös, *Lower Bounds for Clique vs. Independent Set*, IAS, 23 Feb.
  2015, key `afefbda709ba39acd2b7a84f4f022589`,
  https://www.ias.edu/video/csdm/2015/0223-MikaGoos.
- Wilhelm Schlag, *On Structure Results for Intertwining Operators*, IAS,
  29 Mar. 2017, key `46182cb7217bb70e1c90e2f8e7ae016b`,
  https://www.ias.edu/video/analysis/2017/0329-WilhelmSchlag.
- Viktor Ginzburg, *Invariant Sets and Hyperbolic Periodic Orbits*, IAS,
  10 May 2024, key `3007cd718c9c9bfa85f714e21232adbf`,
  https://www.ias.edu/video/invariant-sets-and-hyperbolic-periodic-orbits.

`counterexample: null`
