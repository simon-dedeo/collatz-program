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

For a finite exact Collatz macro grammar, give every edge `e:i->j` its dyadic
address cost `D(e)` and define

```text
M_s(i,j) = sum_{e:i->j} 2^(-s D(e)).
```

This is the multi-state extension of a Kraft sum.  The exact proposed theorem
is: if a grammar is claimed to cover every state in some dyadic cylinder and
`rho(M_1)<1`, then a finite-depth open subcylinder is uncovered.  A rational
positive Perron supersolution should supply a checkable depth bound.  This
would prune impossible strongly connected components before valuation-
recursive CEGIS.  It cannot exclude a single exceptional atomic ray and is
therefore only an architecture filter.

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
edge flow satisfying the tropicalized resource inequalities.  Solve this
rational polyhedral cone first.  An exact Farkas dual which strictly decreases
on every edge closes the architecture; an extremal feasible ray identifies a
small block support for semantic testing.  A feasible ray is not an ordered
trajectory, and tropicalization can discard the valuation cancellations that
matter.

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
| preflight | Swastik Kopparty, *A local central limit theorem for triangles in a random graph*, key `69956d38eef0339ec0f4207f78499dcd`, S1--S2/S4--S7/E2 | Establish exact modular/lattice support of carry zero conditional on interfaces before any local-limit or entropy argument. | Collatz word contributions are dependent, and a finite zero-carry block does not supply a prefix-compatible infinite orbit. |
| warning | Alexander Gamburd, *Varieties of Markoff Type*, key `76f210c2e1fbd9df473b9ca8890f1e5a`, and Daniel Martin, *Arithmetic on Markoff Surfaces*, key `dfe6aa197a4b6c233c6312357c4670a6` | Use finite residue components and dual obstruction vectors as exact features, but demand a separate edge-lifting and ordinary-integral theorem. | Many finite-field points can have no integer lift; Markoff's reversible group action is unlike the Collatz semigroup. |

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
- Swastik Kopparty, *A local central limit theorem for triangles in a random
  graph*, IAS, 28 Mar. 2016, key `69956d38eef0339ec0f4207f78499dcd`.
- Alexander Gamburd, *Varieties of Markoff Type: Arithmetic, Combinatorics,
  Dynamics*, IAS, 12 Dec. 2022, key `76f210c2e1fbd9df473b9ca8890f1e5a`.
- Daniel Martin, *Arithmetic on Markoff Surfaces*, IAS, 7 Apr. 2026, key
  `dfe6aa197a4b6c233c6312357c4670a6`.

`counterexample: null`
