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

## Lead A: a recursively parameterized valuation selector

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
open-hole theorem for any fixed finite congruence-cylinder selector.

**Exact CEGIS obligation.** Add grammar nodes

```text
Layer(L,a,regular_table,exceptional_child)
```

with exact semantics: inspect `L(X) mod 3^a`; dispatch on nonexceptional
residues; on the unique divisible class replace the designated coordinate by
`L(X)/3^a` and enter `exceptional_child`.  Enumerate only small finite graphs
of these nodes.  For every candidate, return the least ordinary state where
the selected first-passage word is illegal or invariant closure fails.

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

## Negative lessons already extracted

- Greenfeld's hierarchy explains why a finite residue table is the wrong
  endpoint: a finite *recursive* table can have unbounded scale.
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

`counterexample: null`
