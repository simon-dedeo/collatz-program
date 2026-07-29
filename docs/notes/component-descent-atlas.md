# The arithmetic descent atlas

## Outcome

The condensed-set viewpoint is useful, but only after changing the local
object. A binary residue cylinder is not enough: it records a compact
`2`-adic neighbourhood but forgets the ordinary lower endpoint on which an
affine Collatz identity is descending. Moreover, multiplication by `3` is a
unit in `Z_2`, so a purely `2`-adic picture can erase the ternary
subprogression created by an odd step.

The correct elementary local object found here is an **oriented arithmetic
ray**

```text
source(k) = sourceBase + sourceStep*k,
mate(k)   = mateBase   + mateStep*k,
```

equipped with a checked Syracuse collision between `source(k)` and `mate(k)`
for every `k`, and with

```text
0 < mateBase < sourceBase,
0 < sourceStep,
mateStep <= sourceStep.
```

Consequently `0 < mate(k) < source(k)` for every ordinary `k`. This retains
the three pieces of information that the problem actually uses:

1. profinite residue information;
2. the `2`/`3` change of slope under a parity word;
3. the Archimedean orientation which says which representative is smaller.

Lean checks this object and the claims below in
`KontoroC/KontoroC/ComponentDescentAtlas.lean`.

## The presheaf operation

An oriented ray restricts along every finite-index tail embedding

```text
k |-> digit + factor*k,       factor > 0.
```

The restricted source and mate are exactly the corresponding subrays, and a
point covered by a restriction is covered by its parent. This is the
elementary presheaf structure behind the proposed arithmetic site. It is
important that source and mate restrict together: projecting to the source
residue alone loses the descent certificate.

Two existing constructions map into this presheaf.

* Every constant-gap `CollisionShadow` is an oriented ray with equal source
  and mate steps.
* Every literal finite parity-word execution `start -> finish` with
  `0 < finish < start` extends to a whole ray. If the word has length `S`
  and `O` odd instructions, its source step is `2^S` and its mate step is
  `3^O`.

The second statement has a useful exact bonus. Lean derives

```text
3^O < 2^S
```

from the existence of the one strict drop; it is not an additional
hypothesis. The affine defect of the word is nonnegative, so an expanding
homogeneous coefficient cannot take one positive source to a smaller
endpoint.

## Exact global endpoint

An **arithmetic descent atlas** is any family of oriented rays covering every
ordinary integer `n > 1`. Strong induction on the ordinary order proves

```text
ArithmeticDescentAtlas rays -> SyracuseConjecture.
```

Conversely, if Syracuse holds, the finite word ending at a strict forward
drop from each `n > 1` supplies such a ray. Lean therefore checks the exact
equivalence

```text
(there exists an arithmetic descent atlas) <-> SyracuseConjecture.
```

This equivalence is a specification, not a proof of Collatz. It identifies
the one genuinely useful global statement: the map from the disjoint union
of descent rays to the discrete ordinary locus is surjective. In sheaf
language, the residual or survivor object must have no ordinary stalk above
`n > 1`.

Two charts are checked explicitly:

```text
2+2k  has mate 1+k,
6k+5  has mate 4k+3.
```

The second is a genuinely mixed `(2,3)` chart: one Syracuse step from
`4k+3` lands on `6k+5`.

## What Scholze's work contributes

The relevant part of Peter Scholze's work is condensed mathematics, jointly
developed with Dustin Clausen, rather than perfectoid spaces or diamonds.
It supplies the right discipline for simultaneously retaining a topological
completion and its discrete ordinary points. Here that discipline prevents
two invalid moves:

* compactness of `Z_2` cannot turn a cover of the discrete natural locus into
  a finite bar;
* inverting `3` in the `2`-adic coordinate cannot be allowed to forget the
  ternary tail or the Archimedean orientation.

The high-leverage Scholze-style target is now precise. Construct a sheaf (or
condensed object) of proof-carrying descent rays on an oriented adelic basis,
with a morphism

```text
DescentWitnesses -> N_{>1,disc}.
```

One must prove that this morphism is an epimorphism after restriction to the
ordinary locus. Equivalently, prove that its survivor cokernel has no
ordinary stalk. Derived or solid methods would become useful only if the
arithmetic collision identities produce a complex for which this vanishing
can be proved locally and then glued. At present no such acyclicity or
surjectivity theorem is known; condensed formalism does not manufacture the
local sections.

Perfectoid tilting and diamonds appear low leverage here. There is no
identified Frobenius, almost-purity statement, or geometric cohomology group
whose vanishing controls Collatz. Introducing them now would add machinery
without supplying the missing arithmetic production rule.

## Where the arithmetic mechanism could be found

Here **arithmetic** means the part that uses special facts about integers and
the particular pair `(2,3)`: divisibility, positivity, valuations, and the
multiplicative independence and relative sizes of powers of `2` and `3`.
Topology can glue already existing charts. It cannot prove that a congruence
class contains a legal Collatz collision with a smaller positive mate.

The most plausible mechanism is not one isolated theorem but a three-stage
rigidity argument.

### 1. A recursive mixed-base transducer produces the charts

Parity cylinders naturally read binary digits. Odd inverse steps impose
ternary divisibility. The desired rule should therefore be a finite set of
*chart types* with unbounded integer state, not a finite list of charts and
not a payload-independent finite automaton. Each transition would solve an
exact affine `S`-unit equation of the form

```text
2^S y - 3^O x = A
```

and either emit a descent ray or pass to finitely many narrower `(2,3)`-adic
subrays with a strictly improved rank. Recursion gives unbounded precision,
so it is compatible with the no-finite-bar theorem.

Component holonomy is the most likely source of these transitions. It
already creates several inverse words with the same linear coefficient and
nearby affine offsets. Subtracting such identities cancels the large payload
and can expose a smaller mate. The live discovery problem is to find the
right normalized gap/rank for which every nonterminal transition decreases.

### 2. `x2/x3` rigidity eliminates a residual exceptional set

If the recursive rules do not visibly cover every branch, form the closed
survivor object of branches which evade all produced charts. The useful
target is to prove that its image on a circle, solenoid, or adelic quotient is
stable under independent multiplication-by-`2` and multiplication-by-`3`
actions. Established topological `x2/x3` orbit rigidity then gives a sharp
dichotomy: a nontorsion survivor tends to force a large or dense invariant
set, which would meet an explicitly excluded open descent chart; torsion
survivors reduce to exact rational residue cases.

There is an equivalent symbolic version. If the survivor language has finite
binary and ternary kernels, Cobham-type rigidity makes it ultimately
periodic. If its generating series satisfies regular `2`- and `3`-Mahler
equations, Mahler rigidity similarly forces rationality. The repo already
uses the Mahler side successfully to close regular counterexample payloads.
The new challenge is to derive one of these finite-kernel or regularity
hypotheses from the holonomy restriction rules without discarding their
unbounded arithmetic state.

This rigidity step is an *amplifier*: it could turn an almost-everywhere or
open-dense descent theorem into an everywhere theorem. It cannot start until
the survivor set is proved to have the two genuine scaling symmetries.

### 3. An Archimedean pressure inequality kills the large alternative

The final input must use the quantitative advantage special to `3x+1`.
For the accelerated odd map, a branch with valuation `a` has homogeneous
slope `3/2^a`. A proof needs to force sufficiently much binary valuation,
on every rigid survivor, that the product of these slopes contracts. This is
where transfer operators, entropy/pressure, or an exact potential may enter.

This clause is also the essential `5x+1` control. A proof based only on
profinite topology, parity, or multiplicative independence would risk
applying unchanged to `5x+1`, where divergent behaviour is known. The valid
mechanism must use an inequality which changes sign when `3` is replaced by
`5`—for example a pressure/drift comparison involving `log 3` versus binary
valuation cost. That is what “arithmetic” means at the global level.

### Secondary source: effective `S`-unit bounds

Baker-type lower bounds for linear forms in `log 2` and `log 3`, or explicit
continued-fraction bounds for their ratio, can control exceptionally long
near-neutral words. They are well suited to turning a symbolic reduction
into finitely many exact residue cases. They do not by themselves select the
parity word followed by every integer, so they are more likely to finish the
argument than to originate it.

In short, the best location to search is the intersection

```text
component-holonomy S-unit identities
    + recursive (2,3)-adic restriction
    + x2/x3 survivor rigidity
    + a 3-specific Archimedean pressure gap.
```

Condensed mathematics supplies the category in which the survivor and its
ordinary stalks can be stated correctly. The new mathematics would be the
mixed-base production/rank theorem and the proof that its survivor really
has enough `x2/x3` symmetry for rigidity to act.

## Research target

Do not search for a finite set of residue classes. The previous condensed
boundary theorem proves that any complete ordinary holonomy bar has
unbounded binary precision. Instead seek a **productive restriction rule**:
from a descent ray and a finite residue obstruction, construct finitely many
strict subrays such that every uncovered ordinary tail enters one of them,
while a well-founded Archimedean charge decreases.

This would turn the current presheaf into a sufficiently acyclic descent
system. The exact proof obligation is arithmetic and can be tested without
importing the full condensed library:

```text
every n > 1 is covered by some constructively generated oriented ray.
```

The formal atlas makes any future proposed production rule immediately
composable with the global termination theorem.

## Machine-checked scope

Lean checks:

```text
AffineDescentRay.restrict
AffineDescentRay.descent
merge_one_of_arithmeticDescentAtlas
syracuseConjecture_of_arithmeticDescentAtlas
ofCollisionShadow
ofForwardDrop
fiveModSixRay
evenRay
syracuseConjecture_iff_forwardDrops
orbitWord_executes
exists_arithmeticDescentAtlas_iff_syracuseConjecture
```

No complete atlas, survivor-vanishing theorem, or proof of Collatz is
claimed.
