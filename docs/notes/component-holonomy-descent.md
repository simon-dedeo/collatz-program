# Component holonomy and a new descent interface

**Status (2026-07-29).**  The finite identities and the five-consecutive-points
theorem below are kernel-checked in
`KontoroC/KontoroC/CollatzComponentHolonomy.lean`.  They do **not** prove the
Collatz conjecture.  The proposed holonomy-descent principle is an open
research program, stated here so that its exact proved input and missing
global step cannot be confused.

## 1. Change the object: components, not trajectories

Write

```text
T(n) = n/2             (n even),
T(n) = (3n+1)/2        (n odd).
```

Say that `x ~ y` when some forward iterate of `x` equals some forward iterate
of `y`.  This is the connected-component relation of the undirected Syracuse
functional graph.  The usual question follows one forward ray.  The new idea
is to exploit *holonomy*: two different legal inverse words can have the same
linear part but different affine offsets.  If those offsets differ by the
denominator `3^m`, the corresponding inverse images differ by one.

The familiar first collision is

```text
T^3(8k+4) = T^3(8k+5) = 3k+2.
```

Elia and Tucker studied this adjacent-pair phenomenon in
[Consecutive Integers and the Collatz Conjecture](https://arxiv.org/abs/1511.09141).
The collision atlas continues:

```text
T^5(32k+4+j)     = 9k+2       for 0 <= j < 3,
T^8(256k+98+j)   = 27k+11     for 0 <= j < 5.
```

These are identities for every natural `k`, not search observations.

## 2. Exact global consequence

Every positive component contains a unit modulo three.  Indeed, an even
multiple of three can be halved until it is odd, while one odd step from an
odd multiple of three gives a unit.  Multiplication by two is a legal backward
move.  Since the powers of two act transitively on the 18 units modulo 27,
every unit can be doubled into residue 11 modulo 27.  Applying the five-way
collision gives:

> **Kernel-checked theorem.** Every positive Syracuse component contains five
> consecutive positive integers.

The Lean proof checks the complete finite mod-27 statement with `decide` and
checks all five eight-step affine paths symbolically.  In particular this is
not based on floating point or a finite trajectory bound.

Thickness alone is insufficient: two disjoint subsets of the naturals can
both contain finite intervals, or even intervals of unbounded length.  The
theorem becomes useful only when coupled to order or height.

## 3. The proposed termination mechanism: holonomy descent

Assume a nontrivial component exists and let `m` be its least positive
element.  Necessarily `m` is odd (unless it is 1), and every forward and
inverse-word collision representative must remain at least `m`.  This converts
termination into a sharp adversarial statement:

> **Holonomy-descent target.** For every odd `m>1` whose forward orbit never
> falls below `m`, an affine collision generated along that orbit has a legal
> representative below `m`.

This target is stronger and more arithmetic than a negative average drift.
It is allowed to inspect the orbit's actual residues and choose a competing
inverse word after seeing them.

There is already a concrete descent portal.  If `n=9k+2`, the three-way
diamond contains the intermediate component mate

```text
d = 8k+1,              d+1 < (8/9)(n+1).
```

Thus visits to `2 mod 9` expose an exact `8/9` height contraction inside the
same component.  What is missing is a charge proving that an orbit confined
above its component minimum cannot postpone or undo these contractions.

The natural height is `H(n)=n+1`.  It removes the affine error exactly on odd
steps:

```text
H(Tn) = (3/2) H(n)                   (n odd),
H(Tn) = (n+2)/2 <= (2/3) H(n)        (n even, n>=2).
```

So any obstruction to descent must shadow the 2-adic fixed point `-1`: long
odd stretches expand by exactly `3/2`, but requiring a long odd stretch
consumes exact binary precision in `n+1`.  This is the same exceptional mode
that defeated autonomous projective contraction elsewhere in the program.
Here, however, the precision is not merely an obstruction: it is potential
currency.  The intended proof should spend the forced low bits of `n+1` to
select a high-multiplicity inverse-word collision whose affine offset crosses
below the component minimum.

## 4. A precise attack, not another numerical lane

For an inverse word `w`, record its affine chart

```text
x_w(t) = (2^L t - B_w) / 3^M,
```

together with its legality cylinder.  Words with the same `(L,M)` form a
holonomy fiber; arithmetic progressions among the offsets `B_w` give
consecutive component representatives.  The proposed proof has three parts:

1. **Collision amplification.**  Construct, recursively and symbolically,
   holonomy fibers whose normalized offset diameter grows with the binary
   precision forced by a `-1` shadow.  The observed 2-, 3-, and 5-way diamonds
   are the first exact templates, not evidence for the general theorem.
2. **Adaptive charging.**  Define a potential combining `log H`, remaining
   `v2(n+1)` precision, and collision-fiber offset width.  An ordinary even
   step pays height; a long odd shadow pays precision; a `2 mod 9` portal pays
   the explicit `log(9/8)` holonomy contraction.
3. **Minimum crossing.**  Prove that a complete charged excursion has a legal
   inverse representative `x` in the same component with `x<m`.  This is the
   only step that would contradict minimality and prove termination.

The key falsification tests are structural.  A valid potential must survive
the exact `-1` shadow rather than average it away; collision words must be
legal for the feedback-selected ordinary integer, not merely congruent in a
completion; and the final inequality must compare with the component minimum,
not just with a later, larger portal value.

## 5. Why this may be specific enough to work

The proposal simultaneously uses all three exceptional features of `3x+1`:

- division by powers of three in inverse odd branches;
- the fact that two generates the unit group modulo `3^q`, permitting global
  placement of collision charts;
- exact real multipliers `3/2` and the `H=n+1` affine cancellation.

It therefore is not a parity-only heuristic.  A serious proof attempt should
also run the symbolic argument against `5x+1`: if the same minimum-crossing
lemma survives unchanged there, it has almost certainly discarded the
arithmetic feature that matters.

The next mathematical deliverable is not a deeper atlas search.  It is a
general collision-amplification lemma indexed by forced `v2(n+1)` precision,
followed by one complete charged-excursion inequality.  Either would be a new
theorem; together they would give a genuinely new reason for termination.
