# The successor six-cell bouncer

**Status (2026-07-30).** The affine shift rule, exact reproduction inequality,
one-generation successor-family compiler, and conditional all-level ray
consumer are kernel-checked in
`KontoroC/KontoroC/LongReturnSuccessorBouncer.lean`. No infinite ordinary tail
orbit or Collatz counterexample is constructed. Literal intermediate-cell
semantics remain to be connected to the existing counterexample consumer.

## 1. Keep the long return; slow the opcode clock

The two-rail audit found that fixed-shape families cannot reproduce along
`g -> 2g`: the next dyadic source width grows too fast. The legal long-return
balance itself does not mention the next opcode. Its boundary output may
instead be required to support the same macro at `g+1`.

Use six total high cells in the form

```text
TwoRailCode(5,g,0,F,u).
```

Here the intrinsic capacity is zero: the initial register immediately uses
its terminal 77-bit exit, and the complete return length is `5+0+1=6`. For a
base output `Y`, lifting the complete current family by a tail `t` gives

```text
F(t)=F+2^Wsrc(g)t,
Y(t)=Y+2*3^R6(g)t.                                 (SB1)
```

The complete next family at `g+1` is

```text
Fnext(v)=Fnext+2^Wnext v,
Wnext=S_6(g+1)+1.                                  (SB2)
```

Both boundary bases are odd. Divide the alignment `Y(t)=Fnext(v)` by two.
Because the remaining coefficient `3^R6(g)` is odd, one unit congruence gives
positive `r,q` such that for **every** `s>=0`,

```text
t = r + 2^(Wnext-1)s,
v = q + 3^R6(g)s,                                  (SB3)
Y(t)=Fnext(v).                                     (SB4)
```

This is a genuine BB-style shift rule, not a single CRT hit. Lean's
`exists_successor_six_shiftRule` proves that both lifted endpoints remain
complete `TwoRailCode`s and packages SB4 as an exact `TwoRailStepAt` whose
ordinary boundary output is the next ordinary source.

## 2. The quotient reproduces

The low word consumed in SB3 has width

```text
Wnext-1=S_6(g+1)=616+138g.
```

The surviving quotient is multiplied by

```text
3^R6(g),       R_6(g)=354+102g.
```

Lean proves, for every `g>=3`,

```text
2^S6(g+1) < 3^R6(g).                               (SB5)
```

At `g=3` this is the exact integer inequality `2^1030<3^660`; every opcode
increment multiplies the two sides by `2^138` and `3^102`, respectively, and
`2^138<3^102`. Thus the tail quotient has strictly positive bit production
from the first stage onward. The surplus grows linearly with `g`.

This reverses the doubling-ladder resource law. The earlier rational
successor-quine no-go only excludes rational functions of the normalized
base; SB3 is a nonlinear digit machine and is not covered by that theorem.

There is also a free finite alphabet hidden in “six cells.” For any

```text
k+n+1=6,
```

Lean proves

```text
twoRailSourceWidth(k,g,n)=S_6(g)+1,
boundaryOutputStride(k,g,n)=2*3^R6(g).             (SB5a)
```

Every one of the six splits has an ordinary finite code. Switching the
intrinsic counter phase `n=0,...,5` therefore changes the required residue
word without changing either consumption or production. This six-letter
alphabet is the first concrete candidate for the missing substitution
language; it should be tested symbolically for a closed ruler grammar, not by
enumerating isolated integers.

## 3. Exact all-level target

Lean defines `SuccessorSixRay(g0)` as ordinary sequences `F_t,u_t` with

```text
TwoRailCode(5,g0+t,0,F_t,u_t),
(3^Q-2^P)F_(t+1)=3^Q u_t+2^(P-77).                 (SB6)
```

Every such link kernel-checks

```text
ReturnBalance(6,g0+t,F_t,F_(t+1)).                 (SB7)
```

So the counterexample search has become a sharply defined programming-set
problem for the tail rules SB3:

```text
find one finite natural tail whose successive low blocks are the required
alignment words, while the expanding quotient keeps reproducing forever.
```

SB5 solves the resource half of that problem: the machine does not run out of
binary tape. It does not solve address coherence. Iterating arbitrary finite
alignments can still select a nonordinary 2-adic initial tail. The next
fundamental target is a finite substitution/ruler language in which the
required residue at stage `g+1` is emitted by the multiplication at stage
`g`, rather than prescribed from infinity.

The most promising nonlinear freedom is precisely this intrinsic phase `n`.
Fixed `n=0` makes every tail derivative odd and cannot write a whole new zero
block uniformly. A ruler union over exact valuations
`v2((3^Q-2^P)z-1)=nP+77` can change the derivative discontinuously and is the
natural place to search for the missing substitution rule.

Before any algebraic ray is called a Collatz counterexample, the composite
`ReturnBalance` must also be peeled into its literal sequence of negative unit
cells and connected to the already checked infinite-execution consumer.
