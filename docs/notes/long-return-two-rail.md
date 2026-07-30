# The two-rail long-return machine

**Status (2026-07-30).** The reattachment, local-solvability, affine-tail, and
one-parameter stride-obstruction theorems below are kernel-checked in
`KontoroC/KontoroC/LongReturnSelfDelimiting.lean` and
`KontoroC/KontoroC/LongReturnTwoRail.lean`. They do not construct a Collatz
counterexample. They replace a false scalar recurrence with the exact
two-register construction problem.

## 1. Boundary and work are different registers

Put

```text
A=3^Q(g),  B=2^P(g),  D=A-B,  e=P(g)-77.
```

A finite macro of base length `k` and intrinsic counter `n` consists of

```text
3^R F = defect(k,g)+2^(S+e) z,                     (TR1)
D z-1 = 2^(nP+77) u,       u odd.                 (TR2)
```

The self-delimiting core and terminal Hensel exit produce an odd boundary
payload `Y` satisfying

```text
D Y = A^(n+1)u+2^e,                               (TR3)
ReturnBalance(k+n+1,g,F,Y).                       (TR4)
```

At opcode `2g`, `Y` is the new ordinary source. It is **not** the new work
register. The next macro must independently find `z'` and `u'` with

```text
3^R' Y = defect(k',2g)+2^(S'+e')z',               (TR5)
D' z'-1 = 2^(n'P'+77)u'.                          (TR6)
```

Lean packages TR1--TR2 as `TwoRailCode` and TR1--TR6 plus TR3 as
`DoubledTwoRailStep`. A checked consumer proves that every such step realizes
TR4 without changing the old source.

Eliminating `z` from TR1--TR2 gives the useful public equation

```text
D 3^R F = D defect(k,g)
          +2^(S+e)(1+2^(nP+77)u).                 (TR7)
```

This is a Diophantine surface in the two public rails `(F,u)`, not a scalar
map on `u`.

## 2. Every individual finite macro exists

There is no local congruence obstruction. For every `(k,g,n)`, Lean constructs
positive `F` and odd `u` satisfying TR1--TR2. The proof is exact and uses two
unit congruences.

First choose `z` modulo `2^(nP+78)` so that

```text
D z = 1+2^(nP+77)      mod 2^(nP+78).              (TR8)
```

Because `D` is odd, this is soluble and makes the quotient in TR2 odd. Add a
multiple of `2^(nP+78)` to `z` to solve the independent entrance congruence

```text
defect(k,g)+2^(S+e)z = 0 mod 3^R.                 (TR9)
```

Every coefficient added at this second step is a power of two, hence a unit
modulo `3^R`; it preserves TR8. Dividing TR9 defines the positive ordinary
source `F`. The theorem is `exists_finite_twoRailCode`.

This is important negative information for search design: rejecting isolated
macros tests nothing. All difficulty is coherence of infinitely many boundary
links TR3--TR6.

## 3. Exact affine family and the one-parameter wall

For a fixed code, let

```text
Wsrc=S(k,g)+(n+1)P(g)+1.
```

Every `t>=0` gives another exact code with

```text
F(t)=F+2^Wsrc t,
u(t)=u+2D 3^R t,
z(t)=z+2^(nP+78)3^R t.                            (TR10)
```

The corresponding boundary output is

```text
Y(t)=Y + 2*3^(R+(n+1)Q)t.                         (TR11)
```

The source-family stride contains at least two binary factors (in fact
hundreds or more). The output-family stride in TR11 contains **exactly one**.
Lean proves for every next macro shape

```text
2^Wsrc(next) does not divide 2*3^(R+(n+1)Q).       (TR12)
```

Consequently the whole natural one-parameter formula-tape family cannot map
into one next source cylinder. This does not exclude an individual zero-lift
hit or a restricted subfamily. It says that restriction necessarily consumes
a large block of low bits from `t`; the ordinary-root problem has reappeared
as parameter consumption.

## 4. Surviving construction target: a reproducing programming set

The Busy-Beaver bouncer analogy and the difference-map idea now have a precise
job. Seek a language `L_g` which is a union of **multi-parameter** two-rail
families, with a machine-checked shift rule having all four properties:

1. every word in `L_g` decodes to a `TwoRailCode`;
2. TR3 sends its boundary source into some word of `L_(2g)`;
3. meeting the next dyadic cylinder may consume one counter, but the update
   reproduces at least one unbounded counter elsewhere;
4. one explicit ordinary word belongs to the initial language.

A fixed `(k,n)` one-parameter language is now ruled out by TR12. The live
degrees of freedom are therefore nonlinear switching among intrinsic counter
values `n`, several affine tail parameters, or a substitution language in
which a consumed low-bit block is copied into another rail before the next
stage. In difference-map terms, closure is not enough: the incidence matrix
of counter updates must have a nonnegative expanding direction after the
dyadic-consumption row is included.

The next high-leverage mathematical object is an exact two-parameter shift
rule, not a larger bounded search. A candidate should be rejected immediately
unless its symbolic counter-update matrix survives TR12 and its boundary
output is literally the next ordinary source.

Literal intermediate Collatz-cell reconstruction remains a separate audit
before any such algebraic infinite ray could be called a counterexample.
