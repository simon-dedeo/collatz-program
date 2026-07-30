# Self-delimiting long returns

**Status (2026-07-30).** The finite-capacity theorem and the exact odd-exit
law below are kernel-checked in
`KontoroC/KontoroC/LongReturnSelfDelimiting.lean`. They do not construct a
Collatz counterexample. They remove the externally selected return length
from the live adjacent-return architecture and expose the next arithmetic
closure condition.

## 1. The return length lives in the payload

For one high opcode put

```text
A=3^Q(g),       B=2^P(g),
P(g)=23g+54,    Q(g)=17g+40.
```

Consecutive long-return siblings expose the core cell

```text
A z = 1+B z'.                                      (SD1)
```

The correct coordinate is its positive fixed-point defect

```text
w(z)=(A-B)z-1.
```

One line of algebra gives

```text
B w(z')=A w(z).                                    (SD2)
```

Since `gcd(A,B)=1`, a chain of `n` cells exists if and only if

```text
B^n | w(z).                                        (SD3)
```

The converse is constructive, not compactness. If
`w(z)=B^(n+1)t`, set `z'=z+B^n t`; then SD1 holds and
`w(z')=B^n A t`. Lean proves the generic theorem for arbitrary coprime
`A,B` with `A-B>1`.

Consequently the intrinsic counter

```text
capacity(g,z)=v2(w(z))/P(g)                        (SD4)
```

is exact: precisely `capacity(g,z)` high cells can be executed, and the next
one cannot. The return length therefore need not be stored in a finite phase,
printed by an external schedule, or guessed by a search. Literal divisibility
of the current ordinary payload supplies a self-delimiting unary instruction.

## 2. Why the remainder must be exactly 77

The final adjacent-sibling decoder is

```text
3^Q(g) z = 1+2^77 y.                               (SD5)
```

Every source of an adjacent long-return pair is odd: reducing its return
balance modulo two leaves an odd defect and an odd ternary coefficient. Thus
an endpoint `y` that is to become the next doubled-opcode source must be odd.

For `g>1`, the other dyadic term has valuation `P(g)>77`. Comparing SD5 with
the definition of `w` shows that an odd `y` forces

```text
v2(w(z))=77.                                       (SD6)
```

Combining SD2 through `n` complete cells with SD6 gives the exact endogenous
length law

```text
v2(w(z_0))=n P(g)+77,                              (SD7)
capacity(g,z_0)=n.
```

Lean also checks SD7 directly when the odd endpoint already satisfies the
next `AdjacentSource(k_next,2g,...)` condition. This is the precise bouncer
semantics: consume `P(g)`-bit packets while possible, then use the terminal
77-bit packet as the exit instruction.

## 3. What remains

This is construction progress, not an orbit. The earlier diagonal splice
proved that a retroactive dyadic lift can always manufacture the next source;
the ordinary-root theorem proved that infinitely many such repairs yield only
a 2-adic address. The remaining problem is now narrower:

```text
find one positive ordinary state whose self-delimited odd exit y satisfies
the adjacent-source cylinder at opcode 2g without changing the old source.
```

Equivalently, the exit map must preserve two payload-computed conditions:
the exact ruler valuation SD7 at the current opcode and the unique source
residue at the doubled opcode. A proposed selector for `n` is now redundant
and should be rejected; `n` is already decoded by SD4. The next fundamental
attack is to express the doubled-opcode source residue in the terminal odd
cofactor of SD7 and look for a stationary odd-cofactor recurrence. Small
bounded survival by itself would not address the ordinary-root gate.

No Collatz theorem, divergent orbit, or counterexample is claimed.
