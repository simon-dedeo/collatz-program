# The ordinary-root gate for adjacent long returns

**Status (2026-07-29).** The reductions and no-go theorem below are
kernel-checked in `KontoroC/KontoroC/LongReturnOrdinaryRoot.lean`. They do not
construct an infinite Collatz orbit. They identify the exact arithmetic that
an ordinary construction must satisfy after the unconditional local splice.

## 1. One source cylinder, exactly

Write

```text
AdjacentSource(k,g,F)
  :<=> exists X,Y,
       ReturnBalance(k,g,F,X) and ReturnBalance(k+1,g,F,Y).
```

For `g>0`, put

```text
W = S(k,g)+P(g),
E = S(k,g)+P(g)-77.
```

Lean proves the exact equivalence

```text
AdjacentSource(k,g,F)
<->
  defect(k,g) < 3^R(k,g) F
  and
  3^[Q(g)+R(k,g)] F
    = 3^Q(g) defect(k,g)+2^E       (mod 2^W).       (OR1)
```

The coefficient on `F` is odd. Therefore (OR1) is one and only one residue
class modulo `2^W`. The file constructs its canonical representative
`sourceResidue(k,g)<2^W` using an exact unit inverse and proves

```text
AdjacentSource(k,g,F)
<-> lower bound and F mod 2^W = sourceResidue(k,g).           (OR2)
```

Once `2^W>F`, congruence becomes literal equality
`F=sourceResidue(k,g)`. Thus adaptive return length is not free branching: at
large `k`, a fixed ordinary endpoint must equal a rapidly changing canonical
integer exactly.

## 2. Retroactive lifts and ordinary stabilization

The unconditional splice modifies the current source by

```text
F_(n+1) = F_n + 2^[S(k_n,g_n)+P(g_n)] t_n.                    (OR3)
```

These representatives are monotone. Lean proves the exact ordinary-root
criterion

```text
EventuallyConstant(F_n) <-> t_n=0 eventually.                (OR4)
```

So infinitely many positive splice tails can only produce an unbounded tower
of finite representatives, hence a nonordinary inverse-limit address. A
counterexample from this architecture must eventually stop changing its past.
After that point it must be a genuine forward chain

```text
ForwardAdjacentSplice(k_n,g_n,F_n,F_(n+1)),
g_(n+1)=2g_n,                                                (OR5)
```

whose longer endpoint already satisfies the next cylinder (OR2). This is the
precise zero-retroactive-lift target.

## 3. Fixed-opcode adaptive length is closed

The adjacent-source cylinders are nested in return length:

```text
AdjacentSource(k+1,g,F) -> AdjacentSource(k,g,F).             (OR6)
```

The reason is exact. Reversing `defect_succ` reconstructs the missing shorter
output, and the appended defect is precisely the Hensel marker.

If one fixed source supported unbounded `k`, (OR6) would make it support every
`k`. The successive Hensel cores would then obey

```text
3^Q z_n = 1 + 2^P z_(n+1).                                  (OR7)
```

Set `A=3^Q`, `B=2^P`, and `D=A-B`. Since `A>2B`, the fixed-point defect
`w_n=D z_n-1` is positive and satisfies

```text
B w_(n+1)=A w_n.
```

As `gcd(A,B)=1`, iteration forces `B^n | w_0` for every `n`, impossible for
one fixed positive natural `w_0`. Lean packages the general affine-division
lemma and concludes

```text
not (forall bound, exists k>=bound, AdjacentSource(k,g,F)).   (OR8)
```

This closes “camp at one opcode and use `k` as an infinite counter.” It does
not close the moving diagonal `g,2g,4g,...`.

## 4. The live construction

The counterexample target is now one exact countable-state relation, with no
finite-search surrogate:

```text
find positive F_n and k_n such that

  g_n = 2^n g_0,
  ForwardAdjacentSplice(k_n,g_n,F_n,F_(n+1)),
  F_(n+1) mod 2^[S(k_(n+1),g_(n+1))+P(g_(n+1))]
    = sourceResidue(k_(n+1),g_(n+1)),

and the literal long-return semantics link every displayed balance.        (OR9)
```

The local existence theorem may still be used finitely to enter such a chain,
but (OR4) says it cannot be used with positive retroactive tails forever.
What must replace them is a payload-generated choice of `k_(n+1)` for which
the current endpoint already equals the next canonical residue once the
modulus exceeds it.

The next fundamental attack is therefore on the moving residue sequence
`sourceResidue(k,2g)`: derive a recurrence in `k` and `g`, then seek a
payload-dependent selector that makes (OR9) invariant. Any fixed, periodic,
or externally prescribed selector should be rejected before invoking literal
semantics; only a genuine ordinary forward invariant can complete the goal.
