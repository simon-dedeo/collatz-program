# The six-high-cell long doubling return

## 1. Why this is a new construction attack

The no-go for the original doubling quine is not a verdict against opcode
doubling.  It diagnoses a resource imbalance in one particular legal route.
That route contains only two transitions whose large source/target opcode is
`g`.  Its exact dyadic precision demand grows like `23g`, while its complete
positive real-height budget grows like only

```text
2 (17 log2(3)-23) g = 7.888... g.
```

There is a canonical way to change this balance without inventing a new
machine instruction: remain at the legal state `g` for more `g -> g`
self-transitions before returning to state one.

## 2. The exact long-return family

Let `k>=1` be the number of transitions whose source and target accounting
uses the large opcode.  The route is

```text
1 -> 1 -> g -> g -> ... -> g -> 1,
```

with `k-1` copies of the self-transition `g -> g`.  Put

```text
P(g)=23g+54, Q(g)=17g+40,
R_k(g)=114+k Q(g), S_k(g)=154+k P(g).
```

If `T_0=0` and

```text
T_(k+1)=3^Q T_k+2^(kP),
C_k=3^(kQ)(3^57+2^77)+2^(77+P)T_k,
```

then exact composition of the legal cells has macro balance

```text
3^R_k F(g)=C_k+2^S_k F(2g).                       (LR1)
```

Lean checks the recurrence

```text
C_(k+1)=3^Q C_k+2^(77+(k+1)P),                    (LR2)
```

which is precisely the effect of appending one further `g -> g` cell.
It also checks the central factorization, for every `k>=1`,

```text
3^(kQ)(3^114 F(g)-(3^57+2^77))
 =2^(77+P)(T_k+2^(77+(k-1)P)F(2g)).               (LR3)
```

Thus every member of the family forces the *same first precision factor*
`2^(77+P)`.  Extra self-loops increase the height budget without increasing
the terminal precision slope.

In the normalized coordinate
`z_g=2^P/3^Q`, LR1 is the degree-`k` equation

```text
3^114 f(z)-2^154 z^k f(kappa z^2)
 = (3^57+2^77)+2^77(z+z^2+...+z^k).               (LR4)
```

The schedule `g->2g` is still literally the Mahler substitution after the
same `x=kappa z` change.  What changed is the power `z^k`, hence the
Archimedean resource balance—not the opcode dynamics.

## 3. The sharp threshold is six

At leading order in `g`, one return multiplies height by

```text
3^(17kg)/2^(23kg).
```

To pay the independent forced precision `2^(23g)`, the necessary slope test
is

```text
2^(23(k+1)) < 3^(17k).                             (LR5)
```

Lean proves the exact equivalence

```text
LR5  iff  6 <= k.                                  (LR6)
```

The proof is finite and integer-only: it checks `2^161<3^102` at `k=6`,
checks all `k<6`, and propagates upward using `2^23<3^17`.  Hence:

- `k<=5`: the precision-versus-height attack still wins asymptotically;
- `k=6`: the first legal return on the other side of the wall;
- `k>6`: more height surplus, but a longer and more complicated return.

The exact definitions, LR2--LR3, and LR6 are kernel-checked in
[`LongDoublingQuineThreshold.lean`](../../KontoroC/KontoroC/LongDoublingQuineThreshold.lean).

## 4. Why `k=6` is the preferred candidate

The point is not that six makes an integer payload likely.  It is that six is
the **minimal structural repair** of the failure theorem:

- it uses no new cells, signs, CRT choices, or external instruction stream;
- it retains the self-similar `g->2g` return;
- it crosses the two-place obstruction by the smallest possible margin;
- its forcing is the rigid geometric block `z+...+z^6`, which offers more
  algebraic structure than an arbitrary degree-six polynomial.

This is an internal analogue of the 5x+1 control.  The low-bit mechanism has
not changed, but the Archimedean drift has crossed from insufficient to
sufficient.  It is therefore exactly the sort of modification that parity-
only or purely 2-adic reasoning cannot dismiss.

## 5. The next theorem-shaped construction problem

No orbit or integer payload is claimed.  A successful attack now has a
specific target: construct positive odd naturals `F(g),F(2g),...` satisfying
LR1 at `k=6`, with the intermediate divisions realizing the literal legal
route.  The important questions are symbolic, not bounded-search questions:

1. Does the geometric forcing in LR4 admit a special singular section whose
   values on `z_g,z_(2g),...` are natural numbers?
2. Can LR3 be reorganized as an autonomous carry recurrence, with the six
   self-loops writing the next high dyadic block rather than merely requiring
   it?
3. If one scalar payload is still too rigid, does a two-rail version preserve
   the `k=6` height surplus while moving the forced precision into a
   determinant/covolume condition rather than one rational approximation?

The first kill test should be an exact rational-function classification for
LR4, now with denominator degree at most six.  The two denominator
divisibilities turn its nonzero poles into a finite set constrained by both
forward squaring and square-root preimages.  Over the algebraic closure that
is a multiplicity/cyclotomic question, not merely a census of rational poles,
and it should be classified rather than guessed.  If rationality is again
closed, the target remains the singular integer section—but now in a regime
where height no longer rules it out.
