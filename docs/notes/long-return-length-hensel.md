# Adaptive return length as a self-supplying Hensel register

**Status (2026-07-29).**  Every identity and inequality labeled “checked”
below is kernel-checked in
`KontoroC/KontoroC/LongReturnLengthHensel.lean`.  This is a new construction
interface, not a Collatz counterexample.  No ordinary infinite orbit has yet
been constructed.

## 1. Compare return lengths instead of solving one in isolation

For the legal long doubling return, write

```text
P(g)=23g+54,             Q(g)=17g+40,
R_k(g)=114+kQ(g),        S_k(g)=154+kP(g),

Return(k,g,F,X) :<=> 3^R_k F = defect_k + 2^S_k X.
```

The earlier attack fixed `k=6`, the first return length whose real height can
pay the forced input precision.  The new move is to regard `k` itself as an
unbounded instruction and compare the length-`k` and length-`k+1` returns from
the *same* source `F`.

The forcing recurrence

```text
defect_(k+1)=3^Q defect_k+2^(77+(k+1)P)
```

cancels every large source-dependent term.  If the two candidate outputs are
`X` and `Y`, Lean proves the exact equivalence

```text
Return(k+1,g,F,Y)
  <-> 3^Q X = 2^(P-77) + 2^P Y,                  (RLH1)
```

conditional only on `Return(k,g,F,X)` and `g>0`.  Notice that `k`, `F`, and
the composite defect have disappeared from the right side.

## 2. The hidden instruction

Because `P-77=23(g-1)` and the ternary multiplier is odd, (RLH1) is equivalent
to

```text
X=2^[23(g-1)] z,
z odd,
3^[17g+40] z = 1 + 2^77 Y.                       (RLH2)
```

Thus appending one high cell performs two exact operations:

1. it demands a zero block of precisely `23(g-1)` bits in the shorter
   candidate output;
2. after removing that block, it executes one **stationary 77-bit negative
   Hensel division**.

This identifies a previously hidden instruction set.  Adaptive return length
is neither a free choice nor merely extra Archimedean budget.  It is an
unbounded unary counter whose increment exposes one Hensel cell.

## 3. It carries a full payload cylinder

Define

```text
HenselStep(g,z,Y) :<=> 3^Q(g) z = 1 + 2^77 Y.
```

If one cell exists, then for every natural tail `t`, Lean checks

```text
HenselStep(g, z+2^77 t, Y+3^Q t).                (RLH3)
```

The target is unique.  Therefore the cell reads one 77-bit input cylinder and
passes the untouched ordinary tail forward with odd gain `3^Q`.  This is the
same algebraic shape sought in the signed-shuttle and public-cofactor work,
but here it arises internally by comparing two lengths of one already-legal
return family.  No extra sign, opcode, CRT address, or invented macro is used.

## 4. Exact self-supply

The crucial resource inequality is much stronger than the six-cell threshold:

```text
2^[P(g)+1] < 3^Q(g)                              (all g>=0).   (RLH4)
```

It follows from the exact base inequalities `2^55<3^40` and
`2^23<3^17`.  Combining (RLH2) with (RLH4), Lean proves

```text
X < Y.                                            (RLH5)
```

So the Hensel instruction does not merely decode the forced bits.  The longer
candidate is strictly larger than the shorter candidate *after* the shorter
one has paid its complete `23(g-1)`-bit zero block.  This is the first exact
single-register primitive in the quine lane that simultaneously has:

- literal origin inside the legal return family;
- an unbounded instruction parameter;
- a full arbitrary-tail lift;
- exact output uniqueness;
- positive net real growth after its dyadic precision charge.

That combination is why this is a construction advance rather than another
finite survivor observation.

## 5. The diagonal-shuttle construction now suggested

At opcode `g`, keep both adjacent candidate returns conceptually available.
Use the shorter candidate `X` as the hidden work register and execute the
longer return, whose actual output is `Y`.  Equation (RLH2) converts the zero
block in `X` into the public `Y`; equation (RLH3) transports the remaining
tail.  At opcode `2g`, repeat with a new adjacent pair.

The desired infinite invariant has the form

```text
(g_n,F_n,k_n,X_n,z_n)
   -> (2g_n,F_(n+1),k_(n+1),X_(n+1),z_(n+1)),

Return(k_n,g_n,F_n,X_n),
Return(k_n+1,g_n,F_n,F_(n+1)),
X_n=2^[23(g_n-1)]z_n,
HenselStep(g_n,z_n,F_(n+1)).
```

The finite base alignment is now unconditional at the Hensel level.  For any
current output `Y`, a dyadic unit congruence constructs `r,z_next,Y_next` with

```text
Y+3^Q r = 2^[P(2g)-77] z_next
```

and `z_next` a valid next Hensel input.  Then **every** higher tail `t`
passes through both levels:

```text
z_in = z+2^77(r+2^[P(2g)]t),
Y_out = 2^[P(2g)-77](z_next+2^77 3^Q t),
next output = Y_next+3^Q(2g) 3^Q(g) t.             (RLH6)
```

Lean proves this diagonal splice exactly.  After the constructed finite
alignment, no further choice depends on `t`; the full tail survives with the
product of two odd ternary gains.

There is also a stronger algebraic result.  Every positive odd affine
progression of candidate sources contains an adjacent return pair at every
positive opcode and every chosen return length.  Combining this with the
full-tail lift proves that any realized adjacent pair at `g` can be lifted so
that its longer endpoint is **literally the source** of a new adjacent pair at
`2g`.  This removes the earlier source/output coordinate mismatch and gives
an unconditional one-step return-to-return splice.

The remaining closure is no longer finite alignment.  Iterating the splice
changes earlier sources by higher tails.  One must prove that a nested family
stabilizes at one finite positive initial natural, rather than converging only
to an infinite 2-adic address.  In addition, `ReturnBalance` is the exact
algebra extracted from the legal long-return family, but the final composite
theorem must reconnect every balance to the literal intermediate-cell
semantics.  Until those two gates are discharged this is an algebraic return
chain, not an ordinary orbit.

## 6. Falsification gates

Any continuation must pass all of these:

1. `k_n` is selected from the current ordinary payload, not from an external
   infinite schedule;
2. both adjacent balances are literal instances of the existing legal return
   semantics;
3. the output of the longer return is the next ordinary source payload, not a
   hypothetical sibling value;
4. regenerated binary width is measured after every division, rather than
   before the forced `23(g-1)` block is removed;
5. the construction supplies one finite natural root and not only compatible
   residues at every finite depth.

RLH1--RLH6 and the odd-progression theorem satisfy the local algebra,
unconditional alignment, resource, arbitrary-tail transport, and literal
endpoint-matching gates.  The ordinary-root stabilization and literal
intermediate-cell bridge remain open.
