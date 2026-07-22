# Determinant-four resonant phase gliders

This note records the first nontrivial opcode conjugacy found after equal
one- and two-letter matrix collisions were closed.  It is an exact arithmetic
construction in the canonical public-cofactor transducer.  It is not an
invariant language, a universal literal-Collatz compiler, or an infinite
orbit.

## 1. The determinant leaves a four-cell phase slip

One public tail branch has

```text
2^P t' = 3^Q t + kappa,
P=154h+23m',
Q=114h+17m.
```

The exponent identities

```text
114*391 = 17*2622,
154*391 = 23*2618
```

show that

```text
(m,h,m') -> (m+2622k,h-391k,m'+2618k)            (RG1)
```

preserves both `P` and `Q`.  But the source phase shifts by `2622k` while the
target shifts by only `2618k`.  The mismatch is

```text
2622k-2618k=4k,                                   (RG2)
```

the same determinant-four residue which appeared in the power resonances.
Here it is spatial: equal-gain opcode charts are displaced by four defect
cells.

## 2. Parallel branches admit exact public-tail conjugacies

Let

```text
F_a(t)=(3^Q t+kappa_a)/2^P,
F_b(t)=(3^Q t+kappa_b)/2^P.
```

For an affine public-tail embedding `E(t)=s*t+c`, the commutative-square
condition

```text
E(F_a(t))=F_b(E(t))                                (RG3)
```

is exactly

```text
(3^Q-2^P)c=s*kappa_a-kappa_b.                     (RG4)
```

Thus an integral embedding exists whenever

```text
gcd(kappa_a,3^Q-2^P) | kappa_b.                   (RG5)
```

This is stronger than a formal affine identity because it automatically
respects the exact source cylinders.  If

```text
t=rho_a+2^P u,
s*rho_a+c=rho_b+2^P(v_0+s*u),
```

then RG3 gives

```text
E(F_a(t))=sigma_b+3^Q(v_0+s*u)=F_b(E(t)).         (RG6)
```

The cylinder compatibility follows algebraically from RG4 and the two branch
congruences; it is not another sampled coincidence.

## 3. The first exact up and down cells

The phase-down pair is

```text
a=(1,392,1),
b=(2623,1,2619).
```

Both have

```text
Q=44705, P=60391,
```

and `gcd(kappa_a,3^Q-2^P)=1`.  The least positive integral conjugacy has a
21,330-decimal-digit slope and a 21,330-digit intercept.  It maps the full
source cylinder and the full output family, not just one member.  In the
target chart the defect phase moves from `2623` to `2619`, a four-cell motion.

The phase-up pair is

```text
a=(1,392,5),
b=(2623,1,2623).
```

Here `P=60483`, `Q=44705`, the same gcd is one, and the affine embedding again
has 21,330-digit coefficients.  The low chart moves from phase `1` to phase
`5`, while the high chart is stationary.

More generally the two cell families are

```text
Down_(r,k): (r+2622k,1,r+2618k)
  conjugate to (r,391k+1,r),

Up_(r,k): (r,391k+1,r+4k)
  conjugate to (r+2622k,1,r+2622k).               (RG7)
```

This is the closest current analogue of Kontorovich's spatial glider.  One
chart regards a long recharge as stationary internal work; the resonant chart
regards the same affine gain as translation of a defect boundary.

There is also a concrete ultra-small-language interpretation.  On any fixed
residue class modulo four, the public opcode `m` is an unbounded counter.
`Up_(r,k)` increments it by `4k`; `Down_(r,k)` decrements it by `4k`, with the
positivity threshold `r>=1` acting as a coarse zero/boundary test.  The affine
tail is the remote data rail.  This is not yet a compiled two-counter machine:
the current integer must autonomously choose the instruction and retain
finite control.  But it identifies actual increment/decrement-like opcodes
instead of arguing from the vague fact that the bouncer has two valuations.

There is a sharper control-theoretic point.  Fix `k=1` and define the public
one-counter policy

```text
U(m)=(m,392,m+4).                                  (RG8)
```

The current `m=v2(y+1)/23` is canonically decoded from the public normalized
integer, so the infinite sequence

```text
U(r), U(r+4), U(r+8), ...
```

is not an oracle-supplied word.  It is an autonomous infinite-state policy:
read the counter, increment it by four, and use a constant recharge.  This is
exactly how it evades the theorem excluding autonomous *finite*-state
controllers.  What remains missing is the invariant data domain: one
ordinary tail which belongs successively to every decoded source cylinder.
Thus the phase glider has already solved causal opcode generation, but not
address regeneration.

## 4. Why this is not yet reproduction

For `k=1`, down cells link geometrically as

```text
Down_r : r+2622 -> r+2618,
Down_(r-4) : r+2618 -> r+2614.
```

They form a finite delay line until the positive phase is exhausted.  Up
cells link in the other direction:

```text
Up_r : r -> r+4,
Up_(r+4) : r+4 -> r+8.
```

That gives the public one-counter policy RG8, but finite-prefix compilability
does not say that one ordinary tail realizes it.  Moreover the affine
embeddings `E_r` change with `r`; one commutative square is not a
depth-independent self-map on the tail.  A fixed periodic up/down bounce is
already closed by the arithmetic periodic-schedule obstruction.

Closure therefore requires at least one of:

1. a payload invariant making the successive `E_r` telescope;
2. a public marker which chooses variable `k` and direction, then survives the
   move (constant `k=1`, direction up, is already causally decoded by RG8);
3. an exact turnaround which converts a finite down delay into a regenerated
   larger up delay; or
4. a theorem that the infinite up schedule has one ordinary positive tail.

The first three are versions of Simon's “splash the gap”: the four-cell phase
is the moving gap, while the 21,330-digit affine tail is the remote payload.
The fourth is now the sharpest closure gate for RG8: an ordinary-versus-2-adic
question which should be attacked symbolically, not by extending finite
prefixes.

## 5. Exact verification and next attacks

[`unit_charge_resonant_conjugacy.py`](../../experiments/kontorovich/unit_charge_resonant_conjugacy.py)
reconstructs both canonical public branches in each pair, solves RG4 exactly,
checks RG3 and both cylinder faces coefficientwise, and replays two members of
each source and target through the arithmetic bouncer formula.  The verifier
and artifact SHA-256 values are

```text
worker    70666b9ff3a47436a3fd45003af37b631c7c592b913ee94201f0fdc24deb362c
artifact  e3db4d58871f3a8b0493969405ad4f29ca1e2f4e988eda0038eb578f78a333b1
```

The next theorem-shaped attacks are:

- kernel-check RG1--RG6 and ask whether the source/target embeddings can be
  packaged as a public conjugacy rather than a representation choice;
- derive the exact nested-tail series for `Up_r,Up_(r+4),...` and decide
  whether its unique 2-adic address can be an ordinary natural;
- classify when RG5 fails or succeeds along a whole phase walk; and
- solve the telescoping equations `E_(r+4) after E_r` before searching any
  larger opcode box.

The guiding distinction remains: this construction moves a boundary and
preserves an affine tail.  A counterexample needs the moved boundary to tell
the same mechanism what to do next.
