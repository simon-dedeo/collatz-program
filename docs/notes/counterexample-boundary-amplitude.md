# Boundary amplitude and the stationary Hensel shuttle

There is still no Collatz counterexample.  This note changes the constructive
target; it does not report a numerical candidate.  The point is to separate
what an infinite address specifies from the datum that an ordinary positive
orbit would have to preserve, and then to identify a mechanism capable in
principle of preserving it.

## 1. Exact finite theorem: the address is not the whole orbit

For the zero-carry three-word system, the charge branches are

```text
A: 2 H' =  3 H
B: 8 H' =  9 H +  3
C:64 H' = 81 H + 63.
```

For a branch prefix `b_0,...,b_(n-1)`, define its numerator product `A_n`,
denominator product `D_n`, and composed offset `C_n` by

```text
A_0=D_0=1, C_0=0,
A_(n+1)=a_n A_n,
D_(n+1)=d_n D_n,
C_(n+1)=a_n C_n+c_n D_n.
```

Lean now proves, for every literal labeled charge path,

```text
D_n H_n = A_n H_0 + C_n,                            (BA1)
9^n D_n <= 8^n A_n,                                 (BA2)
C_n + 7 D_n <= 7 A_n,                               (BA3)
A_n H_0 <= D_n H_n <= A_n(H_0+7).                   (BA4)
```

The local facts behind this are only

```text
9d_b <= 8a_b,
c_b+7d_b <= 7a_b
```

for each of the three branches.  No limiting argument and no search row is a
premise.  The same file proves the exact forward growth estimate

```text
9^n H_0 <= 8^n H_n.                                 (BA5)
```

After division by `A_n`, BA4 says that the renormalized charge
`(D_n/A_n)H_n` always lies in the compact seven-unit window
`[H_0,H_0+7]`.  Meanwhile BA2 says that `D_n/A_n` tends to zero at least as
fast as `(8/9)^n`.  Thus a positive orbit has a nonzero Archimedean boundary
term which survives every renormalization.  The address contributes only the
bounded inhomogeneous term `C_n/A_n`; it does not manufacture `H_0`.

This explains several formerly separate failures.

- A finite prefix supplies only a dyadic cylinder.
- An infinite externally prescribed prefix supplies a `2`-adic point, usually
  not a natural number.
- A periodic address makes the affine boundary series rational and forces the
  positive homogeneous boundary to disappear; this is the existing periodic
  no-go.
- Adding another recursive compiler level keeps refining the `2`-adic point
  but still does not transport a positive Archimedean boundary from one
  generation to the next.

The counterexample problem is therefore not “find enough correct low bits.”
It is: **build a finite public mechanism that transports its nonzero boundary
amplitude while generating the next low-bit constraint.**

The kernel-checked implementation is
[`OutwardThreeWordBoundaryAmplitude.lean`](../../KontoroC/KontoroC/OutwardThreeWordBoundaryAmplitude.lean).

## 2. Why the existing Hensel tower does not solve this

`OutwardExponentCylinder.lean` already contains an exact, unbounded Hensel
recursion.  Its canonical address `a_k` satisfies one divisibility condition
at precision `k`, and exactly one child

```text
a_(k+1) = a_k                 or
a_(k+1) = a_k + 2^k
```

satisfies the condition at precision `k+1`.  This is symbolic and
machine-checked, not a bounded lookup.  But `OutwardPowerChargeNoGo.lean`
also proves that this ever-changing address cannot be one fixed natural
exponent.  The recursion is a correct computation living outside the Collatz
state; treating its limit as the initial program merely preloads a `2`-adic
tape.

The useful part is the one-bit update law.  At dyadic precision `D`, a unit
congruence has exactly one Hensel repair bit.  In its simplest form, for
`D>=3`,

```text
3^(2^(D-2)) = 1+2^D                 (mod 2^(D+1)).   (HS1)
```

Consequently, if `3^q u=1 (mod 2^D)`, exactly one of
`q` and `q+2^(D-2)` repairs the congruence modulo `2^(D+1)`.  A counterexample
machine should *execute this transition forward*, carrying `q`, `D`, and the
odd payload as public data, rather than requiring its initial integer to know
all repair bits in advance.

## 3. Selected construction: a stationary signed Hensel shuttle

The most promising architecture is a fixed finite compiler level with two
roles which swap after every repair.

1. The **boundary rail** carries the positive odd packet responsible for the
   homogeneous term in BA1.  It may change by an explicit integer self-map,
   but it must not be replaced by a fresh CRT representative.
2. The **work rail** forms `U=3^q u` and tests the next Hensel bit through the
   exact valuation of `U-1` or `U+1`.
3. The signed pair

   ```text
   U-1, U+1
   ```

   differs by two.  If `U=1+2^D r`, the minus rail exposes the new packet
   `r` behind a `D`-bit gap, while the plus rail retains the complementary
   marker `2+2^D r`.  At the next signed phase their roles can swap.
4. The unit-debris ISA already realizes the two public signs

   ```text
   H=2^p h  ->  H'=(3^q h+s)/2^e,   s in {+1,-1},   (HS2)
   ```

   at fixed finite compiler levels.  The sign-alternating hierarchy and the
   phase-swap cells show that both halves are genuine Collatz arithmetic.
   What is missing is one depth-independent return identity that preserves
   the boundary packet while exposing the next repair bit.

Call this proposed return a **stationary Hensel shuttle**.  “Stationary” is
essential: it repeatedly uses one finite public state space.  It does not add
another nesting level, because the positive-tail theorem already closes that
route.

## 4. Exact acceptance test

A proposed shuttle is promoted only if it supplies all of the following as
identities.

```text
public state:       S(D,q,u,s),  D>=3, u>0 odd, s=+1 or -1
decode:             the current integer canonically recovers D,q,u,s
Hensel invariant:   3^q u = 1                    (mod 2^D)
repair:             q'=q+epsilon*2^(D-2), epsilon in {0,1}
next precision:     3^q' u = 1                   (mod 2^(D+1))
macro semantics:    T^tau(S(D,q,u,s))=S(D+1,q',u',-s)
ordinary transport: u'=Phi(D,q,u,s), with Phi total on the invariant
growth:             the encoded positive integer strictly increases
```

The repair bit must be recovered from the current public payload.  `u'` must
be the output of the same macro, not a new modular choice.  Exact valuations,
not divisibility alone, are required at every division.  A finite proof that
these clauses hold for all states in one nonempty invariant family would
produce an infinite ordinary orbit and hence a counterexample through the
existing Lean consumers.

This target is deliberately stronger than a table of successful links.  It
asks for a semiconjugacy between a one-bit Hensel lift and literal Collatz
macros.  The Hensel recursion supplies the aperiodic control; the second rail
supplies the boundary amplitude that an address alone lacks.

## 5. What not to do next

The following are now subordinate diagnostics, not research lanes:

- widen the three-word charge census;
- extend a finite Hensel prefix;
- add another sign-alternating compiler level;
- fit another finite-state selector;
- prescribe another long branch schedule and solve its CRT cylinder.

Any of these can make the `2`-adic shadow longer without addressing BA4.
Further computation is justified only after a proposed shuttle identity
exists, as an exact coefficient solver or falsifier for that identity.

## 6. Immediate symbolic work

The next derivation should compose one positive-sign and one negative-sign
unit cell in public coordinates, retain both `U-1` and `U+1` factors until the
second collision, and eliminate the internal quotient.  The desired output
is a formula in `(D,q,u)` whose dyadic valuation test is exactly HS1 and whose
odd cofactor becomes the next public `u'`.  There are three kill tests:

1. coefficient comparison must not collapse the two rails to the existing
   rank-one affine residual;
2. the public output must canonically decode the opposite sign phase without
   a fresh address restriction;
3. the boundary packet in BA4 must be transported by an integer formula,
   rather than set to the next canonical residue.

Failure of one composition should close that algebraic ansatz.  Success would
be the first result in the program that actually regenerates future address
information from a finite ordinary payload.
