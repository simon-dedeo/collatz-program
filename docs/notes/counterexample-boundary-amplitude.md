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

## 7. First kill test: a bare sign swap is still one rail

The first opposite-sign composition can be done without choosing any
coefficients.  Write a signed unit cell as

```text
2^P h'=3^Q h+s,   s in {+1,-1}.
```

Two consecutive cells eliminate their intermediate core exactly:

```text
2^(P0+P1) h2
 =3^(Q0+Q1) h0 +3^Q1*s0+2^P0*s1.                 (HS3)
```

At the first sign-positive level

```text
p+(n)=8n+15,    q+(n)=6n+11,
```

and the second sign-negative level

```text
p-(n)=23n+54,   q-(n)=17n+40.
```

Lean proves that the two possible internal debris terms are

```text
R+-(m)=3^(17m+40)-2^(8m+15)  >0 and odd,
R-+(m)=2^(23m+54)-3^(6m+11)  >0 and odd.           (HS4)
```

Thus `U-1` and `U+1` are not independent public stores.  The sign swap
rectifies to another rank-one affine balance, and its residual has no dyadic
gap of its own.  A following exact division again selects one low-bit
cylinder of the same surviving core.  This closes the *bare* two-cell sign
shuttle proposed in Section 3; it does not close a nonlinear public pairing
or a macro which promotes `R+-(m)`/`R-+(m)` itself to the next decoded state.

The checked algebra is
[`SignedUnitShuttle.lean`](../../KontoroC/KontoroC/SignedUnitShuttle.lean).

## 8. The first nonlinear quine also needs infinite boundary data

The strongest formula-level escape already suggested by the returning unit
macro was the opcode update `g -> 2g`.  With

```text
z_g=2^(23g+54)/3^(17g+40),
kappa=3^40/2^54,
```

one has `z_(2g)=kappa*z_g^2`.  A payload `F(g)=f(z_g)` would obey

```text
3^114 f(z)-2^154 z^2 f(kappa z^2)
  =(3^57+2^77)+2^77 z+2^77 z^2.                    (HS5)
```

The nonzero coefficient at exponent one propagates under

```text
j -> 2j+2:
1,4,10,22,46,...
```

and can therefore never have finite support.  Lean now proves that HS5 has
no finite Laurent-polynomial payload over `Q`.  This is an all-degree
symbolic obstruction, not a bounded opcode calculation.  It does not exclude
an infinite Mahler payload or a singular homogeneous boundary term; indeed
those are precisely where BA4 says an ordinary solution would have to live.

The checked obstruction is
[`DoublingQuineNoGo.lean`](../../KontoroC/KontoroC/DoublingQuineNoGo.lean).

The revised stationary target is consequently narrower: construct a
canonical nonlinear public state in which the odd power-difference debris is
the next work register and a separate homogeneous component transports the
ordinary boundary amplitude.  Merely alternating signs, or replacing the
successor quine by the first base-squaring Laurent ansatz, is now closed.

## 9. The debris already contains an unbounded canonical clock

Promoting the power-difference debris is not merely a speculative escape.
On every even public level `n=2k`, put

```text
Q=17n+40,   P=8n+15,   R=3^Q-2^P.
```

Binary LTE and the strict scale separation give the exact identity

```text
v2(R-1)=v2((3^Q-1)-2^P)=v2(3^Q-1)=2+v2(Q).        (HS6)
```

The middle equality is not heuristic cancellation: Lean proves that
`2+v2(Q)<P`, so subtracting `2^P` cannot alter the lower valuation.  It also
proves the literal factorization

```text
R-1=2^(2+v2(Q))*W_k,   W_k>0 odd.                  (HS7)
```

Thus the debris rejected as a second *affine* rail canonically emits an
unbounded ruler clock and a new positive odd packet *if it is materialized as
the next work register*.  The clock is intrinsic to the residual family; it
is not a fresh CRT address.  Explicit levels with `Q=3*2^(8j+1)` prove
unboundedness in Lean rather than by sampling.  This is the first decoder
interface of the proposed stationary shuttle to survive its exact kill tests,
not yet a literal orbit link.

What remains is precise.  One must identify a legal fixed-level word which
materializes `R`, accepts `W_k`, recovers or updates the public level, and
carries a separate positive boundary packet.  HS6--HS7 supply the nonlinear
decoder arithmetic, but not that return or the counterexample.

The checked interface is
[`SignedDebrisRuler.lean`](../../KontoroC/KontoroC/SignedDebrisRuler.lean).

## 10. Semantic correction and the odd-level typed router

HS6 is exact but is not the valuation tested by a following public unit cell.
If the residual `R_m` is reached with public target label `ell`, the next
cell sees

```text
3^q(ell)*R_m - 1    or    3^q(ell)*R_m + 1,         (HS8)
q(x)=17x+40.
```

The missing source scale is decisive.  Any materialization based on
`3^T | 2^B-1` has even total binary exponent `B`; because
`B=p+(m)+p-(ell)`, Lean proves that `ell` must be odd.  When `m` is even,
`q(ell)+q(m)` is odd, and exact arithmetic gives

```text
v2(3^q(ell)*R_m-1)=1,
v2(3^q(ell)*R_m+1)=2.                               (HS9)
```

Both are below the smallest public unit exponents.  Thus the unbounded raw
ruler from Section 9 cannot be executed merely by materializing an
even-level residual and appending another unit cell.  This branch is closed,
and the correction prevents repeating the earlier source-label mistake.

For odd `m` the minus rail remains live.  Put

```text
E=q(ell)+q(m).
```

Whenever `2+v2(E)<p+(m)`, Lean proves the correctly scaled identity

```text
v2(3^q(ell)*R_m-1)=2+v2(E).                         (HS10)
```

More strongly, there is now an explicit all-parameter router.  Given an odd
residual level `m` and requested sign-negative target `r` with

```text
p-(r)<p+(m),
```

set `d=p-(r)-2` and construct

```text
u =17+80*2^(7d+8)+34m,
G =(2^(8(d+1))-1)/17,
b =2^d+80G+2m*2^d,
ell=b-m.
```

The identities `2^(8j)=1 (mod 17)` and

```text
q(ell)+q(m)=2^d*u,    u odd,    ell odd             (HS11)
```

are proved in Lean.  Consequently

```text
3^q(ell)*R_m-1 = 2^p-(r) * W,
W>0 odd.                                             (HS12)
```

This is the first correctly typed nonlinear residual router in the program:
it uses a closed formula, has exact public valuation, and emits its next odd
core without a bounded search or fresh CRT choice.  It is still not a
counterexample.  The remaining reproduction equation is to show that `W`
is the next residual/boundary state, with its reached target `r` equal to the
next router's source label under one autonomous rule.

The checked correction and constructor are in
[`SignedDebrisSemanticNoGo.lean`](../../KontoroC/KontoroC/SignedDebrisSemanticNoGo.lean).

## 11. Scalar reproduction is impossible

The first closure equation suggested by HS12 is

```text
W = R_next = 3^q(next)-2^p+(next).                  (HS13)
```

This equation is now closed for the explicit router.  The proof is entirely
symbolic.  If HS13 held, reduction of

```text
3^q(ell) R_m - 1 = 2^p-(target) R_next
```

modulo `3^K`, where

```text
K=min(q(ell),q(next)),
```

would give

```text
2^(p-(target)+p+(next)) = 1 (mod 3^K).              (HS14)
```

The target is therefore odd, and the exact order of `4` modulo `3^K`
implies

```text
2*3^(K-1) <= p-(target)+p+(next).                   (HS15)
```

On the other hand, elementary size bounds for the debris show that the room
condition `p-(target)<p+(m)` forces

```text
ell <= next <= ell+m+2.                             (HS16)
```

The explicit router also has `target<=m<=ell`.  Thus the right side of HS15
is at most linear in `ell`, while `K=q(ell)=17ell+40`.  Lean discharges the
final universal inequality by bounding the ternary power below by a
quadratic dyadic power.  There is no exceptional finite range and no
numerical search.

Consequently the cofactor from HS12 cannot be the next scalar debris at any
level.  The remaining live architecture must let that cofactor act on a
second component: a boundary amplitude, a multi-rail packet, or a genuinely
infinite Mahler/automatic payload.  The scalar family alone cannot be its
own autonomous state space.

The checked congruence, order clock, size window, and universal no-go are in
[`SignedDebrisReproduction.lean`](../../KontoroC/KontoroC/SignedDebrisReproduction.lean).

## 12. The scalar no-go leaves an exact boundary cylinder

The impossibility of `W=R_next` does **not** destroy the router.  Its natural
state space was one dimension too small.  Write the checked base collision as

```text
3^a R_m-1=2^B W.
```

Then distributivity gives, for arbitrary `w,z : Nat`,

```text
3^a(R_m+2^(B+w)z)-1=2^B(W+2^w 3^a z).             (HS17)
```

Lean proves HS17 as a natural-number identity, proves that the output
cofactor is odd for `w>0`, and proves its exact 2-adic valuation is still
`B`.  The public router therefore computes on the base rail while carrying
an arbitrary positive ordinary amplitude on a homogeneous second rail.  It
does not choose a new congruence class for each `z`.

There is also a direct ordinary interface.  If the requested target label is
even, then `B=p-(target)` is even.  Reduction of the base factorization modulo
three gives `W=2 (mod 3)`, and hence

```text
W+2^w 3^a z = 3(H+2^w 3^(a-1)z)-1.                (HS18)
```

Thus the entire cylinder is a family of completed Collatz boundaries.  It
feeds the exact three-word map without a residue conversion.

The finite transport law is now kernel-checked as well.  Give branches A, B,
C dyadic costs `1,3,6` and ternary gains `1,2,4`.  If a prefix has cumulative
cost `s_n<=w` and gain `t_n`, its homogeneous coefficient is exactly

```text
2^w 3^a  ->  2^(w-s_n) 3^(a+t_n).                 (HS19)
```

The affine offsets are paid entirely by the base charge.  HS19 is proved for
an arbitrary finite branch function and arbitrary payload, via the exact
prefix balance rather than sampling trajectories.

This changes the foundational target.  Finite routing and finite ordinary
transport are no longer missing.  Every nonempty A/B/C prefix spends positive
dyadic width, so no fixed finite `w` supports an infinite address.  A true
counterexample construction must couple HS17--HS19 to a return operation that
regenerates width autonomously.  Equivalently, one needs a stationary cycle
on a *width-bearing state*, not a scalar debris cycle.  The decisive equation
should account for net dyadic width over a complete router/ordinary return:
the return must create at least the `1,3,6` bits spent by its address while
preserving a positive ordinary boundary coefficient.  This is now the live
construction problem; another bounded residue search does not address it.

The exact cylinder, completed-boundary conversion, local branch lift, and
arbitrary finite-prefix resource law are in
[`SignedDebrisBoundaryLift.lean`](../../KontoroC/KontoroC/SignedDebrisBoundaryLift.lean).

There is no width gain hidden in an affine change of payload coordinates.
Lean proves that any identity valid for every `z`,

```text
X+Cz = Y+2^K(v+uz),
```

forces `C=2^K u`.  If `u` is odd, then `K=v2(C)` exactly.  Consequently a
uniform affine return can only expose dyadic width already present after
HS19; it cannot regenerate any.  The live construction must break uniformity
by selecting a special payload with a nonlinear/automatic return, or enlarge
the state beyond an affine cylinder.  This is a structural no-go, not evidence
from testing a finite collection of payloads.

## 13. The base-squaring return has no rational payload

The first special-payload candidate was the legal four-cell return with
opcode update `g -> 2g`.  In the normalized coordinate it requires

```text
A f(z)-D z^2 f(kappa z^2)=b0+b1 z+b2 z^2.         (HS20)
```

The previous finite-Laurent obstruction did not exclude a rational function
with poles.  That gap is now closed symbolically.  If `f=N/Q` is reduced,
clearing HS20 and reducing once modulo each denominator gives

```text
Q(z)             | Q(kappa z^2),
Q(kappa z^2)     | z^2 Q(z).                       (HS21)
```

Since substitution doubles degree, the second divisibility implies
`2 deg Q <= deg Q+2`, hence `deg Q<=2`.  Lean classifies all possibilities
allowed by both divisibilities:

```text
Q = q,  qz,  qz^2,  or  q(1-kappa z).              (HS22)
```

The constant case is polynomial and fails by degree doubling plus the
nonzero linear forcing.  For `qz`, the degree-two coefficient appears before
either competing term.  For `qz^2`, cancellation would require
`A*kappa^2=D`.  The only genuine rational pole is the nonzero fixed point
`z=1/kappa`; evaluating the canceled equation there shows that its residue
would require

```text
2 A kappa^2 = D,                                   (HS23)
```

which is false for the exact powers of two and three.  All steps, including
the `RatFunc Q` numerator/denominator bridge, are kernel-checked in
[`DoublingQuineRationalNoGo.lean`](../../KontoroC/KontoroC/DoublingQuineRationalNoGo.lean).

This does not close genuinely infinite Mahler or automatic payloads.  It
does identify their indispensable feature: the payload cannot be a rational
function of the normalized state, and its ordinary positive value must retain
the homogeneous boundary term that a purely convergent particular solution
loses.  The next constructive target is therefore an exceptional nonrational
2-adic value with an independently proved natural-number realization, not a
higher-degree rational ansatz.

## 14. Standard Mahler coordinates: the regular lane is a wall, the boundary lane is not

HS20 was written in a useful computational coordinate, but not in the
coordinate used by Mahler theory.  Put

```text
x = kappa*z,
H(x) = x^2 f(x/kappa),
alpha = 2^23/3^17,
lambda = D/(A*kappa^2) = 2^262/3^194.
```

Then Lean proves the exact identities

```text
kappa*z_g = alpha^g,
alpha^(2g) = (alpha^g)^2,
H(x) = Q(x) + lambda H(x^2),                       (HS24)
Q(x) = x^2/A * (b0+b1*x/kappa+b2*(x/kappa)^2).
```

Both `alpha` and `lambda` lie strictly between zero and one in the real
absolute value.  They are also strictly 2-adically contracting.  Thus the
legal opcode update is not merely analogous to a Mahler substitution: in the
standard coordinate it is literally `x -> x^2`.

For every solution of HS24 and every finite `N`, Lean further proves

```text
H(x) = sum_(j<N) lambda^j Q(x^(2^j))
       + lambda^N H(x^(2^N)).                       (HS25)
```

The implementation uses an equivalent recursive finite prefix, so HS25 has
no convergence premise.  The last summand is exactly the homogeneous
boundary amplitude in standard coordinates.  The difference `K` of any two
solutions obeys

```text
K(x) = lambda^N K(x^(2^N)).                         (HS26)
```

This makes the literature test decisive.

### 14.1 Mahler transcendence closes the regular analytic payload

There is a unique solution of HS24 holomorphic at zero,

```text
H_an(x) = sum_(j>=0) lambda^j Q(x^(2^j)).           (HS27)
```

The matrix system for `(1,H_an)` has constant nonzero determinant `lambda`,
so every nonzero point of the open unit disk is regular.  The rational
no-go of Section 13, transported by the invertible rational change of
coordinate and gauge above, says that `H_an` is not rational.  The
specialization theorem of Adamczewski--Faverjon therefore applies: for every
`g>=1`,

```text
H_an(alpha^g) is transcendental.                   (HS28)
```

Their homogeneous lifting theorem says that an algebraic linear relation
between `1` and `H_an(alpha^g)` would lift to a rational-function relation
between `1` and `H_an`; regularity excludes the exceptional-value escape.
Since an ordinary payload would give

```text
H(alpha^g)=alpha^(2g) F(g) in Q,
```

the regular analytic Mahler solution cannot be that payload.  This is a
source-audited application of a published transcendence theorem, not a new
kernel proof of Mahler's method.  The exact coordinate change, finite
unrolling, and boundary split are kernel-checked in
[`DoublingQuineMahlerNormalForm.lean`](../../KontoroC/KontoroC/DoublingQuineMahlerNormalForm.lean).

Crucially, HS28 does **not** close the discrete return.  An ordinary solution
must have

```text
H = H_an + K,
K(alpha^(2^N g)) = lambda^(-N) K(alpha^g),          (HS29)
```

with `K(alpha^g)` canceling the transcendental particular value.  Such a
`K` cannot be holomorphic at zero.  In the real coordinate
`t=log(1/x)`, the homogeneous equation is `k(t)=lambda*k(2t)`; its general
shape is a power of `t` times a one-periodic function of `log_2 t`.
Therefore the live object is not a more complicated regular power series.
It is a **log-singular homogeneous boundary section on one dyadic opcode
ray**, with enough arithmetic structure to make every recovered `F(2^N g)`
positive odd and to satisfy the exact router valuations.

### 14.2 What `x2/x3` rigidity does and does not close

The constants in `alpha` involve both primes two and three, but HS24 has only
one dynamical dilation, `x -> x^2`.  Classical `x2/x3` rigidity does not arise
merely because the evaluation point is an `S`-unit.  Adamczewski--Bell says
that a characteristic-zero power series which is both 2-Mahler and 3-Mahler
is rational.  Consequently, if a proposed public payload is also compatible
with an independent canonical update `g -> 3g` (or otherwise supplies a
genuine 3-Mahler equation for the same regular germ), rigidity makes it
rational and Section 13 kills it.

This closes bi-scale automaticity and any attempt to gain regeneration by
imposing two independent commuting opcode dilations.  It does not touch one
orbit-specific dyadic ray `g,2g,4g,...`, nor the singular homogeneous section
in HS29.  The constructive search must therefore be rank one in opcode scale
and use its unbounded arithmetic payload, not a finite object natural under
both `x2` and `x3`.

### 14.3 The `5x+1` control identifies the missing invariant

The 5x+1 Terras map is the necessary control.  Its finite parity coding and
its Haar dynamics on `Z_2` are the same full Bernoulli shift as for 3x+1,
while its Archimedean cocycle has the opposite mean sign:

```text
(1/2)log 3 - log 2 < 0,
(1/2)log 5 - log 2 > 0.                            (HS30)
```

The first inequality predicts contraction for 3x+1 and the second predicts
growth for 5x+1; Kontorovich--Lagarias emphasize that the two maps are
topologically and measurably conjugate on `Z_2` despite this opposite
integer-side behavior.  It remains open to prove even one specific divergent
5x+1 orbit, so this is a control, not a theorem that can be imported to finish
the construction.

The control nevertheless gives a sharp methodological verdict.  Any
obstruction depending only on the parity address, 2-adic regularity, or a
regular Mahler germ is missing the invariant that distinguishes 3 from 5.
The three-word outward code conditions the 3x+1 dynamics onto a positive
Archimedean cocycle, deliberately making its exceptional orbit look like the
typical 5x+1 model.  The nonzero boundary term in HS25 is exactly the datum
that records that distinction.  A successful construction must couple it to
the **3-specific** divisibility and odd-cofactor laws of the typed router.

The verdict is therefore asymmetric:

- regular analytic Mahler payload: **wall**;
- simultaneous 2-Mahler/3-Mahler or bi-scale automatic payload: **wall**;
- singular homogeneous section on one dyadic opcode ray, synchronized with
  the exact 3x+1 router: **construction site**.

References: B. Adamczewski and C. Faverjon,
[*Méthode de Mahler: relations linéaires, transcendance et applications aux
nombres automatiques*](https://arxiv.org/abs/1508.07158), especially the
regular-point homogeneous lifting theorem and Corollary 1.5; B. Adamczewski
and J. P. Bell, [*A problem around Mahler
functions*](https://arxiv.org/abs/1303.2019); A. V. Kontorovich and
J. C. Lagarias, [*Stochastic Models for the 3x+1 and 5x+1
Problems*](https://arxiv.org/abs/0910.1944), especially Theorems 2.1, 7.1,
and Sections 8.2 and 10.

## 15. A two-place slope obstruction closes the singular doubling ray

Section 14 correctly identified the logical gap left by regular Mahler
theory, but its final construction-site verdict for this *particular* return
is superseded by a direct integer argument.  Write the cleared legal return
at opcode `g` as

```text
3^R F(g)=C(g)+2^S F(2g),
P=23g+54, Q=17g+40, R=194+34g, S=262+46g.
```

The four monomials of `C` have the exact factorization

```text
3^(2Q)(A F(g)-b0)
 =2^(77+P)(3^Q+2^P+2^(77+P)F(2g)),                (HS31)
A=3^114, b0=3^57+2^77.
```

For positive natural payloads the right side is positive.  Coprimality of
two and three therefore gives the strict forced-precision bound

```text
2^(131+23g)<A F(g).                                (HS32)
```

The same return supplies the opposite estimate without any asymptotics.
Because `C(g)>0`, and because the exact coarse comparisons
`3^34<2^54` and `3^194<2^308` hold,

```text
F(2g)<2^(46+8g)F(g).                               (HS33)
```

Along `g_n=g_0 2^n`, iteration of HS33 gives

```text
F(g_N)<=F(g_0) 2^[46N+8g_0(2^N-1)].               (HS34)
```

But HS32 at `g_N` has exponent `131+23g_0 2^N`.  After also using
`A<2^181` and `F(g_0)<2^F(g_0)`, the explicit choice
`N=F(g_0)+4` makes the HS32 lower bound exceed the complete HS34 upper
bound.  This is a contradiction.  Lean checks the factorization, both
bounds, the finite iteration, the explicit exponent gap, and the final
theorem `no_positive_integer_doubling_chain` in
[`DoublingQuineIntegerNoGo.lean`](../../KontoroC/KontoroC/DoublingQuineIntegerNoGo.lean).

This is not merely another no-go for a function class.  It is a reusable
**two-place slope test** for proposed autonomous returns.  A return that
forces `2^(ell*g)` precision in a fixed nonzero rational approximation while
allowing only `2^(u*g+O(1))` positive real growth per scale-doubling step is
impossible whenever `ell>u`: both exponents accumulate at the terminal scale,
but with incompatible slopes.  Thus a viable counterexample compiler must
change at least one structural quantity:

- regenerate real height at slope at least the forced dyadic-precision slope;
- distribute precision across several state variables so it is not a fixed
  rational approximation by one positive integer; or
- replace rank-one scale doubling by a return whose accumulated height budget
  is not dominated by the terminal precision demand.

The singular boundary mechanism remains conceptually important for other
architectures, and the 5x+1 control still rules out parity-only reasoning.
What is closed is the exact rank-one four-cell `g -> 2g` quine, including
every arbitrary positive integer section on its opcode ray.
