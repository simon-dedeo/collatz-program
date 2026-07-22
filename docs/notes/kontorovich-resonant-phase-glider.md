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

### 3.1 Fixed jump is still too rigid

The one-counter policy above does not survive the ordinary-integer gate.  In
fact the same argument closes every fixed jump `k>=1`.  Write

```text
h=391k+1,                 m_i=m_0+4ki.
```

In the canonical cofactor, PC4 is the subtraction-free natural recurrence

```text
2^(154h+23m_(i+1)) w_(i+1)
  +(3^(114h)-2^(154h))
  =3^(114h+17m_i) w_i.                            (RG9)
```

Exact backward unrolling forces one 2-adic initial cofactor.  Coefficientwise
it is a nonzero rational multiple of Väänänen--Wallisser's

```text
f_q(alpha),
q=3^(68k)/2^(92k),
alpha=2^(23m_0+154h)/3^(17m_0+114h).              (RG10)
```

Their 1989 main theorem applies with `ell=1`, derivative order zero, and
`p=2`.  The argument-ratio condition is vacuous.  The only delicate size
parameter is

```text
gamma=1-23 log(2)/(17 log(3)),
```

and the already audited exact inequalities `3*23>=4*17`, `2^8>3^5`, and
`45<64` give
`gamma<1/6<(3-sqrt(5))/2`.  Hence `f_q(alpha)` is irrational in `Q_2` and
cannot equal an ordinary integer cofactor.  Lean's
`ChargePhaseUpTheta.lean` checks RG9, the full finite and completed-series
unrolling, the coefficientwise RG10 conversion, and the implication from the
external irrationality statement to no ray.  The transcendence theorem
itself remains cited external mathematics, exactly as in the prior
constant-rate unit-clock audit.

So causal control was necessary but not sufficient.  The fixed-rate counter
still writes an irrational infinite 2-adic tape.  Any constructive use of the
phase glider must vary `k` or direction from public payload infinitely often,
and must do so in a way that makes the resulting debris series telescope or
otherwise become rational.

There is also a schedule-independent interface obstruction.  Put

```text
tau_m=3^(-17m),       beta_m=2^(-23m),
a=2^(154h+23m')/3^(114h+17m).
```

Every public cofactor step, up or down, has the exact normal form

```text
w-tau_m = a (w'-beta_m').                         (RG11)
```

Since `tau_m-beta_m<0`, composing cells creates one strictly negative
ordinary mismatch at every internal boundary.  Hence phase-up and phase-down
are not complementary bare opcodes: both are ternary-entry to binary-exit
instructions.  A finite word cannot become a debris-free chart converter
merely by returning its phase.  A useful turnaround must carry an additional
public correction rail—most plausibly the intercept of a resonant affine
embedding—which converts the binary exit chart back to the ternary entry
chart.  This is the precise algebraic target behind “splash, scrub, reseed.”

There is also a discrete fuel law before tails are considered.  A parallel
resonant cell starts with the two opcode charts separated by `2622k` phase
units and ends with them separated by `2618k`.  To use that target pair as the
source pair of the next resonant cell requires

```text
2622 k_(i+1)=2618 k_i,
1311 k_(i+1)=1309 k_i.                            (RG12)
```

Because `1309` and `1311` are coprime, an `N`-cell ladder forces
`1311^N | k_0`.  No positive finite initial separation feeds an infinite
ladder.  Opposite phase motion does not change this inter-chart contraction:
it only changes which chart is called moving.  Thus the present conjugacy
cell consumes two units of resonant separation every time it runs.  A genuine
turnaround needs a complementary **phase booster** with inverse expansion
`1311/1309`, or another public operation that regenerates that separation.
This is the spatial closure principle: the glider must reproduce its chart
gap as well as its data payload.

### 3.2 A word-level phase swap evades the one-cell fuel loss

The separation law also says how to escape it: the two charts must cross
inside a longer word.  For two equal-total-gain words with boundary phase
differences `d_0,...,d_N`, eliminating their recharge differences gives

```text
1311 d_N-1309 d_0=-2 sum_(0<i<N) d_i.             (RG13)
```

Thus a word which restores a positive endpoint separation must have negative
signed separation internally.  The minimal construction is

```text
W_r=[(r,h_0,L-r),(L-r,h_1,r+d)].                  (RG14)
```

Consecutive words `W_r,W_(r+d)` have boundary differences `(d,-d,d)`
and the identical total exponents

```text
Q=114(h_0+h_1)+17L,
P=154(h_0+h_1)+23(L+d).                           (RG15)
```

This is a true two-opcode phase-swap at the exponent level: the outer phase
advances while the middle phase retreats.  The exact research artifact checks
the smallest phase line

```text
1 -> 3 -> 2,
2 -> 2 -> 3,
3 -> 1 -> 4
```

with `h_0=h_1=1`.  Both adjacent composite maps have `P=423,Q=296`, gcd-one
affine conjugacies, exact nested source-cylinder embeddings, and sixteen
arithmetic-bouncer step replays.  But the conjugacy-selected next input is
strictly larger than the current output for every nonnegative tail: its
constant term and its slope `2^P s` both exceed those of
`sigma+3^Q u`.  These are parallel commutative squares, not orbit links along
the advertised embeddings.  The rays do have distinct direct coprime handoff
progressions `u=u0+2^P t`, `v=v0+3^Q t`, which the updated artifact replays;
those are fresh dyadic cylinder selections and do not preserve the conjugacy
or regenerate their address.  Fixed `L` would also be finite fuel.
Reproduction therefore needs two gates: first a self-writing typed handoff,
then a turnaround replacing exhausted `L` by a larger public `L'`.

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
   move (every fixed positive `k`, direction up, is closed by RG9--RG10);
3. an exact turnaround which converts a finite down delay into a regenerated
   larger up delay; or
4. a nonlinear jump schedule whose forced 2-adic series can be proved to be
   one ordinary positive tail.

Items 1--3 must now be read through RG11: the desired object is a **typed
adapter**, not just a phase loop.  A schedule of period four is the first one
escaping the current multi-theta *bound*, but it still pays the same interface
tax and should not be searched blindly.  RG12 adds a second acceptance test:
the adapter must replenish resonant chart separation rather than spend a
finite stock of it.

The first three are versions of Simon's “splash the gap”: the four-cell phase
is the moving gap, while the 21,330-digit affine tail is the remote payload.
The fourth remains an ordinary-versus-2-adic question, but fixed-rate RG8 is
now closed.  It should be attacked by a rational coboundary or another
symbolic value theorem, not by extending finite prefixes.

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
- derive the exact nested-tail series for a *variable*, publicly decoded jump
  law and make it telescope to an ordinary natural (fixed jump is closed);
- classify when RG5 fails or succeeds along a whole phase walk; and
- solve the telescoping equations `E_(r+4) after E_r` before searching any
  larger opcode box.

The guiding distinction remains: this construction moves a boundary and
preserves an affine tail.  A counterexample needs the moved boundary to tell
the same mechanism what to do next.
