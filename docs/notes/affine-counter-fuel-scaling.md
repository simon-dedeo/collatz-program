# Recurrent boosts and the binary-counter scaling wall

## Question

Can the present Collatz gate systems turn an `n`-bit seed into `2^n`
controlled steps by storing an ordinary binary countdown and repeatedly
returning to a boost instruction?

The answer for the two natural one-parameter implementations is no.  One is
algebraically impossible; the other stores the proposed binary counter in
unary space.  A genuine two-coordinate counter/fuel cell does exist, and it
can boost for any prescribed finite number of rounds, but its exact address
cost is linear in the number of rounds.  Thus the checked construction gives
`Theta(n)` controlled time from `n` actual seed bits, not `2^n`.

Nothing here is a Collatz counterexample or an upper bound on what other seed
families could do.

## 1. The current standard family

For `R` regenerated two-rail rounds, exact summation of the checked schedule
gives

```text
seed bits       <= (R^2 + 23R + 12)/2,
accelerated steps = (R^2 + 13R)/2,
total halvings    = (R^2 + 21R)/2,
ordinary steps    = R^2 + 17R.
```

Consequently both programmed accelerated and ordinary time are linear in the
seed bit length.  The number of semantically interesting regenerated rounds
is only `Theta(sqrt(n))`.  At `R=247` the exact replay has a 33,351-bit seed,
32,110 programmed accelerated steps, and 65,208 programmed ordinary steps.

## 2. Why the YAH lift parameter is not a binary counter

The lift decoder's source packet is

```text
2(01)^(17+128t).
```

It has exactly `35+256t` ternary cells.  Its canonical numerical value has an
implicit leading ternary one, so its binary bit length is strictly larger
than its displayed cell count.  If an `m`-bit logical countdown is represented
by `t=2^m-1`, the actual seed therefore needs at least

```text
36 + 256(2^m-1)
```

binary bits.  A hypothetical `t -> t-1` instruction would be exponential
only in the short *description* of `t`; it would be linear in the actual seed
size.  The existing full-period YAH carry clock has the same accounting
problem: its states occur across a spatially repeated block.

## 3. Scalar affine decrement is impossible

Every fixed finite valuation word has an integer endpoint balance

```text
2^S y = 3^O x + delta.
```

Suppose one word acted as a decrementer on two adjacent members of a scalar
affine counter family.  The source pair and target pair would have the same
nonzero spacing `d`:

```text
x -> y,
x+d -> y+d.
```

Subtracting their endpoint balances gives

```text
2^S d = 3^O d,
```

hence `2^S=3^O`.  For a nonempty Collatz word `S>0`; parity makes that
impossible.  [`AffineBinaryCounterNoGo.lean`](../../KontoroC/KontoroC/AffineBinaryCounterNoGo.lean)
kernel-checks the general statement and the affine-decrement specialization.
The result also covers any finite composition which returns to the same
scalar affine chart, because the composition is again one affine balance.

This does **not** rule out payload-dependent words, nonlinear encodings, or a
state with more than one independently recoverable coordinate.

## 4. An exact counter/fuel boost cell

The shortest useful two-coordinate instance found in the exact search is the
valuation word

```text
[1,1,2],             16y = 27x + 19.
```

Define

```text
x(c,u) = 16c + 176u + 7.
```

Whenever

```text
16u' = c + 27u + 2,
```

literal accelerated Collatz execution has valuations `[1,1,2]` and lands at

```text
y = x(c-1,u').
```

Moreover `y>x` for every natural `c,u`.  Thus each cell is genuinely a
strict boost, not merely a bookkeeping round.  The semantic companion
[`AffineCounterFuelCell.lean`](../../KontoroC/KontoroC/AffineCounterFuelCell.lean)
checks the literal word, endpoint linkage, counter decrement, and strict
outwardness for all linked natural inputs.  The scalar no-go is kept in a
small algebra-only module so it can compile without importing the Collatz
semantics.

The checks can therefore be run at two dependency levels:

```bash
cd KontoroC
lake build KontoroC.AffineBinaryCounterNoGo   # small algebra-only graph
lake build KontoroC.AffineCounterFuelCell     # adds literal Collatz semantics
```

The more general identity explains the mechanism.  Put

```text
A=2^S, C=3^O, B=C-A,
E(c,f)=A c + B f + e.
```

Then the source fuel `f=A u` can be transformed to

```text
f' = c + C u + gamma
```

while decrementing `c`; the second coordinate absorbs the `C/A` slope
mismatch.  This is precisely the freedom absent from a scalar affine chart.

## 5. Why it is still only linear

For an `R`-round countdown the linkage equations determine the initial fuel
in one residue class modulo

```text
16^R = 2^(4R).
```

The worker solves that congruence exactly, chooses its least nonnegative
representative, and replays every cell.  Uniformly,

```text
seed bits        <= 4R+9,
accelerated steps = 3R,
ordinary steps    = 7R,
strict boosts      = R.
```

So one may set the *logical* counter to `R=2^m`, but the required fuel residue
then contains `4R` actual bits.  The construction has merely moved the unary
program tape into a dyadic address.  It is a clean recurrent-boost system,
but not exponential scaling.

The exact Python artifact replays countdowns through `R=1024`, checks the
standard two-rail formulas through `R=247`, and audits the YAH bit accounting:

```bash
python3 experiments/kontorovich/affine_counter_fuel.py selftest
python3 experiments/kontorovich/affine_counter_fuel.py verify \
  experiments/kontorovich/affine_counter_fuel_audit.json
```

## 6. The remaining target

To obtain `2^n` controlled steps from `n` **actual** seed bits, a system must
regenerate the address information it consumes.  For this cell that means a
writer which restores four correct low fuel bits per decrement.  Merely
multiplying the fuel by `27/16` grows its magnitude but does not create the
required residue: an `R`-step preimage is still a unique class modulo
`16^R`.

The smallest live specification is therefore:

1. a counter coordinate recoverable from the public integer over an
   exponentially large window;
2. a separate fuel/scale coordinate which absorbs `3^O/2^S`;
3. both low-bit branches, including a writer branch that replenishes at least
   as many address bits as the next decoder consumes;
4. an exact return to the same finite set of public chart types;
5. total seed bit length `O(m)` for a counter range `2^m`.

The long-return two-rail system already exposes the right kind of two-rail
public state `(F,u)`, but no checked writer presently satisfies item 3.  That
writer—not another scalar decrement congruence—is the next high-leverage
construction target.
