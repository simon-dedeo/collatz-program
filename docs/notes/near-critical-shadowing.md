# Near-critical shadowing: the crack is indexed by convergents of log2(3)

The three-word lane is uniformly supercritical: its slowest words have
`T/S = 2/3 > log(2)/log(3) = 0.6309`, so no in-lane address is near-critical.
This note quantifies what happens in the full valuation-word language of the
accelerated odd map `T(x) = (3x+1)/2^(v2(3x+1))`, where contracting words
exist — the only region where the classical transcendence machinery has
known soft spots.  Result: the softness is real but pays exponentially, and
its exact price is the linear-forms-in-logarithms quantity `|2^S - 3^n|`.

## 1. Shadowing bound in the full language

For a valuation word `V = (v_1..v_n)`, width `S`, offset `A_V`, the composed
map is `2^S T^n(x) = 3^n x + A_V`; exact-valuation cylinders are single
classes mod `2^(S+1)`; the point with address `V^infinity` is
`xi_V = A_V/(2^S - 3^n)`, negative for expanding words and **positive** for
contracting ones (a rational would-be cycle with odd denominator
`d = |2^S - 3^n|`).  The same argument as the in-lane repetition bound gives:
if an odd integer `x` follows `V^k` exactly and is not literally on the
rational cycle, then `2^(kS)` divides the nonzero integer
`(2^S - 3^n) x - A_V`, hence

```text
k <= log2(d x + A_V)/S.                             (SB)
```

For integer `x` the excluded case `x = xi_V` is a genuine Collatz cycle
(none below the `2^71` verification bound; Hercher's cycle bounds apply
beyond).  Verification and two sharp exhibits
([experiments/word-atlas/atlas.py](../../experiments/word-atlas/atlas.py)):

- the `-5` cycle word `(1,2)` (`d = 1`): `x = 2^(3k+1) - 5` follows
  `(1,2)^k` for exactly `k` periods against a bound of `k + 0.33` — (SB) is
  achieved;
- the contracting convergent word `(2,2,2,1,1)` (`S,n = 8,5`, `d = 13`,
  drift `243/256`): minimal integer shadows grow `129, 60545, 1.29e7,
  1.32e9` per extra period, tracking (SB).

## 2. The crack index

At fixed width, the words allowing the deepest integer shadowing are those
minimizing `d = |2^S - 3^n|`: exactly the continued-fraction convergents of
`log2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]`.  Depth caps below the
verification bound `x <= 2^68`:

```text
(S,n)      d/3^n       shadow cap (periods)
(2,1)      3.3e-1      34.0
(3,2)      1.1e-1      22.7      (the -5 cycle)
(8,5)      5.4e-2       9.0      (the 13-denominator cycle)
(19,12)    1.4e-2       4.3
(65,41)    1.2e-2       1.9
(84,53)    2.1e-3       1.7
(485,306)  1.0e-3       1.1
```

Two readings.

1. **For the counterexample program.**  A near-critical divergence
   certificate must keep an integer inside contracting-word cylinders for
   unbounded depth.  (SB) prices that: depth `k` costs height
   `2^(kS)/d`.  The only parameter that could cheapen it is `d` small
   relative to `2^S`, i.e. abnormally good rational approximations to
   `log2(3)`.  Effective irrationality measures for `log2(3)`
   (Baker-descendant bounds, e.g. Rhin-type; citation boundary, not
   re-derived here) cap this: `d >= 2^S / S^mu` for an effective `mu`,
   so the shadow cap gains at most `O(mu log S / S)` — the crack is
   logarithmically thin, uniformly in the word.  A stationary machine
   exploiting it would need its own opcode data to compress the convergent
   structure of `log2(3)`; nothing in the current ISA does this.
2. **For the proof direction.**  (SB) is a clean, Lean-able statement that
   integer orbits cannot shadow any periodic pattern — expanding or
   contracting — deeper than `log2(height)/S + log2(d)/S` periods.  It
   subsumes the in-lane repetition bound (there `d ~ 3^(t_V)` is large,
   which is why the lane is rigid) and makes the drift-independence of the
   phenomenon explicit: what varies with drift criticality is only the
   constant `log2(d)`, i.e. the Baker quantity.

## 3. Placement

Together with [address-repetition-bound.md](address-repetition-bound.md)
and [doubling-payload-rigidity.md](doubling-payload-rigidity.md), the
geography is now uniform in one respect: every lane's obstruction has been
reduced to an explicit Diophantine quantity — the repetition exponent
`log2(3)` (in-lane), the 2-adic Mahler value `F_0(g)` (doubling return),
the convergent denominators `|2^S - 3^n|` (near-critical).  These are the
three classical faces of the multiplicative independence of 2 and 3, which
is the single principle the counterexample architecture keeps colliding
with.  Any future lane proposal should state up front which of the three
faces it intends to evade, and at what quantified price.
