# Stopping-time scaling from actual seed bits

Date: 2026-08-04

## Target

For the ordinary Collatz map, let `tau(n)` be the first time the orbit of a
positive terminating seed `n` reaches `1`, and let

```text
b(n) = floor(log_2 n) + 1
```

be its actual binary length.  The target is an explicit infinite family
`n_m` for which

```text
tau(n_m) / b(n_m) -> infinity.
```

Thus `tau(n_m) >= b(n_m)^2` would already succeed.  Exponential scaling,
such as `tau(n_m) >= 2^(c b(n_m))`, is a stronger target.  A long programmed
prefix is not enough: every member of the family must also be proved to
reach `1`.

## Exact compositional principle

The most local useful object is a **terminating detour wrapper**.  It consists
of encoded states `s`, a wrapping operation `W`, and a delay `d(s)` such that

```text
b(encode(W(s))) <= b(encode(s)) + C,
T^[d(s)](encode(W(s))) = encode(s),
T^[j](encode(W(s))) != 1                 for 0 <= j < d(s).
```

The second and third lines are finite literal Collatz claims.  They imply
that any certified terminating tail from `encode(s)` may be prepended to the
detour.  If `s_m=W^m(s_0)`, then

```text
b(encode(s_m)) <= b(encode(s_0)) + C m,
tau(encode(s_m)) >= L_0 + sum_{i<m} d(s_i).
```

This gives two exact sufficient principles.

1. **Polynomial principle.**  If `d(s_m) >= 2m+1`, then the first `m` delays
   sum to `m^2`, so the lifetime is quadratic in construction depth while
   the bit cost is linear.  More generally, delays of order `m^(k-1)` give a
   degree-`k` lifetime lower bound.
2. **Exponential principle.**  If the new delay is at least the lifetime
   accumulated before that level, the certified lifetime doubles at every
   wrapper.  With at most `C` new bits per wrapper, this gives
   `2^m` steps in `B_0+C m` bits, or exponential growth with base
   `2^(1/C)` per actual bit.  Literal `2^b` scaling would require the sharp
   one-bit/one-doubling case (`C=1`), up to the fixed initial overhead.

This formulation identifies the missing resource precisely.  A construction
must not merely encode a long prescribed word; it must return to the previous
encoded state so that the old terminating tail is reused.  That return is the
source of compression.

## Kernel-checked interface

`KontoroC/KontoroC/StoppingTimeScaling.lean` now checks:

- `ExactPrefix.prepend`, the finite detour-composition theorem;
- `EncodedDetourWrapper.toAccumulatingScalingCertificate`;
- the partial-sum lifetime theorem for additive delays;
- the exact identity `sum_{i<m}(2i+1)=m^2` and the resulting quadratic bound;
- exponential scaling when each new gain dominates the accumulated duration;
- the more abstract bounded-bit multiplicative renormalizer theorem; and
- the calibration family `n_m=2^m`, which has `m+1` bits and exactly `m`
  steps before reaching `1`.

These are conditional construction theorems, not a constructed superlinear
Collatz family.  They are stated using actual binary length and retain an
explicit termination witness.

## Audit of the present seed systems

The existing constructions do not meet the criterion.

| family | actual-bit upper bound | certified ordinary time | scaling |
|---|---:|---:|---|
| powers of two | `m+1` | `m` | linear |
| standard `R`-round two-rail | `(R^2+23R+12)/2` | `R^2+17R` | linear in bits |
| `[1,1,2]` counter/fuel cells | `4R+9` | `7R` programmed steps | linear in bits |
| YAH packet with `t=2^m-1` | at least `36+256(2^m-1)` | apparent `m`-bit counter | unary payload |

For the two-rail family, both storage and time are quadratic in `R`; their
ratio tends to a constant.  In the counter/fuel family, every cell consumes
four dyadic address bits and returns only constant delay.  The construction
would become quadratic if the `m`th bounded-cost cell returned a delay of
order `m`, and exponential if it recreated a detour at least as long as the
entire inner run.  At present it does neither.

## Research direction

The next search should target a literal return gadget, not another long open
prefix.  A candidate must supply:

```text
new encoded seed --d_m literal Collatz steps--> old encoded seed
```

with a proof that the prefix avoids `1`, bounded added binary length, and a
delay law growing with the wrapper level.  Promising representations are
multi-rail affine states in which one rail is an invariant payload and the
other rails implement a self-delimiting excursion.  The decisive accounting
question is whether the excursion regenerates its dyadic address rather than
consuming a fresh unary residue class.

Finite search can discover candidate wrappers, but the acceptance test must
be symbolic: one affine identity valid for an infinite encoded state family,
plus exact parity/valuation conditions and a bounded-bit recurrence.

## Literature position

Applegate and Lagarias proved that infinitely many terminating seeds have
shortcut total stopping time greater than `6.14316 log n`.  This is a major
rigorous lower bound, but it remains linear in binary length (about `4.25811`
steps per bit under their shortcut convention).  Stochastic models of
Kontorovich and Lagarias likewise place extremal stopping times on a constant
multiple of `log n`, not on a known superlinear scale.  We found no published
explicit infinite family for the ordinary integer Collatz map with
`tau(n)/log n -> infinity`.

There is a useful nearby contrast: for a Collatz analogue over `F_2[x]`,
Alon, Behajaina, and Paran prove a subquadratic `O(deg(f)^(3/2))` upper bound
and structured stopping-time phenomena.  This shows that polynomial scaling
questions are natural in algebraic analogues, but it does not transfer a
superlinear lower-bound family to the integer problem.

Primary references:

- D. Applegate and J. C. Lagarias, *Lower bounds for the total stopping time
  of 3X+1 iterates* (2003), arXiv:math/0103054.
- A. V. Kontorovich and J. C. Lagarias, *Stochastic models for the 3x+1 and
  5x+1 problems and related problems* (2010), arXiv:0910.1944.
- G. Alon, A. Behajaina, and E. Paran, *On the stopping time of the Collatz
  map in F_2[x]* (2024), arXiv:2401.03210.
