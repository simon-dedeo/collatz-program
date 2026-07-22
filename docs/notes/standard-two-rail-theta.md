# The standard two-rail schedule as a 2-adic partial theta value

## Scope

This note isolates the ordinary-integer gate for the standard splash schedule.
It does **not** prove irrationality and does not disprove or prove Collatz.
Its exact contribution is to identify one familiar special function whose
2-adic rationality decides whether this particular infinite gate schedule can
come from an ordinary positive seed.

## 1. Kernel-checked recurrence

For the standard two-rail gate

```text
s=1, a=b=1, L=r+2,
word = [1]^r ++ [2,2,3],
```

Lean commit `db0971c` proves the necessary payload recurrence

```text
2^(r+8) P_(r+1) = 3^(r+3) P_r + 69.          (1)
```

It also proves that every outgoing payload has exactly one factor of three.
After the first gate, write `P_r=3U_r`.  Equation (1) becomes

```text
2^(r+8) U_(r+1) = 3^(r+3) U_r + 23,   r>=5. (2)
```

Every exact infinite standard two-rail program would therefore supply a
positive odd integer sequence satisfying (2).  The converse is not automatic:
one must still reconstruct the odd intermediate `+1` payload and both gate
balances.

## 2. Exact unrolling

Solving (2) backwards gives

```text
U_5 = -23/3^8
      -23*2^13/3^17
      -23*2^(2*27/2)/3^(3*18/2)
      - ... .
```

More cleanly, the unique 2-adic candidate is

```text
U_5 = -(23/3^8) * sum_(n>=0)
        (2/3)^(n(n-1)/2) * (2^13/3^9)^n.     (3)
```

The `n`th unscaled term has exponents

```text
v_2 numerator = n(n+25)/2,
v_3 denominator = (n+1)(n+16)/2.
```

For `K>=1`, exact finite unrolling is

```text
U_5 = -23 * sum_(n=0)^(K-1)
              2^(n(n+25)/2) / 3^((n+1)(n+16)/2)
      + 2^(K(K+25)/2) U_(5+K) / 3^(K(K+15)/2).  (4)
```

The terminal term tends to zero in `Q_2`, proving (3).  It need not tend to
zero in the ordinary real interpretation along a hypothetical growing
positive sequence; no sign conclusion may be imported between completions.

[`standard_two_rail_theta.py`](../../experiments/kontorovich/standard_two_rail_theta.py)
checks (1), the exact factor of three, (2), and (4) against every payload in
the depth-247 compiler.  Its terminal congruence reaches 33,333 bits of 2-adic
precision.  The check is exact integer arithmetic, but it is only a finite
regression for the displayed all-level algebra.

## 3. Tschakaloff identification

For

```text
F(q,z) = sum_(n>=0) q^(n(n-1)/2) z^n,
```

equation (3) is

```text
U_5 = -(23/3^8) F(2/3, 2^13/3^9).             (5)
```

Thus any theorem proving this 2-adic value irrational would rule out an
ordinary standard schedule immediately: a positive ordinary payload `U_5`
would be a rational integer.

The literature audit is promising but deliberately incomplete.

- Väänänen and Wallisser's 1991 paper, [*A linear independence measure for
  certain p-adic numbers*](https://doi.org/10.1016/0022-314X(91)90045-D),
  studies exactly `F(q,z)` for rational `q` with `0<|q|_p<1`.  Our parameters
  have `p=2`, `q=2/3`, so they pass the condition visible in the abstract.
  The full theorem says “certain values”; its remaining height, orbit, and
  exceptional-point hypotheses have not yet been checked line by line.  The
  abstract is not treated as a certificate.
- Zudilin's [real/complex irrationality
  theorem](https://arxiv.org/abs/math/0506086) uses the equivalent notation
  `T_q(z)=sum z^n q^(-n(n-1)/2)`.  Our value has `q=3/2`, but his displayed
  hypothesis requires
  `log|q_2|/log|q_1| < (3-sqrt(5))/2`; here
  `log(2)/log(3)≈0.63093>0.38197`.  That theorem does not apply.

Until the 1991 hypotheses are recovered and checked—or the one-value case is
reproved—(5) is a target, not a no-go theorem.

## 4. Why this is the right next attack

The recurrence has already absorbed all 10,040 digits and all 247 finite
gates into one special value.  More range search is irrelevant.  There are
now two crisp outcomes:

1. prove the value in (5) is irrational in `Q_2`, closing the complete
   standard schedule; or
2. if it is rational, compute and audit the rational value, then test the
   positivity, oddness, and eliminated-`Q` gate conditions required to turn it
   into an actual infinite program.

Either outcome is a theorem about an all-level controller rather than a long
trajectory.
