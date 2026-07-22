# The standard two-rail schedule as a 2-adic partial theta value

## Scope

This note isolates and closes the ordinary-integer gate for the standard
splash schedule.  Lean and exact arithmetic identify one familiar 2-adic
special value; a published Väänänen--Wallisser linear-independence theorem,
with every application hypothesis audited below, proves it irrational.  This
rules out one infinite gate schedule.  It does not prove or disprove Collatz.

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

Any theorem proving this 2-adic value irrational rules out an ordinary
standard schedule immediately: a positive ordinary payload `U_5` would be a
rational integer.  A full-source theorem does apply.

Väänänen and Wallisser's 1989 paper, [*Zu einem Satz von Skolem über lineare
Unabhängigkeit von Werten gewisser
Thetareihen*](https://gdz.sub.uni-goettingen.de/download/pdf/PPN365956996_0065/LOG_0016.pdf),
studies

```text
f_q(x) = sum_(n>=0) q^(-n(n+1)/2) x^n,
f_q(qx) = x f_q(x) + 1.
```

Our value is exactly

```text
F(2/3, 2^13/3^9) = f_(3/2)(2^12/3^8).       (6)
```

Use their theorem with `ell=1`, derivative order `sigma=0`, `q=3/2`,
`alpha=4096/6561`, and `p=2`.  The nonzero-rational and reduced-`q`
hypotheses are immediate, and the distinct-argument ratio condition is
vacuous for one argument.  Their only delicate size condition becomes

```text
gamma = 1 - log(2)/log(3) < (3-sqrt(5))/2 = Gamma.
```

This needs no floating-point estimate.  The rational separator `3/8` works:

```text
2^8=256 > 243=3^5       => gamma < 3/8,
5*4^2=80 < 81=9^2       => 3/8 < Gamma.
```

The theorem therefore makes `1` and the value in (6) linearly independent
over the rationals in `Q_2`; in particular, (6) is irrational.  Consequently
the candidate in (5) is irrational and cannot equal the positive integer
`U_5`.  The complete standard schedule has no ordinary positive payload
stream.

Lean commit `3fc63a6` proves the function substitution for every coefficient,
the logarithmic and square-root inequalities, and the final implication from
irrationality of the explicit `Q_2` value to nonexistence of the normalized
payload stream.  The Väänänen--Wallisser linear-independence theorem remains a
cited external theorem rather than a new axiom or a reproof inside Lean.

[`standard_two_rail_irrationality.py`](../../experiments/kontorovich/standard_two_rail_irrationality.py)
checks the function substitution coefficientwise with exact fractions and
checks both strict inequalities as integer comparisons.  Its certificate is
an exact hypothesis/application audit of the cited theorem, not a reproof of
Väänänen--Wallisser.

For calibration, Väänänen and Wallisser's later 1991 paper, [*A linear
independence measure for certain p-adic
numbers*](https://doi.org/10.1016/0022-314X(91)90045-D), studies the same
function in the reciprocal notation, but the 1989 open full text is already
sufficient.  Zudilin's [real/complex irrationality
  theorem](https://arxiv.org/abs/math/0506086) uses the equivalent notation
  `T_q(z)=sum z^n q^(-n(n-1)/2)`.  Our value has `q=3/2`, but his displayed
  hypothesis requires
  `log|q_2|/log|q_1| < (3-sqrt(5))/2`; here
  `log(2)/log(3)≈0.63093>0.38197`.  That theorem does not apply.

## 4. Why this is the right next attack

The recurrence absorbed all 10,040 digits and all 247 finite gates into one
special value; the published irrationality theorem then closes the all-level
standard controller without any larger trajectory search.  This is a useful
pattern for the disproof program even though the outcome here is negative:
reduce each low-description schedule to its `Q_2` value, then either prove the
value nonrational or exploit a rational exception as a candidate ordinary
program.  The remaining two-rail search must vary or branch its gate shapes;
the rigid `[1]^r ++ [2,2,3]` schedule is closed.
