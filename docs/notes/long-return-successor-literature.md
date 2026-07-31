# Literature audit for the successor zero-carry value

**Status (2026-07-30).** The eventual-zero-carry question for the six-cell
successor return reduces to one rational linear form in six 2-adic
Tschakaloff values.  No published theorem located in this audit proves that
linear form rational or irrational.  The closest broad theorem, Rochev
(2011), misses for one precise reason: the theta parameter expands at both
the real and 2-adic places.  This is a theorem-shaped research target, not a
proof of zero carry or of nonzero carries.

## 1. Exact theta normal form

Put

```text
c = 2^23/3^17,
z_g = 2^(23g+54)/3^(17g+40),
lambda = 2^154/3^114,
p(z) = (3^57+2^77 + 2^77(z+...+z^6))/3^114.
```

Then `z_(g+1)=c z_g`, and the six-cell balance is exactly

```text
F_g = p(z_g) + lambda z_g^6 F_(g+1).                 (LZ1)
```

Iterating from `g=g0` gives the unique 2-adic candidate

```text
sum_(t>=0) lambda^t z_g0^(6t) c^(3t(t-1)) p(c^t z_g0).
                                                               (LZ2)
```

For

```text
f_q(x)=sum_(t>=0) q^(-t(t+1)/2)x^t,
q=c^(-6)=3^102/2^138,
alpha_i=lambda*z_g0^6*c^(i-6),       0<=i<=6,
```

LZ2 is a rational linear combination of the seven values
`f_q(alpha_i)`.  These are only six independent theta slots: since
`alpha_0=q alpha_6`, the functional equation

```text
f_q(qx)=1+x f_q(x)
```

eliminates one endpoint.  The remaining arguments have pairwise ratios
`c^d`, `0<|d|<6`, hence no ratio is a power of `q`.  Thus the natural
published-theorem input is the family `1,f_q(alpha_1),...,f_q(alpha_6)`.

The scale is genuinely two-dimensional.  The constant part of
`lambda*z_g^6` and the step `c` have prime-exponent determinant `16`, so the
arguments are not exceptional integral powers of `q`.  The classical
theta-transcendence shortcut for `alpha=q^k` therefore does not apply.

## 2. What applies, and what does not

### Väänänen--Wallisser (1989)

Their local 2-adic theorem is the correct kind of statement and handles
several values, but its sufficient height threshold depends on the number of
theta slots.  Here

```text
gamma = 1 - 23 log(2)/(17 log(3)) = 0.146389...,
Gamma(6,0) = (13-sqrt(145))/12      = 0.079867... .
```

Thus the six-value sufficient inequality fails substantially.  The existing
periodic-theta formalization already proves the stronger separator
`Gamma(4,0)<1/8<gamma`, so adding values cannot repair this application.

### Amou--Väänänen (2005) and the Borel--Dwork route

This qualitative theory controls relations simultaneously over the full set
of places where the parameter expands.  For

```text
q=3^102/2^138
```

both `|q|_infinity>1` and `|q|_2>1`.  Eventual zero carry supplies only a
relation in `Q_2`, not the corresponding real relation.  The theorem
therefore does not decide the candidate.

### Amou--Matala-aho--Väänänen (2007), Väänänen (2013)

These Siegel--Shidlovskii-style results admit non-Archimedean places, but
their global height condition is already known to fail at the easier
three-value EC17 specialization.  Six values only worsen that dimension
cost.

### Bézivin (1988)

The p-adic theorem for `sum p^(M(n))z^n` removes a denominator-height problem
when the quadratic coefficient uses a single prime.  Our coefficient has
both a quadratic power of `2` and a quadratic unit denominator power of `3`.
The latter is invisible to the 2-adic norm but not to global height, so this
cannot be rewritten into Bézivin's one-prime class.

### Rochev (2011): the closest near-hit

Rochev proves linear independence of arbitrary finite families of values and
derivatives of a broad class of q-series over an algebraic number field at an
Archimedean or p-adic place `w`.  Unlike the 1989 theorem, the statement has
no dimension-dependent `Gamma(L,0)` gate.  Its standing arithmetic
hypothesis, however, is

```text
|q|_w > 1,             |q|_v <= 1 for every v != w.              (R)
```

Taking `w=2` fails (R) because the ordinary real absolute value of our `q`
is also greater than one.  This is not cosmetic: Rochev uses (R) to keep the
height of auxiliary forms small at every place other than the one where the
remainder decays.

The failure has a structural interpretation.  The inequality

```text
3^17 > 2^23
```

is what gives the six-cell return enough real gain to pay for its binary
precision.  The same inequality creates the second expanding place which
blocks Rochev's local theorem.  The construction crosses the Archimedean
precision wall and the arithmetic proof wall at the same slope.

### Pure q-difference Galois theory

Modern difference-Galois results establish functional algebraic
independence for suitable q-difference functions.  They do not automatically
lift that functional statement to a rational special value in `Q_2` when
the global parameter has two expanding places.  Functional
nonrationality is therefore useful input to a Padé proof, not the missing
value theorem itself.

## 3. Highest-leverage theorem to build

The most direct new attack is a **two-expanding-place, fixed-linear-form
version of Rochev's auxiliary construction** for `S={infinity,2}`.  It does
not need full six-value linear independence.  It only needs to exclude the
one coefficient vector forced by `p(z)`.

There are two plausible sources of extra cancellation unavailable to the
generic theorem:

1. Use Hermite--Padé approximants for the six arguments simultaneously, but
   optimize for the single known coefficient vector rather than all linear
   forms.  The generic `Gamma(6,0)` loss may then be avoidable.
2. Demand a remainder which is small at both expanding places.  The 2-adic
   smallness comes from the quadratic binary exponent.  At the real place,
   the original backward recurrence has positive terms and
   `lambda*z_g^6<1`; its special geometric polynomial may permit a
   telescoping or sign-controlled Padé remainder that a generic six-value
   theorem cannot use.

The first concrete algebraic task is to construct the minimal simultaneous
Hermite--Padé determinant for the six arguments and compute its exact
2-adic order and real height symbolically.  A surplus at this fixed vector
would prove nonzero carries arbitrarily late and close the successor lane.
A determinant collapse, on the other hand, would reveal the exceptional
rational identity needed for eventual zero carry.

## Sources

- K. Väänänen and R. Wallisser,
  [*Zu einem Satz von Skolem über lineare Unabhängigkeit von Werten gewisser
  Thetareihen*](https://gdz.sub.uni-goettingen.de/download/pdf/PPN365956996_0065/LOG_0016.pdf)
  (1989).
- M. Amou and K. Väänänen,
  [*Linear Independence of the Values of q-Hypergeometric Series and Related
  Functions*](https://doi.org/10.1007/s11139-005-1871-8) (2005).
- M. Amou, T. Matala-aho and K. Väänänen,
  [*On Siegel--Shidlovskii's theory for q-difference
  equations*](https://doi.org/10.4064/aa127-4-2) (2007).
- I. P. Rochev,
  [*Linear independence measures for values of certain
  q-series*](https://arxiv.org/abs/1102.2014) (2011), especially the standing
  single-expanding-place hypothesis and Theorem 1.
- K. Väänänen,
  [*On Tschakaloff, q-exponential and related
  functions*](https://doi.org/10.1007/s11139-012-9375-9) (2013).
- W. Zudilin,
  [*An elementary proof of the irrationality of Tschakaloff
  series*](https://arxiv.org/abs/math/0506086) (2005); its own final remarks
  record that removing the rational-height hypothesis is open even for one
  ordinary real value.
