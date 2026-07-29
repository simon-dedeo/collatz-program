# Integer no-go for the doubling-quine payload

This note records the route from 2-adic value rigidity to the complete
positive-integer no-go for the `g -> 2g` return left open by QM184.  Lemma V
first reduced the question to one explicit 2-adic constant per ray (QM185).
Section 7 supersedes that remaining seam by a kernel-checked elementary
precision-versus-height contradiction (QM187); the numerical floor in between
remains a reproducible historical check, not a premise of the final theorem.

## 1. Setting

All coordinates as in QM183/QM184 and Section 13 of
[counterexample-boundary-amplitude.md](counterexample-boundary-amplitude.md).
Any payload for the legal four-cell return with opcode update `g -> 2g`
satisfies the exact rational identity

```text
A F(g) - D z_g^2 F(2g) = b(z_g),                    (R)
A = 3^114,  D = 2^154,  z_m = 2^(23m+54)/3^(17m+40),
b(z) = (3^57+2^77) + 2^77 z + 2^77 z^2,
```

equivalently, in the QM184 Mahler normal form, `H(x)=Q(x)+lambda*H(x^2)` with
`lambda = 2^262/3^194` and evaluation points `x = alpha^g`, `alpha=2^23/3^17`.
Identity (R) is arithmetic over `Q`, so it holds simultaneously in every
completion.  QM184 closed regular analytic payloads through the
Adamczewski--Faverjon regular-point theorem (an Archimedean statement), and
left one survivor: a non-holomorphic homogeneous section `K` on a dyadic ray,

```text
K(alpha^(2^N g)) = lambda^(-N) K(alpha^g),          (QM184c)
```

whose boundary value would cancel the transcendental analytic value to
produce integer payloads.

## 2. Lemma U (formal uniqueness)

The homogeneous equation `A h(z) = D z^2 h(kappa z^2)` has only `h = 0` among
formal power series: comparing coefficients gives `h_k = 0` for `k` equal to
`0` and all odd `k`, and `A h_(2m+2) = D kappa^m h_m`, so every coefficient
is forced to zero by induction.  Hence (R) has exactly one solution of
function type analytic at `0`; call its coefficient series `f_0`.  This
matches the QM184b finite decomposition and is stated here only to fix
notation.

## 3. Lemma V (2-adic value rigidity on a ray)

The series

```text
F_0(g) = sum_(j>=0) A^(-1) (D/A)^j (prod_(i<j) z_(2^i g)^2) b(z_(2^j g))
```

converges 2-adically: its terms have exact valuation

```text
v2(t_j) = 262 j + 46 g (2^j - 1),                   (V1)
```

strictly increasing in `j`, with `v2(t_0)=0`; so `F_0(g)` is a 2-adic
integer and no partial sum equals the limit.  `F_0(g)` is the 2-adic
evaluation of `f_0` at `z_g`.

Now let `F` be ANY solution of (R) along one doubling ray `{2^N g}` with all
values in `Z_2` (positive integers qualify).  Set `Delta = F - F_0`.  Then
(R) gives

```text
Delta(2g) = (A/(D z_g^2)) Delta(g),
|A/(D z_g^2)|_2 = 2^(262+46g) > 1,
```

so `|Delta(2^N g)|_2 = |Delta(g)|_2 * 2^(sum_(i<N)(262+46g 2^i))` is
unbounded in `N` unless `Delta(g) = 0`.  Since `|Delta|_2 <= 1` everywhere on
the ray, `Delta` vanishes identically:

**every integer-valued payload equals, value by value, the 2-adic evaluation
of the unique holomorphic solution.**

In QM184 coordinates this reads: `|lambda^(-1)|_2 = 2^262`, integrality
bounds `|K|_2` along the ray, and QM184c inflates it; hence `K = 0`
2-adically.  The surviving non-holomorphic section of QM184 cannot carry
integer payloads on any dyadic ray.  Note the exact complementarity: the
Archimedean homogeneous direction is expanding too slowly to force anything
(`|lambda^(-1)|_infinity` acts on values that may grow), but 2-adic
integrality is a bounded condition, and there rigidity is total.

## 4. The former remaining seam, and its numerical floor

By Lemmas U and V the discrete `g -> 2g` return admits an integer payload on
the ray of odd root `g` **iff the explicit 2-adic constant `F_0(2^N g)` is a
positive integer for every `N`**.  There is no remaining functional or
homogeneous freedom; this is now a question about explicitly computable
2-adic numbers, one per opcode.

Exact computation ([experiments/doubling-payload/f0_compute.py]
(../../experiments/doubling-payload/f0_compute.py), integer arithmetic,
valuations (V1) asserted term by term, cross-checked at 2048 vs 4096 bits):

- for `g = 1..6`, the binary digits of `F_0(g)` do not terminate through
  4096 bits (top nonzero computed bit at 4095 in every case);
- rational reconstruction at modulus `2^4096` finds no representation
  `p/q` with odd `q` and `|p|,|q| <= 2^2040` (so in particular `F_0(g)` is
  not an integer below `2^2048`, and not a rational of moderate height, which
  also excludes eventually periodic digits at that scale);
- consequently any integer payload for the `g -> 2g` return at opcode
  `g <= 6` exceeds `2^2048`; doubling the precision doubles this floor at
  linear cost.

## 5. Former sharp open lemma (now unnecessary)

At this stage of the argument, full closure appeared to need:
`F_0(g)` is irrational (as a 2-adic number) for every
`g >= 1`.  The naive route fails by an exact margin worth recording: partial
sums are rational approximants with 3-power denominators `~ 3^(34 g 2^N)`
while the 2-adic gap to the limit is `2^(-46 g 2^N)`; the Liouville balance
compares `46` against `34 log2(3) = 53.89`, ratio `0.8536 < 1`.  So
term-truncation approximants can never prove irrationality, and any proof
must improve the exponent by at least 17%, e.g. by the Mahler
auxiliary-polynomial method run 2-adically on the degree-2 equation (R).
This is a bounded, well-posed target: the equation is inhomogeneous
first-order in Mahler normal form, `Q` is quadratic, and the relevant
p-adic Mahler literature (Nishioka's method; recent p-adic treatments of
Mahler values) should be surveyed before any new machinery is invented.
Per current budget policy this was not dispatched externally.  Section 7
shows why it need not be proved: positivity supplies an Archimedean upper
bound that contradicts the same exact divisibility directly.

## 6. Kill-test discipline

Ways this note could be wrong, and why they are excluded:

- (R) misquoted: it is the kernel-checked HS5/QM183 equation; the constants
  were re-verified here by checking `z_(2g) = kappa z_g^2` and
  `lambda = D/(A kappa^2) = 2^262/3^194` exactly.
- (V1) wrong: asserted for every used term in exact arithmetic.
- reconstruction bug: the routine provably recovers a planted rational of
  comparable height (self-test in the script).
- a payload evading (R): then it is not the `g -> 2g` return; QM184's
  scope, not this note's.

## 7. Complete elementary closure: precision outruns height

Clear denominators in (R), using

```text
P(g)=23g+54, Q(g)=17g+40,
R(g)=194+34g, S(g)=262+46g.
```

The forcing polynomial splits exactly, and the return becomes

```text
3^(2Q(g)) (A F(g)-b0)
 = 2^(77+P(g))
   (3^Q(g)+2^P(g)+2^(77+P(g))F(2g)).               (V2)
```

For a positive natural payload, the bracket is positive.  Since the left
factor `3^(2Q)` is coprime to `2^(77+P)`, (V2) implies

```text
2^(131+23g) < A F(g).                              (V3)
```

Positivity of the original forcing polynomial gives a real upper bound in
the other direction.  The checked inequalities `3^34<2^54` and
`3^194<2^308`, together with `S=262+46g`, yield

```text
F(2g)<2^(46+8g)F(g).                               (V4)
```

For `g_n=g_0 2^n`, (V4) iterates to

```text
F(g_N)<=F(g_0) 2^[46N+8g_0(2^N-1)].               (V5)
```

The terminal lower exponent in (V3) has slope `23g_0 2^N`; the accumulated
upper exponent in (V5) has slope only `8g_0 2^N`.  Using `A<2^181` and
`F(g_0)<2^F(g_0)`, the explicit depth `N=F(g_0)+4` makes the bounds
incompatible.  No limiting argument, numerical search, Mahler theorem, or
irrationality input is used.

The complete statement is kernel-checked as
`DoublingQuineIntegerNoGo.no_positive_integer_doubling_chain` in
[`DoublingQuineIntegerNoGo.lean`](../../KontoroC/KontoroC/DoublingQuineIntegerNoGo.lean).
Consequently the exact four-cell base-squaring return is closed for arbitrary
positive natural payloads.  The broader lesson is a two-place slope test:
forced dyadic approximation precision must not grow faster than the complete
Archimedean height budget of an autonomous return.
