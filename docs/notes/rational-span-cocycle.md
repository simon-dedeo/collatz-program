# The critical base-3/2 span as a Collatz cocycle

Status: **research-side exact derivation plus exact bounded diagnostics; not a
Collatz result**.  The identities in Sections 2--6 are elementary consequences
of the published rational-base definitions, but the all-level derivation has
not been kernel-checked and is not a certified repo result.  The finite claims
in Section 7 are checked by exact rational intervals in
`experiments/full/diagnose_rational_span_cocycle.py`.  No statement below
excludes a divergent orbit or a nontrivial cycle.

## 1. Why this object was worth isolating

Akiyama--Marsault--Sakarovitch associate to every node `n` of the rational
base-`p/q` representation tree a bottom word, a top word, and a normalized
span `sigma(n)`: the length of the interval represented by the infinite
branches below that node.  Their construction was developed from rational
numeration, automata, Mahler's problem, and the Josephus problem, not selected
for a Collatz application [AMS18].  A local full-text audit of the AMS and AFS
PDFs found no case-insensitive occurrence of `Collatz`, `3x+1`, or `Syracuse`.
This documents search separation, not historical priority.  At the critical base

```text
p=3, q=2, p=2q-1,
```

the span-set is especially non-rigid: its closure is an interval rather than
a null Cantor set [AMS18, Theorem II].  The same base is where an odd Syracuse
step appends the digit `1` to the integer representation [EVG25].  This makes
the span a plausible capacity or Lyapunov coordinate for the *full* problem,
not only for predecessor counts.

The useful outcome is an exact geometric model:

> `sigma(n)` is the discrete derivative of an increasing coordinate which
> conjugates the least-child map `n -> ceil(3n/2)` to multiplication by
> `3/2`.

The bad outcome is equally exact.  The even Syracuse branch is not coercive in
this coordinate, spans have explicit exponentially small subsequences, and
the resulting cycle cocycle is a coboundary.  Thus the scalar span alone is
not a Lyapunov proof of Collatz.  A possible use remains as a
bounded-discrepancy capacity on predecessor sets, but that requires a new
arithmetic anti-correlation theorem.

## 2. Bottom-word evaluation and the span identity

Write the bottom word from node `n` as

```text
w^-(n)=b_0(n)b_1(n)b_2(n)...,       b_j(n) in {0,1}.
```

For base `3/2`, the after-radix evaluation of a digit word is

```text
rho(a_0 a_1 ...) = sum_(j>=0) (a_j/2)(2/3)^(j+1).
```

Define

```text
F(n) = rho(w^-(n)).                                      (2.1)
```

The tree transition is

```text
2m = 3n+a,       a in {0,1,2}.
```

The least admissible digit is `a=0` for even `n` and `a=1` for odd `n`.
Consequently, with

```text
b(n)=n mod 2,
U(n)=(3n+b(n))/2=ceil(3n/2),
```

peeling the first bottom digit gives the exact recurrence

```text
F(n) = b(n)/3 + (2/3)F(U(n)).                            (2.2)
```

The published bottom/top successor lemma says, at `p-q=1`, that the top word
at `n` is obtained by adding `1` digitwise to the bottom word at `n+1`.
Since

```text
rho(111...) = sum_(j>=0) (1/2)(2/3)^(j+1) = 1,
```

the normalized span is

```text
sigma(n) = 1 + F(n+1)-F(n).                              (2.3)
```

This is the requested formula.  It is not numerical: it follows from
[AMS18, Lemma 25 and Definition 55].

Bottom digits lie in `{0,1}`, so

```text
0 <= F(n) <= 1.                                         (2.4)
```

The AMS interval theorem and the Akiyama--Frougny--Sakarovitch identification
of the endpoint give more context:

```text
closure {sigma(n): n>=0} = [0,K(3)],
K(3)=1.6222705028847673159... .                          (2.5)
```

Here `K(3)` is the ceiling-iteration/Josephus constant of
Odlyzko--Wilf [OW91, AFS08].  In particular, the critical case itself warns
against expecting a positive lower span.

## 3. The exact odd, even, and inverse recurrences

Let `T` be the normalized Syracuse map

```text
T(n)=n/2                 if n is even,
T(n)=(3n+1)/2            if n is odd.                    (3.1)
```

If `n` is odd, then `U(n)=T(n)`, while `U(n+1)=T(n)+1`.
Substitution of (2.2) into (2.3) gives

```text
sigma(n) = (2/3)sigma(T(n))              (n odd),        (3.2)
sigma(T(n)) = (3/2)sigma(n).                              (3.3)
```

For `n=2r`, the two adjacent least-child states are `3r` and `3r+2`.
The middle difference telescopes, giving

```text
sigma(2r) = (2/3)(sigma(3r)+sigma(3r+1)).                (3.4)
```

Thus the convenient inverse/refinement form is

```text
sigma(3r+2) = (3/2)sigma(2r+1),                          (3.5)
sigma(3r)+sigma(3r+1) = (3/2)sigma(2r).                  (3.6)
```

Equation (3.5) is deterministic because a state `3r+2` has the odd
predecessor `2r+1`.  Equation (3.6) is irreducibly a *pair* relation: the
even node branches into two adjacent rational-base cells.  Any argument which
silently replaces (3.6) by a pointwise recurrence has discarded the exact
geometry.

## 4. The linearizing coordinate and a genuine capacity

Define

```text
H(n)=n+F(n).                                             (4.1)
```

Combining (2.2) with `U(n)=(3n+b(n))/2` cancels the parity digit:

```text
H(U(n)) = (3/2)H(n).                                    (4.2)
```

Equivalently,

```text
H(n)=lim_(k->infinity) (2/3)^k U^k(n).                  (4.3)
```

Indeed, unrolling `U(n)=(3n+b(n))/2` makes the error series exactly
`F(n)`.  This is the nodewise version of the ceiling-iteration constant
studied by Odlyzko--Wilf.  Equation (2.3) becomes

```text
sigma(n)=H(n+1)-H(n).                                   (4.4)
```

The span is positive, so `H` is increasing.  The cells

```text
I_n=[H(n),H(n+1)]
```

tile the positive real line with lengths `|I_n|=sigma(n)`.  Dilation by
`3/2` acts exactly as the rational representation tree:

```text
(3/2)I_n = I_(T(n))                         if n is odd,
(3/2)I_(2r) = I_(3r) union I_(3r+1)         if n=2r.     (4.5)
```

The union in the second line is an interval union with a common endpoint.
This is an actual finite-additive capacity model, not a generic cellular-
automaton analogy.

There is also an unusually strong discrepancy identity.  For all integers
`0<=a<b`,

```text
sum_(a<=n<b) sigma(n)
  = H(b)-H(a)
  = (b-a)+F(b)-F(a),                                    (4.6)
```

and hence

```text
|sum_(a<=n<b) sigma(n) - (b-a)| <= 1.                   (4.7)
```

Thus span-capacity agrees with counting measure to bounded discrepancy on
every interval, despite having arbitrarily small individual atoms.

There is a second exact capacity bound hidden by the pointwise small spans.
Put

```text
delta_k(a,b)=U^k(b)-U^k(a).
```

The elementary ceiling inequality gives

```text
floor((3/2)delta_k) <= delta_(k+1)
                            <= ceil((3/2)delta_k).       (4.8)
```

After multiplication by `(2/3)^k` and passage to (4.3), this compares every
block length `H(b)-H(a)` with stable floor and ceiling iterations started at
`b-a`.  Two cases are particularly sharp.  The upper ceiling iteration
started at `1` has normalized limit `K(3)`, while the lower floor iteration
started at `2` has the same limit: if

```text
g_0=1,  g_(k+1)=ceil(3g_k/2),
f_0=2,  f_(k+1)=floor(3f_k/2),
```

then `f_k=g_k+1`.  Therefore

```text
sigma(n) <= K(3),
sigma(n)+sigma(n+1) >= K(3)                 for all n.  (4.9)
```

This is a **research-side all-level lemma**, not a machine-checked theorem in
the repository.  The bounded checker independently confirms its strict
finite instances over the scan stated in Section 7.

Combining the second inequality with (3.4) yields the parity gap

```text
sigma(2m) >= (2/3)K(3),
sigma(m)/sigma(2m) <= 3/2.                             (4.10)
```

So individual cells can be arbitrarily small only on the odd side; every
even cell carries a fixed amount of span-capacity.  This is a genuine
all-level invariant, although by itself it does not control which even cells
a forward lineage visits.

## 5. What happens on the full Syracuse map

For odd `n`, equation (4.2) is already a Syracuse identity:

```text
H(T(n))/H(n)=3/2.                                       (5.1)
```

For an even state `n=2m`, introduce the doubling defect

```text
d(m)=2H(m)-H(2m)=2F(m)-F(2m).                           (5.2)
```

The ceiling map is subadditive:

```text
U(x+y) <= U(x)+U(y).
```

Iteration followed by (4.3) proves

```text
H(x+y) <= H(x)+H(y),       d(m)>=0.                     (5.3)
```

Therefore the exact even multiplier is

```text
H(T(2m))/H(2m)
  = H(m)/H(2m)
  = (1/2)(1+d(m)/H(2m)) >= 1/2.                        (5.4)
```

This looks like a corrected multiplicative Collatz cocycle, but the
correction is not uniformly positive.  Peeling one even bottom digit gives

```text
d(2r)=(2/3)d(3r),                                      (5.5)
d(2^k r)=(2/3)^k d(3^k r).                             (5.6)
```

Since `0<=F<=1`, one has `0<=d<=2`, and hence

```text
d(2^k r) <= 2(2/3)^k,
d(2^k r)/H(2^(k+1)r) <= 1/(3^k r).                     (5.7)
```

The even correction can therefore be arbitrarily close to zero along an
explicit family.  No uniform drift improvement over the classical factors
`3/2` and `1/2` is available from this scalar cocycle.

The normalized coordinate `h(n)=H(n)/n` makes the obstruction still clearer:

```text
1 <= h(n) <= 1+1/n,
h(T(n))/h(n)=3n/(3n+1)<1                if n is odd,
h(T(2m))/h(2m)=1+d(m)/H(2m)>=1          if n=2m.        (5.8)
```

It moves in opposite directions according to parity and tends uniformly to
`1` at large states.  It is a bounded coordinate change, not a proper
Lyapunov function.

The inverse-tree form of (3.2) and (4.10) is potentially more useful.  Every
target `m` has the even predecessor `2m`; when `m=2 mod 3` it also has the odd
predecessor `(2m-1)/3`.  Hence

```text
Cap_sigma(T^-1{m})
 = sigma(2m)
   + 1_{m=2 mod 3}(2/3)sigma(m),                       (5.9)
```

and (4.10) gives

```text
Cap_sigma(T^-1{m})/sigma(m) >= 2/3             always,
Cap_sigma(T^-1{m})/sigma(m) >= 4/3     if m=2 mod 3.   (5.10)
```

This is an exact capacity analogue of the local predecessor inequalities.
It is not uniformly expanding because the first lower bound is sharp in the
limit, and odd side branches can enter the residue-`0` doubling ray.  Any
iteration theorem must retain those residue/capacity correlations rather
than multiply favorable `4/3` rows independently.

Iterating only the universal part gives the exact but usually weak bridge

```text
Cap_sigma(T^-k{m})
 >= (2/3)^k sigma(m) #T^-k{m}.                          (5.11)
```

Each inverse branch contributes at least `2/3` of its parent's capacity.
Equation (5.11) explains why a weighted predecessor theorem is compatible
with the existing counting program, but it also exposes the loss: one needs
enough branching to defeat `(2/3)^k`, and even then backward abundance does
not by itself force forward termination.

## 6. Cycle and divergent-orbit identities: exact but tautological

Suppose a Syracuse cycle has length `L`, with `O` odd states and `E=L-O`
even states.  Multiplying (5.1) and (5.4) around the cycle gives

```text
2^L/3^O = product_(even states 2m)
                    (1+d(m)/H(2m)).                    (6.1)
```

But multiplication of the ordinary integer ratios gives the classical
identity

```text
2^L/3^O = product_(odd states n) (1+1/(3n)).            (6.2)
```

So the span formulation yields the exact dual equality

```text
product_even (1+d/H) = product_odd (1+1/(3n)),          (6.3)
```

but no new inequality.  It is just the telescoping of `h=H/n`.

Likewise, extend the endpoint map piecewise affinely from each half-open cell
`I_n` onto `I_(T(n))`.  Its cell slope is

```text
J(n)=sigma(T(n))/sigma(n).                              (6.4)
```

Odd cells have `J=3/2`; even cells have no fixed sign relative to `1`.
On every hypothetical cycle,

```text
product_cycle J(n)=1                                   (6.5)
```

by telescoping.  Hence every cycle is neutral in this coordinate.  A
hyperbolicity or negative-log-Jacobian argument based only on `sigma` cannot
exclude nontrivial cycles.

For a noncyclic nonterminating integer orbit, absence of a bounded recurrent
subsequence would imply `n_j -> infinity`, and hence `h(n_j)->1`.  The exact
finite-time identity is

```text
h(n_N)/h(n_0)
 = product_even(1+d/H) / product_odd(1+1/(3n)).         (6.6)
```

Thus a divergent orbit would merely force a balance between two vanishing
correction series.  It does not contradict either one.

## 7. Exact truncation experiment and kill tests

For a depth `L` bottom-word prefix, let

```text
F_L(n)=sum_(1<=i<=L) b_(i-1) 2^(i-1)/3^i.
```

This is an exact rational with denominator `3^L`, and the omitted tail obeys

```text
0 <= F(n)-F_L(n) <= (2/3)^L.                            (7.1)
```

The checker uses (7.1), never floating point, to enclose `F`, `sigma`, all
ratios reported below, and `d`.  It also verifies the exact depth-`L` versus
depth-`L-1` versions of (2.2), (3.2), (3.4), and (5.5).

Run:

```bash
python3 experiments/full/diagnose_rational_span_cocycle.py
```

Audited scope and output:

- all four prefix recurrences pass for `0<=n<=20,000` at depth `96`;
- `sigma` is not monotone even on even Syracuse steps: `2->1` decreases it,
  while `12->6` increases it;
- `sigma(n)/n` is also not monotone on even steps;
- among `1<=m<=20,000`, all even cell slopes
  `sigma(m)/sigma(2m)` are interval-separated from `1`: `15,627` contract and
  `4,373` expand; the finite-scan range is enclosed near
  `[0.0031765661,1.4969101053]`;
- the two directions already have small certified witnesses:
  `sigma(14)/sigma(28)>1` and `sigma(63)/sigma(126)<1`.
- the stable-gap consequences `sigma(m)<K(3)`,
  `sigma(2m)>(2/3)K(3)`, and `sigma(2m)/sigma(m)>2/3` are independently
  interval-certified throughout that finite scan;
- for every root `1<=m<=1,000` not divisible by `3`, the exact-depth
  predecessor capacity was computed through depth `12`.  The smallest
  enclosed ratios `Cap_sigma(T^-j{m})/sigma(m)` at depths `1,2,3,4,8,12`
  were respectively
  `0.669729..., 1.337105..., 1.645273..., 2.301779..., 6.507290...,
  19.840057...`.

These are exhaustive finite diagnostics at the stated bounds, not asymptotic
theorems.

There are, however, two exact all-level noncoercivity families.  Starting at
`n_k=2^k-1`, the first `k` Syracuse steps are odd and

```text
T^j(n_k)=3^j 2^(k-j)-1       (0<=j<=k).
```

Using (3.2) and the stable-gap bound `sigma<=K(3)` gives

```text
sigma(2^k-1)
  =(2/3)^k sigma(3^k-1)
  <=K(3)(2/3)^k -> 0.                                  (7.2)
```

Equation (5.7) gives the independent small-defect family

```text
d(7*2^k)<=2(2/3)^k -> 0.                               (7.3)
```

The exact rational intervals printed by the checker lie below these theorem
bounds for `k=4,8,12,16`.

## 8. Verdict and the one formulation still worth testing

### What is genuinely new/useful for this program

1. The scalar span has an exact full-orbit interpretation: it is the cell
   length of a bounded-displacement linearizing coordinate `H`.
2. Span-capacity has discrepancy at most one on every integer interval.
3. Every even cell has capacity at least `(2/3)K(3)`, and the one-step inverse
   capacity inequalities (5.10) are exact.
4. Odd Syracuse transport is exact dilation, while the even branch exposes a
   named nonnegative defect `d(m)`.
5. The formulas give cheap exact diagnostics for whether a proposed orbit or
   predecessor estimate is using real arithmetic structure or just changing
   coordinates.

### What is killed

- a positive lower bound for `sigma`;
- monotonicity of `sigma`, `sigma/n`, or the even cell Jacobian;
- a uniform positive even correction in the `H` cocycle;
- cycle exclusion by span hyperbolicity;
- any argument which uses only that `H(n)=n+O(1)`: this is a bounded
  coordinate change and cannot create termination.

### Remaining hinge

For a set `A` of integers define its geometric span-capacity

```text
Cap_sigma(A)=sum_(n in A) sigma(n).                     (8.1)
```

On intervals this is counting measure up to error one, but on sparse
arithmetic sets the individual weights can be arbitrarily small.  The only
credible bridge to the predecessor/KL program is therefore a *selection
anti-correlation theorem*, for example:

```text
predecessor bushes or a hypothetical divergent lineage cannot concentrate
on the tiny-span cells and tiny-d(m) even states at every scale.           (8.2)
```

Such a theorem would let predecessor abundance become geometric capacity and
might interact with disjoint side-bush arguments.  Nothing here proves (8.2),
and the explicit families (7.2)--(7.3) show that it cannot be pointwise or
finite-window.  It must retain long-range arithmetic correlations between
the minimizing/predecessor policy, future parity, and the rational-base
cells.  This is close in shape to the program's existing localization gap,
so the span does not presently open an independent full-Collatz route.

The rising exact-depth capacity ratios in Section 7 are the concrete reason
not to discard this formulation outright.  A uniform theorem of that shape
would be a new weighted predecessor estimate, but it would still not by
itself prove forward termination: it needs the separate side-bush packing or
lineage anti-correlation bridge.  Treat the finite scan as a theorem-discovery
target, not evidence that such a uniform rate holds.

**Candid classification:** a clean new measurable coordinate and a useful
no-go theorem for scalar span Lyapunov arguments; not yet a proof route.  The
capacity anti-correlation hinge is precise enough to test, but should remain
lower priority than a lane which supplies an independent arithmetic source of
that correlation.

## References

- **[AMS18]** Shigeki Akiyama, Victor Marsault, and Jacques Sakarovitch,
  "On subtrees of the representation tree in rational base numeration
  systems," *Discrete Mathematics & Theoretical Computer Science* 20:1
  (2018), [arXiv:1706.08266](https://arxiv.org/abs/1706.08266),
  [journal DOI](https://doi.org/10.23638/DMTCS-20-1-10).
- **[AFS08]** Shigeki Akiyama, Christiane Frougny, and Jacques Sakarovitch,
  "Powers of rationals modulo 1 and rational base number systems," *Israel
  Journal of Mathematics* 168 (2008), 53--91,
  [author PDF](https://www.irif.fr/~cf/publications/AFSwords05.pdf).
- **[OW91]** Andrew M. Odlyzko and Herbert S. Wilf, "Functional iteration and
  the Josephus problem," *Glasgow Mathematical Journal* 33 (1991), 235--240,
  [DOI](https://doi.org/10.1017/S0017089500008272).
- **[EVG25]** Shalom Eliahou and Jean-Louis Verger-Gaugry, "The number system
  in rational base 3/2 and the 3x+1 problem," *Comptes Rendus. Mathématique*
  363 (2025), [arXiv:2504.13716](https://arxiv.org/abs/2504.13716).  This is
  used only for the already-published Collatz-to-rational-base bridge; the
  span/Josephus sources above were selected independently of Collatz.
