# Yap local-energy preflight for Collatz first passages

Jit Wu Yap's IAS talk on uniform boundedness of torsion points is the most
promising proof-side template in the completed talk audit.  Its transferable
shape is unusually precise: define nonnegative local energies, prove a global
height identity, establish pointwise positivity on every boundary model, and
use compactness/degeneration to upgrade pointwise positivity to a uniform
gap.  This note tests the cheapest possible Collatz candidate for that local
energy before attempting a more elaborate compactification.

## Exact finite test

A shortcut parity word of length `L` with `O` odd steps has homogeneous
multiplier

```text
3^O / 2^L.
```

For every `L`, choose the least `O` for which `3^O>2^L`.  When also
`3^(O-1)<=2^(L-1)`, the explicit word

```text
0^(L-O) 1^O
```

is a literal first-passage word: its multiplier crosses one only at its final
symbol.  Every finite parity word has one canonical residue modulo `2^L`;
the worker constructs its least representative and replays every parity bit
and endpoint exactly.

The exhaustive scan through `L=10000` has seven strict records.  The last is

```text
L=1054, O=665,
(3^O-2^L)/2^L =
8426554879...21859 / 2^1054
                       ~= 4.36550634432e-5.
```

The full integers, canonical seed, endpoint, and hashes are retained in
`ias_yap_local_energy_audit.json`.  This is exact bounded evidence only.  It
shows that raw Archimedean multiplier drift has already become a very weak
candidate uniform energy at modest word length; it does not establish an
asymptotic zero gap.

The literal cylinders also have a closed form:

```text
n_L,O = 2^(L-O)*(2^O-1),     T^L(n_L,O)=3^O-1.
```

Thus the endpoint satisfies `T^L(n)+1=3^O` exactly.  The worker factors both
endpoints and checks this identity.  On every nontrivial multiplier record,
the existing coercive resource

```text
R23(n)=v2(n+1)+v3(n+1)+u,  n+1=2^a*3^b*u
```

decreases, often by essentially its entire primitive-unit term.  At the
length-1054 record the endpoint has factorization `(a,b,u)=(0,665,1)` while
the source has a 317-digit primitive unit.  Therefore neither raw multiplier
gain nor `R23` itself supplies Yap's required pointwise positive local
energy.  This is still an architecture rejection, not evidence against the
Collatz conjecture.

## Analytic continuation to formalize

There is a short standard argument suggesting the bounded observation is an
actual no-go.  Put `alpha=log(2)/log(3)`, which is irrational because
`2^a != 3^b` for positive integers `a,b`.  Infinitely many upper continued-
fraction convergents `O/L` satisfy

```text
0 < O/L-alpha < 1/L^2.
```

Consequently

```text
0 < O log(3)-L log(2) < log(3)/L,
```

so `3^O/2^L -> 1` from above.  For all sufficiently large such convergents,
the right side is below `log(3/2)`, which is exactly
`3^(O-1)<=2^(L-1)`.  The displayed zero-then-one word is therefore a
first-passage realization.  This argument has not yet been kernel-checked and
is not promoted as a repository theorem.

## Consequence for the Yap lane

A viable Yap-style proof cannot use the homogeneous Archimedean multiplier
as its sole positive local energy.  It needs a mixed dyadic/triadic boundary
term that:

1. detects the near-neutral continued-fraction degeneration;
2. participates in an exact global height or product identity;
3. is coercive in the ordinary canonical root rather than only a profinite
   address; and
4. has a uniform positive gap across all boundary models.

The endpoint factorization data `n+1=2^a 3^b u` are now attached.  The next
experiment is to search exact combinations of their valuation and primitive-
unit changes for a boundary correction which does not collapse on these
records, then test it on the full first-passage code rather than this one
explicit family.  A finite fit remains CEGIS evidence; promotion requires a
symbolic identity and a machine-checked uniform bound.
