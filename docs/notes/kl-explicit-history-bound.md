# An explicit depth bound for record-admissible KL histories

**Status (2026-07-21): independently audited proof proposal, not yet
kernel-checked.**  This note gives a finite-fuel alternative to the preferred
well-founded branch-checkpoint constructor.  The bound is deliberately crude
and astronomically large.  It is useful because it turns the qualitative
branch-arrival compactness argument into a structurally recursive specification;
it is not a practical enumeration bound.

## Abstract arrival theorem

Let `Q` be a finite state set of cardinality `N >= 2`, and put

```text
alpha = log_2(3),
M = N(N-1),
Q0 = M 3^M,
B = M Q0 = M^2 3^M.
```

Consider states `r_0,...,r_L`, heights `h_0,...,h_L`, and integer costs
`c_0,...,c_(L-1)` satisfying

```text
h_0 = 0,
h_n >= 0,
c_n >= 1,
h_(n+1) - h_n = alpha - c_n,
i <= j and r_i = r_j  =>  h_j <= h_i.
```

Then the proposed explicit theorem is

```text
L < B = N^2 (N-1)^2 3^(N(N-1)).
```

The existing Lean theorem `no_infinite_KL_branch_arrivals` proves qualitative
finiteness.  The point here is the uniform numerical bound.

## 1. Height and bucket bound

Every increment is at most `alpha-1 < 1`.  Fix a prefix ending at `n` and
chronologically erase every block between two visits to the same state.  Each
erased block has nonpositive net height by the return-antitonicity hypothesis,
so erasing it can only increase the sum of the retained increments.  The
remaining state path is simple and has at most `N-1` edges.  Therefore

```text
0 <= h_n < N-1.
```

There are consequently only

```text
N * (N-1) = M
```

possible buckets `(r_n, floor(h_n))`.

## 2. A quantitative one-sided approximation

The needed arithmetic lemma is

```text
exists q, 1 <= q < M 3^M and 0 < {q alpha} < 1/M.
```

Pigeonholing the `M+1` fractional parts
`{0 alpha},...,{M alpha}` gives `1 <= d <= M` for which the distance from
`d alpha` to an integer is strictly less than `1/M`.  Irrationality makes all
equalities strict.

If `0 < {d alpha} < 1/M`, take `q=d`.  Otherwise write

```text
epsilon = ceil(d alpha) - d alpha,
0 < epsilon < 1/M,
p = ceil(d alpha).
```

Since `2^p` and `3^d` are distinct integers with `2^p > 3^d`,

```text
2^epsilon = 2^p / 3^d >= 1 + 3^(-d).
```

Strict convexity of `2^x` below the chord joining `(0,1)` and `(1,2)` gives
`2^epsilon < 1+epsilon` for `0<epsilon<1`.  Hence

```text
epsilon > 3^(-d).
```

Set `ell=floor(1/epsilon)` and `q=ell*d`.  Irrationality implies
`ell*epsilon<1<(ell+1)*epsilon`, so

```text
{q alpha} = 1 - ell*epsilon,
0 < {q alpha} < epsilon < 1/M,
q < d 3^d <= M 3^M.
```

This is the only materially heavy new formalization obligation.  A
non-quantitative alternative can choose `q` from density of the irrational
rotation and retain a finite but unnamed bound `Mq`.

## 3. The bucket contradiction

Because every cost is integral,

```text
h_n = n alpha - C_n
```

for an integer `C_n`, so `h_n` and `n alpha` have the same fractional part.
Let `delta={q alpha}`.  If `L >= Mq`, inspect the `M+1` times

```text
0, q, 2q, ..., Mq.
```

Since `M delta<1`, their fractional heights are exactly

```text
0, delta, 2 delta, ..., M delta,
```

in strictly increasing order.  Two sampled times share one of the `M`
state/floor-height buckets.  The later height is then strictly larger, contrary
to statewise antitonicity.  Thus `L<Mq<B`.

## 4. Raw KL occurrence-word depth

For the KL history forest at precision `k`, take

```text
N = 3^(k-1),
R = ceil((N-1)/2) = floor(N/2),
D = B R.
```

Between surviving branch arrivals a selected raw path has the form `T^t;B`.
The starting height is below `N-1`, and the branch source remains nonnegative,
so `t+1 <= R`.  A final block ending at a negative transport leaf or a
negative/marked branch leaf also has at most `R` edges.  If `L` is the number
of surviving arrivals, the strict estimates above give

```text
word depth <= (L+1)R <= MqR < BR = D.
```

This is a bound on occurrence-word or semantic-edge depth.  It is **not** the
literal constructor depth of the compiled `OccurrenceTree`, whose
principal/add/binary-min encoding adds a constant-factor overhead.

For `k=19`, `N=3^18=387420489`, so even much sharper bespoke rational
approximants produce bounds far beyond enumeration.  The value of the theorem
is proof-theoretic: fuel `D` cannot be exhausted by an expandable occurrence.

## Audit notes

Two independent audits checked the height bound, one-sided approximation,
bucket count, terminal block, and off-by-one inequalities.  They also rejected
an earlier tempting shortcut: loop-erasing a walk into simple cycles and
assigning every simple cycle a uniform negative loss is invalid, because
removing a strongly negative nested cycle can leave a positive synthetic outer
cycle.  The fractional-part proof above does not use that shortcut.

Until the quantitative approximation and bucket theorem are formalized, the
well-founded checkpoint route in `docs/FOR_CLEAN_LEAN.md` reply 16 remains the
preferred Lean implementation.
