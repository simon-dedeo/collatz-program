# Cyclic descent proof mining

## Outcome

The Busy-Beaver-style idea can be made exact for Collatz. We now have:

1. a finite cyclic certificate language for infinite affine families;
2. a kernel-checked Lean theorem that any valid root certificate proves the
   Syracuse conjecture;
3. an exact component-path miner;
4. an independent Python certificate checker;
5. a Z3 synthesis layer for state-dependent affine size-change ranks.

No root certificate was found in the first bounded grammars. This is a new
proof-search instrument and a scoped negative diagnostic, not a proof of
Collatz.

## The central trick

A proof state `(a,b)` denotes every integer

```text
source(k) = a + b*k.
```

Checking finitely many values of `k` would be irrelevant. Instead a rule
chooses `q=2^p` and writes

```text
k = q*t+d,      0 <= d < q.
```

It then supplies an exact Syracuse-component path from

```text
a+b*(q*t+d)
```

to another state's family at a transformed tail parameter. There are two
certificate systems.

### Tail-deletion system

The target parameter is literally `t`. Since `t<k` for `k>0`, ordinary strong
induction makes the graph sound even when its state graph has cycles. Every
state separately supplies a checked orbit from its base point `a` to `1`.

### Ranked size-change system

The target parameter may be

```text
t' = u*t+v.
```

Each state carries a natural affine rank

```text
R_i(k) = w_i*k+c_i.
```

For an edge from state `i` to state `j`, Z3 checks the universal inequality

```text
R_j(u*t+v) < R_i(q*t+d)
```

on every legal tail. Because both sides are affine, this reduces exactly to
one slope inequality and one endpoint inequality. Lean's general
`RankedTailSystem.merge_one` theorem only assumes the resulting pointwise
rank decrease; it does not trust Z3.

## Exact component paths

The miner walks between affine families using four proof-carrying operations:

```text
E   (a,b) -> (a/2,b/2)                 a,b even
O   (a,b) -> ((3a+1)/2,3b/2)          a odd, b even
I0  (a,b) -> (2a,2b)
I1  (a,b) -> ((2a-1)/3,2b/3)          a=2 mod 3, 3|b
```

They are respectively the uniform even and odd Syracuse steps and their two
legal inverse branches. Every path is an identity for all `t>=0`, not a
sample. The independent checker replays the coefficient identity, operation
preconditions, base orbit, residue partition and rank inequalities with
unbounded integers.

This grammar automatically contains the mixed chart

```text
5+6t  --I1--> 3+4t,
```

so the earlier `6k+5` holonomy descent is not inserted as a special case.

## First calibrated audits

### Literal tail deletion

Default exact bounds:

```text
1 <= base,step <= 96
split powers p <= 4
component-path length <= 14
walk box base <= 768, step <= 1536
```

The candidate universe has `9,216` affine states and `28,487` distinct
component-walk queries. Its greatest recursively closed subset disappears in
seven pruning rounds. The root `(1,1)`, representing every `1+k`, survives
until the final round. An independent Z3 encoding on the `48 x 48` state
universe returns `unsat`.

Scaling square universes gives:

```text
bound       32   64   96   128   192   384
states    1024 4096 9216 16384 36864 147456
rounds       6    7    7     8     8      9
```

This is bounded diagnostic data. Its shape is informative: the deepest
states run into growing affine coefficients rather than closing a finite
cycle. Merely enlarging the concrete `(a,b)` box buys roughly logarithmic
proof depth.

### Affine size-change rank

The richer audited grammar uses:

```text
1 <= base,step <= 12               144 states
one-bit splits
component paths of length <= 6
1 <= rank weight <= 48
0 <= rank constant <= 96
u,v <= 12
five best reparameterized edges per branch
```

Z3 checks `1,440` candidate edges and returns `unsat`. With eight candidates
per branch, the monolithic encoding becomes resource-heavy; the next
implementation should generate edges lazily by counterexample-guided
refinement rather than materializing the full disjunction.

These UNSAT statements exclude only the displayed bounded grammars. They do
not exclude cyclic proofs in general and say nothing negative about Collatz.

## Mathematical interpretation

The experiment separates three levels that were previously conflated:

1. **finite charts** are impossible by the unbounded-width theorem;
2. **finite recursive chart types with concrete coefficients** are sound and
   highly expressive, but the audited universes chase increasing scale;
3. **finite types with unbounded arithmetic counters** are the live target.

The third level is exactly where Busy Beaver rule mining succeeds: a small
set of rule schemas transports symbolic exponents or counters, and a
size-change argument certifies induction. For Collatz, the next state should
therefore not be another concrete `(a,b)`. It should be a template such as

```text
(a(r), b(r))
```

with powers of `2` and `3`, valuations, or a normalized holonomy gap carried
as a symbolic counter. The current ranked theorem already accepts an
arbitrary target-parameter map and arbitrary natural rank, so this extension
requires a new miner front end rather than a new soundness argument.

## Next high-leverage move

Replace concrete coefficient enumeration by CEGIS over a small grammar of
parametric chart templates:

```text
a(r)=alpha*2^r+beta,
b(r)=gamma*2^r,
```

and the analogous `3^r`/mixed forms suggested by odd pullback. Candidate
templates should be learned from the deepest eliminated obligations. Each
proposed symbolic edge is then proved coefficientwise, and Z3 handles only
the linear size-change constraints. A successful certificate can be
translated directly into a `RankedTailSystem` instance in Lean.

## Artifacts

```text
KontoroC/KontoroC/ComponentCyclicTail.lean
experiments/cyclic_descent/cyclic_descent.py
experiments/cyclic_descent/search_audit.json
experiments/cyclic_descent/z3_search_audit.json
experiments/cyclic_descent/ranked_search_audit.json
```

No Syracuse certificate or proof of Collatz is claimed.
