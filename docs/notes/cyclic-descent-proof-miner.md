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

## Busy-Beaver power-word extension

The next front end is now implemented in
`experiments/cyclic_descent/bb_power_rules.py`. It copies the useful proof
architecture of the bbchallenge rule validator rather than its Turing-machine
syntax:

```text
configuration       A(r)+B(r)*k
exact simulation    E, O, I0, I1
chain rules          2^r X -> X
                     2^r X-1 -> 3^r X-1
rule application     target(r+delta,u*t+v)
induction check      one global size-change rank in (r,k)
```

Here `A` and `B` are finite rational linear combinations of `base^r`. This
class is closed under primitive component operations, counter shifts, and both
chain rules; second-level rules may therefore contain `6^r`, `9^r`, and other
product bases without changing the validator.

Operation guards are not checked on a finite sample. If `D` clears the
coefficients' denominators, the checker follows the finite deterministic state

```text
(base_1^r,...,base_s^r) mod mD
```

through its complete preperiod and period. This decides parity, divisibility
by three, and integrality exactly even for non-coprime bases. Candidate rules
are then replayed from JSON by a separate verification command.

The template learner used the final two pruning layers of the `96 x 96`
concrete audit. Of the 366 frontier states, 224 have a nontrivial common
dyadic scale, 43 have a nontrivial uniform odd-run factor in `gcd(a+1,b)`, and
only 22 have a common ternary scale. This validates the BB diagnosis: dyadic
run length is the dominant compressed coordinate, while the odd chain is the
essential conversion from dyadic to ternary scale.

The calibrated symbolic audit contains:

```text
48 learned/derived chart templates
2,110 exact symbolic states explored
947 retained universal macro-rules
243 rules using an unbounded chain
302 residue-automaton states in the independent replay
```

Every rule is valid for all exponents and tails in its displayed guard. This
is substantially more information than another larger concrete box, but it is
not a termination certificate. Restricting to the 24 chart types whose
zero-tail family is already certified leaves 576 candidate rules. The Boolean
closure prepass retains all 24, including the root, but Z3 returns `unsat` for
both a global rank

```text
R_i(r,k)=e_i*r+w_i*k+c_i,
0 <= e_i,w_i <= 64,  0 <= c_i <= 128.
```

and a lexicographic pair of ranks of the same bounded form. The second query
is the first BB-style nested-induction test; it rules out neither larger
coefficients nor deeper/multiset orders.

Thus the new atlas separates two obstructions which the concrete miner mixed
together:

1. exact symbolic transport is abundant and finite;
2. the transport that uses the crucial odd-chain conversion naturally enters
   charts `a*3^r-1+b*3^r*k` whose zero-tail arithmetic is not yet uniformly
   discharged, while the presently certified charts admit neither a bounded
   affine two-counter rank nor a bounded two-phase lexicographic rank in this
   grammar.

The second point is the new high-leverage target. It is not “search a larger
box”; it is first to find reusable base rules for the dyadic-minus/ternary-
minus charts. If that fails, the next order class is a genuine recursive or
multiset BB rule level, not merely a second affine lexicographic phase. Those
experiments directly test whether the power-word lane is a construction site
or a termination-order wall.

## Lean soundness extension

`CounterRuleSystem` now makes `(chart, exponent, tail)` a first-class
configuration. A terminal rule may discharge any configuration; a recursive
rule may change both counters arbitrarily; the only trusted global premise is
strict decrease of a natural rank. Lean proves that a root chart equal to
`1+k` at exponent zero implies Syracuse termination. Lean also checks the
all-odd stride identity

```text
T^[r](2^r*x-1)=3^r*x-1  (x>0),
```

and its component-merge form. No Collatz proof is claimed.

## Artifacts

```text
KontoroC/KontoroC/ComponentCyclicTail.lean
experiments/cyclic_descent/cyclic_descent.py
experiments/cyclic_descent/search_audit.json
experiments/cyclic_descent/z3_search_audit.json
experiments/cyclic_descent/ranked_search_audit.json
experiments/cyclic_descent/bb_power_rules.py
experiments/cyclic_descent/bb_power_rule_audit.json
```

No Syracuse certificate or proof of Collatz is claimed.
