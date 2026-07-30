# Difference maps for self-reproducing Collatz languages

## Verdict

The difference-map method is a genuinely good fit for the next search, but
only after separating four constraints that our previous searches mixed
together. The right use is not to iterate the Collatz map on floating-point
integers. It is to search a continuous embedding of **finite counter
programs**, then validate any recovered program exactly.

The target is a finite language whose productions are:

1. positive-time forward Syracuse executions;
2. total on every reachable residue branch;
3. anchored at one ordinary positive integer; and
4. equipped with an unbounded reproductive resource.

Such a program would encode one ordinary divergent orbit, rather than a
compatible `2`-adic address or a component relation assembled with backward
moves. No such program has been found.

## What the difference map contributes

Elser--Rankenburg--Thibault consider two constraint sets `A,B` with tractable
nearest-point projections `P_A,P_B`. Their map is

```text
D_beta(x) = x + beta * (P_A(f_B(x)) - P_B(f_A(x))),

f_A(x) = P_A(x) - (P_A(x)-x)/beta,
f_B(x) = P_B(x) + (P_B(x)-x)/beta.
```

At a fixed point the two displayed projections agree, producing a point of
`A intersect B`. Unlike alternating projection, the map is designed not to
stagnate at a local nonzero minimum of the distance between nonconvex sets.
For more than two constraints the paper points to the standard product-space
construction: project componentwise onto the Cartesian product and project
onto the diagonal by consensus.

That product-space construction is exactly what is needed here.

## The four copies of a candidate program

Let `p` describe a finite chart grammar: chart coefficients, residue guards,
one selected production per branch, target charts, counter maps, and a root.
Make four independent copies and define

```text
S = exact positive-time Syracuse semantics,
C = total reachable language closure,
R = unbounded reproduction,
O = ordinary-root / no-completion condition.

A = S x C x R x O,
B = {(p,p,p,p) : p is a candidate program}.
```

Projection to `A` applies four easy or at least sharply isolated repairs;
projection to `B` averages the four copies in the continuous coordinates and
reconciles their discrete rule logits. The difference map searches for a
consensus program on which all four repairs agree.

### Semantic projection `P_S`

Each rule slot is independently replaced by the nearest exact symbolic
execution. The existing power-chart validator already supplies the required
primitive:

```text
A(r)+B(r)k --split k=2t+d--> exact E/O/chain path
           --> A'(r+delta)+B'(r+delta)(u*t+v).
```

Coefficient identities are rational and exact. Parity, divisibility, and
integrality guards are decided by complete preperiod/period automata for
`base^r mod mD`. For a counterexample program this projection must forbid
`I0`, `I1`, empty paths, and any rule whose claimed macro-time can vanish on
its guard.

The first implementation can project to the nearest member of a dynamically
grown exact-rule library. A stronger implementation lets symbolic BFS/SMT
alter the endpoint coefficients and path while minimizing distance to the
requested rule feature vector.

### Closure projection `P_C`

Given soft costs on rules, select a minimum-cost rooted subgraph with exactly
one production for every reachable `(chart,residue)` slot and with every
target retained. This is a finite graph/assignment problem. Greatest-fixed-
point pruning is the feasibility oracle; a MILP or min-cost closure routine
provides a nearest repair when the current choices are inconsistent.

This projection asks for **forward-language closure**, not component closure.
The distinction is load-bearing.

### Reproduction projection `P_R`

Select a reachable recurrent kernel and a resource that grows without bound.
A certificate-friendly version assigns every chart an affine resource on its
counters and requires positive gain around every directed cycle. For a fixed
graph, positivity of every cycle can be checked by minimum-cycle-mean
algorithms. Its dual form introduces chart potentials `h_i` and a margin
`epsilon>0` such that every selected edge has adjusted gain

```text
gain(edge) + h_source - h_target >= epsilon.
```

This is a linear projection once the discrete graph is fixed. More expressive
versions use lexicographic or matrix counter resources. The resource must be
bounded above by the decoded integer's bit length (or another proper height),
so unbounded resource proves unbounded ordinary values rather than growth of a
dummy register.

The productive kernel need not make every primitive Collatz step increase.
It makes a checked macro-resource increase after a positive number of forward
steps.

### Ordinary-root projection `P_O`

This projection forces a literal finite starting configuration and forbids an
infinite preloaded tail. Every production is evaluated forward from the
current natural counters. Counter initialization at the root is explicit;
later counter updates are functions of the current configuration, not fresh
CRT choices.

This constraint is what prevents the difference map from rediscovering the
already-closed failure: an infinite compatible `2`-adic address whose finite
prefixes never stabilize to one natural number. If a proposed language is
instead defined by backward cylinders, `P_O` must enforce the existing
eventual-zero-lift criterion.

## Exact certificate target

A successful finite program should compile to the following mathematical
object. For configurations `c` it provides

```text
value(c) : positive natural,
next(c) : configuration,
duration(c) : positive natural,
resource(c) : natural,

T^[duration(c)](value(c)) = value(next(c)),
the intermediate segment avoids 1,
resource(next(c)) > resource(c),
resource(c) <= bitLength(value(c)).
```

Starting from one explicit ordinary configuration, these clauses give a
forward orbit that never reaches `1` and has unbounded macro-endpoints. The
search remains untrusted; this small semantic theorem and each emitted rule
are suitable for Lean.

There is a useful weaker target too: omit resource growth and require the
forward language to exclude both `1` and `2`. A nonempty ordinary-rooted,
forward-invariant language already gives a counterexample, possibly a cycle.
The reproductive condition specifically targets escape to infinity.

## What the current atlas says

The new command

```text
python3 experiments/cyclic_descent/bb_power_rules.py forward-audit \
  experiments/cyclic_descent/bb_power_rule_audit.json
```

independently replays the source atlas and then removes inverse and zero-time
rules. In the displayed 48-template, 947-rule grammar it finds:

```text
357 positive-time forward rules,
243 of them using an unbounded chain,
26 templates initially having both binary branches,
greatest closed subset: 48 -> 26 -> 2 -> 0.
```

The root disappears in the second pruning round. This remains a scoped exact
statement about the *cap-12 retained atlas*, not a no-go theorem. In
particular, it is not stable under increasing the rule cap. Re-mining the same
48 templates at symbolic depth 6 and cap 64 gives 3,389 retained rules. After
the positive-time and semantically-vacuous-counter filters used by the new
engine, 621 canonical edges remain, and greatest-fixed-point pruning is

```text
48 -> 36 -> 24,
```

with the root still present. Thus the earlier empty closure was substantially
a truncation artifact. The expanded closure is still not a counterexample:
it includes terminating configurations (notably the ordinary root `k=0`) and
its apparent reproductive counters can consume an ever longer finite binary
tail. The real intersection problem is now reproduction **plus** an ordinary
root, not missing forward semantics alone.

## Implemented fixed-word probe

`experiments/cyclic_descent/difference_map_programs.py` implements the
four-copy product-space update on a deliberately restricted first grammar: a
candidate is one composable cycle of exact positive-time macro-rules. The
semantic projection selects exact edges; closure selects a directed cycle;
reproduction selects a cycle with an expanding tail/counter proxy; and the
ordinary projection selects cycles with low-amplitude exact finite cylinders.
Every displayed candidate is independently replayed symbolically. Run and
recheck the committed audit with

```text
python3 experiments/cyclic_descent/difference_map_programs.py search \
  --pool-mode exhaustive --cycle-length 6 --cylinder-depth 32 \
  --ordinary-pool-size 2000 --iterations 120 --restarts 8
python3 experiments/cyclic_descent/difference_map_programs.py verify \
  experiments/cyclic_descent/difference_map_program_audit.json
```

The exact length-six enumeration contains 102,111 based cycles. Of these,
95,424 satisfy the structural reproductive proxy and 102,106 have a valid
ordinary witness for 32 repetitions. The least witnesses are already 188--193
binary digits long. There is no nontrivial exact periodic point and no exact
invariant arithmetic ray. The full exact recount and all 20 emitted candidates
pass the verifier.

One of eight numerical restarts reaches residual `1.51e-18`. This is a useful
calibration failure, not a near-counterexample: the finite-cylinder ordinary
projection and the reproductive proxy genuinely intersect, but the exact
infinite-ordinary postcondition rejects their consensus cycle. A small
difference-map residual therefore cannot replace that postcondition.

The computation also exposes a general fixed-word obstruction. If a word has
`L>0` binary tail reads and all exact tail multipliers are odd, its composite
tail slope is `A/2^L` with `A` odd. Preserving a full arithmetic ray would make
the induced coefficient of its free parameter an integer, which would require
`2^L | A`. Hence no fixed word in this atlas can reproduce an arithmetic ray.
Its nested finite cylinders converge only to a 2-adic address unless the
composite affine map has an actual nonnegative integral fixed point. The
arithmetic implication is kernel-checked as
`Collatz.no_fixed_odd_word_ray` in `formal/Formal/Collatz.lean`.

This closes the fixed-word version. The next high-leverage object is no longer
generic: it is the **autonomous 17-adic place-value counter** already isolated
in the EC17 public-payload lane. The evolving public state must store `n`,
execute `n -> n+1`, expose `v_17(n+1)`, and emit

```text
m_n = j + 8*17^v_17(n+1),       1 <= j <= 8.
```

The externally printed sequence and its rank-two Mahler identities are
already exact; `RankTwoRulerMahler.lean` checks the latter. They are not a
program. The construction target is a finite local carry transducer whose
unbounded tape/register is part of the ordinary evolving payload. This lets
the language split and regroup cylinders according to regenerated data and
is not covered by the odd-over-power-of-two lemma. PSC work should therefore
parallelize synthesis of this public odometer compiler and exact replay, not
grind longer repetitions of one word or rediscover the external schedule.

## First implementation

Use a small but extensible chart budget and encode each rule slot by continuous
features plus one-hot logits:

```text
chart bases and coefficients,
residue guard,
primitive/chain opcode sequence,
target chart,
counter affine map,
resource gain.
```

Run the four-copy product-space difference map at `beta=1,-1` and a short
parameter sweep. Each iteration is massively parallel across rule slots in
`P_S`; independent restarts are embarrassingly parallel and appropriate for
PSC. Candidate fixed points are accepted only after exact JSON replay, the
forward-closure audit, reproduction-cycle certification, and Lean checking.

Diagnostics should record the four residuals separately. A persistent
semantic residual identifies a missing arithmetic macro. A closure residual
identifies a missing branch. A reproduction residual means the language is
closed but bounded. An ordinary-root residual identifies a completion-only
phantom. This decomposition is more informative than a single SAT/UNSAT bit.

## Cautions

The method is a search heuristic on nonconvex sets. The paper explicitly says
that convergence theory covers convex constraints, not the difficult
applications. A small displacement is not evidence of a Collatz result; it is
only a candidate-extraction trigger.

Likewise, closure plus an expanding grammar is not automatically a divergent
Collatz orbit. Forward semantics, positive macro-time, intermediate avoidance
of `1`, proper resource growth, and an ordinary root are all necessary. These
conditions are included separately precisely because every one has failed in
an earlier construction.

## Sources

- V. Elser, I. Rankenburg, and P. Thibault, “Searching with iterated maps,”
  *PNAS* 104 (2007), 418--423,
  https://www.pnas.org/doi/10.1073/pnas.0606359104
- Open full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC1766399/

No counterexample, divergent orbit, or Collatz proof is claimed.
