# Same-policy defect automaton: exact semantics, full-state no-go

2026-07-21. Status: **pinned exact finite combinatorics + floating spectral
diagnostics + negative verdict on the natural small quotient**. Run

```bash
python3 experiments/kl/diagnose_same_policy_defect_automaton.py
```

The checker uses the portable `k=12` selected certificate. It SHA-pins the
manifest, verifies the residue/carry maps and their inverses, and separates
the exact graph statements from the explicitly floating Perron radii.

## 1. What “same policy” makes exact

Let a level-`k` vector have `N=3^(k-1)` coordinates and put `n=N/3`. Write

```text
x_(u,a)=x_(u+a n),       0<=u<n,  a in F_3.
```

On a strict minimizing-policy cell, one label

```text
sigma(u)=argmin_a x_(u,a)
```

is fixed in each fiber. The nonlinear minimum is then a coordinate
projection, so the KL map is a single nonnegative matrix `A_sigma`. In
particular, whenever `x` and `y` lie in that same cell,

```text
F(x)-F(y)=A_sigma(x-y).                              (1.1)
```

This is the semantic difference from the old annealed ball automaton. The
annealed operator sends all three siblings down a branch with weight
`w_beta/3`. The active operator sends only the sibling actually selected by
`sigma`, with weight `w_beta`.

The support graph of `A_sigma` is the finite defect automaton tested here.
Its vertices are the `N` fine coordinates. A source `i` always has the
transport successor

```text
T^(-1)(i)=4^(-1)(i-2) mod N.                         (1.2)
```

If `i=u+sigma(u)n` is the selected child of fiber `u`, it has two additional
successors: the unique type-2 and type-8 rows whose branch target is `u`.
Thus a selected-coordinate defect can split into transport, type-2, and
type-8 descendants. Every branch output also has its ordinary transport
input, so independently propagated defects can merge there. All carry maps
are retained exactly.

Sibling masses enter through the domain on which (1.1) is valid. For a
perturbation `d` and amplitude `eta`, the policy remains fixed precisely while

```text
x_(u,a)-x_(u,sigma(u))
  + eta (d_(u,a)-d_(u,sigma(u))) > 0                (1.3)
```

for every nonselected sibling. The exact sibling gaps therefore provide a
policy-validity radius for any proposed defect mode; a recurrent path in the
support graph alone is not enough.

## 2. Exact recurrence, splitting, and merging

For the pinned `k=12` vector all `59,049` fiber minima are strict, with policy
counts

```text
(#sigma=0,#sigma=1,#sigma=2)=(20037,19545,19467).
```

The checker applies the rationally tightened active operator once using a
common integer denominator and verifies that **all 59,049 minimizing labels
are retained**. This validates the same-policy interpretation on the pinned
reference step; it does not prove invariance of the whole policy cell.

Restrict vertices to the complement of the first `J` backward-orbit balls of
`-1`, exactly as in the inherited zero-charge test. Strongly connected
components and the split/merge counts are purely combinatorial:

| `J` | kept vertices | largest recurrent SCC | fraction kept | split vertices in SCC | merge vertices in SCC |
|---:|---:|---:|---:|---:|---:|
| 3 | 118,098 | 37,082 | 0.31399 | 19,223 | 12,990 |
| 4 | 150,903 | 116,858 | 0.77439 | 43,979 | 64,212 |
| 5 | 166,212 | 154,968 | 0.93235 | 53,200 | 97,720 |

So the zero-charge recurrence is not an artifact of averaging: the actual
selected policy contains large recurrent components in which defects really
split and merge.

For orientation only, power iteration on the rational-weight matrix rendered
in double precision gives restricted radii

```text
J=3: 0.782366571501
J=4: 0.893411431491
J=5: 0.954415774337.
```

These are **not certified spectral bounds**. Reconnaissance at `k=13,14`
gave respectively

```text
k=13: 0.6973915574, 0.8890088769, 0.9524357554
k=14: 0.6924988383, 0.8850952372, 0.9499478626.
```

At fixed `J` the active restriction looks subcritical, while increasing `J`
pushes the radius toward one. The corresponding active and annealed radii at
`k=13,14` differ by less than about one percent. This is useful evidence that
policy selection changes individual cycles without producing a new uniform
spectral gap.

## 3. The small-state quotient fails

The decisive test is deterministic partition refinement. Start by observing
only

```text
(ball mod 27, top digit, local minimizing label),
```

which gives `81` states. Refine two coordinates whenever their labeled
transport/type-2/type-8 successors have different current states; a missing
branch goes to one common sink. This is the standard exact future-equivalence
test for this labeled transition system. The state counts are

```text
81 -> 5276 -> 57306 -> 96549 -> 134040 -> 161680
   -> 173871 -> 176464.                              (3.1)
```

After seven steps it distinguishes `99.61%` of all `177,147` coordinates.
Adding the complete order of the three sibling masses starts with `162`
states and refines even faster:

```text
162 -> 28214 -> 84090 -> 131567 -> 165355 -> 175338
    -> 176973 -> 177119.                             (3.2)
```

That is `99.984%` of the full state space. Finally, sort each fiber, subtract
its minimum, and reduce the two positive gaps by their gcd. The resulting
exact projective gap pair is different on **every one of the 59,049 fibers**.
The same uniqueness holds in the reconnaissance records at `k=13,14`.
Therefore retaining exact sibling-mass information does not close a small
automaton; it recovers the full record immediately.

## 4. Verdict

The restricted active radius

```text
rho(A_(sigma(c)) restricted to the zero-charge complement)
```

is a well-defined, policy-sensitive finite diagnostic. It is more honest than
the annealed radius and is capable of falsifying a proposed policy-free
envelope. The recurrent SCCs also give a concrete genealogy of propagation,
splitting, and merging.

It is **not yet a new all-level invariant**. With exact sibling data the
construction is essentially the full active Jacobian in automaton language;
with only policy and carry data its deterministic quotient explodes back to
that full system within a handful of steps. The fixed-`J` floating radii show
contraction but no sign of a `J`-uniform gap, and topological recurrence alone
does not guarantee the finite-amplitude inequalities (1.3).

The only credible revival is a genuinely coarser, selection-specific
conditional cone: finitely many inequalities on *ranges* of sibling ratios
that are invariant under the active maps and strong enough to certify a
uniform restricted radius. No such cone emerged here. Without it, the defect
automaton is a useful audit instrument but mostly a repackaging, not a new
proof mechanism.

## 5. External inspiration and scope

Pivato's [defect-particle kinematics in one-dimensional cellular
automata](https://arxiv.org/abs/math/0506417) motivates asking whether localized
violations propagate, split, merge, or persist. Paige and Tarjan's [partition
refinement](https://doi.org/10.1137/0216062) supplies the standard
future-equivalence methodology behind the quotient test. Neither result is
transferred as a theorem here: the KL active graph is derived directly from
the same-policy Jacobian, and all numerical state counts are computed afresh.
