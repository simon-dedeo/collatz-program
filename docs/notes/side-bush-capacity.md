# Side-bush capacity along a hypothetical divergent orbit

2026-07-21.  Status: **kernel-Lean structural theorem plus exact bounded
diagnostic**.  Lean commit `b47aa31` packages the side-target identities,
disjoint predecessor packing, explicit targetwise KL bound, and their finite
capacity composition.  This note asks a deliberately
full-Collatz question: can predecessor abundance be converted into an
obstruction to a single escaping forward orbit?  The answer is a new packing
inequality, but the first numerical audit also shows why the present KL
exponents do not yet make it decisive.

The useful outside analogy is not generic branching-process language.  It is
the **spinal decomposition / Carleson packing** pattern: cut the inverse tree
into disjoint bushes attached to one distinguished forward ray, then charge
each bush by the lower bound supplied by KL.

## 1. The exact side targets

Use the Syracuse normalization

```text
T(n) = n/2              (n even),
       (3n+1)/2         (n odd).
```

Let `n_j=T^j(n_0)` be an injective positive orbit.  A divergent orbit is
injective: a repeated value would make its tail periodic.  At every odd
`n_j`, the point `n_(j+1)` has two immediate predecessors.  The spine uses the
odd one `n_j`; the even side predecessor is

```text
a_j = 3 n_j+1 = 2 n_(j+1).
```

For the KL class `2 mod 3`, take one further even predecessor

```text
b_j = 2 a_j = 6 n_j+2.                                (1.1)
```

Then, exactly,

```text
b_j = 2 (mod 3),       T^2(b_j)=n_(j+1).              (1.2)
```

The extra doubling is not cosmetic: `a_j=1 mod 3`, whereas every `b_j` is a
literal KL target state.

## 2. Disjoint-bush lemma

Write `Pred(b)` for all positive integers whose forward orbit reaches `b`.

**Lemma (research proof, independently packaged in Lean).**  If the spine `(n_j)` is
injective, then the sets `Pred(b_j)`, over odd spine positions `j`, are
pairwise disjoint.  Every `b_j` is also nonperiodic.

**Proof.**  First `a_j` is not on the spine.  If `a_j=n_t`, then
`n_(j+1)=T(a_j)=T(n_t)=n_(t+1)`.  Injectivity gives `j=t`, contradicting that
`n_j` is odd while `a_j` is even.

Suppose one `x` reaches both `b_i` and `b_j`.  Along the deterministic orbit
of `x`, one target occurs first.  If the occurrences are simultaneous, (1.2)
and injectivity give `i=j`.  If `b_j` occurs one step after `b_i`, then
`b_j=T(b_i)=a_i`, impossible modulo `3`.  If it occurs at least two steps
later, (1.2) says it is a point on the forward spine from `n_(i+1)`, whereas
the preceding paragraph says no side target can be on that spine.  Thus
`i=j`.  Finally, if `b_j` were periodic, its iterate `n_(j+1)` would be
periodic, contradicting injectivity of the spine.  QED.

Consequently, for every finite set `J` of odd spine positions and cutoff `X`,

```text
sum_(j in J) pi_(b_j)(X) <= X,                         (2.1)
```

where `pi_b(X)=#(Pred(b) intersect [1,X])`.  This is the exact Carleson
packing step: no independence or random-orbit hypothesis occurs.

## 3. Insert the KL lower bound

Fix a level-`k` feasible KL vector `c`, parameter `1<lambda<=2`, and

```text
C = sum_s c(s),       gamma=log_2(lambda).
```

Lean commit `b47aa31` exposes in
`CLEAN_LEAN/CleanLean/KL/CountingTransfer.lean` the named explicit targetwise
estimate

```text
pi_b(X) >= [c(state_k(b))/(4C)] (X/b)^gamma            (3.1)
```

for every nonperiodic `b=2 mod 3` and every `X>=b`.  The theorem is
`predecessorCount_lower_bound_klTarget_of_feasible`; the previous eventual
exponent wrapper is now derived from it.

Combining (2.1) and (3.1) gives the **side-spine capacity inequality**

```text
sum_(j in J) c(state_k(b_j)) / b_j^gamma
    <= 4 C X^(1-gamma),                               (3.2)
```

whenever every `b_j<=X`.  Equivalently, with the probability profile
`mu_k=c/C`,

```text
sum_(j in J) mu_k(state_k(b_j)) (X/b_j)^gamma <= 4X.  (3.3)
```

The combined finite statement is kernel-packaged as
`sideSpine_capacity_of_feasible` in
`CLEAN_LEAN/CleanLean/KL/SideBushCapacity.lean`.  Its orbit and disjointness
inputs are proved in `CLEAN_LEAN/CleanLean/Collatz/SideBush.lean`.  Commit
`3577b8f` adds the normalized form (3.3) as
`normalized_sideSpine_capacity_of_feasible`.  The full project build and axiom
audit pass; the new capacity theorems use only the standard axioms reported in
the Lean audit.

For a completely rational finite check one can replace `log_2(X/b_j)` by
`floor(log_2(X/b_j))` and use

```text
pi_(b_j)(X) >= [c(state_k(b_j))/(4C)]
                lambda^floor(log_2(X/b_j)).           (3.4)
```

The diagnostic uses (3.4), so it never compares floating powers in its exact
gate.

## 4. What this would need in order to prove Collatz

The inequality is a real bridge from KL to a forward counterexample, but it
also identifies two separate missing statements.

1. **Endpoint capacity.**  Merely knowing `lambda_k -> 2` lets `gamma` approach
   one while both the state profile and its normalization change with `k`.
   It does not produce a single limiting measure for which (3.2) survives at
   `gamma=1`.  A projectively tight KL measure, or a uniform Carleson embedding
   theorem for the selected tower, would be new information beyond the
   `(1-epsilon)` result.
2. **A divergent-charge theorem.**  Even an endpoint inequality of the form
   `sum_j w_j/b_j<infinity` does not contradict an exponentially growing
   orbit: its reciprocal series can converge.  One would need an arithmetic
   theorem forcing a hypothetical divergent orbit to visit enough
   high-`mu_k` states at sufficiently small height.  This is where an adelic
   Poisson-boundary, Maharam-conservativity, or rational-tile argument could
   genuinely enter; a measure-zero statement cannot do the job.

The construction says nothing new about a nontrivial cycle because its spine
is not injective.  Cycle exclusion still needs the exponential-sum or
compatible-lift lane.

## 5. Finite diagnostic and verdict

Run

```text
python3 experiments/full/verify_side_bush_capacity.py
```

The script:

- exhaustively checks the side-target identities and pairwise first-entry
  disjointness on bounded orbit prefixes;
- SHA-pins the portable exact `k=12` certificate;
- checks the rational lower-load formula (3.4) against brute-force
  predecessor counts; and
- measures the bound on the longest stopping-time trajectory among seeds at
  most `200000`.

On that finite champion (`156159`, 241 Syracuse steps, 141 odd attachments),
the actual side bushes occupy a large part of `[1,10^6]`, but the certified
`k=12` lower load is tiny because the normalized target weights are tiny.
At cutoff `10^6`, the first 50 active side targets have an actual disjoint
union of `658073`, while the rational KL lower load is only
`0.00976939675461`.  The latter is about `9.77e-9` of the interval.
This is a useful falsifier: side-bush disjointness by itself does **not**
amplify the present exponent into a contradiction.

**Verdict.**  This produces a new measurable invariant--the KL-weighted
side-spine capacity--and an exact full-orbit interface.  It is not presently a
proof route on its own.  Its value is that any proposed endpoint regularity
theorem can now be tested against a concrete necessary condition on every
hypothetical divergent orbit, rather than ending at predecessor abundance.

## 6. Outside sources

- Lyons, Pemantle, and Peres, *Conceptual proofs of `L log L` criteria for
  mean behavior of branching processes*, Ann. Probab. 23 (1995): the
  size-biased-tree/spine change of measure.  The Collatz bushes here are
  deterministic; only the decomposition pattern is imported.
- Brofferio, *The Poisson boundary of random rational affinities*
  ([arXiv:math/0403198](https://arxiv.org/abs/math/0403198)): the product-of-
  places boundary candidate for the missing divergent-charge theorem.
- Morgenbesser--Steiner--Thuswaldner, *Patterns in rational base number
  systems* ([arXiv:1203.4919](https://arxiv.org/abs/1203.4919)): adelic
  self-affine tiles and character sums for rational-base digit patterns,
  another possible way to couple height to the arithmetic section.
