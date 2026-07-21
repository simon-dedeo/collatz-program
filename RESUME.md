# Restart note

Paused: 2026-07-21

Start from the latest `origin/main`.  The last CLEAN_LEAN mathematical
milestone is `4419b30` (`Add intermittent and soft KL endpoint bridges`); the
formalizer's own restart guide is `CLEAN_LEAN/CLEAN_LEAN_RESUME.md` from
`eaa2f0d`.

## Read first

1. [`README.md`](README.md) for the synchronized claims, failure ledger, and
   ranked Future directions.
2. This file and [`HANDOFF.md`](HANDOFF.md) for workflow and historical
   context.
3. [`CLEAN_LEAN/CLEAN_LEAN_RESUME.md`](CLEAN_LEAN/CLEAN_LEAN_RESUME.md), then
   the tail of [`CLEAN_LEAN/FOR_FABLE.md`](CLEAN_LEAN/FOR_FABLE.md), for the
   exact formal boundary.
4. [`CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md`](CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md)
   and [`CLEAN_LEAN/AUDIT.md`](CLEAN_LEAN/AUDIT.md) before citing a Lean result.
5. The relevant note under [`docs/notes/`](docs/notes/) before rerunning an
   experiment.

Do not assume that any local, cluster, or agent job survived the pause.  Check
external state explicitly before reusing it.

## What is actually proved

- The exact local `k=19` KL record supports every fixed predecessor exponent
  below `0.9094372617...` under the documented mixed exact-Python/kernel-Lean
  trust policy.  Its SHA-pinned 2.9 GB sidecar is local, not portable.  A fresh
  clone is self-contained through `k=15`.
- The `k=12` certificate and counting consequence are fully Lean-native.
- Strict feasible improvement and an infinite increasing feasible ladder are
  proved, but no quantitative rate forces their parameters to two.
- The side-bush packing and normalized capacity inequality along an injective
  Syracuse spine are exact.  Their present numerical load does not exclude an
  exponentially escaping orbit.
- None of this proves the Collatz conjecture, `klLambda k -> 2`, positive
  density, absence of nontrivial cycles, or absence of divergent orbits.

The 8,784-job CLEAN_LEAN build at the pause had no project axiom, `sorry`, or
`admit`.  The reported headline axioms were exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact open endpoint interfaces

There are two independent kernel-checked consumers.  Future work should
supply an input to one of them, not rebuild their downstream algebra.

### A. Hard-min amortized pressure

For a positive exact selected fixed tower, it is enough to choose increasing
precision checkpoints independently of the observed defect values and prove

```text
epsilon_(t_(i+1))
  >= epsilon_(t_i)+a_i epsilon_(t_i)^2,
a_i>=0,
sum_i a_i/(1+a_i) -> infinity.
```

Commit `4419b30` telescopes this to `klLambda k -> 2` and then to literal
`X^(1-epsilon)` one-halving Syracuse predecessor counting.  It permits zero
gain stages, gains tending to zero, and arbitrary intermediate motion.  It
does not construct the fixed tower or prove the gain.  Research indexing is
finest-to-coarsest; Lean stores the recurrence in reverse order.

The spatial `5->2->8->5` carry cycle is within one precision.  It is not three
precision checkpoints.  A holonomy argument must first aggregate within-level
frustration into a cross-depth inequality.

### B. Fixed-temperature soft-to-hard transfer

For `beta>0`, `4419b30` defines the normalized ternary cold mean, replaces only
the KL refinement-fiber minimum, retains transport, and proves

```text
F_hard(x) <= F_beta(x) <= 3^(1/beta) F_hard(x).
```

A positive soft subeigenvector

```text
r*x <= F_beta(x),       3^(1/beta) < r
```

normalizes to exact hard feasibility.  Arbitrary sparse witness levels with
parameters tending to two then imply almost-linear predecessor counting.  The
missing input is fixed-temperature saturation or finite certified positive
soft subeigenvectors crossing the displayed factor.  Exact soft eigenvectors,
Brouwer, consecutive levels, and a hard-min quadratic estimate are not needed.

## Ranked restart choices

For the full conjecture, prefer the first two; `lambda_infinity=2` remains a
strictly weaker milestone.

1. Turn side-bush plus rational-base span capacity into a deterministic
   no-escape theorem for one feedback-selected arithmetic orbit.
2. Find a cycle obstruction that couples compatible ramified-refinement walks
   to the cycle-modulus exponential sums and sees more than `(K,L)`.
3. Prove the hard-min checkpoint law above, perhaps with a compensating
   tie-wall/second-gap potential.
4. Prove soft saturation or generate certified cold subeigenvectors crossing
   `3^(1/beta)` along parameters tending to two.
5. Find a genuinely new cofinal exact feasible ansatz; tested OBDD, aligned
   grammar, sparse-ANF, and tensor-train policy models did not compress.

One concrete diagnostic for item 3 is an induced carry-return operator.  Doob-
transform the selected or softened active Jacobian, induce on branch-reset or
defect/tie-wall states, retain policy and sibling masses, and mark excursions
by transport-versus-branch mismatch.  Operator-renewal and complex Ruelle--
Perron--Frobenius theory suggest twisting returns by carry/minimizer holonomy.
The literal neutral section `Y={m:m=5 (mod 9)}` has a pure-transport return
`5->2->8->5`; for its Doob kernel `P`, start with
`R_n=1_Y P (1_(Y^c) P)^(n-1) 1_Y` and retain the full three-sheet return
action rather than collapsing it to a scalar voltage.
Before promoting this route, test selected-policy self-consistency, cylinder-
variation decay, excursion summability, finite irreducibility/aperiodicity,
and spectral and reward bounds uniform in refinement and inverse temperature.
The known annealed block law is geometric, so infinite-measure heavy-tail
theorems do not apply to it directly.

## Closed or low-priority lanes

Do not restart these without a new hypothesis that evades the recorded
counterexample:

- bounded predictive-memory / epsilon-machine inference;
- the natural finite defect-automaton quotient;
- generic local `D_KL` or other simplex-divergence coercivity;
- uniform unweighted shell-`L2` contraction;
- a cone-wide quadratic coarse-minimum law;
- more unrestricted larger-level numerics as a substitute for an all-level
  mechanism.

`experiments/kl/diagnose_active_path_memory.py` is the accepted finite negative
diagnostic.  `experiments/kl/diagnose_predictive_defect.py` was left as
uncommitted exploratory scratch; preserve it unless a future driver explicitly
decides to rehabilitate or archive that lane.

## Quick verification

From the repository root:

```bash
git status --short
git log --oneline -8
python3 experiments/kl/verify_iterated_minimum_growth.py
python3 experiments/kl/diagnose_active_path_memory.py
git diff --check
```

The first exact script needs local certificate sidecars for its highest rows.
The memory diagnostic uses the portable `k=12` record and took about seven
seconds at the pause.

For the expensive formal audit:

```bash
cd CLEAN_LEAN
lake build
lake env lean CleanLean/Audit.lean
rg -n '\bsorry\b|\badmit\b|^axiom\b|^unsafe\b' CleanLean -g '*.lean'
```

## Worktree and communication rules

- Preserve unrelated and untracked work.  Inspect before staging.
- The research driver must not edit or stage `CLEAN_LEAN/*`.  Send
  research-to-Lean statements through `docs/FOR_CLEAN_LEAN.md`; read replies in
  `CLEAN_LEAN/FOR_FABLE.md`.
- Distinguish exact/Lean/exhaustive results from floating diagnostics in every
  claim.
- Update the root README and the relevant note after a substantive result or
  failure.
- Commit only coherent files, push useful checkpoints, and include exactly:

  ```text
  Co-authored-by: OpenAI Codex <codex@openai.com>
  ```

The failure ledger is part of the result.  Resume ambitiously, but do not blur
a finite pattern, a conditional theorem, and a proof of Collatz.
