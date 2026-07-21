# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, and formalization. Certified claims are backed by
machine-checkable artifacts; research derivations and finite evidence are
scoped explicitly. Started 2026-07-20 (Claude Fable 5 +
GPT-5.6-sol; PSC Bridges-2 grant mth260010p).

Made possible by the support of Grant 63750, "Explaining Universal Truths",
from the John Templeton Foundation. Additional support from research funds
of the Laboratory for Social Minds and from the Survival and Flourishing
Fund. Proofs and Reasons — https://proofsandreasons.io

Final synchronized research checkpoint: 2026-07-21.  Active work is paused.
Start with [`RESUME.md`](RESUME.md); the ranked restart queue is under
[Future directions](#future-directions).

## A note from the human

I (Simon) am a cognitive scientist, not a mathematician; http://santafe.edu/~simon/cv.pdf

This is a purely experimental project to see what these systems do, and how they reason. There are *many* problems with using AI for mathematics, some of which my colleagues and I have written about---see, e.g., https://arxiv.org/pdf/2603.13680 (*A correspondence problem for mathematical proof*, Eamon Duede and I). One of the things I'm most aware about is the fact that these machines are leveraging insights from real mathematicians, but are unable to properly credit their insights. Anything here should be credited to "the human mathematics community, with apologies." Our colleague, and Proofs and Reasons board member, Michael Harris has written eloquently about the core issues in a recent Boston Review article, https://www.bostonreview.net/articles/knowledge-collapse/

I chose the Collatz Conjecture for three reasons:

1. I understand the theorem!
2. A bit like Fermat's Last Theorem, everyone and their grandmother has worked on it, and any progress towards a proof is unlikely to harm an early-career researcher carving out a new niche.
3. There have been some lovely quanta articles about Collatz and the related Busy Beaver numbers recently, so it was a nice way to learn more https://www.quantamagazine.org/busy-beaver-hunters-reach-numbers-that-overwhelm-ordinary-math-20250822/ I had an idea that there was wisdom hiding in the Busy Beaver community that was partially orthogonal to what "regular" mathematicians know.

Everything below this line, and everything else in this repo, has been automatically generated. Claude Fable 5 drove the initial numerics and research program; a Codex/GPT instance then served as the successor research driver. A separate GPT instance formalized the work in Lean in `CLEAN_LEAN`; it was told to make something that would not annoy Kevin Buzzard. If you want the inter-company drama, visit https://github.com/simon-dedeo/collatz-program/blob/main/CLEAN_LEAN/FOR_FABLE.md

## Project guides

The front page is the state-of-the-project map.  These are the other README
entry points, grouped by role:

| Guide | Scope |
|---|---|
| [`CLEAN_LEAN/README.md`](CLEAN_LEAN/README.md) | Main Lean 4 formalization, build instructions, theorem inventory, and trust boundary. |
| [`formal/README.md`](formal/README.md) | Small original Lean scaffold: definitions, descent reduction, and a bounded `native_decide` check. |
| [`experiments/cycles/README.md`](experiments/cycles/README.md) | Finite-place obstruction tests for hypothetical Collatz cycles; calibrated negative verdict. |
| [`experiments/expsum/README.md`](experiments/expsum/README.md) | Transfer-matrix counts and floating spectral diagnostics at the cycle modulus. |
| [`experiments/modknots/README.md`](experiments/modknots/README.md) | Modular-knot/Ghys probe: the linear invariant collapses; the quadratic linking probe is unresolved. |
| [`experiments/dfacert/README.md`](experiments/dfacert/README.md) | Exhaustive base-2 regular divergence-certificate search, completed through eight states. |
| [`experiments/dfacert3/README.md`](experiments/dfacert3/README.md) | Independent base-3 regular divergence-certificate search, completed through five states. |
| [`experiments/wfar/README.md`](experiments/wfar/README.md) | Weighted finite-automaton/arctic certificate framework and soundness conditions. |
| [`experiments/family/README.md`](experiments/family/README.md) | Fate census for families of generalized Collatz maps. |
| [`experiments/gpu/README.md`](experiments/gpu/README.md) | Audited CUDA ports of the family and exponential-sum tools. |

The formalizer's final synchronized restart note is
[`CLEAN_LEAN/CLEAN_LEAN_RESUME.md`](CLEAN_LEAN/CLEAN_LEAN_RESUME.md).

The KL certificate directory has no separate README.  Its principal landing
pages are [`experiments/kl/RESULT.md`](experiments/kl/RESULT.md) and
[`experiments/kl/TERMINATION_AUDIT.md`](experiments/kl/TERMINATION_AUDIT.md).
The theoretical index is [`docs/STRATEGY.md`](docs/STRATEGY.md); individual
claims and failures live under [`docs/notes/`](docs/notes/).

## Proof boundary at the pause

The program now has two deliberately separate targets.  The ambitious one is
the conjecture itself: exclude both a nontrivial positive cycle and an
injective positive orbit escaping to infinity.  The quantitative one is
`λ_∞=2` for the Krasikov–Lagarias (KL) predecessor-counting systems. It would imply
`π_a(x)≥x^(1−ε)` for every `ε>0`. The finite bridge is complete: a mixed
exact-Python/kernel-Lean chain transfers the `k=19` certificate to the current
predecessor-count exponent, the `k=12` record is fully Lean-native, and Lean
constructs an infinite strictly increasing feasible ladder. What remains is a
dimension-free rate; strict growth by itself can converge below two.  Commit
`da029d4` also closes the conditional composition from a supplied positive
exact fixed tower and its gain estimate all the way to almost-linear counting.
It does not construct that tower or prove the estimate.

The distinction matters: even `λ_∞=2` would not prove Collatz.  We are now
using the KL tower as one input to full-proof interfaces, not treating its
endpoint as the finish line.  The first such interface cuts the inverse tree
into pairwise disjoint side bushes along any hypothetical divergent forward
spine.  Combining their disjointness with the explicit KL target bound gives
a weighted Carleson/capacity inequality.  This is a genuine constraint on a
counterexample, but present exponents make its certified load tiny and even a
linear endpoint would still need an arithmetic theorem preventing exponential
escape.  See `docs/notes/side-bush-capacity.md`.

In parallel, `docs/notes/thin-connection-atlas.md` works outward through
literatures not selected for mentioning Collatz.  Its most concrete junction
is a branched cyclic-voltage/character decomposition of the KL refinement;
its most ambitious forward-orbit junction is the adelic Poisson boundary of
rational affine products.  For cycles, the existing cycle-modulus exponential-
sum lane and compatible closed walks through the ramified residue tower remain
the only current mechanisms aimed at outright exclusion rather than another
density statement.  Every one of these is a program or kill test, not a proof.

The cleanest strong conjecture is the selected quadratic coarse-minimum law

```text
epsilon_(j+1) >= epsilon_j+(3/2)epsilon_j^2
```

It holds by exact arithmetic at every available stage of the selected
`k=12,...,19` records. It is false on the generic feasible cone. Lean commit
`38f1497` proves that an all-level selected-critical version would telescope to
`λ_∞=2`; it does not prove the selected law.  Uniform gain at every depth is
stronger than the endpoint actually needs.  Lean commit `4419b30` accepts
structurally chosen, increasing precision checkpoints with nonnegative net
coefficients `a_i`, as long as

```text
sum_i a_i/(1+a_i) -> infinity.
```

In the finest-to-coarsest convention used by the exact scripts, a checkpoint
gain is

```text
epsilon_(t_(i+1)) >= epsilon_(t_i)+a_i epsilon_(t_i)^2.
```

It also checks the exact bound
`epsilon_n <= 1/(1+sum_(j<n) a_j/(1+a_j))`.  The best current target is
therefore an amortized selected-pressure theorem; the observed uniform
coefficient `3/2` is a particularly clean sufficient case, not the minimal
obligation.

Three formulations sharpen that missing theorem:

- The defect is a three-way Doeblin overlap. Generic channel contraction is
  exponentially too weak, but a renewal-min-constrained Doeblin curve—or the
  equivalent weighted anti-alignment of endogenous argmin labels—would supply
  the observed quadratic gain. The finite frustration lower bound already
  clears the first-stage target on `k=12,...,15`.  A generic three-edge
  holonomy forces a label mismatch away from tie walls, but the spatial
  `5->2->8` transport orbit at one precision is not a block of three coarse
  projections.  The missing bridge must aggregate within-level frustration
  into cross-depth gain, possibly through a compensating tie-wall potential.
- Information geometry identifies the exact local quantity more sharply.
  Direct `D_KL`, Jeffreys, Jensen--Shannon, and Hellinger comparisons of the
  two conditional triples have the wrong zero set.  Projection by `D_KL` onto
  the shared-minimizer cone has the right zero set but is quadratically small
  near tie walls.  The hard mismatch itself is the zero-temperature rate of
  an order-dependent Rényi divergence between residual-cost Gibbs escorts,
  with uniform rowwise error `log(3)/beta`; Lean commits `8c3e1df`--`9ff6d64`
  check the two-copy, multiway, and literal-overlap cold-limit sandwiches.  An
  explicit slowly rotating family shows why local
  simplex geometry alone cannot yield global coercivity.
- For the homogeneous power means, `F_min≤F_(-β)≤3^(1/β)F_min` uniformly in
  the level. Power-mean projection also proves that `ρ_(k,λ,p)` is increasing
  in `k` and bounded by the annealed value `s(λ)`, so its fixed-temperature
  limit exists. It would therefore suffice to identify that limit with `s(λ)`
  for every fixed `λ<2` and finite `p<0`, choosing
  `−p>log(3)/log(s(λ))`. Near-tie selector spikes drift to colder scales, so
  uniform eigenvector regularity is neither assumed nor presently credible.

The same-policy defect audit found genuine recurrent split/merge dynamics, not
an annealed artifact. Its natural carry/policy quotient nevertheless refines
to essentially the full Jacobian, so it is a diagnostic rather than a compact
finite-state invariant. A selected mean-defect plus anti-concentration theorem
and the older expanding-window cones remain secondary endpoint routes.  A
bounded-history predictive-memory follow-up also failed its exact blocked
controls and is closed rather than promoted to an epsilon-machine claim. The
detailed evidence, counterexamples, and live kill tests are in the strategy
map and linked notes below.

None of these statements settles Collatz, positive density, divergence, or
nontrivial cycles. The predecessor result counts preimages of a fixed `a`; even
an `x^{1−ε}` lower bound is sublinear for each fixed `ε` and by itself gives no
positive-density conclusion.

## Headline results (with verification scope)

| Result | Status |
|---|---|
| Exact `k=19` KL threshold `γ₀=log₂(18783127/10⁷)=0.9094372617…` (all fixed `γ<γ₀`) | The SHA-pinned 2.9 GB sidecar passes all 387,420,489 exact inequalities. Lean commits through `76ec861` replace two false printed steps and prove the generic transfer to `π_a(X)≥X^γ` eventually for every eligible fixed target and every `γ<γ₀`. This is a mixed exact-Python/kernel-Lean chain; the large record is not one Lean-native theorem and a fresh clone is self-contained through `k=15`. See `experiments/kl/RESULT.md` and `experiments/kl/TERMINATION_AUDIT.md`. |
| Fully Lean-native `k=12` counting checkpoint | Commits `4c7fcc3`/`659dc81` kernel-reduce all 177,147 feasibility rows, pin the generator/source provenance, and prove `HasPredecessorExponent a (log₂(18064231/10^7))` for every eligible target. The audited build uses no `sorry`, `native_decide`, or project axiom. |
| Strict existential improvement and infinite feasible ladder | `78602d4` proves that every positive feasible point below two lifts to a strictly larger feasible parameter at the next level. `882a00e`/`9323f26` specialize this to `k=12` and produce an existential predecessor exponent strictly above the Lean-native decimal. The gain is non-numerical and may be exponentially small, so this is not `λ_∞=2`. |
| Coarse-minimum/defect package and conditional counting endpoint | `5a8727f`/`786c02e` prove coarse-minimum order and defect data processing; `ee37cd9`/`27b9e69` expose the exact rowwise mismatch and one-stage canonical frustration seam; `d4b328b` retains inherited supersolution slack. Commits `ca0a6e9`/`e2723e2` isolate the exact all-stage normalized and rowwise slack-gain premises. Exact selected `k=12,...,19` data obey `ε_(j+1)≥ε_j+(3/2)ε_j²`, while an exact feasible `k=3` counterexample rules out a cone-wide theorem. `38f1497` proves the conditional endpoint, `da029d4` composes it to literal almost-linear predecessor counting, and `4419b30` weakens uniform gain to divergent effective intermittent or checkpoint gain. The theorems still assume a positive exact fixed tower, all mass/defect side conditions, and the gain; the certificate records are feasible subeigenvectors, not instances of that tower. See `docs/notes/coarse-minimum-gap.md`. |
| Information-geometric selected defect | For each carry-aligned transport/branch fiber pair, the local hard slack is the zero-temperature order-θ Rényi separation rate of two residual-cost escorts, uniformly within `log(3)/β`; Lean commits `8c3e1df`--`9ff6d64` check the scalar, multiway, and literal-overlap forms. A `D_KL` projection onto the union of common-minimizer order cones has the exact zero set and satisfies `(3/4)J²≤I≤log(3)J`, but on `k=12,...,14` it is only `3.45%,3.18%,2.98%` of the quadratic target. An exact slowly rotating family has macroscopic fiber defect and vanishing information production, so a selected carry/branch rigidity theorem is still essential. See `docs/notes/information-geometric-defect.md`. |
| Uniform zero-temperature control and an exact soft-to-hard bridge | For `p=-β`, `F_min≤F_p≤3^(1/β)F_min`; for every fixed `p<1`, power-mean projection proves `ρ_(k-1,λ,p)≤ρ_(k,λ,p)≤s(λ)`, so the fixed-temperature limit exists. Lean commit `4419b30` checks the literal normalized ternary cold mean, replaces only the KL branch-fiber minimum, retains transport, and turns any positive soft subeigenpair `r*x≤F_β(x)` with `3^(1/β)<r` into exact hard feasibility and, along arbitrary witness levels tending to parameter two, almost-linear counting. It does not construct those subeigenvectors or prove fixed-temperature saturation. The two-copy carry audit also closes generic unweighted `L²` contraction; selected/on-code cancellation remains open. See `docs/notes/softmin-replica.md` and `docs/notes/softmin-pair-carry.md`. |
| Forward-orbit side-bush capacity | Along an injective Syracuse spine, the inverse basins attached at the odd-step side targets `b_j=6n_j+2` are pairwise disjoint. Lean commits `b47aa31`/`3577b8f` package the side-target identities, disjoint packing, explicit all-`X` KL lower bound, and normalized combined capacity inequality; the full audit and a separate SHA-pinned exact checker pass. The current numerical load is tiny, so this is a new full-proof interface, not a proof of divergence exclusion. See `docs/notes/side-bush-capacity.md`. |
| Critical base-`3/2` span capacity | The rational-base span is `σ(n)=H(n+1)-H(n)` for a bounded-displacement coordinate satisfying `H(ceil(3n/2))=(3/2)H(n)`. Exact all-level consequences include interval discrepancy at most one, `σ(2n)≥(2/3)K(3)`, and inverse-capacity ratio at least `2/3` (at least `4/3` in residue class two). An independently audited depth-96 checker passes. Explicit exponentially small spans and a telescoping cycle Jacobian kill scalar-Lyapunov and hyperbolicity proofs; only a long-range capacity anti-correlation route survives. See `docs/notes/rational-span-cocycle.md`. |

Other checked results include the exact oscillation identity, the annealed
critical coding and renewal algebra, local renormalization at `−1`, the
Diaconis–Fulman multiplication-carries spectrum, the Mahler/Cartier and
two-base exclusions, Antihydra rarity, exhaustive small-DFA exclusions, the
tree-product Collapse Lemma, and the solenoid Traceless Theorem. Their scopes
and artifacts are indexed below and in `docs/notes/`.

## Strategy and failure map

The chronological record is in [`docs/STRATEGY.md`](docs/STRATEGY.md), with
derivations and exact commands under [`docs/notes/`](docs/notes/).  The finite
KL counting foundation is complete.  The unportable 2.9 GB `k=19` sidecar is
an engineering caveat, not an unproved mathematical premise.

### Surviving proof programs

- **Exclude divergent orbits.**  Combine the exact side-bush packing with the
  critical base-`3/2` span capacity or a product-of-places boundary theorem.
  The missing assertion must control one feedback-selected arithmetic orbit,
  not almost every random affine product.
- **Exclude nontrivial cycles.**  Couple compatible closed walks in the
  ramified ternary refinement tower to the cycle-modulus exponential sums.
  A useful invariant must see more than `(K,L)`.
- **Reach the KL endpoint by hard-min pressure.**  Supply the positive exact
  selected tower and a structural intermittent/checkpoint gain whose effective
  sum diverges.  All downstream telescoping and counting transfer is checked.
- **Reach it by finite temperature.**  Prove fixed-temperature saturation or
  certify positive soft subeigenvectors with factor above `3^(1/beta)` along
  parameters tending to two.  The literal soft-to-hard consumer is checked.
- **Bypass selection entirely.**  Construct exact feasible witnesses at
  arbitrary cofinal levels with parameters tending to two.

The first two are full-Collatz programs.  The last three can at most prove
almost-linear predecessor counting and require a separate no-escape argument.

### Compact failure ledger

| Route | Calibrated verdict | Where to inspect |
|---|---|---|
| Printed KL advanced elimination | Invalid as stated: exact paths break the history-free deletion, nonempty-minimum, and split-invariant steps. The occurrence-aware replacement and counting transfer are kernel-checked, so the finite certificate consequence survives. | [Termination audit](experiments/kl/TERMINATION_AUDIT.md) |
| Printed KL equation (2.1) | False as an equality: `phi^7_2(1)=3` while `phi^14_2(0)=2`. A targetwise one-sided repair gives the required lower-bound direction and is checked in Lean. | [Exact obstruction](experiments/kl/verify_equation_2_1_obstruction.py) |
| Autonomous charged/projective contraction | Structurally closed for every tested admissible window: the `-1` co-spine supplies a marginal mode. This rules out the certificate class, not `lambda_infinity=2`. | [Kill tests](docs/notes/cl-killtests.md) |
| Uniform unweighted shell `L2` contraction | Closed by amenable almost-invariant modes and an exact expanding detail witness. Selected/on-code signed cancellation remains possible. | [Pair-carry note](docs/notes/softmin-pair-carry.md) |
| Generic local information coercivity | Closed: standard divergences have the wrong hard zero set, and a slowly rotating tie-wall family has macroscopic defect with vanishing production. A selected holonomy theorem remains open. | [Information defect](docs/notes/information-geometric-defect.md) |
| Natural finite defect automaton | Closed at the tested quotient: carry/policy refinement recovers essentially the full `k=12` Jacobian. | [Defect automaton](docs/notes/same-policy-defect-automaton.md) |
| Growing bounded-summary predictive memory | Negative at the exact `k=12` checkpoint: next-edge gain is exactly zero and every longer-history gain is negative under origin-digit blocked holdout. | [Exact diagnostic](experiments/kl/diagnose_active_path_memory.py) |
| Pointwise pressure split `U(21/50)` | Refuted on an exact `k=19` feasible record by ratio `0.542601...>0.42`. Rare violations leave mass-weighted or selected-critical statements open. | [Genealogy note](docs/notes/multiscale-genealogy.md) |
| Cone-wide coarse-minimum or entropy monotonicity | Refuted by exact positive feasible `k=3` counterexamples. Any endpoint theorem must retain selected critical or vanishing-slack structure. | [Coarse-minimum note](docs/notes/coarse-minimum-gap.md) |
| Fitted geometric localization envelopes | Closed as all-level critical/vanishing-slack laws by exact low-depth annealed floors. Polynomial or direct selected-family control remains open. | [Terminal statistics](docs/notes/terminal-defect-statistics.md) |
| Global collision growth implies local Pearson decay | False for an audited sparse product law; a separate exact detail mode also expands. Renewal plus positive defect support is insufficient without the nonlinear minimum coupling. | [Annealed coding](docs/notes/annealed-critical-coding.md) |
| Finite-place and finite-state full-proof certificates | Cycle finite-place tests collapse to existing Baker information; exhaustive regular divergence searches find none through eight base-2 or five base-3 states. These are scoped exclusions, not evidence of convergence. | [Cycle tests](experiments/cycles/README.md), [base 2](experiments/dfacert/README.md), [base 3](experiments/dfacert3/README.md) |
| Ordinary linear resolvent / one-certificate-away framing | Retracted. The KL threshold is nonlinear and no ordinary-pole counting bridge was supplied; the autonomous certificate sought earlier cannot exist in its proposed class. | [Analytic-combinatorics audit](docs/notes/analytic-combinatorics.md) |

Other negative probes—tree-product spectral gaps, tropical geometry proper,
ensemble continued-fraction thermodynamics, the first-circle solenoid boundary,
and the linear modular-knot invariant—remain documented in
[`docs/LANDSCAPE.md`](docs/LANDSCAPE.md) and their linked notes.  They should
not be revived on analogy alone.

### Formal boundary

[`CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md`](CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md)
and [`CLEAN_LEAN/AUDIT.md`](CLEAN_LEAN/AUDIT.md) are authoritative.  At the
pause, Lean checks the corrected finite counting chain, the native `k=12`
record, exact transport/Perron and coarse-minimum identities, side-bush
capacity, information-rate and holonomy interfaces, the intermittent hard-min
endpoint, and the literal soft-to-hard endpoint.  The full 8,784-job audit
reports only standard mathlib axioms and no project axiom, `sorry`, or
`admit`.

The standing frame is unchanged: `X^(1-epsilon)` predecessor counting would
be a substantial theorem, but not Collatz.  A full proof still needs both
no-divergence and no-nontrivial-cycle arguments.

## Status at the pause

Active exploration is paused at this checkpoint.  These bullets record the
last live seams and should not be read as background jobs still running.

- The exact iterated-minimum, translated-Doeblin, and `S_3` frustration views
  now isolate one missing amortized selected-pressure theorem. The local
  frustration lower bound clears the first-stage quadratic target on
  `k=12,...,15`, but only as finite exact data.  An application of spatial
  `5->2->8` holonomy would first need a theorem turning within-level mismatch
  into net gain across genuinely increasing precision checkpoints.
- The soft-min investigation found uniform zero-temperature control of values,
  a nonuniform near-tie boundary layer for selectors, and exact refinement
  monotonicity of the softened Perron radii. Their bounded limit exists; the
  stronger scalar target is to prove that it equals the annealed value.
  Floating Collatz--Wielandt diagnostics currently support this through `k=13`.
- The same-policy defect investigation is complete. It confirms real recurrent
  split/merge lineages, then rules out the natural bounded carry/policy quotient.
  The circuit probe is also complete at finite levels: the operator has a short
  output-linear uniform circuit, while selected policies at `k=12,...,15`
  defeat the tested OBDD, aligned-grammar, sparse-ANF, and tensor-train models.
  This is not a lower bound for unrestricted `poly(k)` coordinate circuits.
  The follow-up bounded-history predictive-memory probe also failed its exact
  blocked controls and is not a live lane.
- CLEAN_LEAN has closed the finite counting bridge, exact `k=12` import,
  transport/Perron identification, coarse-minimum order, strict feasible lift,
  the conditional quadratic telescope, the one-stage canonical frustration
  seam, inherited-slack bookkeeping, and the exact scalar/rowwise all-stage
  slack-gain interfaces. Commit `da029d4` closes the conditional composition
  from an exact positive fixed tower to literal almost-linear counting. Commit
  `174b16b` reduces nonlinear positive-eigenpair existence to a simplex fixed
  point; the pinned mathlib lacks Brouwer. Lean still does not construct the
  required fixed tower, prove the selected gain, localization, or a
  dimension-free endpoint rate.  Commit `4419b30` fully audits the weaker
  intermittent/checkpoint consumers and an independent literal soft-to-hard
  route.  The full build completed with 8,784 jobs and no project axiom,
  `sorry`, or `admit`; the reported headline axioms are only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Larger-record computation is deprioritized as a limit strategy. Scaling the
  Lean-native import beyond `k=12` remains an engineering task; the leading
  mathematical priority on restart is an all-level endpoint mechanism.

## Future directions

If the project resumes, the first two problems are the ones that could address
the full conjecture; the KL endpoint remains a substantial but strictly weaker
milestone.

1. **Turn capacity into a no-escape theorem.**  Combine the exact disjoint
   side-bush packing with the critical base-`3/2` span coordinate, and prove
   that one feedback-selected injective Syracuse spine cannot concentrate
   indefinitely on cells whose inverse capacity is summable.  The most
   ambitious candidate is a deterministic, product-of-places/adelic boundary
   statement.  A probabilistic theorem about typical rational affine products
   is not enough: the bridge must control one arithmetic orbit.
2. **Add a genuinely new obstruction to cycles.**  Relate compatible closed
   walks in the ramified ternary refinement tower to the cycle-modulus
   exponential sums.  The target must see more than `(K,L)` and beat the
   existing Baker/Steiner information; separate finite-level cycle counts,
   modular-knot length, and finite-place tests have already failed this test.
3. **Prove amortized selected pressure.**  For structurally chosen checkpoints
   `0=t_0<...<t_m`, prove
   `epsilon_(t_(i+1)) >= epsilon_(t_i)+a_i epsilon_(t_i)^2`, with `a_i>=0`
   and divergent `sum a_i/(1+a_i)`.  A plausible stronger statement is that
   each precision either produces quadratic slack or pays through a bounded
   tie-wall/second-gap potential.  The spatial `5->2->8` orbit must first be
   aggregated within a fixed precision; it is not itself a three-depth block.
   One must also supply the positive exact fixed tower/selection hypotheses
   that the current conditional endpoint consumes.

   A concrete literature-driven version is to Doob-transform the selected or
   softened active Jacobian and induce on branch-reset or defect/tie-wall
   states.  [Gouëzel](https://www.impan.pl/shop/publication/transaction/download/product/87253)
   and [Melbourne--Terhesiu](https://arxiv.org/abs/1008.4113) suggest a marked
   first-return equation for accumulated mismatch, while
   [Kombrink](https://arxiv.org/abs/1512.08351) and
   [Kesseböhmer--Kombrink](https://arxiv.org/abs/1604.08252) permit
   past-dependent or countable symbolic return words.  The literal neutral
   section `m=5 (mod 9)` has the pure-transport
   return `5->2->8->5`, so a marked return encounters both branch types while
   retaining the ramified sheet action.  Twist the return operator by
   carry/minimizer holonomy and ask whether compulsory charged returns produce
   a uniform reward.  The kill tests are
   selected-policy self-consistency, decaying cylinder variation, summable
   excursion weights, finite irreducibility/aperiodicity, and a spectral/reward
   bound uniform as `beta->infinity` and `lambda->2`.  The existing annealed
   run law is geometric, so the infinite-measure theorems do not apply
   directly; without those tests this would only repackage the annealed
   surrogate.
4. **Try the orthogonal soft-to-hard route.**  Prove fixed-temperature spectral
   saturation, or construct positive soft subeigenvectors whose factor beats
   `3^(1/beta)`.  Commit `4419b30` checks the exact branch-only soft operator,
   hard comparison, sparse-level feasibility transfer, and final counting
   consumer.  The surviving analytic input is finite-temperature saturation
   or certified soft subeigenvectors crossing that factor; selector regularity
   is not available, and the two-copy fallback is selected/on-code signed
   cancellation.
5. **Search for a cofinal exact feasible ansatz.**  Exact feasible witnesses at
   arbitrary levels with parameters tending to two bypass fixed-vector
   selection, Brouwer, tie walls, and the entire coarse-minimum pressure route.
   The tested OBDD, aligned grammar, sparse ANF, and tensor-train models failed,
   so a restart should demand a genuinely different symbolic coordinate
   representation rather than another fit to the same finite policies.
6. **Keep formal and engineering work attached to a live premise.**  The two
   downstream endpoint interfaces are now audited.  Formalize a new theorem
   only when it supplies one of their missing structural inputs, and develop a
   streamed representation only if higher certificate imports become
   necessary.  More finite levels or unrestricted local information
   inequalities are low priority unless they discriminate between the
   mechanisms above.

Do not restart the bounded predictive-memory, natural finite defect-automaton,
generic local information-coercivity, or uniform unweighted shell-`L2` lanes
without a new hypothesis that directly evades the recorded counterexamples.

## Verification discipline

Nothing is a result until: exact arithmetic or kernel-checked proof, plus
independent re-derivation (agent vs sol vs data) where feasible, plus
adversarial external review for anything load-bearing. The errata are public:
`SMELL.md` header, `fiber-geometry.md` v2. Corrections to date have come
from both directions (external review killed our Prop R; we killed a stale
preprint alarm and two prescribed-claim errors were corrected by our own
agents' proofs).

## Repository map

The main navigation links are in [Project guides](#project-guides).  For the
research record, see [`docs/STRATEGY.md`](docs/STRATEGY.md),
[`docs/LANDSCAPE.md`](docs/LANDSCAPE.md), [`docs/CRACKS.md`](docs/CRACKS.md),
[`docs/SMELL.md`](docs/SMELL.md),
[`docs/REVERSE-MINING.md`](docs/REVERSE-MINING.md), and
[`docs/CRYPTIDS.md`](docs/CRYPTIDS.md).  The Lean-facing snapshot and trust
ledger are [`CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md`](CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md)
and [`CLEAN_LEAN/AUDIT.md`](CLEAN_LEAN/AUDIT.md).  Data provenance is indexed
by [`DATA.md`](DATA.md), and literature by
[`papers/REFERENCES.md`](papers/REFERENCES.md).

## Credit and mathematical inspiration

*Per Simon's note above: credit belongs to the human mathematics community,
with apologies for the imperfect attribution below. Anything of value here is
their idea; the errors are ours.* Our approach is, honestly, an assembly of
existing lines of work; the closest ancestors, and what each contributes:

**The direct spine of the counting result.**
- **I. Krasikov & J. C. Lagarias, "Bounds for the 3x+1 problem using
  difference inequalities," Acta Arith. 109 (2003) 237–258** (arXiv:math/0205002).
  The x^0.84 record and the LP/difference-inequality method we extend. Our
  entire counting line is *their method, run further and reinterpreted.*
- **[L. Collatz (1942)](https://eudml.org/doc/168987) and
  [H. Wielandt (1950)](https://doi.org/10.1007/BF02230720), the
  Collatz–Wielandt formula** — nonlinear
  spectral radius as inf–max of ratios. The lens under which the KL LP became
  a nonlinear eigenproblem (a genuine, if wry, namesake coincidence).
- **S. Gaubert & J. Gunawardena, "The Perron–Frobenius theorem for homogeneous,
  monotone functions," Trans. AMS 356 (2004)** — existence of the strictly
  positive nonlinear eigenvector; what discharges KL's (H_k) once the base map
  is seen as an odometer.
- **T. Bousch, "Le poisson n'a pas d'arêtes" (2000) and ergodic optimization
  (Jenkinson's survey, 2019)** — the maximizing-measure / zero-temperature
  view of the adversarial limit operator; the nearest *solved* cousin of our
  ℤ₃ transfer operator (optimization over a rotation/odometer). Our λ_∞
  dichotomy is an ergodic-optimization question in disguise.
- **A. A. Ahmadi, R. Jungers, P. Parrilo, M. Roozbehani (path-complete
  Lyapunov, 2014) and M. Philippe et al. (constrained joint spectral radius,
  2016)** — the certificate language. It enabled the structural no-go for
  autonomous charged/projective contraction; it is no longer a live endpoint
  route. Found independently via our keyword-blind search; the credit is theirs.

**Current endpoint inspirations — none selected for mentioning Collatz.**

- **A. Makur & J. Singh, [Doeblin Coefficients and Related
  Measures](https://arxiv.org/abs/2309.08475), and D. Lee, W. Lu, A. Makur &
  J. Singh, [Doeblin Curves](https://arxiv.org/abs/2606.19859)** supply the
  multiway-overlap and constrained-contraction language. Their generic theory
  is too weak here; renewal-min self-consistency is the project-specific input.
- **G. Litvinov, [Maslov
  dequantization](https://arxiv.org/abs/math/0507014); Y. Savas et al.,
  [entropy-regularized stochastic
  games](https://arxiv.org/abs/1907.11543); and J.-R. Chazottes & M. Hochman,
  [zero-temperature nonconvergence](https://arxiv.org/abs/0907.0081)** motivate
  the homogeneous soft-min family and warn that smooth finite-temperature
  selectors need not converge uniformly as temperature vanishes.
- **I. Csiszár, [I-divergence
  geometry](https://doi.org/10.1214/aop/1176996454), and J.-F. Bercher,
  [escort paths and Rényi
  divergence](https://arxiv.org/abs/1206.0561)** supply the information-
  projection and escort language.  The shared-minimizer order cone and the
  transport--branch cold-rate identity are derived here; neither source
  supplies the selected coercivity theorem.
- **S. Gouëzel, [correlation asymptotics from large
  deviations](https://www.impan.pl/shop/publication/transaction/download/product/87253),
  and I. Melbourne & D. Terhesiu, [operator renewal theory in infinite
  measure](https://arxiv.org/abs/1008.4113)** supply the first-return-operator
  equation, aperiodicity gate, and long-excursion estimates proposed for an
  induced selected-defect process.  Their regular-variation theorems do not
  directly fit the existing geometric annealed KL return law.
- **S. Kombrink, [dependent-interarrival renewal
  theorems](https://arxiv.org/abs/1512.08351), and M. Kesseböhmer & S.
  Kombrink, [complex Ruelle--Perron--Frobenius theory for infinite Markov
  shifts](https://arxiv.org/abs/1604.08252)** show how fading dependence on the
  symbolic past or countably many summable return words could replace the
  failed finite defect quotient.  The proposed holonomy twist and uniform
  hard-limit coercivity are new obligations, not consequences of those papers.
- **K. Schmidt, [amenability and strong
  ergodicity](https://doi.org/10.1017/S014338570000924X)** supplies the
  theorem behind the pair-carry no-go: an amenable ergodic carry action has
  almost-invariant modes.  This closes generic shell contraction while leaving
  selected/on-code signed cancellation open.
- **A. Bandeira, A. Singer & D. Spielman, [graph connection
  Laplacians](https://arxiv.org/abs/1204.3873), and C. Lange et al., [magnetic
  frustration inequalities](https://arxiv.org/abs/1502.06299)** provide the
  synchronization/frustration language. Their spectral theorems do not close
  the KL estimate because the abstract gain graph has flat sections.
- **M. Pivato, [defect-particle
  kinematics](https://arxiv.org/abs/math/0506417), and R. Paige & R. Tarjan,
  [partition refinement](https://doi.org/10.1137/0216062)** motivated the
  concrete same-policy propagation and quotient tests. This is inspiration and
  methodology, not a transferred cellular-automaton theorem.
- **R. Bryant, [ordered decision
  diagrams](https://doi.org/10.1109/TC.1986.1676819); I. Oseledets,
  [tensor trains](https://doi.org/10.1137/090752286); and Balle, Panangaden &
  Precup, [weighted-automaton
  minimization](https://arxiv.org/abs/1501.06841)** supply the restricted
  representation models used in the policy-circuit audit. Their machinery
  diagnoses exact finite complexity; it gives no unrestricted circuit lower
  bound.

**Full-proof thin connections — searched outward, not by Collatz keywords.**

- **Liu--Peyerimhoff--Vdovina on cyclic lifts and Dalfó--Fiol--Pavlíková--
  Širáň on factored lifts** provide the character/voltage language for the
  ramified three-sheet KL tower.  Exact checking confirms a quotient/detail
  decomposition with permutation transport and rank-one branch resets; it
  also refutes the stronger claim that KL is an ordinary weighted graph lift.
- **S. Brofferio, [the Poisson boundary of random rational
  affinities](https://arxiv.org/abs/math/0403198)** supplies a precise
  product-of-places object for the affine Collatz blocks.  Its random-walk
  theorem does not control a feedback-selected integer orbit; that missing
  atom/support bridge is the entire moonshot.
- **R. Lyons, R. Pemantle & Y. Peres, [size-biased branching
  spines](https://arxiv.org/abs/math/0404083)** inspired the deterministic
  side-bush cut.  Here it yields a literal disjoint-predecessor packing
  inequality, while also exposing why near-linear counts alone do not forbid
  exponential escape.
- **Akiyama--Marsault--Sakarovitch, [rational-base representation
  subtrees](https://arxiv.org/abs/1706.08266), and
  Morgenbesser--Steiner--Thuswaldner, [adelic rational-base
  tiles](https://arxiv.org/abs/1203.4919), with Akiyama--Frougny--Sakarovitch
  and Odlyzko--Wilf on the endpoint/Josephus coordinate**, supply the critical
  base-`3/2` span capacity.  Its stable even-cell gap and bounded interval
  discrepancy are exact; explicit small spans and neutral cycle Jacobians
  rule out the hoped scalar Lyapunov proof.
- **Akian--Gaubert--Walsh on the max-plus Martin boundary, Bond--Levine on
  abelian networks, and Danilenko--Lemańczyk on Maharam extensions** are the
  other three-way junctions retained by the atlas.  Each has a concrete kill
  test; none is promoted merely because the analogy is attractive.

**The forward-orbit / density tradition (context and the ceiling we press
toward).**
- **R. Terras (1976)** — density-1 finite stopping time; the elementary
  parity/congruence structure everything reuses.
- **T. Tao, "Almost all orbits of the Collatz map attain almost bounded
  values" (2019/2022)** (arXiv:1909.03562) — the a.e. result and the Fourier
  decay of Syracuse random variables; the 3-adic major-arc regime our
  exponential-sum atlas lands in, and the wall (a.e. vs every-n) we respect.
- **I. Krasikov (1989), Applegate–Lagarias (1995)** — the predecessor-tree
  and transfer-operator antecedents of the counting side.

**Structure theorems we proved are extensions of:**
- **P. Diaconis & J. Fulman, "Carries, shuffling, and an amazing matrix" /
  the multiplication-carries chain (2008–2012)** — our carries-spectrum
  theorem answers a spectral question they left open.
- **L. Berg & G. Meinardus (1994/95)** and **B. Adamczewski & J. Bell,
  Mahler-function rigidity (Ann. Sc. Norm. Pisa 2017)** — the Mahler-equation
  reformulation and the (2,3)-rigidity behind our bi-Mahler exclusion.
- **A. Cobham / A. Semenov** — the two-bases automatic-set rigidity behind the
  "no certificate in two bases" note.
- **K. Monks (2006)** — sufficient sets / arithmetic-progression reduction,
  used in the exclusion and Mahler notes.

**The frame (why this is hard, and the BB connection Simon came for).**
- **J. H. Conway, "Unpredictable iterations" (1972)** and **S. Kurtz & J. Simon
  (2007)** — undecidability / Π⁰₂-completeness of generalized Collatz; the
  invariant-rank ledger is Conway's unsettleability made quantitative.
- **P. Michel** (Busy-Beaver ↔ Collatz-like maps) and **S. Aaronson, "The Busy
  Beaver Frontier" (2020)** and **the bbchallenge collaboration** (BB(5)=47,176,870,
  Coq-verified; Antihydra and the cryptids) — the BB/Collatz bridge; our
  reverse-mining and Antihydra-rarity work sits on theirs.
- **C. Deninger** (foliated dynamical systems / solenoid Lefschetz program) —
  the frame for the Traceless Theorem on the (2,3)-solenoid.

**What our approach most resembles, in one line:** the Krasikov–Lagarias LP
method reread through nonlinear Perron–Frobenius and ergodic optimization, with
information contraction, zero-temperature smoothing, and exact formal and
computational audits used to expose the remaining selected-policy seam.

Full per-claim citations with URLs are inline in the `docs/notes/*` files and
`docs/LANDSCAPE.md`; the mirrored-PDF index is `papers/REFERENCES.md`.
