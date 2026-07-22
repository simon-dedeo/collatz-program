# KontoroC

Lean 4 formalization support for the Kontorovich disproof challenge.

This is intentionally separate from `CLEAN_LEAN`: it imports the faithful
standard Collatz definition from that package, but develops the fully
accelerated odd map and replayable counterexample-certificate interfaces here.

Current checked target:

- exact maximal-power-of-two odd step;
- legal finite valuation words;
- the affine identity
  `2^(sum k) * T^N(x) = 3^N*x + A_N`;
- a replayable Boolean cycle checker whose soundness theorem concludes the
  literal negation of `CleanLean.Collatz.Conjecture`.

For a nonempty legal word, Lean also proves closure equivalent to the exact
search equation `(2^S-3^N)*seed=A_N`, proves the denominator strictly positive,
and identifies the seed with `A_N/(2^S-3^N)`.  Divisibility does not replace
the separate exact-valuation replay premise.

The richer `CycleArtifact` mirrors the worker's
`collatz-accelerated-cycle-v1` mathematical payload (`word`, `seed`, `orbit`,
affine constant, both step counts).  Lean recomputes every redundant field.
`checkNontrivial = true` is an end-to-end kernel theorem yielding
`¬ CleanLean.Collatz.Conjecture`.

`MacroGlider` is the corresponding infinite symbolic endpoint.  It accepts
variable nonempty valuation blocks connecting a strictly increasing sequence
of states above `4`, expands them to ordinary Collatz time, and proves the
literal negation of the conjecture.  Constructing such a glider remains the
open mathematical/search problem.
`EventualMacroGlider` permits a finite irregular prefix and proves that any
later exact, large, strictly outward tail is sufficient for the same literal
disproof endpoint.

Literal periodic software is ruled out: `repeated_legal_block_fixed` proves
that if one nonempty valuation block remains exactly legal under every
successive repetition, its first endpoint already equals its start.  The proof
uses denominator growth in a coprime integer recurrence, not a numerical
search.  Thus an outward glider must use genuinely unbounded symbolic memory.
The package also exposes the arbitrary-state periodic-tail form and proves
that an infinitely repeatable positive block necessarily has
`3^length < 2^totalValuation`; the opposite sign is impossible.

The finite compiler lane now has an exact intermediate target:
`AffineOddFactor x w` says that the final affine numerator is `2^sum(w)`
times an odd endpoint.  For a positive valuation word, Lean proves this
equivalent to literal legality of every instruction plus an odd replay
endpoint.  This prevents a final-congruence compiler from silently accepting
a word with an incorrect intermediate valuation.
It also proves this factorization equivalent to the worker's exact congruence
`3^N*x+A_N = 2^S (mod 2^(S+1))`; hence that single congruence is now proved
necessary and sufficient for full finite-word legality.
Using invertibility in `ZMod` and mathlib's Chinese remainder theorem, Lean
then proves that every positive finite word has a legal positive seed in each
class `1` and `5 mod 6`.  The power-of-two solution is unique modulo
`2^(S+1)`; combining it with the class modulo three gives the worker's
progression modulus `3*2^(S+1)=6*2^S`.

`PathArtifact` mirrors every mathematical field of the worker's
`collatz-k-path-v1` payload.  Its executable checker recomputes the affine
constant, lengths, endpoint, seed modulus, and endpoint stride.  Checked
theorems prove that its seed is the unique canonical representative and that
all lifts have endpoint stride `6*3^N`.

For the separated-bit search lane, `PacketTiming.lean` proves the exact clock

```text
orderOf (3 mod 2^(n+3)) = 2^(n+1),
```

and packages both period-shift and exact exponent-congruence interfaces.  Thus
packet scheduling may use this fact without leaving it as a prose premise.

`IntegerGate.lean` proves that canonical compiled seeds for longer and longer
prefixes stabilize if and only if the stream is realized by one ordinary
natural seed.  In particular, eventual stabilization is now a proved
necessary condition for the morphic searches, not merely a heuristic score;
a compatible non-stabilizing tower supplies only a 2-adic program.

`NegativeShadow.lean` gives the negative-cycle controller search a signed but
sound interface.  It proves the exact shifted-coordinate endpoint from a
positive natural `WordLegal` macro, and proves that a supercritical controller
with bounded collision valuation is eventually strictly outward.  A negative
state is only an affine controller here; an infinite renewal witness is still
required before the existing `MacroGlider` theorem applies.
The `PhaseShadowRenewal` variant permits a different signed controller phase
and rotated word at each level, matching the phase-changing exact worker.
`BoundedPhaseShadowOrbit` removes the remaining asymptotic boilerplate: a
common supercritical multiplier and a uniform bound on collision extras imply
eventual strict growth, automatically produce a large outward tail, and reach
the literal disproof endpoint.
`SignedController.lean` independently checks that the worker's `-1`, `-5`,
and `-17` controllers are literal signed accelerated cycles and derives the affine fixed
equation consumed by the shadow endpoint.  These negative cycles remain
controllers only, never positive counterexamples.
Every cyclic rotation is also proved legal and closing at its corresponding
phase state, so the phase-changing worker needs only one checked base cycle.
Negativity and nonempty exact closure also imply the controller is
supercritical (`2^S < 3^N`); this no longer needs a separate search premise.
`CertifiedCyclePhaseShadowOrbit` is the highest-level phase-worker endpoint:
from one checked controller and per-level cyclic splits it derives every
rotated fixed equation, common multiplier, and bounded-renewal premise before
reaching the literal disproof theorem.
For the special `-1` controller, `MersenneShadowOrbit` is a smaller exact
endpoint matching `search_mersenne_shadow.py`: the controller, word `[1]`,
multiplier `3/2`, and affine fixed equation are no longer artifact fields.
Only the infinite positive coordinate/legality/renewal data and a uniform
collision bound remain for the worker to supply.
The compressed block used by the Python search is also proved rather than
trusted: a level-`m`, extra-`e` macro has affine data
`(steps, halvings, constant) = (m, m+e, 3^m-2^m)`.
The worker's current three-macro outward chain from `24017279` is replayed in
`Examples.lean`; Lean also verifies that its endpoint misses the required
level-ten `-1` residue class, so it is explicitly not an infinite artifact.
`MersennePacketRenewal` reduces the infinite interface further: a pure
Diophantine recurrence between positive odd packets automatically generates
the natural states, every exact valuation word, and every macro endpoint.
Its constant-extra corollary directly matches `search_mersenne_constants.py`.
The recurrence also forces an explicit next-packet congruence modulo `3^m`,
available as `next_packet_mod_threePow` for modular search pruning.
With uniformly bounded extras, the packet sequence itself is proved to become
strictly increasing after a finite level.
Fixing the complete extra stream is even more rigid: there is at most one
ordinary initial state, and hence at most one entire positive packet sequence,
that can realize it.  This is the unbounded-power-of-two integer gate for the
state-dependent grammar.
The shifted recurrence around `-1` is now also exposed as an exact finite
backward series over `ℚ`: after any number of blocks, the initial state plus
one equals the product of the backward coefficients times the terminal state
plus one, minus the accumulated weighted defects.  This is a size-independent
reduction, not a bounded search.
`PadicMersenne.lean` completes the convergence step in mathlib.  For every
positive starting level and arbitrary symbolic extra stream, the weighted
defect terms are summable in `ℚ₂`; their canonical sum is
`prescribedPadicCandidate`.  Any ordinary packet renewal forces this candidate
to equal `-(x₀+1)`.  Therefore proving that the candidate misses all negative
ordinary integers rules out the entire infinite schedule, independently of
whether a hypothetical seed has ten digits or ten thousand.  Establishing
that arithmetic avoidance for useful schedule classes remains open.

`PacketGate.lean` supplies the complementary large-integer interface.  A gate
stores one low binary residue `r`, its next-packet offset `s`, and one checked
base collision.  Lean proves the universal equivalence

```text
PacketCollision m e h h'
  ↔ ∃ q, h = r + 2^(m+e+2) q ∧ h' = s + 2*3^m q
```

for positive `h,h'` with odd `h'`, and proves the payload is unique.  It also
derives the exact two-adic valuation and triadic next-packet scheduler.  Thus a
10,000-digit packet is handled as an arbitrary payload in one theorem, not by
replaying or trusting a bounded sweep.

`DelayLine.lean` proves the spatial wire family itself.  For odd positive `p`
and `2*n+2 ≤ J`, the compressed word of `n` valuation-two instructions sends

```text
1 + p*2^J  ↦  1 + 3^n*p*2^(J-2*n).
```

The order-ten Colussi seed `(4^19683-1)/3^10` is then checked end to end.  Lean
kernel reduction proves its 19-bit header address and one large affine
balance; the final-congruence theorem supplies all ten exact header
valuations; the parametric wire theorem supplies all 19,673 delay ticks and
the endpoint `1+4*3^19673`.  No decimal expansion, flat trajectory, or
`native_decide` proof is used.  The subsequent collision and eventual descent
of this particular seed are not soundness claims in this module.

`SplashGate.lean` closes the first apparent collision architecture.  A datum
may contain arbitrary positive odd input and output payloads and any positive
input/output wire lengths, but if it stays entirely on states of the form
`1+p*2^J`, Lean derives the full exact word and proves

```text
endpoint < 3^(r+1)*p+1 < 4^(r+1)*p+1 = start.
```

Thus every pure `+1` delay/splash macro is strictly dissipative, regardless
of how many digits the payload has.  Outward constructions must change rail,
offset, sign, or packet geometry; a larger finite search cannot evade this
obstruction.

`TwoRailGate.lean` certifies the corresponding escape architecture.  From two
affine balances and arbitrary odd positive payloads, Lean derives every exact
valuation and the endpoint of

```text
(-1 rail) [1]^r ++ [1+a]  →  (+1 rail) [2]^s ++ [2+b]  →  (-1 rail).
```

The first standard gate `94751 ↦ 101183` is a small kernel-checked regression.
More importantly, `InfiniteTwoRailProgram` states the missing all-level
obligation precisely: linked gates and strict outward growth produce the
existing `MacroGlider` and hence the literal negation of Collatz.  A finite
247-round chain, even with a 10,000-digit seed, does not inhabit that type.
The payload size is computationally harmless; proving infinite linkage from
one ordinary seed is the substantive problem.

`TwoRailChain.lean` provides the finite artifact format.  It composes a list
of gates using only sparse endpoint linkage, proves the exact iterate of the
ordinary Collatz map for the flattened program, and proves strict net growth
when every gate is outward.  If such a nonempty chain instead closes at a
seed other than `1`, the existing cycle theorem immediately yields
`¬ Collatz.Conjecture`.  This is the appropriate verifier for a large finite
cycle: its work scales with the compact gate list and affine balances, not
with the seed's decimal length or a flat elementary orbit.

`StandardTwoRail.lean` eliminates the intermediate cleanup payload from the
standard shape (`s=a=b=1`, output gap `r+2`).  Every such gate obeys the
single recurrence

```text
2^(r+8) P' = 3^(r+3) P + 69,
```

and its outgoing payload has exactly one factor of three.  Lean also proves
`2^(r+7) < 3^(r+3)` for every `r≥4`, so standard gates are automatically
outward.  `LinkedStandardTwoRailProgram` consequently requires only standard
gate data, rail lengths at least four, and exact linkage; those fields already
imply a macro-glider and `¬ Collatz.Conjecture`.  The search problem is now a
precise integrality/stabilization problem for one nonautonomous recurrence,
not a numerical growth question.

`AffineTwoRail.lean` verifies whole gate families and their index transducers
coefficientwise.  One exact base gate and two stride balances generate an
exact `TwoRailGate` for every natural family index.  A handoff then needs only
one base-payload equality, one stride equality, and matching sparse gaps to
prove endpoint/start linkage for every unbounded tail.  The first standard
handoff is checked universally:

```text
source index = 6245 + 8192*u,
target index = 1667 + 2187*u.
```

Thus the 13-bit address deletion and `3^7` tail update are theorems, not
conclusions from sampled members.  An infinite counterexample still requires
these affine instructions to close into one all-level ordinary program.
Consecutive instructions can also be certified coefficientwise:
`AffineTwoRailHandoff` proves that two affine tail progressions select the
same middle gate, then derives the exact two-gate iterate of the ordinary map.
For the first two standard edges, the universal compatibility is

```text
first residual tail  = 5994 + 16384*t,
second residual tail =  800 +  2187*t.
```

This is the first compositional transducer path theorem; extending such paths
still refines the admissible initial tail and does not by itself establish an
ordinary infinite seed.

Nothing here currently supplies a counterexample.  A finite prefix is not an
ordinary positive infinite orbit certificate.

Build locally with:

```text
lake update
lake build
```

The small numerical regressions in `KontoroC/Examples.lean` use
`native_decide` and therefore trust the Lean compiler.  They are not imported
by any certificate-soundness proof.  `KontoroC/Audit.lean` prints the axioms of
the headline mathematical theorems separately.
