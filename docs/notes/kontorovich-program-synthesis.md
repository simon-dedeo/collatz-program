# Kontorovich program synthesis: exact finite words and the integer gate

Status (2026-07-21): **exact compiler and bounded exact searches; cycle
soundness and the all-level periodic-itinerary obstruction kernel-checked; no
counterexample found**.  Lean commits `92b01ff`/`2f93df7` prove Section 4 and
its eventual-tail and sign corollaries.

## 1. The challenge in exact form

For a positive odd integer coprime to `3`, use the fully accelerated map

```text
T(x)=(3x+1)/2^v2(3x+1).
```

Write a desired finite program as positive integers
`w=(k_0,...,k_(N-1))`, set

```text
S_j=sum_(i<j) k_i,
A_N=sum_(j<N) 3^(N-1-j) 2^S_j.
```

Direct induction gives the affine identity

```text
2^S_N T^N(x)=3^N x+A_N.                              (1.1)
```

This identity and its transfer to the ordinary Collatz map are now
kernel-checked in the independent `KontoroC/` package.  In particular, its
Boolean `CycleArtifact.checkNontrivial` theorem turns a valid positive cycle
artifact with seed other than `1` into the literal negation of the repository's
standard Collatz conjecture.

## 2. Compiling every finite program

The last endpoint must be odd.  Thus the exact final valuation is equivalent
to

```text
3^N x+A_N = 2^S_N (mod 2^(S_N+1)).                   (2.1)
```

Because `3^N` is invertible modulo `2^(S_N+1)`, (2.1) fixes one class modulo
that power of two.  CRT with either admissible class `x=1` or `5 (mod 6)`
then fixes one class modulo

```text
3*2^(S_N+1)=6*2^S_N.                                 (2.2)
```

The earlier prefixes are automatically exact: reducing the final affine
congruence at their precisions recovers the same odd-endpoint condition.
`experiments/kontorovich/path_compiler.py` nevertheless replays every claimed
valuation rather than trusting this derivation.  Its exhaustive regression
compares compilation with literal membership over a complete progression
period for every word of length at most four with `1<=k_i<=4`, in both
classes modulo `6`.  It reproduces Kontorovich's example

```text
w=(1,1,2,2),  x=199 (mod 384),  T^4(199)=253.
```

This makes the finite/infinite gap executable.  Extending a word refines its
seed progression.  The canonical least positive representative either changes
by a multiple of the old modulus, or stays fixed because that ordinary seed
really follows the longer prefix.  An infinite prescribed word represents a
fixed ordinary positive seed only if these representatives eventually
stabilize.  Lean commit `ad36f08` proves the converse as well: in a fixed
admissible mod-6 class, eventual stabilization at `x` is equivalent to the
entire stream being legal for the ordinary positive integer `x`.  A generic
compatible non-stabilizing tower represents only a 2-adic integer.

## 3. Replayable cycle artifacts

If a legal word closes, (1.1) gives

```text
(2^S_N-3^N)x=A_N.                                    (3.1)
```

The Python `collatz-accelerated-cycle-v1` verifier recomputes `S_N`, `A_N`,
the orbit, the accelerated length, and the ordinary length `S_N+N`; checks
positive exact division in (3.1); replays each valuation; and checks closure.
Large JSON integers are decimal strings.  `KontoroC.CycleArtifact` mirrors
this payload, recomputes every redundant field, and proves

```text
checkNontrivial artifact = true -> not Collatz.Conjecture.
```

The Python and Lean interfaces deliberately keep the disproof gate separate
from validity: the repeated word `(2,...,2)` validly encodes seed `1`, but is
the trivial cycle.

## 4. Why a literal periodic glider fails

This is the first structural lesson from the hardware view.  Suppose the same
nonempty word `w` is legal for every consecutive block of a positive orbit.
Put

```text
P=3^N, Q=2^S_N, D=Q-P, A=A_N.
```

After `m` copies, concatenation gives

```text
Q^m T^(mN)(x)=P^m x+A_m,
A_m=A sum_(i=0)^(m-1) P^(m-1-i)Q^i,
D A_m=A(Q^m-P^m).                                    (4.1)
```

The left side says `Q^m` divides `P^m x+A_m`.  Multiplying by `D`, using the
second identity, and cancelling the term visibly divisible by `Q^m` shows

```text
Q^m divides P^m(Dx-A).
```

Since `P` and `Q` are coprime, `Q^m` divides the fixed integer `Dx-A` for
every `m`; hence `Dx=A`.  Therefore the block endpoint equals the start.  If
`D>0`, the itinerary is a cycle.  If `D<0`, its unique periodic 2-adic seed is
negative because `A>0`, so no positive seed has that infinite itinerary.

Thus an eventually periodic valuation stream cannot be a positive growing
glider.  A genuine divergent “program” must have unbounded symbolic memory:
a nonperiodic substitution, counter, stack, or arithmetic feedback that keeps
renewing exact divisibility.  `KontoroC/PeriodicItinerary.lean` proves the
coprime recurrence, the repeated-block fixed-point theorem, the arbitrary
eventually periodic tail corollary, and the strict sign obstruction.  The
axiom audit reports only the standard mathlib axioms documented by the
package.

## 5. First bounded searches

Run

```text
cd experiments/kontorovich
python3 path_compiler.py selftest
python3 search_programs.py --selftest
python3 search_programs.py \
  --max-total-halvings 22 \
  --max-uniform-width 4 \
  --max-k 4 \
  --max-word-length 16384 \
  --max-seed-word-length 512 \
  --output search_results.json
```

The committed result, source digest
`08c7a02de3bfadc918577c8dbc76c28d9d1474393c0556c1a5327b0d362eec03`,
contains two exact bounded exclusions.

1. Every ordered positive composition with total valuation `S<=22` and
   positive cycle denominator was tested: `3,447,691` words.  The only `11`
   closing words are the repetitions `(2)`, `(2,2)`, ..., `(2,...,2)` allowed
   by the bound, all at seed `1`.  No nontrivial positive cycle occurs.
2. Every binary uniform morphism of width `2`, `3`, or `4` prolongable on
   symbol `0` was tested (`168` morphisms), with every coding of the two
   symbols by valuations in `{1,2,3,4}`.  Across `20,224` depth instances and
   expanded word lengths through `16,384`, the `1,960` exact closure hits are
   all the trivial seed-`1` cycle; no nontrivial cycle occurs.  Canonical-seed
   stabilization was separately checked through word length `512`.  Of `932`
   stabilization events, only five avoid `1` throughout the stabilized
   prefix.  The longest has seed `107`, morphism
   `0->011, 1->010`, coding `0->1, 1->2`, and length `9`; its next morphic
   extension fails, and exact continuation reaches `1` after `36` accelerated
   steps with peak `3077`.

These bounds do not approach the general verification frontier and are not
presented as evidence that Collatz is true.  They are a kill test for the
smallest low-description glider ansatz and a regression target for stronger
SAT, one-counter, and recursive-template searches.

## 6. Next search moves

The immediate search should skip literal periodic words and fixed-width
uniform morphisms unless a new arithmetic constraint is added.

- Search **one-counter substitutions** whose emitted block depends on a
  growing counter and can replenish, not merely spend, the 2-adic precision
  budget.  The first distributed step is the exact non-uniform binary
  morphism worker `search_nonuniform.py`; unequal image lengths already create
  growing gaps, while remaining a finitely enumerable ansatz class.
- Search **macrostep identities on parametric binary templates** and require
  symbolic closure `T^ell(x_t)=x_(t+1)` plus a monotone height theorem.
  Lean commit `121cb13` has already kernel-checked the proposed packet clock,
  `ord_(2^(n+3))(3)=2^(n+1)` and its exact scheduling corollaries; the missing
  component is a carry collision that emits a renewed packet.
- Use the exact compiler inside **SMT/modular branch-and-bound**, scoring
  extensions by ordinary-seed stability and recurrent carry motifs rather
  than finite growth alone.
- Continue the **cycle lane** with meet-in-the-middle or lattice search on
  (3.1), but target compressed aperiodic words; a repeated block can only
  reproduce the same rational fixed point.

Any candidate from these lanes must pass the existing Python replay and the
kernel `CycleArtifact` checker when finite.  A divergent candidate needs a
separate inductive certificate; no finite prefix can supply one.

## 7. Supercritical negative-cycle shadows

A useful source of finite glider-like motion is a negative accelerated cycle.
Let its fixed phase be `c<0`, its legal word have affine multiplier `P/Q`, and
assume `P>Q`.  If

```text
x_M=c+Q^M h_M > 0,   h_M odd,
```

then the positive trajectory shadows the negative controller for `M` copies.
At the last valuation the parity necessarily changes.  If the valuation gains
`e_M` extra powers of two, direct affine algebra gives

```text
x_(M+1)=(c+P^M h_M)/2^e_M.                          (7.1)
```

The one-counter renewal condition is

```text
x_(M+1)=c+Q^(M+1) h_(M+1),   h_(M+1) odd and positive. (7.2)
```

If (7.1)--(7.2) hold indefinitely with bounded `e_M`, then after finitely many
levels every macrostep is strictly outward, since
`P^M>2^e_M Q^M`; the remaining finite prefix can be checked directly.  This
would provide exactly the variable-word state sequence required by Lean's
`MacroGlider` interface.  The ordinary-integer gate has merely moved: every
finite collision program can be compiled, while an infinite compatible tower
usually denotes only a 2-adic seed.

`search_shadow.py` implements (7.1) with literal valuation replay.  Its first
artifact checks the supercritical controllers `c=-5`, `w=(1,2)` and `c=-17`,
`w=(1,1,1,2,1,1,4)`, start levels through six, collision extras through eight,
and every extra word of length at most four in both mod-6 classes.  All
`112,320` compiled paths replay, but none stabilizes its ordinary seed or
renews the terminal precision.  This is a small ansatz failure, not an
obstruction theorem; phase-changing and substitution-driven collisions remain
open.

Allowing a collision to change phase within the same negative cycle does
produce finite renewals.  For the two-cycle `-5 -> -7 -> -5`, write phase zero
for `(-5;(1,2))` and phase one for `(-7;(2,1))`.  The exact program

```text
(phase,extra) = (1,2), (0,3), (1,1), (1,1)
counter level = 1,     2,     3,     4
```

has the ordinary positive seed and macro-states

```text
53403857 -> 15019835 -> 2376185 -> 1691641 -> 1354843.
```

The fourth macro is a genuine canonical-seed stabilization: the same seed was
already the least representative for the first three macros.  Nevertheless,
the last state is not congruent to either negative phase modulo `8^5`, so the
renewal stops immediately; all four macrosteps also shrink at these low
levels.

`search_phase_shadow.py` exhausts this grammar for both negative cycles.  The
`-5/-7` run checks `1,677,696` compiled paths (start levels through 12, extras
through eight, depth through four) and finds 15 terminal renewals, all at
start level one or two; none survives the next collision.  The seven-phase
`-17` run checks `273,168` paths (start levels through six, extras through
four, depth through three) and finds none.  Thus phase change is a real finite
carry mechanism, but the bounded grammar does not reach the outward regime.

The full implication is no longer informal.  Lean commits `3d9cedc` and
`93cafe1` prove (7.1), the eventual strict-growth inequality for uniformly
bounded extras, and that an infinite exact (possibly phase-changing) renewal
constructs a `MacroGlider` and refutes the literal ordinary Collatz
conjecture.  Commits `edcee1a` and `0d8c3d2` check the two signed controller
cycles and derive every rotated phase from the base certificate.  What remains
is exactly the infinite positive renewal witness; the bounded events here do
not provide it.

## 8. The `-1` controller and finite outward motion

The signed fixed point `c=-1` with word `(1)` gives `P/Q=3/2`.  Writing

```text
x_M=2^M h_M-1,  h_M odd,
```

the collision macro with extra valuation `e_M` is simply

```text
x_(M+1)=(3^M h_M-1)/2^e_M.                         (8.1)
```

Renewal requires `x_(M+1)+1` to be an odd multiple of `2^(M+1)`.  Unlike the
weaker `-5` controller, this grammar reaches the outward regime at small
levels.  Exact compilation gives

```text
M=7,8,9; e=4,3,1:
24017279 -> 25647359 -> 82164223 -> 1579334395.
```

All three macrosteps grow, and the same least ordinary seed realizes the
two- and three-macro prefixes.  The endpoint nevertheless fails the level-10
renewal congruence, and exact continuation reaches `1` after 108 accelerated
steps with peak `8,538,035,597`.

`search_mersenne_shadow.py` checks start levels through 100, extras through
12, and all programs of depth at most three in both mod-6 classes: `376,800`
compiled positive paths.  It finds 522 terminal renewals, 80 seed
stabilizations, and three all-outward stabilization events, but no second
stabilized extension.  This is a sharper motif, not a disproof.  The next
question is whether the collision extra can be generated by arithmetic
feedback on `h_M` so that (8.1) renews indefinitely.
