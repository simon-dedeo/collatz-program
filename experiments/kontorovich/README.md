# Kontorovich challenge: exact program synthesis

This directory turns the “Collatz hardware, seed as software” proposal into
exact search objects.  It uses the accelerated odd map

```text
T(x)=(3x+1)/2^v2(3x+1)
```

on positive integers coprime to `6`.  Nothing here treats a long finite path
as a counterexample.

## Exact compiler and certificate verifier

`path_compiler.py` compiles every finite positive valuation word into the
canonical least seed in either admissible class modulo `6`.  For a word
`k_0,...,k_(N-1)`, put `S_j=sum_(i<j) k_i` and

```text
A_N = sum_(j<N) 3^(N-1-j) 2^S_j.
```

The compiler checks by exact replay that

```text
2^S_N T^N(x) = 3^N x+A_N.
```

Exactness of the final valuation fixes `x` modulo `2^(S_N+1)`; CRT with one
class modulo `3` gives the Kontorovich--Sinai progression modulo
`3*2^(S_N+1)=6*2^S_N`.  The thread's example reproduces exactly:

```bash
python3 path_compiler.py selftest
python3 path_compiler.py compile 1,1,2,2 --class 1
```

The second command returns canonical seed `199`.  JSON integers that may
exceed the interoperable 53-bit range are strings.  A stored certificate is
independently replayed with

```bash
python3 path_compiler.py verify certificate.json
```

For a cycle word, closure requires

```text
x = A_N/(2^S_N-3^N).
```

`path_compiler.py cycle WORD` emits a certificate only when the denominator
is positive, division is exact, the seed is positive and coprime to `6`, every
claimed valuation replays exactly, and the endpoint equals the seed.  Seed
`1` is explicitly classified as the trivial accelerated cycle.  Any seed
greater than `1` would be a machine-checkable disproof candidate.

## Bounded adversarial searches

`search_programs.py` has two exact modes, run together:

1. exhaustive ordered compositions through a stated total-halving bound;
2. every binary uniform substitution prolongable on `0`, through a stated
   uniform width, every coding of its two symbols by bounded positive
   valuations, and every substitution depth below an expanded-length bound.

The second family is a deliberately low-description “glider” ansatz.  Besides
cycle closure, the search asks whether the least ordinary seed stabilizes as
nested morphic prefixes grow.  Stabilization is necessary for an infinite
prescribed 2-adic program to become one fixed ordinary positive seed.  Finite
stabilization remains only a prefix event.  Lean commit `ad36f08` proves the
infinite statement exactly: in a fixed admissible mod-6 class, a stream is
legal for an ordinary positive seed if and only if its canonical prefix seeds
eventually stabilize at that seed.

```bash
python3 search_programs.py --selftest
python3 search_programs.py \
  --max-total-halvings 22 \
  --max-uniform-width 4 \
  --max-k 4 \
  --max-word-length 16384 \
  --max-seed-word-length 512 \
  --output search_results.json
```

The result file records all bounds, exact counts, any cycle certificates, the
strongest seed-stabilization event, and a SHA-256 digest of the two source
files.  Cycle divisibility is tested through `--max-word-length`; the more
expensive CRT seed-stabilization test has its separately reported
`--max-seed-word-length` bound.  A negative result excludes only this finite
template class.  It does not improve the global computational verification
frontier.

## Distributed non-uniform morphic search

`search_nonuniform.py` expands the template class to every nonempty binary
morphism

```text
0 -> u,  1 -> v,
```

where `u` begins in `0` (so the fixed point is nested) and `u,v` have bounded,
not necessarily equal lengths.  Non-uniform images create growing gaps and
simple one-counter-like geometry unavailable to the uniform sweep.  The
worker carries compressed exact `(3^N,2^S,A_N)` blocks and is deterministically
sharded by morphism index.  Each shard still expands and literally replays
every closure or seed-stabilization hit.

`merge_nonuniform.py` requires every shard exactly once, checks common source
hashes and bounds, proves complete morphism-index coverage, and independently
replays any nontrivial cycle artifact.  A small two-shard regression is part
of `search_nonuniform.py --selftest`.

```bash
python3 search_nonuniform.py --selftest

# Example shard
python3 search_nonuniform.py \
  --max-image-length 6 --max-k 4 --max-depth 12 \
  --max-word-length 4096 --max-seed-word-length 512 \
  --shard-index 0 --shards 32 --output shard-000.json

# Merge only succeeds when all 32 consistent shards are present.
python3 merge_nonuniform.py --expect-shards 32 \
  --output nonuniform_results.json shard-*.json
```

`psc_nonuniform.sbatch` is the Bridges-2 64-way launch prescription.  Its
bounds are part of every shard artifact; changing the launch file creates a
different finite search and must not be silently merged with an earlier run.
The first length-eight job, `42499002`, timed out after two hours with only 7
of 64 shards complete.  `merge_nonuniform.py` therefore correctly has no
complete input set, and the run supports no exhaustive mathematical claim.
It is not being relaunched unchanged after the strategy pivot to symbolic
bouncers.  A separate 24-way Ganesha length-seven run remains in progress as
background bounded evidence.

## One-counter shadows of negative cycles

`search_shadow.py` turns a supercritical negative cycle into a finite carry
controller.  This does **not** use a negative integer as a counterexample.  For
the controller state `c<0`, valuation word `w`, and

```text
P=3^|w| > Q=2^sum(w),
```

a positive state `x=c+Q^M h` with odd `h` shadows `w` for `M` repetitions.
If the last valuation gains exactly `e` further powers of two, exact replay
gives the collision endpoint

```text
x'=(c+P^M h)/2^e.
```

The one-counter ansatz asks that `x'=c+Q^(M+1)h'`, replenishing the precision
spent by the collision.  With bounded `e`, sufficiently large successful
macrosteps grow because `(P/Q)^M/2^e>1`.  An infinite exact renewal would be a
candidate for the Lean `MacroGlider` endpoint; any finite chain is only a
prefix event.

```bash
python3 search_shadow.py --selftest
python3 search_shadow.py \
  --max-start-level 6 --max-extra 8 --max-program-depth 4 \
  --output shadow_results.json
```

The committed artifact exhausts the negative cycles at `-5` with word
`(1,2)` and `-17` with word `(1,1,1,2,1,1,4)`, every start level `1..6`, all
extra-valuation words over `{1,...,8}` of length at most four, and both
admissible classes modulo `6`.  All `112,320` compiled paths pass literal
valuation and shifted-coordinate replay.  There are zero ordinary-seed
stabilization events and zero terminal next-level renewals in this stated
class.  Source digest:
`dc33070c7d14db452aafe19c59ce097e301e895c593e2c0ec2d89424b2d72696`.

## Phase-changing shadow collisions

`search_phase_shadow.py` allows a carry collision to land near a different
phase of the same negative cycle.  At level `M`, a symbol `(i,e)` means: start
near negative phase `c_i`, run `M` copies of the valuation word rotated to
that phase, and add `e` powers of two at the terminal collision.  The next
symbol must start near its selected phase modulo `Q^(M+1)`.  The worker checks
the shifted-coordinate formula and literally replays every positive path.

Two committed runs use different bounds because the cycles have two and seven
phases:

```bash
python3 search_phase_shadow.py --selftest
python3 search_phase_shadow.py --cycle minus5 \
  --min-start-level 1 --max-start-level 12 \
  --max-extra 8 --max-program-depth 4 \
  --output phase_minus5_results.json
python3 search_phase_shadow.py --cycle minus17 \
  --min-start-level 1 --max-start-level 6 \
  --max-extra 4 --max-program-depth 3 \
  --output phase_minus17_results.json
```

The `-5/-7` artifact exhausts `838,848` phase/extra programs and `1,677,696`
compiled paths in the two mod-6 classes.  It finds 15 terminal next-level
renewals and 10 one-extension canonical-seed stabilizations.  All renewals
start at level one or two, every next macro shrinks, and every event loses
alignment immediately after that added macro.  A compact regression is

```text
phase/extra:  (-7,2), (-5,3), (-7,1), (-7,1)
levels:       1,      2,      3,      4
macro states: 53403857 -> 15019835 -> 2376185 -> 1691641 -> 1354843.
```

The same ordinary seed is canonical before and after the fourth macro, but
`1354843` is in neither negative phase class at precision level five.  This is
an exact finite carry-renewal example, not a divergent orbit.

The seven-phase `-17` artifact exhausts `136,584` programs and `273,168`
compiled paths; it finds no stabilization or renewal.  Together the artifacts
check `1,950,864` paths.  Their common source digest is
`b830ebcea08fb1822b204bfcd60a1570870ffa5a170b14f0d12fbb68bcc857cc`.

The soundness endpoint is kernel-checked.  Lean commits `3d9cedc`/`93cafe1`
prove the shifted-coordinate identity, eventual strict growth when collision
extras are uniformly bounded, and the literal negation of Collatz from an
infinite exact phase-renewal witness.  Commits `edcee1a`/`0d8c3d2` check the
signed `-5` and `-17` cycles and prove that every rotated phase supplies the
required affine controller.  The finite artifacts above do not instantiate
the infinite witness type.

## Mersenne shadows of the signed fixed point `-1`

`search_mersenne_shadow.py` treats `c=-1`, `w=(1)` as a one-counter
controller.  A positive state `x=2^M h-1` with odd `h` has `M-1` exact
valuation-one steps before its collision; if the last valuation is `1+e`, the
endpoint is exactly

```text
x'=(3^M h-1)/2^e.
```

The next level requires `x'=2^(M+1)h'-1`.  This is the simplest realization
of a high Mersenne-like packet feeding the low `+1` boundary, and its nominal
multiplier `3/2` is strongly outward when collision extras remain bounded.

```bash
python3 search_mersenne_shadow.py --selftest
python3 search_mersenne_shadow.py \
  --min-start-level 1 --max-start-level 100 \
  --max-extra 12 --max-program-depth 3 \
  --continuation-steps 100000 \
  --output mersenne_shadow_results.json
```

The artifact exhausts `188,400` extra programs and `376,800` compiled paths
in both admissible mod-6 classes.  It records 522 terminal next-level
renewals, 80 canonical-seed stabilizations, and three stabilizations for which
every macrostep is strictly outward.  The strongest is

```text
start level:  7
extras:       4, 3, 1
macro states: 24017279 -> 25647359 -> 82164223 -> 1579334395.
```

The seed is already canonical before the third macro, but the last state is
not `-1` modulo `2^10`.  Exact continuation reaches `1` after 108 accelerated
steps, with peak `8,538,035,597`.  The highest terminal renewal in the search
starts at level 10 and its added level-13 macro grows, but alignment then
fails.  Thus this artifact verifies finite outward packet behavior while
closing only its stated depth-three grammar.  Source digest:
`9e0be5ec96ed81eebe55c7b7f2281309eef13f7ca0da10638604afd2c1d4ac8f`.

Lean commit `768f4d0` independently checks the signed `(-1,[1])` controller,
proves the exact Mersenne macro identity used here, replays the
`24,017,279` outward event and its level-10 failure, and exposes the literal
Collatz-refutation theorem from an infinite `MersenneShadowOrbit`.  The finite
artifact does not inhabit that all-level structure.

`search_mersenne_constants.py` separately exhausts the simplest feedback
grammar, one constant collision extra:

```bash
python3 search_mersenne_constants.py --selftest
python3 search_mersenne_constants.py \
  --max-start-level 20 --max-extra 32 --max-depth 40 \
  --continuation-steps 100000 \
  --output mersenne_constant_results.json
```

Across `51,200` compiled paths, the unique two-extension stabilization is

```text
constant extra: 1
start level:    1
macro states:   121 -> 91 -> 103 -> 175 -> 445.
```

Seed `121` is the canonical representative for depths two, three, and four.
The fifth macro fails, and exact continuation reaches `1` after 34 accelerated
steps with peak `3077`.  No other constant extra through 32 produces two
extensions within the stated bounds.  Source digest:
`dd0ca553197fa5881a2db36ed2dde00984d7750efc1412bff4648b0b9238ed04`.

`search_mersenne_periodic.py` expands the feedback class to every primitive
periodic extra template within explicit bounds.  The macro valuation word is
still aperiodic because its length increases; only the extra controller is
periodic.  The worker uses the Lean-checked compressed affine macro and
expands plus literally replays every stabilization hit.

```bash
python3 search_mersenne_periodic.py --selftest
python3 search_mersenne_periodic.py \
  --max-start-level 30 --max-extra 8 --max-period 3 --max-depth 80 \
  --continuation-steps 100000 \
  --output mersenne_periodic_results.json
```

The artifact exhausts 568 primitive templates and `2,726,400` compiled
prefixes.  It finds 119 seed-stabilization events, three all-outward events,
and one two-extension event.  The latter is exactly constant extra `1` at
seed `121`; the strongest outward event is exactly period `(4,3,1)` at seed
`24,017,279`.  Both fail as documented above and reach `1`.  Thus no short
periodic template improves the known finite motifs.  Source digest:
`27447b305fc295f6225aa045eaa7110d5ccc44ae66055356de9afa7d5842ba49`.

Lean commits `32a0896`--`a2652f2` now expose the narrow all-level target

```text
2^e_t (2^(M+t+1) h_(t+1)-1) = 3^(M+t) h_t-1.
```

From positive odd packets and uniformly bounded extras satisfying this
recurrence, Lean derives the macro legality, eventual packet growth, and the
literal Collatz refutation.  It also proves the unique necessary residue class
for `h_(t+1)` modulo `3^(M+t)`.  That scheduler is the next search filter.

## Symbolic dyadic--triadic packet gates

`packet_gate.py` decodes one recurrence step as a whole-payload instruction
rather than enumerating packets.  For fixed positive level `m` and collision
extra `e`, it computes exact odd constants `r,s` such that all renewals in
that branch, and only those renewals, have

```text
h  = r + 2^(m+e+2) q
h' = s + 2*3^m q,              q>=0.
```

The low `m+e+2` bits of `h` are therefore an instruction address, while the
arbitrarily large high quotient `q` is its payload.  The same gate computes
the required residue of `h'` modulo `3^m`, making the instruction a bridge
between dyadic and triadic phases.  This implements the deliberately nonlocal
ISA described in the [research
note](../../docs/notes/kontorovich-delocalized-isa.md).

```bash
python3 packet_gate.py selftest
python3 packet_gate.py describe 7 4
python3 packet_gate.py audit --max-level 8 --max-extra 8 \
  --payloads 128 --converse-limit 65536
```

The self-test checks 8,192 gate/payload pairs and then exhaustively recovers
all 16,316 literal renewal events for odd packets below `2^16` at levels
`1..8`.  These finite loops are implementation tests of the displayed exact
algebra, not a search frontier.  The next task is to close a family of these
affine gates on a symbolic payload relation; no such all-level controller is
known.

## Formula-generated Colussi delay line

`colussi_delay.py` reconstructs Colussi's order-10 repetend value from the
short formula

```text
a_10 = (4^19683-1)/3^10.
```

The integer has 39,351 significant binary bits and 11,846 decimal digits, but
no huge decimal literal is stored.  Its exact ten-instruction header is

```text
(1,1,2,1,1,1,5,1,4,1).
```

The compiler recomputes that this word has total halving count `18` and
affine offset `262145=2^18+1`; literal replay therefore lands at

```text
1+2^39348.
```

This is a direct spatial realization of Kontorovich's delay-line picture.  For
exactly 19,673 further accelerated steps,

```text
x_t = 1+3^t*2^(39348-2t),
v2(3*x_t+1) = 2.
```

The high packet advances two bit positions per tick and its payload is
multiplied by three.  The terminal state is `1+4*3^19673`; its next valuation
is exactly three and the collision endpoint is `(1+3^19674)/2`.

```bash
python3 colussi_delay.py selftest
python3 colussi_delay.py build colussi_delay_h10.json
python3 colussi_delay.py verify colussi_delay_h10.json
```

The verifier reconstructs all formula values and literally checks all 19,684
header/delay/collision macrosteps as a regression for the symbolic formulas.
It also continues the original generated seed exactly to `1`: 95,146
accelerated steps, 190,153 total halvings, hence 285,299 ordinary steps.  The
peak occurs at accelerated step six and has 39,353 significant bits.

The natural collision does not replenish the wire.  Among its first 1,024
post-collision states, the largest `v2(x-1)` is only 10 (at step 907), versus
the incoming gap exponent 39,348.  This is a bounded diagnostic, but full
continuation supplies the stronger verdict for this seed: it converges.  The
active target is a distributed defect in the compact header/background which
changes the collision into a larger delay state, not a longer run of this
unmodified program.

```text
artifact SHA-256  384ba545e86b203ed1aee78ad8832326330b868e26dbdd775205c85f47f64ce5
verifier SHA-256  9d7a0bd2a807e8c022e0aafea79d33b1054e2c39be8ff5f4e6b95e78a488d7be
```

## Carry-splash gates and the pure-rail no-go

`splash_gate.py` implements Simon's suggestion that sacrificial packets can
use collision carries to erase a dirty suffix and emit a new empty gap.  For
positive `r,r',a`, it solves

```text
3^(r+1) Q + 1 = 2^a (1+2^(2r'+2) Q')
```

in positive odd payloads.  The input `1+2^(2r+2)Q` traverses `r` exact
valuation-two delay ticks, collides with valuation `2+a`, and becomes the new
wire `1+2^(2r'+2)Q'`.  Invertibility of powers of two modulo `3^(r+1)` gives
one odd base solution and the complete affine family

```text
Q' = Q'_0 + 2*3^(r+1) z,
Q  = Q_0  + 2^(a+2r'+3) z,       z>=0.
```

```bash
python3 splash_gate.py selftest
python3 splash_gate.py describe 1 2 1
python3 splash_gate.py describe 19673 19674 1
```

The small example has `Q=185,Q'=13` and literal orbit

```text
2961 --k=2--> 2221 --k=3--> 833,
```

so its gap grows from four to six bits.  The order-10-scale command constructs
an exact 78,700-bit input whose splash grows a 39,348-bit gap to 39,350 bits;
the CLI suppresses giant decimal literals and reports formula metadata.

The self-test literally replays all 15,360 members with
`1<=r<=8`, `1<=r'<=10`, `1<=a<=6`, and `0<=z<32`.  More importantly, the
symbolic formula exposes a no-go: every pure `+1` splash strictly decreases
the integer.  Its leading multiplier is
`(3/4)^(r+1)/2^a<1`, and direct comparison in the exact balance gives the same
verdict including the affine term.  The splash is a cleanup/timing primitive;
an outward program needs a `-1`/valuation-one amplification rail and exact
phase switches between the two.

## Two-rail outward gates and a 10k-digit finite program

`two_rail_gate.py` supplies the amplifying phase missing from the pure
`+1` splash.  It alternates the exact rails

```text
-1+2^J P -> -1+3^t 2^(J-t)P       (valuation one),
 1+2^K Q ->  1+3^t 2^(K-2t)Q      (valuation two),
```

and solves both collision equations by modular inversion.  For any fixed
amplifier length `r`, cleanup length `s`, collision extras `a,b`, and output
gap `L`, it returns the complete affine family of positive odd payloads
satisfying

```text
3^(r+1)P-1 = 2^a(1+2^(2s+2)Q),
1+3^(s+1)Q = 2^b(-1+2^L P').
```

The standard gate uses `s=1`, `a=b=1`, and `L=r+2`.  Its first regression is

```text
94751 -> 142127 -> 213191 -> 319787 -> 479681
      -> 359761 -> 269821 -> 101183,
valuations [1,1,1,1,2,2,3].
```

It grows the `-1` gap from five to six bits and the whole state strictly
increases.  Consecutive complete payload families are intersected
symbolically; no seed interval is searched.

```bash
python3 two_rail_gate.py selftest
python3 two_rail_gate.py describe 4
python3 two_rail_gate.py build two_rail_chain_247.json
python3 two_rail_gate.py verify two_rail_chain_247.json
```

The generated depth-247 certificate contains no giant decimal literal.  Its
least seed has 33,351 significant bits (10,040 decimal digits) and executes
247 strict outward rounds, or 32,110 accelerated steps, while its clean gap
grows from 5 to 252 bits.  The designed endpoint has 51,146 significant bits
(15,397 decimal digits).  Every gate and step is reconstructed and replayed
with exact integers.

This finite program is not a counterexample.  The least seed for 248 rounds
is different, and exact continuation of the depth-247 seed reaches `1` after
155,190 accelerated steps (434,511 ordinary steps); its peak has 51,293
significant bits.  The artifact therefore certifies both the promised large
two-rail behavior and the ordinary-integer stabilization failure of this
particular schedule.

```text
artifact SHA-256  42599de911e74bbb5a5af4ec7da630878d59fe41d2d6d0000fffc83b84a94380
verifier SHA-256  e1006e7bfc4df2ae3fa21467265130c1d2526808f37cf4a2767b8d23b81500bd
```

## Direct GPU packet census

`mersenne_packet_gpu.cu` enumerates the state-dependent recurrence directly,
rather than choosing an extra template.  The current launch checks every odd
packet `h<2^36` at start level one, follows up to eight exact renewal steps,
and stores every chain of length at least six.  All arithmetic is unsigned
64-bit integer arithmetic; a nonzero overflow counter makes the run fail.

`verify_mersenne_packet_gpu.py` recomputes every stored hit with Python
arbitrary-precision integers, including its collision extras.  Exhaustiveness
comes from the CUDA launch's complete index range and successful kernel status;
the Python pass independently checks candidate soundness.

```bash
nvcc -O3 -std=c++17 mersenne_packet_gpu.cu -o mersenne_packet_gpu
./mersenne_packet_gpu \
  --h-bits 36 --max-steps 8 --threshold 6 \
  --output mersenne_packet_gpu_results.json
python3 verify_mersenne_packet_gpu.py mersenne_packet_gpu_results.json
```

`psc_mersenne_packet.sbatch` is the H100 launch prescription.  The first full
run completed on Akdeniz's RTX 4090 and checked exactly
`34,359,738,368=2^35` odd packets.  Its overflow counter is zero.  Of 243
chains with at least six renewals, exactly three have seven and none has eight;
the Python verifier replays all 243.  One length-seven example is

```text
initial h: 15301803983
seed:      30603607965
extras:    2,1,3,2,2,2,1
states:    30603607965 -> 11476352987 -> 12910897111 -> 5446784719
           -> 6893586911 -> 13087043903 -> 37267402367
           -> 318374253823.
```

The final four macrosteps grow.  The eighth renewal fails, and exact
continuation of the seed reaches `1` after 152 accelerated steps with peak
`5,439,722,602,445`.  Thus the artifact is a complete bounded census and a
source of state-dependent motifs, not a counterexample.

Provenance hashes:

```text
artifact  2769cce1866927c863b02626e561a6876b6289a6171ce7096e0045ea37e189bf
CUDA      f5e9bb3054dbf0b29247154a5ac3f90c614880e41ff58a71e3643d49e6c668a5
verifier  de52aab1c97921484d8e547d1cb4609c29a2ef735a8f60fa2dbe66b9a2eaf919
```

PSC H100 job `42500602` completed the same `h<2^36` census independently on
an NVIDIA H100 80GB HBM3.  It has the same zero-overflow counter, maximum
renewal length seven, and 243 stored hits.  After sorting by initial packet,
renewal length, and collision extras, every hit agrees exactly with the RTX
4090 artifact; the Python arbitrary-precision verifier also passes directly
on the H100 output.  The files deliberately remain separate so the device
provenance is visible:

```text
H100 artifact  26d093ba1e79ddde4e9a452e557d8367530ea9916d396579b99571349abd7222
RTX artifact   2769cce1866927c863b02626e561a6876b6289a6171ce7096e0045ea37e189bf
```

This is independent-hardware corroboration of candidate generation, not a
larger search bound and not an independent implementation of the CUDA kernel.

A nested wider run raises the packet bound to `h<2^39`, sets the recording
threshold to seven, and checks all `274,877,906,944=2^38` odd packets.  Its
overflow counter is zero; all 14 length-seven hits pass Python replay, and no
packet completes the eighth renewal.  Artifact SHA-256:
`676eb8a8c8f5c8c1987a505fe71c08bffe30f613c5348f1fb5852199972b8fe5`.
The narrower artifact remains useful because it records length-six chains
that the wider run intentionally omits.

The current outer run raises the bound to `h<2^42`, records only completed
eight-renewal chains, and exhausts `2,199,023,255,552=2^41` odd packets.  It
has zero overflows, maximum renewal length seven, and zero stored hits.  The
Python verifier passes.  Artifact SHA-256:
`c724370e0db7550965cbec141b8a7efbe171df26e52408012c01f5620b73a8b2`.
This is the bounded start-level-one packet frontier; it does not constrain
larger packets, other start levels, or other controller families.
