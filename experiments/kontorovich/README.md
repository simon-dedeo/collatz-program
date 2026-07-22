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

## Payload-index tag transducers

`two_rail_transducer.py` exposes the programming-language operation hidden in
the complete affine gate families.  Write a source gate's output payload and a
target gate's input payload as

```text
P_out(z) = c + 2*3^R z,
P_in(w)  = a + 2^D w.
```

Exact linkage is the single address equation

```text
3^R z + (c-a)/2 = 2^(D-1) w.
```

It selects one residue `z=rho mod 2^(D-1)`.  Writing
`z=rho+2^(D-1)u` leaves

```text
w = w0 + 3^R u.
```

Thus a splash gate is an exact variable-length tag instruction on a nonlocal
payload tape: it reads and deletes a low binary address block, multiplies the
remaining tail by a power of three, and appends a fixed offset.  The first
standard handoff deletes 13 address bits and maps

```text
source index = 6245 + 8192*u,
target index = 1667 + 2187*u.
```

Lean commits `4789a80`, `1076954`, and `2f2e24e` lift this from sampled
arithmetic to universal gate-family, two-instruction composition, and affine
loop theorems.  In particular, an exact self-link (or finite return circuit)
whose natural residual tail evolves by `u -> c+m*u` is enough for a literal
Collatz disproof when its gates are outward.  The tail may grow; it need not
be a fixed point.  This is the precise regenerative version of Simon's
“splash the gap” idea.

```bash
python3 two_rail_transducer.py selftest
python3 two_rail_transducer.py describe-standard --amp-ticks 4
python3 two_rail_transducer.py build-audit two_rail_transducer_audit.json
python3 two_rail_transducer.py verify two_rail_transducer_audit.json
```

The bounded audit covers 128,000 gate shapes with amplifier length at most
40, cleanup length at most four, collision extras at most four, and output gap
at most 41.  It finds 98,760 outward canonical gates and 25 links between
their zero-index members; the longest such canonical chain has two gates:

```text
45247 -> 48319 -> 103199,
valuations [1,1,1,1,1,2,4, 1,1,1,1,1,2,3].
```

Exact continuation reaches `1` after 86 accelerated steps.  A separately
stated next-gate audit finds no zero-index continuation of its endpoint with
cleanup/extras at most 20 and output gap at most 300.  This closes only the
canonical zero-preload slice; it says nothing against the unbounded affine
tail links certified in Lean.  The live search target is an affine return map,
not another longer canonical chain.

```text
artifact SHA-256  d961269507a35fbbcc154e8131c2d1062539d12d70566d4caad02e121851a9ba
verifier SHA-256  c8781d45b2ac7dbe371b6ba71c881f16439806561ffe6a757a0a970d6e046c18
```

## The LSB-first splash instruction code

`two_rail_prefix_code.py` turns payload-dependent branching into a literal
instruction decoder.  For fixed amplifier length `r`, a gate with cleanup
length `s`, positive collision extras `a,b`, and output gap `L>=2` accepts one
odd input-payload residue modulo

```text
2^E,  E=a+b+2s+L+3.
```

These residues are least-significant-bit-first binary codewords.  The code is
prefix-free: from a literal accepted payload one recovers `a`, then `s`, then
`b`, then `L` as four successive exact 2-adic valuations.  Thus no payload can
select two different next gate shapes.  After the `E-1` nontrivial address
bits are removed, the affine handoff multiplies the residual tape by a power
of three.  The two-rail language is therefore a deterministic mixed-base tag
machine: binary prefix read, global ternary write.

The exact Kraft mass among odd 2-adic payloads is

```text
sum_(a,b>=1,s>=0,L>=2) 2^(-(E-1)) = 1/6.
```

This does not say an exceptional ordinary tape cannot survive forever.  It
quantifies why such a tape is sparse and why a total finite-state controller
is the wrong target.

```bash
python3 two_rail_prefix_code.py selftest
python3 two_rail_prefix_code.py build two_rail_prefix_code_audit.json
python3 two_rail_prefix_code.py verify two_rail_prefix_code_audit.json
```

The artifact checks all 1,344 codewords of length at most 20 for each
`r=1,...,16`: 902,496 pairwise prefix comparisons per `r`, 21,504 independent
literal base-payload decodes, and bounded covered mass
`5433/32768 < 1/6`.  Those are bounded regressions.  Prefix uniqueness and the
`1/6` limit follow from the displayed valuation decoder and exact geometric
series, respectively; the requested Lean seam is recorded separately.

```text
artifact SHA-256  cc4c30ad51a942e584c89c518a4adb5b1f231d049843216ad3c16be431d8d6ae
verifier SHA-256  e534fb609813af1f826e9d654507f1a0ca917952e37e07afe52eafd35c095c84
```

## A parity-complete splash instruction set

The `1/6` grammar above deliberately retained only an even intermediate
`+1`-rail gap and an outgoing gap of at least two bits.  Simon's proposal to
line up additional bits to “eat” the bad collision has an exact missing
branch.  When the intermediate gap is odd, after `s` valuation-two ticks the
state is `1+2*3^s Q`; its next valuation is exactly one, and

```text
1+2*3^s Q -> 2+3^(s+1)Q = -1+2^L P'.              (odd catcher)
```

Thus the low bits of `Q` can absorb the dirty `+3` and regenerate a `-1`
rail.  Allowing `L=1` gives a legitimate zero-delay rail whose collision is
immediate.  With positive collision extras, the two complete affine families
have input code lengths

```text
even cleanup: E=a+b+2s+L+3,
odd catcher:  E=a+2s+L+2,
```

and exact Kraft masses among odd 2-adic payloads

```text
sum 2^(-(E_even-1)) = 1/3,
sum 2^(-(E_odd-1))  = 2/3.
```

The total mass is one.  More strongly, literal valuation decoding proves
that every positive odd payload selects exactly one of these gates unless
the current macro reaches `1`.  This removes “failure to decode” as a
hardware obstruction; the disproof problem becomes finding an ordinary
payload orbit whose decoded gates avoid the explicit halt and supply enough
long-run outward growth.  Lean commits `afb86a5`/`f7ac880` independently
certify the odd catcher's exact word, affine cylinders, and cross-branch
disjointness, including `r=0,L=1`.  Commit `78d1048` further constructs a
certified halt, generalized even cleanup, or odd catcher for every positive
odd payload; `92f237c` proves the proof-carrying outcome unique.  The complete
decoder semantics are therefore kernel-checked.

```bash
python3 complete_splash_isa.py selftest
python3 complete_splash_isa.py build complete_splash_isa_audit.json
python3 complete_splash_isa.py verify complete_splash_isa_audit.json
```

The bounded regression checks 1,408 codewords through 18 bits and 990,528
pairwise prefix comparisons for each rail length `r=0,...,8`.  It also
literally decodes every odd `P<2^13` at each of those nine lengths: 12,288
even cleanups, 24,565 odd catchers, and 11 explicit halts.  These finite
counts audit the implementation; total decoding and Kraft mass one follow
from the displayed valuation split and exact geometric series.

The same artifact records a deeper rational-base bridge:

```text
U^12(1023+4096t)=132860+531441t,
digits [1,1,1,1,1,1,1,1,1,1,2,1].
```

Both linked splash families are universally outward.  The saturated orbit
first enters this cylinder at time 622.  What the even-only grammar called
its next “renewal failure” is decoded by the odd catcher
`(r,s,a,L)=(1,0,3,6)`.  It shrinks, and the complete ordinary path parses as
290 splash gates (101 outward) before reaching `1` after 1,016 accelerated
steps.  This is an exact two-stage compiler and total finite parse, not
transferred divergence.

```text
artifact SHA-256  d0c32f2d6c82ab142adf97a528046ef18d836f7db9b162150394aefe87dc269f
verifier SHA-256  7cd2e65d5dcf2ef3f44c4567941657a95c0a2d31a3489563858242cc7748d8c3
```

## The complete saturated-bridge graph in a bounded source box

`complete_u_bridge_graph.py` searches compiler *shapes*, not ordinary seeds.
A source splash with `N=r+s+2` accelerated odd steps can agree with `U^N`
only when its target prefix consumes exactly `N` address bits.  Once the
source is fixed, that equation gives a finite complete list of positive target
shapes; every link is then checked coefficientwise on its entire affine tail
cylinder.

```bash
python3 complete_u_bridge_graph.py selftest
python3 complete_u_bridge_graph.py \
  build complete_u_bridge_graph_audit.json
python3 complete_u_bridge_graph.py \
  verify complete_u_bridge_graph_audit.json
```

The committed source box is

```text
0<=r<=15, 0<=s<=4, 1<=a<=4,
1<=b<=4 on the even branch, 1<=L<=16,
both even-cleanup and odd-catcher sources.
```

It contains 25,600 source shapes, of which 11,312 complete families are
universally outward.  Their complete coefficient-compatible target lists
give 2,751,680 exact link tests and 18 saturated-map bridges.  Four have even
sources and 14 use the new odd catcher; 11 have universally outward linked
target subfamilies.  For each of those 11 target shapes, the worker then
checks its complete list of 718 possible second edges.  None renews as another
saturated bridge.  This is a sharp depth-two failure for these first-edge
hits, not an all-shape theorem.

The smallest new bridge is particularly clean:

```text
odd catcher (r,s,a,L)=(1,0,1,1)
  -> odd catcher (0,0,1,1),
U^3(7+8t)=26+27t,
```

and both selected families are universally outward.  It is one compiler edge,
not a loop; its target has no compatible outgoing saturated edge.

The same audit extracts a universal three-gate outward subcylinder from the
`U^12` bridge.  Restrict its saturated tail to `t=16u`; the indices become

```text
source   1023 + 65536u,
target   132860 + 8503056u,
catcher  39716626454 + 3^26 u.
```

The two even gates are followed by the odd catcher `(1,0,1,2)`, and all three
states increase for every `u>=0`.  At `u=0` the exact chain is

```text
2199021754367 -> 2229023590399
              -> 5083728186203
              -> 8578791314219.
```

That seed reaches `1` after 133 accelerated steps.  Finite tail refinement
can compile more outward gates, but an eventually periodic refinement is
already ruled out; the open target remains an ordinary aperiodic renewing
compiler path.

```text
artifact SHA-256  dcf10371f5a5c8991c3eae958d8efb31f1dba3a7e6b059d0c31ff028d9b5264c
verifier SHA-256  3ec925a23145af3c08065da658d45d19670d35b491b9b76b5230d236fb3b030d
```

## Ordinary splash relays and the universal router

The direct compiler graph stops because a saturated block is too rigid, not
because the complete splash hardware cannot connect its endpoints.  The
first relaxation in `complete_u_relay_graph.py` allows exactly one ordinary
splash between saturated edges.  Exact affine intersections give 22
universally outward four-gate relays among the 11 two-outward compiler nodes.
Their directed graph has just one cycle, the node-3 self-loop.  Its least
member is

```text
16334827 -> 20673767 -> 52330475 -> 66230759 -> 167646611,
```

and it reaches `1`.  Every infinite path in this one-relay graph is eventually
that fixed shape loop, hence repeats one valuation block and is already
excluded by the periodic-word theorem.  This is an exact failure of one
ordinary relay in the stated node set, not of longer catcher circuits.

```bash
python3 complete_u_relay_graph.py selftest
python3 complete_u_relay_graph.py build complete_u_relay_graph_audit.json
python3 complete_u_relay_graph.py verify complete_u_relay_graph_audit.json
```

The failure exposes a universal second relay.  For every incoming rail length
`r>=0` and desired outgoing gap `L>=1`, take

```text
R_(r,L) = odd_catcher(r,0,1,L),
word(R)  = [1]^r ++ [2,1].
```

It has `r+2` odd steps and `r+3` halvings.  Since

```text
3^(r+2) > 2^(r+3)          (base case 9>8),
```

every member is outward, while `L` can be chosen arbitrarily.  Therefore one
router can change the spatial gap from any outward compiler target to the
input gap of any next compiler source.

`complete_u_router.py` constructs the full consequence: all `11*11=121`
five-gate transitions

```text
A --U block--> B --ordinary--> R_(r,L)
  --ordinary--> C --U block--> D
```

exist as unbounded affine families and every gate is outward.  Thus the
two-relay compiler graph is the complete directed graph and supports arbitrary
finite node words at the shape level.  The least transition is

```text
71675 -> 120953 -> 136073 -> 153083
      -> 258329 -> 290621,
```

and reaches `1`.  Completeness of the finite shape graph is not an infinite
ordinary program: an infinite aperiodic node word still selects nested dyadic
cylinders whose limit is generally only a 2-adic tail.  The positive result is
that spatial routing and finite branching are no longer the bottleneck; the
ordinary-integer/self-reproduction gate is.

Lean commit `fedb5ca` checks both sides of that conclusion.  Its universal
router theorem proves every exact `(r,0,1,L)` catcher outward for all
parameters and payloads, without enumerating the shapes used here.  Its
dyadic-boundary theorem proves that if one ordinary natural belongs to nested
cylinders of unbounded precision, their canonical residues must eventually
be that natural literally.  Thus finite graph completeness cannot by itself
hide the ordinary-seed obligation.

Lean commit `e9f791b` then eliminates the externally supplied gate object for
the router-only machine.  Positive odd public payloads satisfying

```text
2^(r'+3) P' = 3^(r+2) P + 3
```

construct the unique canonical `(r,0,1,r'+1)` catcher and automatically prove
both linkage and growth.  Any infinite solution above state `4` refutes
Collatz.  This is the current minimal certificate interface; it remains
conditional because no infinite ordinary solution is known.

Lean commit `c10e5b5` proves the advertised normal form rather than merely
testing it: every recurrence output is divisible by three, and after removing
that factor the next rail length and payload are exactly the maximal power of
two and odd part of `3^(r+2)H+1`.

```bash
python3 complete_u_router.py selftest
python3 complete_u_router.py build complete_u_router_audit.json
python3 complete_u_router.py verify complete_u_router_audit.json
```

```text
one-relay artifact SHA-256  2ccca3f4f334a04c7cd55d404a1a9913a859a490ad348effc95cde2dc4f08865
one-relay verifier SHA-256  54e354c23788b9df4d74b3664d4c3c98816f3099f17543a4752f41d26a2e0cc2
router artifact SHA-256     e64bd5f3a98f352d8211e9104b40f8ee2d118240650a11401764be8a97016e3f
router verifier SHA-256     e2889b9d96f1a83044ecf03b69a657d0f84c48a2efd2a0ac1de84dbf688a4606
```

## Autonomous router break-off counter

`router_breakoff.py` removes all compiler-node bookkeeping from the universal
router.  In the ordinary coordinate `y=8k-1`, factor `k=2^j u` with `u` odd.
One legal outward router is exactly

```text
8k' = 3^(j+2)u + 1,                 k=8 (mod 9).
```

Integrality automatically gives `k'=8 (mod 9)` and `k'>k`.  For each opcode
`j`, the mod-8 legality test and mod-9 invariant select one odd residue
`u_j (mod 72)`, so the complete instruction family is

```text
k  = 2^j (u_j+72t),
k' = b_j + 3^(j+4)t.
```

The six repeating residues are `71,13,47,37,23,61`.  The checker reconstructs
the current and next sparse Collatz states, invokes the canonical
parity-complete decoder, and literally replays the router word.  The artifact
lists opcodes `0..64` and checks 64 tails apiece, or 4,160 exact replays.  This
is a bounded audit of the listed branches; the coefficient formula is the
symbolic construction, and Lean commits `e9f791b`/`c10e5b5` prove the public
recurrence and valuation normal form.  Lean commit `0b12d44` goes the final
step: proof-carrying binary/ternary factorizations of an infinite `k`-orbit
imply the mod-9 invariant, strict growth, and `¬Collatz`; it also proves the
necessary mod-24 interior payload classes.  No infinite ordinary orbit is
known.  Commit `7293975` defines the executable `v2`/odd-part partial map,
proves successful evaluation equivalent to the factorization equation, and
derives the same endpoint from an infinite successful executable orbit.

```bash
python3 router_breakoff.py selftest
python3 router_breakoff.py build router_breakoff_audit.json
python3 router_breakoff.py verify router_breakoff_audit.json
```

```text
artifact SHA-256  05e70ac426e7a6b9a7241a5732522755812a1527ff37b4a2c6ed9ab50e2f9476
verifier SHA-256  2b0d7a00e5921c4342f6ab8b9ebcb1f002d6de35ae62ba4d3b8286785382304d
```

Lean commit `a1a5fd0` proves an additional necessary condition for an infinite
break-off orbit: its exact macro-word is `[1]^r ++ [2,1]`, and neither its
rail lengths nor its opcodes `j=v2(k)` can be eventually periodic.  The six
repeating opcode residue classes are a finite decoder table, not a possible
cyclic generator.

## Regenerative break-off delay gates

`breakoff_delay_gate.py` gives Simon's collision-and-cleanup picture an exact
spatial form.  Begin with

```text
k = 9*2^(3q)c-1,                  q>=1.
```

An opcode-zero break-off step sends `(q,c)` to `(q-1,9c)`: it consumes exactly
three powers of two.  After `q` steps, prescribe collision opcode `j` and a
new positive delay `q'` by

```text
3^(2q+2)c-1 = 2^j u,
3^j u+1 = 2^(3(q'+1))c'.
```

The collision then lands at `9*2^(3q')c'-1`, a new clean delay-line state.
For every `q,q'>=1,j>=0`, the script constructs the unique coefficient class
modulo `2^(j+3q'+4)` that makes both valuations exact.  Every affine member is
replayed through `router_breakoff.literal_step`, hence through the canonical
Collatz splash decoder, at each delay tick and at the collision.

```bash
python3 breakoff_delay_gate.py selftest
python3 breakoff_delay_gate.py build breakoff_delay_gate_audit.json
python3 breakoff_delay_gate.py verify breakoff_delay_gate_audit.json
```

The committed audit covers `q,q'=1..8`, `j=0..16`, all 1,088 resulting
families, and eight affine tails per family: 8,704 exact macro replays.  The
small regression `(q,j,q')=(1,2,1)` is

```text
c=13, u=263, c'=37,
935 -> 1052 -> 2663.
```

It regenerates one three-bit delay cell, but exact continuation reaches `1`.
Lean commit `eac55d3` proves the general compressed delay, collision renewal,
whole-gate execution, and strict outwardness in the executable break-off map.
Commit `1711620` proves that the collision factorization plus the single
subtraction-free affine balance suffices to reconstruct renewal.  The Python
artifact remains the exact audit of the coefficient constructor; the
universal Lean theorem consumes these small displayed identities.

The same script now links finite gates.  The output family of the first and
input cylinder of the second are

```text
c_out=o+2*3^A*t,       c_in=r+2^(m+1)*s.
```

For a positive second collision opcode, both bases are odd.  Dividing their
difference by two leaves an invertible power of three modulo `2^m`, hence the
complete link family is

```text
t=t_0+2^m*v,
s=s_0+3^A*v,           0<=s_0<3^A.
```

It reads `m` low binary bits and appends the `A`-trit word `s_0`.  The link
audit covers all 4,608 shapes with delays at most four, first opcode at most
eight, and positive second opcode at most eight.  Two affine members per link
are checked through both gates, totaling 18,432 literal macro replays.  The
canonical digest of all link records is
`6fad9c93608cac35c24bf59b53e8650c1641b172c9d7cc87f32ce0cb940c8d52`.
Lean commit `54e506f` independently proves that supplied affine base/stride
identities give this coefficient link, exact two-gate execution, and strict
outwardness for every common tail.

One bounded alphabet result is complete: fixing the first gate to
`(q,j,q')=(1,1,1)` gives `A=5`.  Searching next opcodes `1..34` and next
delays `1..44` records an exact address for every `s_0=0..242`, all 243
five-trit write words.  This compiles a rich finite mixed-radix instruction
set, not a returning dispatcher, infinitely linked coefficient sequence, or
ordinary divergent seed.  Lean commit `5254194` makes the last caveat exact:
an ordinary natural lying in nested link-address cylinders of unbounded
precision forces their canonical residues eventually to equal that natural.
Perpetually changing initial-tail addresses describe only a 2-adic program.

```text
artifact SHA-256  2e498bfd6f0dec384ebfc9255233c5a5769980d98ffba7f5c9e4ab397e61c7e5
verifier SHA-256  2867d3a79d19c002a588927e1564c1850a50a03a107fbe4497b7773017585b75
```

## Invariant unit-debris register slice

`breakoff_unit_slice.py` restricts each primitive hierarchy register
`V=r+mK` to its unique packet class modulo `17` for which `17|V`.  Writing
`V=17H` reduces

```text
V=2^(an+b)g -> V'=(3^(cn+d)g+s*17)/2^e
```

to the invariant public map

```text
H=2^(an+b)h -> H'=(3^(cn+d)h+s)/2^e.
```

For every level and cell count, the unit branch is constructed by CRT with
collision constant `s=+1` or `-1`.  Independently, the parent `±17` affine
branch is intersected with its packet residue modulo `17`; both input and
output coefficients must agree after division by `17`.

The same map has a signed radix-swap normal form.  Put

```text
p=a*n+b+e,   q=c*n+d,   W=2^e*H.
```

Every legal member has a core `h` coprime to six and satisfies

```text
W =2^p*h,
W'=3^q*h+s.
```

Hence the instruction removes an exact binary scale, preserves the entire
nonlocal core, installs an exact ternary scale, and writes one signed unit.
For `y=W-s`, `y'=W'-s`, define the corresponding signed router value by

```text
R_s(y)=3^(p-1)*(y+s)/2^p.
```

Then exact cancellation gives

```text
R_s(y)=3^(p-1-q)*y'.
```

The unit ISA is therefore a signed router followed, in this coordinate
comparison, by a positive ternary trim.  The six certified formulas are

```text
level  sign  p                 q                 p-1-q
  1     +    8*n+15            6*n+11            2*n+3
  2     -    23*n+54           17*n+40           6*n+13
  3     +    77*n+177          57*n+131          20*n+45
  4     -    254*n+585         188*n+433         66*n+151
  5     +    839*n+1932        621*n+1430        218*n+501
  6     -    2771*n+6381       2051*n+4723       720*n+1657
```

This does not say that division by `3^(p-1-q)` is another Collatz operation.
It identifies exactly what a second physical rail would have to bank if it is
to turn the unit swap into a self-regenerating router.

```bash
python3 breakoff_unit_slice.py selftest
python3 breakoff_unit_slice.py build breakoff_unit_slice_audit.json
python3 breakoff_unit_slice.py verify breakoff_unit_slice_audit.json
```

The artifact checks six hierarchy levels, `n=1..32`, and four tails per
branch: 192 coefficient comparisons, 768 exact public-map members, and 768
signed radix-swap/trim identities.  It
also literally replays two members for every level-one `n=1..16`, totaling
336 lower links and 672 gate macros.  The parent packet residues modulo `17`
are `3,16,0,2,6,8`.  This certifies the invariant unit slice, not an infinite
orbit.

```text
artifact SHA-256  459bd3feb5a30d931caf43c601db8713354696d9ae072e223e3603d77838b753
verifier SHA-256  4057b56485ea1570d0b5abd2f50415f909e8afbc4b8f04f0c04baaf73ce265ff
```

## Constant-rate unit schedules are partial-theta values

`unit_linear_theta.py` closes the most direct unit-counter clock.  At one
fixed level put

```text
p(n)=a*n+b+e,   q(n)=c*n+d,
2^(p(n_(t+1)))*h_(t+1)=3^(q(n_t))*h_t+s.
```

For every arithmetic schedule `n_t=n_0+k*t`, with fixed integer `k>=1`, exact
finite backward unrolling and 2-adic convergence give the unique initial
candidate

```text
h_0=-s/3^(q(n_0)) *
    F(2^(a*k)/3^(c*k), 2^(p(n_0+k))/3^(q(n_0+k))),
F(r,z)=sum_(j>=0) r^(j*(j-1)/2) z^j.
```

The coefficient identity

```text
F(2^(a*k)/3^(c*k),z)
  =f_(3^(c*k)/2^(a*k))((3^(c*k)/2^(a*k))z)
```

puts the candidate in the full-source Väänänen--Wallisser 1989 theorem
already used for the standard two-rail schedule.  Use `ell=1`, `sigma=0`,
and `p=2`.  The rational argument is

```text
alpha=2^(p(n_0))/3^(q(n_0)),
```

so it is nonzero, and the distinct-argument condition is vacuous.  The exact
uniform size audit is

```text
2^8>3^5                         => log(2)/log(3)>5/8,
3*a>=4*c                        => a*log(2)/(c*log(3))>5/6,
45<64                           => 1/6<(3-sqrt(5))/2.
```

For general `k`, the theorem parameter is `3^(c*k)/2^(a*k)`.  The displayed
size ratio is unchanged because `k` cancels, while
`|3^(c*k)/2^(a*k)|_2=2^(a*k)>1`.  The cited theorem therefore makes
`f_(3^(c*k)/2^(a*k))(alpha)` irrational in `Q_2`; multiplying by the nonzero
rational scale cannot give an ordinary integer `h_0`.

```bash
python3 unit_linear_theta.py selftest
python3 unit_linear_theta.py build unit_linear_theta_audit.json
python3 unit_linear_theta.py verify unit_linear_theta_audit.json
```

The artifact independently compiles the branch schedules
`1,2,...,9` at all six unit levels and checks eight exact recurrences, their
finite rational unrollings, and the terminal 2-adic residues.  The terminal
precision ranges from 472 bits at level one to 172,972 bits at level six.
Those finite linked-branch checks remain a `k=1` regression.  The script also
checks the generalized coefficient-exponent identity for sampled
`k,n_0`, while the displayed symbolic derivation and cited external theorem
give the all-`n_0`, all-fixed-`k` infinite conclusion.  This closes every
positive constant-rate counter, not a nonlinear or packet-branching length
schedule.

```text
artifact SHA-256  682d5636c66f1ea2a8f2cad7e58027da1e821513f248726175c839907bad312a
verifier SHA-256  944eeaa73a8b860d36531b90e866941ab282633b0ebd2736839fd00b8d870e28
```

## Two-layer unit gap regeneration

`unit_gap_regenerator.py` makes the surviving unit ISA implement Simon's
“splash the gap” proposal directly.  For one current branch, write

```text
2^p h'=3^q h+s.
```

Let `C` be the low `L=p_next+1` bits which make `h'` execute a specified next
branch, including the bit which makes its next valuation exact.  Since
`3^q` is odd, there is a unique first correction `A` modulo `2^(p+L)` and an
integer carry `B` with

```text
3^q A+s=2^p C+2^(p+L)B.                         (UG1)
```

For any desired gap length `D>=1`, there is then a unique sacrificial word
`z mod 2^D` and an integer `B_2` with

```text
B+3^q z=2^D B_2.                                 (UG2)
```

Consequently every natural residual tail `u` satisfies the exact identity

```text
h =A+2^(p+L)(z+2^D u)
h'=C+2^(L+D)(B_2+3^q u).                          (UG3)
```

Thus the first layer emits a complete next instruction.  The next `D` bits
of the high packet are consumed in cancelling its carry, and the output has
exactly those `D` bit positions cleared before the untouched tail resumes.
The surviving tail update is affine, with multiplier `3^q`.

The worker additionally restricts `u` to the unique class modulo the odd
unit-register stride.  This makes every family member an actual pair of
linked compiled unit macros, not just a congruence between cores.  It checks
exact valuations, register invariance, coprimality to six, the emitted prefix,
the regenerated gap, and both macro endpoints.

```bash
python3 unit_gap_regenerator.py selftest
python3 unit_gap_regenerator.py build unit_gap_regenerator_audit.json
python3 unit_gap_regenerator.py verify unit_gap_regenerator_audit.json
```

The default artifact reconstructs all 486 families at six hierarchy levels,
all triples of cell counts `1..3`, gaps `1,4,12`, and two residual-tail
members.  It performs 972 linked two-branch unit replays.  At level one, the
case `(n_0,n_1,n_2,D)=(1,2,3,12)` gives the exact core path

```text
96640062369165269810946648141077
 -> 5811505674703125430887858069149
 -> 995193873655264956279801575123.
```

The middle core contains its complete 40-bit next instruction, twelve zero
bits, and then the residual packet.  This construction works algebraically
for arbitrary positive cell counts and `D`; the listed bounds scope the
machine replay.  It does not provide a self-supplying infinite program.  An
infinite preloaded sequence of `z` words is merely a 2-adic stack.  The live
task is to make the affine residual packet write the next required `z` from
its own state, with packet-dependent instruction lengths.

```text
artifact SHA-256  3337b99b291894f6338716a1a2d1e459f3ae414086c239bca693258052212f3d
verifier SHA-256  c737953183b760a9411ad5d2d6e57cad7eb3560578353c78166e2afe8381772a
```

## Formula-generated repetend splashes

`unit_repetend_splash.py` compresses the sacrificial word into one rational
repetend.  Given an odd marker `C` and an exponent `T` such that

```text
2^T*C = s (mod 3^q),
```

put

```text
R=(2^T*C-s)/3^q.
```

Then for every `D>=1` and positive packet `K`,

```text
h =R+2^(T+D)K
h'=C+2^D*3^q*K
3^q*h+s=2^T*h'.                                  (UR1)
```

The low rail `R` is an ordinary positive integer generated by a short
formula.  At collision it is consumed completely; `C` remains at the low end,
the next `D` bit positions are zero, and the remote packet survives with a
power-of-three multiplier.

For the unit ISA, `T` must also equal the next legal affine exponent

```text
T=p(n')=a*n'+b+e.
```

The exact order `ord_(3^q)(2)=2*3^(q-1)` gives the discrete-log class of `T`.
CRT with `T=b+e (mod a)` then produces an enormous positive `n'`.  Marker
`C=1` works at levels two through six.  Level one's `+1` sign needs an odd
`T` but its `C=1` class is even; the smallest audited replacement is `C=5`,
whose exact discrete logarithm is found by baby-step/giant-step.

The register stride is divisible by three, so it cannot be cancelled from
the quotient casually.  The worker computes `R mod M` by evaluating `2^T`
modulo `3^q M`, divides the certified residue by `3^q`, and then solves one
odd dyadic congruence for `K mod M`.  It independently checks both source and
target public register phases.  No huge power of two is materialized.

```bash
python3 unit_repetend_splash.py selftest
python3 unit_repetend_splash.py build unit_repetend_splash_audit.json
python3 unit_repetend_splash.py verify unit_repetend_splash_audit.json
```

The default artifact contains gaps `D=1,64` at all six levels from source
length one.  Its scale summary is

```text
level        1    2    3    4     5     6
marker C     5    1    1    1     1     1
digits(T)    9   29   91  299   980  3235
digits(n')   8   27   89  296   977  3231
```

At level one, `T=105734623` and `n'=13216826`; writing out `R` would already
take about 31.8 million decimal digits.  The higher rows are symbolic by
necessity.  This is an exact nonlinear one-jump family, not a returning
controller.  The live equation is to arrange for
`C+2^D*3^q*K` to generate another repetend splash from its own packet state.

```text
artifact SHA-256  fc73032df9114e59ca3f8926509616b66455d69b61536866cc50728fc7a2d170
verifier SHA-256  d1991059ec7be5b754d9352395d3053ce305496bc2dc85f849ea21eb9b0d3554
```

## Sign-alternating capped-splash hierarchy

`breakoff_renormalization.py` iterates the super-ether construction as exact
affine algebra.  A level has

```text
V=r+mK,
V=2^(an+b)g -> V'=(3^(cn+d)g+s*17)/2^e.
```

Branch one is its background cell and branch two is its defect.  If `F` is
the affine fixed form of the background self-link, the next level retains
`a+b` low bits of `F`.  The verifier checks two independent obligations:

1. the capped boundary has the next defect's residue modulo `2^(a+b+1)`;
2. after the inherited binary and common ternary factors are removed, the
   collision constant is exactly `-s*17`.

Both pass through six constructed levels:

```text
level             1      2       3        4         5          6
collision sign    +      -       +        -         +          -
binary cell       8     23      77      254       839       2771
binary offset    -5      3      24      100       354       1192
ternary cell      6     17      57      188       621       2051
ternary offset   11     40     131      433      1430       4723
fixed division   20     51     153      485      1578       5189
```

The background length is itself an instruction.  For any supplied `j>=1`,
the same constructor may use branch `j` as `B` and the adjacent branch `j+1`
as `H`; it retains `aj+b` bits and checks that the normalized collision is
again `-s*17`.  The artifact verifies all level-one choices `j=1..64` and
three nonconstant four-step meta-words:

```text
(2,2,2,2),  (3,1,4,2),  (8,5,3,1).
```

All three have collision signs `+,-,+,-,+`.  This is a bounded audit of the
variable meta-alphabet, not a universal theorem for every choice word.

The same artifact performs a canonical quine audit over the complete tree
`j=1..8`, depth at most three.  Its `8+64+512=584` nodes contain zero
canonical packet stabilizations and zero decreases: every extension strictly
increases the first-scale packet.  The closest words `(1,1)` and `(1,1,1)`
share 23 and 155 low bits with their parents.  This rejects the least-CRT-tail
quine in the stated tree; the identity below supplies the unbounded conclusion.

There is also an unbounded algebraic obstruction for this entire recursive
constructor.  Put `E=E_B+E_H`, where the two terms are the parent background
and defect input exponents; let `r0>=0` be the inherited valuation and
`q_raw>0` the raw defect input before normalization.  Every positive child
packet `K` enters the parent background at

```text
q=(q_raw-2^E)+2^(E+r0)K
 =q_raw+2^E(2^r0*K-1)>0.
```

Thus every nested adjacent-defect extension is strictly above the canonical
parent base.  Its canonical dyadic address changes at every added hierarchy
level, so the ordinary-tail theorem excludes an infinite nested tower as one
natural program.  This statement is conditional only on a step being produced
by the displayed constructor; it neither proves that the phase identities
continue forever nor excludes an autonomous orbit at one fixed finite level.

For every renormalization and `N=1..8`, a child branch is built twice: once
by CRT from its public register and once directly by composing the parent
`B -> M_2 -> B`, `N` background self-links, and the capped boundary return.
All 40 coefficient pairs agree.  Two members per branch are replayed through
520 parent macro blocks.

The artifact separately expands the canonical length-one, tail-zero program
at every depth to literal level-one gliders.  At depth six this is the
substitution word generated by `n -> 1,2,1^n`: 360 linked glider macros,
1,189 lower links, and 2,378 gate macros from a formula-generated 6,708-digit
ordinary start.  Consecutive first-scale packets share `23,155,589,2013,6715`
low bits but are strictly larger and unequal.  The checked tower is therefore
a sequence of finite 2-adic approximants, not a stabilized ordinary program.

```bash
python3 breakoff_renormalization.py selftest
python3 breakoff_renormalization.py build breakoff_renormalization_audit.json
python3 breakoff_renormalization.py verify breakoff_renormalization_audit.json
```

The artifact contains large exact integer coefficients (up to thousands of
decimal digits); the verifier raises Python's decimal conversion guard before
loading them.  The scope is six finite levels, not an induction to all levels
and not an infinite Collatz orbit.

```text
artifact SHA-256  b568fb1b5228ced1f1198ad6375ba7f256e5f6f3dcf158dfc60d3d018dcdaf50
verifier SHA-256  a0c05f28c9e585194e64b1df755e13ea7c5e4fbbc43cc7a0346f23e8c836b1e9
```

## Three-bit-capped recursive super-ether

`breakoff_superether.py` treats the one-cell returning glider as a 23-bit
background cell.  If its macro tail is `q`, then

```text
F(q)=(3^17-2^23)q+50679661,
2^23 F(q')=3^17 F(q)
```

on every self-link.  An exactly exhausted super-ether has odd `F` and cannot
enter any next glider macro: every macro input packet is odd, and the required
source-tail parity is the opposite one.  Retaining exactly three bits repairs
the phase.  The capped boundary is `9 (mod 16)`, identically the input phase of
the composite defect `M_1 -> M_2 -> M_1`.

After its common factor `3^7` is removed, the defect register is

```text
V=-8744697538656344367967+671265207750760396088265*K.
```

Its public autonomous branch and affine packet branch are

```text
V=2^(23N+3)g -> V'=(3^(17N+40)g-17)/2^51,
K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t.
```

The change from the primitive `+17` register law to `-17` follows from the
exact constant identity

```text
2^54*(-8744697538656344367967)
 - 3^33*(50679661 + 120751555*(-234676942119623)) = -136.
```

```bash
python3 breakoff_superether.py selftest
python3 breakoff_superether.py build breakoff_superether_audit.json
python3 breakoff_superether.py verify breakoff_superether_audit.json
```

The artifact constructs `N=1..64`, checks four affine members of each branch,
and literally replays two members through `N=16`.  The latter 32 super-macro
members expand to 336 returning glider macros, 1,040 lower affine links, and
2,080 literal delay-gate macros.  This certifies a finite recursive delay
constructor and its capped boundary return, not an infinite orbit.

```text
artifact SHA-256  67d6f701420cac98a780db27352d6f3adf4511e6d0958ccc38531f1e9f539a5c
verifier SHA-256  5167fd7b912e4a3da9dca24c2183a5e877f1ea488003d4cd7764b79ab8333491
```

## Autonomous ether-counter normal form

`breakoff_ether_counter.py` removes all hidden gate metadata from the returning
glider.  Put

```text
Y=83790531*K-874281.
```

For a positive invariant register, compute `e=v2(Y)` and `h=Y/2^e`.  The
public partial map accepts exactly when

```text
e=8n-5,  n>=1,
3^(6n+11)*h+51 = 0  (mod 2^20),
```

and returns

```text
Y'=(3^(6n+11)*h+51)/2^20.
```

The register remains `-874281 (mod 83790531)` and grows strictly.  For each
`n`, the odd invariant fixes `h` modulo `83790531`, the binary execution test
fixes it modulo `2^20`, and CRT gives one complete class modulo
`83790531*2^20`.  Its affine input/output packet coefficients are identically

```text
K=R_n+2^(8n+15)*q -> K'=S_n+3^(6n+11)*q,
```

the returning glider macro from `breakoff_ether_glider.py`.

```bash
python3 breakoff_ether_counter.py selftest
python3 breakoff_ether_counter.py build breakoff_ether_counter_audit.json
python3 breakoff_ether_counter.py verify breakoff_ether_counter_audit.json
```

The artifact constructs `n=1..128`, checks four affine members of every
branch, and independently compares both coefficients with all 128 glider
macros.  It also literally replays two macro members for `n=1..32`, totaling
1,184 linked members and 2,368 gate macros.  This verifies the autonomous
coordinate and its bounded executable seam, not an infinite orbit.

```text
artifact SHA-256  1bd14809686ed19e599f95d624c81732daa984a681e28b82fdda868abfedfff0
verifier SHA-256  ac560b6b088d62c685fa7382af7cc5e75a8f0039d9ea55558a00a237214f9dfe
```

## Returning finite ether glider macros

`breakoff_ether_glider.py` closes the finite boundary return left open by the
first ether defect.  An exactly exhausted ether has odd tail.  Among immediate
`E -> H_j -> E` defects, every `j>=2` has an even `E` input address, while
`H=(1,1,1)` has the compatible odd address.  Its links are

```text
E -> H:  67+2^7*v -> 381+3^6*v,
H -> E: 151+2^8*w -> 144+3^5*w,
```

and meet on

```text
v=170+2^8*u,       w=485+3^6*u.
```

With `u=2^5*K-1`, the returned `E` tail obeys

```text
473*t+12=2^5*(83790531*K-874281).
```

One odd residue class of `K` therefore emits exactly `n` ether cells.  A
second exact congruence makes the exposed boundary equal the next defect input

```text
X(K')=2^20*K'-10941.
```

After eliminating the two address residuals, the complete family is

```text
K=R_n+2^(8n+15)*q -> K'=S_n+3^(6n+11)*q,    n>=1.
```

Every macro begins at an ordinary `E` state ready for `H`, executes the two
defect links and `n` ether self-links, and ends at another ordinary `E` state
ready for `H`.

```bash
python3 breakoff_ether_glider.py selftest
python3 breakoff_ether_glider.py build breakoff_ether_glider_audit.json
python3 breakoff_ether_glider.py verify breakoff_ether_glider_audit.json
```

The artifact constructs `n=1..32` and replays tails zero and one of every
macro: 64 members, 1,184 exact linked members, and 2,368 literal gate macros.
Its separate exact macro audit links the staircase `n -> n+1` for
`n=1..128`; after exhausting the remaining high tail, every generated second
macro misses `n+2`, so maximum depth is two.  That is a bounded failure of one
controller, not of nonzero macro tails or other aperiodic length schedules.

```text
artifact SHA-256  7621d987451ebd20d926ab49972e2bfb91b0ab67ba24b797b525297b2ef1d255
verifier SHA-256  0f933e8330e33f0c65c3a6b51d30f0983b504492183ca39ef8a4f6c2f3d76dce
```

## Regenerative finite ether defect

`breakoff_ether_defect.py` turns the spatial delay-line metaphor into an exact
affine ether.  For `E=(q,j,q')=(1,2,1)`, the self-link is

```text
t=20+2^8*v  ->  t'=57+3^6*v,
```

and hence

```text
2^8*(473*t'+12)=3^6*(473*t+12).
```

The 2-adic fixed tail is `-12/473`.  If an ordinary `E` tail has
`v2(473*t+12)=8n`, the self-link consumes exactly one eight-bit cell at each
gate and exposes the defect after exactly `n` cells.

The gate `H=(1,136,1)` gives a concrete `E -> H -> E` return.  The two exact
links reduce to residual coordinates `v=177+2^8*u`, `w=504+3^6*u`.  On the
Mersenne packet `u=2^8*K-1`, the returned `E` tail satisfies

```text
473*t+12=2^8*(r+A*K),
```

where the artifact records the fixed odd `r` and `A`.  For every `D>=1`, the
unique odd class

```text
r+A*K = 2^D  (mod 2^(D+1))
```

gives exact ether depth `8+D`.  Taking `D=8n-8` constructs an `n`-cell finite
ether for every `n>=2`.

```bash
python3 breakoff_ether_defect.py selftest
python3 breakoff_ether_defect.py build breakoff_ether_defect_audit.json
python3 breakoff_ether_defect.py verify breakoff_ether_defect_audit.json
```

The artifact replays `n=2..32`: 31 ordinary starts, 589 linked members, and
1,178 literal gate macros.  The affine identities and residue constructor are
unbounded; the table is a bounded executable regression.  No claim is made
that the exposed boundary returns to another defect or that any orbit is
infinite.

```text
artifact SHA-256  0440872a822089819d4f69818574e59d87b198a7829218c0420257c7037e0c4a
verifier SHA-256  9ec1527e31c54b5b3da3055a0bf6f68469bc178dd9de5eba5d3cc99606ad39ce
```

## Nonlocal sacrificial gap amplifier

`splash_gap_amplifier.py` turns Simon's proposed collision cleanup into an
exact linked-tail identity.  The fixed dispatcher `(q,j,q')=(1,1,1)` writes
with stride `3^5=243` and has a previously certified complete five-trit word
alphabet.  For each `1<=L<=7`, select the concrete word

```text
b=3^5-2^L
```

and the residual packet `v=K*2^L-1`.  Then

```text
b+3^5*v = 2^L*(3^5*K-1).
```

The low run of `L` one-bits is sacrificial: its carry against the written word
becomes a run of zero-bits.  For every `D>=1`, the unique odd class

```text
3^5*K = 1+2^D  (mod 2^(D+1))
```

makes that output gap exactly `L+D`.  The condition reaches across the remote
packet `K`; it is not a local fixed-width cleanup rule.

```bash
python3 splash_gap_amplifier.py selftest
python3 splash_gap_amplifier.py build splash_gap_amplifier_audit.json
python3 splash_gap_amplifier.py verify splash_gap_amplifier_audit.json
```

The artifact uses all seven actual writer witnesses and checks `D=1..32`, or
224 exact linked members and 448 literal gate macros.  The displayed identity
is universal elementary arithmetic; the artifact is a bounded regression of
the constructors and executable replays.  It does not expose the internal
tail gap as a returning public delay and makes no infinite-orbit claim.

```text
artifact SHA-256  2ddec88f152c7a0bbad8cd8e886ef711b715a104964bd0984abec2fce253c261
verifier SHA-256  8cba957c423700af3dd2bf4b9eeae8369584ae9b41c54654b6369ab30e19b386
```

## Canonical tail-zero delay graph

`search_delay_base_graph.py` asks whether the ordinary-tail gate can be met in
the strongest possible way: use the least coefficient (`tail=0`) of one delay
family and require its output to be literally the least coefficient of the
next decoded family.  Such a link consumes no additional bits of an initial
2-adic address.

There is a necessary representation check.  In

```text
k=9*2^(3q)c-1,
```

a coefficient divisible by eight contains another whole delay cell, so the
displayed `q` is not maximal.  The worker records such hits separately as
coordinate aliases and calls a source canonical only when `8` does not divide
`c`.

```bash
python3 search_delay_base_graph.py selftest
python3 search_delay_base_graph.py build delay_base_graph_audit.json
python3 search_delay_base_graph.py verify delay_base_graph_audit.json
```

The artifact exhausts every shape

```text
q=1..100, j=0..100, q'=1..100,
```

or 1,010,000 symbolic gates.  The exact partition is:

```text
no next clean delay          992,129
next gate needs tail > 0      17,861
canonical tail-zero links          3
nonmaximal-delay aliases            7
```

Every retained source and target is reconstructed with
`breakoff_delay_gate.gate` and literally replayed through every executable
delay tick and collision.  The three canonical shape links are

```text
(1,1,90) -> (90,5,1)
(1,2,61) -> (61,4,1)
(2,2,61) -> (61,4,1).
```

Every target fails to emit another clean delay, so the maximum canonical
base-edge chain is one.  Exact ordinary continuation sends their 85-, 59-,
and 59-digit starts to `1` in 330, 1,272, and 1,277 Collatz steps.  This is a
bounded failure of immediate least-representative stabilization.  It does not
exclude a program whose nonzero tail is produced by earlier hardware, a
nonlinear two-packet encoding, or shapes outside the source box.

```text
artifact SHA-256  3a35c71beda163b21e71a3ebaeaf672b24dc37078858ee21410e09510aefa536
verifier SHA-256  bc0fc70026f314466285da28f385894503f64a5a6ccebac967ce03c6da66a3ff
```

## A seven-step base-`3/2` compiler bridge

Eliahou--Verger-Gaugry's saturated-word map

```text
U(n)=(3n+1)/2 for odd n,  (3n+2)/2 for even n
```

is divergent and appends digit `1` or `2` to the rational-base-`3/2`
representation at every step.  On a fixed `D`-bit binary address, `U^D` is an
affine map with slope `3^D/2^D`.  This exactly matches a two-rail index
instruction when its source write exponent `R` equals its target address
length `D`.

`two_rail_u_bridge.py` finds and verifies one outward match.  The source and
target gate shapes are

```text
(r,s,a,b,L) = (5,0,2,1,2) -> (1,0,2,1,2),
```

and their complete index handoff is

```text
z = 95+128*t  ->  w = 1640+2187*t = U^7(z),   t>=0.
```

The seven appended digits are `[1,1,1,1,1,2,1]`.  Because the residue fixes
all seven parities, the equality is universal on the entire affine family,
not a finite orbit coincidence.  The saturated orbit itself enters the
cylinder at `U^41(0)=26906975` and leaves at
`U^48(0)=459730910`; the corresponding exact Collatz gate is

```text
440843894591 -> 470764451891.
```

The next linked gate shrinks to `99301876571`, fails to renew the two-rail
section, and the original ordinary seed reaches `1` after 72 accelerated
steps.  So the bridge compiles one block of the divergent program but does not
yet keep executing it.

```bash
python3 two_rail_u_bridge.py selftest
python3 two_rail_u_bridge.py build two_rail_u_bridge.json
python3 two_rail_u_bridge.py verify two_rail_u_bridge.json
```

The bounded shape audit checks 67,500 links with source `r<=10`, `s<=4`,
collision extras at most three, output gap at most 11, and the corresponding
target parameters.  It finds three exact `U^D` bridges with `R=D=7`, only one
with a universally outward source family.  These are shape bounds, not a seed
range and not an exclusion beyond them.

```text
artifact SHA-256  f00bbe835305612dcc3c78bcd33caa3789bdbeae375ed8655778d19559d249d3
verifier SHA-256  6501d3ed30ba1be27780c10ee7f9e65606a0ca9badd4b88141c3b5a6d31cbfe0
```

## The standard schedule as a 2-adic partial theta value

Lean commit `db0971c` eliminates the intermediate cleanup payload from every
standard gate and proves the necessary recurrence

```text
2^(r+8) P_(r+1) = 3^(r+3) P_r + 69.
```

Every outgoing payload has exactly one factor of three.  With `P_r=3U_r`,
exact backward unrolling identifies the only 2-adic initial candidate as

```text
U_5 = -(23/3^8) * sum_(n>=0)
        (2/3)^(n(n-1)/2) * (2^13/3^9)^n.
```

This is a Tschakaloff/partial-theta value.  Väänänen and Wallisser's 1989
linear-independence theorem applies at `q=3/2`, `p=2`, and argument
`4096/6561`, proving the value irrational in `Q_2`.  Therefore no ordinary
integer can run the complete standard schedule.  The [derivation and theorem-
hypothesis audit](../../docs/notes/standard-two-rail-theta.md) give the exact
parameter mapping and scope.

```bash
python3 standard_two_rail_theta.py selftest
python3 standard_two_rail_theta.py build standard_two_rail_theta_247.json
python3 standard_two_rail_theta.py verify standard_two_rail_theta_247.json
```

The depth-247 artifact reconstructs all compiled payloads and checks 246
normalized recurrences, the exact finite rational identity, and 33,333 bits
of 2-adic congruence precision.  It is a finite regression for the symbolic
reduction, not evidence for irrationality.

```text
artifact SHA-256  66068dc5a8419d1abba99ca6e89d363280e2b4f66a1085a7406e2fa863c5460f
verifier SHA-256  86a544b6dd89993804a51db7773736f4a6b8b4c932988eba5ffde535f34c8165
```

The independent application checker uses no floating point.  It verifies

```text
F(2/3,8192/19683) = f_(3/2)(4096/6561)
```

coefficientwise with rational arithmetic and checks the theorem's strict size
condition through the rational separator `3/8`:

```text
2^8 > 3^5  =>  1-log(2)/log(3) < 3/8,
5*4^2 < 9^2  =>  3/8 < (3-sqrt(5))/2.
```

```bash
python3 standard_two_rail_irrationality.py selftest
python3 standard_two_rail_irrationality.py \
  build standard_two_rail_irrationality_audit.json
python3 standard_two_rail_irrationality.py \
  verify standard_two_rail_irrationality_audit.json
```

The artifact checks the parameter substitution and application hypotheses;
it cites rather than reproves the published theorem.

```text
artifact SHA-256  9b713f7e8191c211cd01c17015c8526f8efd4bc194a1b011c0006c745941c540
verifier SHA-256  20f2dcefa01391369988f14f4aa8dac8cd1849cf8af24a5eab737a9395058b3c
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
