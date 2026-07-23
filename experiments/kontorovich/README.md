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

## Formula-compressed regenerative carry rail

`unit_carry_repetend.py` specializes the preceding arbitrary carry cleanup so
the same collision carry reappears beyond the regenerated gap.  From (UG1),
let `r=v3(B)` and put

```text
e=q-r,
D=ord_(3^e)(2)=2*3^(e-1),
z=B*(2^D-1)/3^q.
```

The canonical isolated carries satisfy `0<B<3^q`, so `z` is a positive
ordinary `D`-bit word.  Exact divisibility follows from `2^D=1 (mod 3^e)`,
and the catcher identity is

```text
B+3^q*z=2^D*B.                                     (UCR1)
```

Substitution into (UG3) gives the formula-compressed glider cell

```text
A+2^(p+L)*(z+2^D*u)
  -> C+2^(L+D)*(B+3^q*u).                           (UCR2)
```

The dirty carry disappears at the collision and the identical carry appears
on the remote side of `D` clean zero bits.  The verifier checks the exact
order of two, the isolated-carry identity, and source, target, and following
unit-register phases without constructing `2^D` or `z`.

```bash
python3 unit_carry_repetend.py selftest
python3 unit_carry_repetend.py build unit_carry_repetend_audit.json
python3 unit_carry_repetend.py verify unit_carry_repetend_audit.json
```

For the canonical branch triple `(1,1,1)` at the six compiled levels:

```text
level:                    1    2    3     4      5       6
q:                       17   57  188   621   2051    6774
v3(B):                    1    0    0     0      0       2
decimal digits of D:      8   28   90   297    979    3231
```

This is a genuine finite spatial glider cell.  It is not a self-writing end
cap: finitely many catcher blocks give finitely many translations, while an
infinite preloaded rail is a 2-adic tape rather than an ordinary natural.

```text
artifact SHA-256      57328afb5c10edbbedfb3e14881e0d1b53925bb2bc67ecd57e5f32f187c97c83
verifier file SHA-256 3f9690acf60481d560c2eddc7056da3b186e0679e1f1c9fae077cdccb6ee96f2
combined source SHA   ed12b495d4bee423466694e9550f12ed303aa2fc4a8e880b0905de1b2fc1ccd7
```

## Formula-compressed strike--scrub--turnaround

`unit_carry_turnaround.py` closes the *finite* end-cap problem for one
regenerative carry rail.  At unit level two, use the sign-negative one-cell
source and target, carry `B=1`, and marker `H=17`.  Then

```text
q_source=q_target=57,   p_target=77,
D=ord_(3^57)(2)=2*3^56
 =1046695266054721074427023042,
P=D+2.
```

The first two collisions and the carry translator are

```text
3^57*A-1=2^77*C+2^(77+L)*B,
B+3^57*z=2^D*B,
3^57*C-1=2^p(ell)*H.
```

Eliminating `A,C` gives one discrete logarithm modulo `3^114`.  Exact
base-three lifting finds the following-length cylinder

```text
ell=985704136832889032287826201378021826095996227497733368
    (mod 1643356469972045002664087635582629208716484341598400646).
```

It is even.  For the remote packet to consume exactly `P` bits, impose

```text
3^(17*ell+40)*17=1+2^P (mod 2^(P+1)).              (UCR3)
```

Because `17=1 (mod 8)`, the right-hand side times `17^-1` is in the
even-power subgroup generated by three.  The kernel-checked theorem
`KontoroC.orderOf_three_twoPow` gives that subgroup order, so (UCR3) selects
an even class modulo `2^(P-1)`.  Its gcd with the displayed ternary period is
two, and the two even classes therefore meet by CRT.  This proves existence
of a finite ordinary `ell` without expanding its roughly `10^27` bits.

Finally restrict the surviving tail by the odd register stride `M` and by
four:

```text
u=u0+4*M*w,
h_out=R+2*M*3^(q(ell)+114)*w.                      (UCR4)
```

The coefficient following the single displayed factor two is odd.  Thus for
every finite `E>=1` and every odd target word `T`, there is a unique
`w mod 2^(E-1)` for which `h_out=T (mod 2^E)`.  In Simon's spatial language,
the first collision **strikes**, the repetend gap **scrubs** the dirty carry,
and the third collision **turns around and reseeds** an arbitrary finite odd
header.  It is a nonlocal three-event instruction spread across the complete
digit span.

```bash
PYTHONPATH=. python3 unit_carry_turnaround.py selftest
PYTHONPATH=. python3 unit_carry_turnaround.py build unit_carry_turnaround_audit.json
PYTHONPATH=. python3 unit_carry_turnaround.py verify unit_carry_turnaround_audit.json
```

The artifact reconstructs the level constants, multiplicative order,
explicit logarithm modulo `3^114`, marker/carry alignment, legal division
class, parity-compatible CRT, and odd-coefficient writer algebra.  Its
subgroup-existence step cites the stated Lean theorem.  It does not expand an
explicit giant `ell`, produce an autonomous infinite ordinary tail, or give
a Collatz counterexample.  Preloading infinitely many desired headers would
still specify a 2-adic stack.

```text
artifact SHA-256      f65eae7c602a6fc38bc7ba528bc090184dcf160e398c01e913099158581f47fe
verifier file SHA-256 114c1ce6bb53fc396f5c06902ae12d55aef59f7a450080b3ab6440f52977a5cd
combined source SHA   1eb852eb1ddecb6505e95281b50cd889434a437677ab15701f2c262aa8d7ea66
```

## RETRACTED: same-scale expanding marker turnaround

**Semantic audit failure (2026-07-22 08:23 EDT).**  The construction below is
retained only as a record of the error.  Its three raw divisions do not form a
linked unit-ISA path: after the second transition the source state is `1`, so
the third transition must use `q(1)=57`, whereas the worker used `q(g)`.  The
worker and artifact have been removed.  None of UMT1--UMT3 is evidence for a
Collatz macro when combined with the advertised state labels.

`unit_marker_turnaround.py` removes the uncontrolled preceding-length class
from the fixed-marker construction.  It keeps the second instruction at one
level-two cell and synthesizes the marker itself.  Put

```text
L=78,  B=1,  D=2*3^56,  P=D+2,
g=(P-54)/23=45508489828466133670740130.
```

The unique ternary residue `h_3 mod 3^114` is defined by

```text
2^154*h_3+2^77+3^57*(2^155+1)=0 (mod 3^114).
```

For every integer `t`, set

```text
H=h_3+3^114*t,
C=C_0+2^77*3^57*t,
A=A_0+2^154*t.
```

Then the first two exact collisions are identities:

```text
3^57*A-1=2^77*C+2^155,
3^57*C-1=2^77*H.                                   (UMT1)
```

Choose `t` modulo `2^(P+1)` from

```text
3^(q(g)+114)t=1+2^P-3^q(g)h_3 (mod 2^(P+1)).       (UMT2)
```

The coefficient is odd, so it permutes all dyadic residues; Lean commit
`a0073fd` kernel-checks the generic writer lemma.  Equation (UMT2) makes
`H` odd and gives

```text
3^q(g)H=1+2^P (mod 2^(P+1)),
```

so the third collision has exact valuation `P`.  Taking the canonical `t`
gives a positive marker of at most `P+183=D+185` bits.  This has the same
scale as the scrub gap and does not require constructing the fixed-marker
length class.

After `z=(2^D-1)/3^57` translates the carry and the ordinary source tail is
restricted as `u=u_0+4Mw`, the input and output `w` coefficients are

```text
2^(D+157)M,
2M*3^Q,       Q=q(g)+114=773644327083924272402582364.
```

The second is strictly larger.  Since `Q` is even, `3^Q=9^(Q/2)>8^(Q/2)`,
and

```text
3Q/2-(D+156)=113771224571165334176850348>0.         (UMT3)
```

Thus this is a finite outward affine family, not merely a cleanup gadget.
The remaining obligation is closure: the output is not proved to lie in a
next marker cylinder selected by its own payload.

```bash
PYTHONPATH=. python3 unit_marker_turnaround.py selftest
PYTHONPATH=. python3 unit_marker_turnaround.py build unit_marker_turnaround_audit.json
PYTHONPATH=. python3 unit_marker_turnaround.py verify unit_marker_turnaround_audit.json
```

The selftest also fully materializes a small surrogate and replays all three
exact divisions.  The public instance remains formula-compressed.  No
invariant family, infinite ordinary orbit, or counterexample is claimed.

```text
artifact SHA-256      475beaa146173295f49c382bc694bc9e11cec247df4d3fe43566f7147906a3a5
verifier file SHA-256 809c95233c79c495ac2222127bd58d70f14d719e0ffbe13bb6d29b28d0b000c0
combined source SHA   14803034960b7c074134b7c126a750c2c408d7fc45e2344a65d2ec875c42b084
```

## RETRACTED: all-opcode synthesized-marker bank

**Semantic audit failure (2026-07-22 08:23 EDT).**  This bank inherits the
same source/target mismatch as the preceding section.  Its rank-one algebra
describes raw affine divisions, not composable public unit instructions.  The
worker and artifact have been removed, and UMB1--UMB5 must not be cited as a
Collatz return bank.

`unit_marker_bank.py` allows every later legal third division after the same
carry translation.  Index the bank by `j>=0`:

```text
P_j=D+2+23*j,
g_j=g_0+j,
q_j=q_0+17*j,
Q_j=q_j+114.
```

Write the marker lift as `t=t_j+2^(P_j+1)s`.  Its contribution to the source
has binary exponent

```text
154+(P_j+1)=P_j+155.                               (UMB1)
```

The remote contribution initially begins after `D+1` clean positions.  For
it to be invisible through the exact `P_j` division, choose

```text
1+3^57*u_j=0 (mod 2^(P_j-D)),
u=u_j+2^(P_j-D)*((M-1)*s+M*w).                     (UMB2)
```

Its raw source exponent is then

```text
155+D+(P_j-D)=P_j+155.                             (UMB3)
```

The `M-1` coefficient is forced by the public invariant register: because the
marker and remote source exponents agree, it cancels the marker lift modulo
the odd stride `M`.  After the third division the same addition occurs.
Hence the two islands are not independent stacks.  With `v=s+w`, the
register-preserving three-collision family has rank-one normal form

```text
x_j=X_j+2^(P_j+155)*M*v,
y_j=Y_j+2*M*3^Q_j*v.                               (UMB4)
```

The spatial islands remain distinct pieces of the finite integer, but exact
valuation alignment identifies their algebraic freedom.  This is the sharp
failure mode for a literal two-stack interpretation of the splash.

The bank still has positive coefficient drift at every opcode.  Opcode zero
is the previous exact `9>8` comparison.  Raising `j` once multiplies the
output/input ratio by

```text
3^17/2^23=129140163/8388608>1.                      (UMB5)
```

Thus the live machine is an unbounded variable-length tag ISA: a successful
ordinary orbit must let its one natural register select a non-eventually-
periodic opcode sequence.  Repeating one `j` is merely the already closed
periodic valuation-word lane.

```bash
PYTHONPATH=. python3 unit_marker_bank.py selftest
PYTHONPATH=. python3 unit_marker_bank.py build unit_marker_bank_audit.json
PYTHONPATH=. python3 unit_marker_bank.py verify unit_marker_bank_audit.json
```

The verifier reconstructs the public exponent and coefficient rows for
`j=0..15`, retaining a digest of all sixteen and the endpoint rows.  It also
fully materializes a small analogue at opcodes `0..5`; each analogue replays
all three exact divisions, both rank-one differences, and preservation of
the small odd register class under the coupled lift.  The first public
artifact omitted that coupling; the corrected version is the one hashed
below.  The all-`j` claim is the symbolic algebra (UMB1)--(UMB5); the listed
ranges scope only the materialized regressions.  No payload-selected opcode
law, infinite orbit, or counterexample is claimed.

```text
artifact SHA-256      8a3bd0fc4ee0788541ed5b6974286ff86e58496404a7fcf2979c5a460c3da1af
verifier file SHA-256 8d9b01da1c7c786117725dd24fc87a625abff495b49def2075ff7474c1ca8971
combined source SHA   5230047c12e4f679ad0278710bbcdd13e70b2cdef8a97dd1b994cb3548016ed8
```

## Legal return macro and reproduction equation

`unit_return_quine.py` replaces the retracted three-collision route by the
source/target-compatible path

```text
1 -> 1 -> g -> g -> 1.
```

For `P=23g+54`, `Q=17g+40`, `R=114+2Q`, and `S=154+2P`, its exact composition
is

```text
3^R*h-C_g=2^S*h',
C_g=3^(2Q+57)+2^77*3^(2Q)+2^(77+P)*3^Q+2^(77+2P).
```

The verifier constructs the unique canonical source modulo `2^(S+1)` and
literally replays all four exact valuations for `g=1..16`.  Its real purpose
is to expose the closure gate

```text
3^R(g)*F(g)-C_g=2^S(g)*F(f(g)).
```

One fixed finite rule `F,f` must supply positive odd states and the same four
legal transitions forever.  Choosing a new CRT residue at every generation
does not pass this gate.  For `f(g)=g+1`, put
`z=2^(23g+54)/3^(17g+40)`.  Exact normalization gives

```text
3^114*f(z)-[(3^57+2^77)+2^77*z+2^77*z^2]
  =2^154*z^2*f((2^23/3^17)*z).
```

The artifact checks a general degree argument excluding every finite Laurent
polynomial.  A rational-function upgrade by pole propagation is documented as
a research derivation pending Lean review.  No infinite solution is known.

```bash
PYTHONPATH=. python3 unit_return_quine.py selftest
PYTHONPATH=. python3 unit_return_quine.py build unit_return_quine_audit.json
PYTHONPATH=. python3 unit_return_quine.py verify unit_return_quine_audit.json
```

```text
artifact SHA-256      fbc46c761aec4319407dc091f2b089f3fba0e4f89e288601f9b2d83cf9ad6ce2
verifier file SHA-256 6b18d52e67904212d8d91f0549b26362d4baa0fe550cb1641792948ff471bdb4
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

## A second sign-negative repetend splash

`unit_double_repetend.py` makes the level-two marker `1` launch one further
formula-generated splash while preserving the first ternary bank.  For

```text
c_m=(2^(3^(m-1))+1)/3^m,
```

write `2^(3^(m-1))=-1+3^m c_m` and cube.  Exact division gives

```text
c_(m+1)=c_m-3^m*c_m^2+3^(2m-1)*c_m^3.          (UD1)
```

Therefore `c_(m+1)=c_m (mod 3^m)`.  For any fixed precision `P`, all later
quotients have the same first `P` ternary digits.  At level two the initial
data are

```text
q_0=57,
T_0=21457252954121782025753972361,
n_1=932924041483555740250172709,
q_1=15859708705220447584252936093.
```

The odd register has `v_3(M)=33`, so use `P=q_0+33=90`.  The exact stable
quotient modulo `3^90`, combined with the affine exponent class modulo `23`,
gives

```text
k=376213925255524775706446580991916826376956379,
T_1=3^(q_1-1)*k,
T_1=54 (mod 23).
```

Because `q_1>=90`, binomial expansion modulo `3^(q_1+90)` gives

```text
2^T_1=-1+3^q_1 (mod 3^(q_1+90)).
```

Thus

```text
R_1=(2^T_1+1)/3^q_1 = 1 (mod 3^90),
A=(R_1-1)/(2*3^q_0)
```

is an ordinary integer and is known modulo the complete level-two register.
For every positive tail in one exact register class and every chosen final
gap `D`, the two genuine unit collisions are

```text
h_0=R_0+2^(T_0+1)*(A+2^(T_1+D-1)*L)
 -> h_1=R_1+2^(T_1+D)*3^q_0*L
 -> h_2=1+2^D*3^(q_0+q_1)*L.                    (UD2)
```

Neither `T_1` nor `R_1` is materialized.  The worker evaluates the stable
3-adic quotient through 89 exact recurrence steps, computes `R_1` modulo the
coprime conductor factors, reduces `T_1` modulo the exact Carmichael exponent
of the register, and checks all three public phases.  `T_1` itself has about
`7.57*10^27` decimal digits.

```bash
python3 unit_double_repetend.py selftest
python3 unit_double_repetend.py build unit_double_repetend_audit.json
python3 unit_double_repetend.py verify unit_double_repetend_audit.json
```

The artifact reconstructs the unbounded families for final gaps `D=1,64`.
This is exact one-time renewal, not an infinite staircase.  Backward nesting
another independently selected repetend consumes a new dyadic address and
again tends to a 2-adic stack.  The remaining target is an autonomous rule by
which the free ordinary packet `L` emits its own third correction.

```text
artifact SHA-256  76ce98689eef74589937e05b3c3295844f49620ab8e2e9fb0a4889b5749a61f5
verifier SHA-256  05dfc41a661089c68fa57cebbb850cc5109bec24803efda227c16825ede0453c
```

## Why consecutive full repetends cannot continue forever

`unit_repetend_energy.py` closes the naive infinite continuation of the
preceding construction.  For a sign-negative marker-one repetend,

```text
2^T=-1 (mod 3^q)
```

forces

```text
T=(2j+1)*3^(q-1).
```

For `q>=3`, exact induction gives `3^(q-1)>=2q+1`; hence

```text
2^T >= 2^(2q+1)=2*4^q > 2*3^q.                  (UE1)
```

In the unit recurrence

```text
2^T*h_next=3^q*h-1,
```

both cores are positive, so (UE1) implies

```text
h>2*h_next.                                      (UE2)
```

After `N` consecutive full-order splashes,
`h_0>2^N*h_N>=2^N`.  No fixed positive integer `h_0` can satisfy this for all
`N`.  The obstruction applies even if a future controller could synthesize
each correction word autonomously; it is a real core-energy obstruction, not
the 2-adic address problem.

```bash
python3 unit_repetend_energy.py selftest
python3 unit_repetend_energy.py build unit_repetend_energy_audit.json
python3 unit_repetend_energy.py verify unit_repetend_energy_audit.json
```

The artifact checks the concrete source-length-one exponent classes at all
three sign-negative finite hierarchy levels `2,4,6`, in addition to the
generic integer separators.  It does not exclude other markers or giant
splashes separated by amplifying instructions.  The surviving engineering
target is a charge--discharge cycle: ordinary outward macros must replenish
more than the core factor spent by each rare repetend erasure.

```text
artifact SHA-256  33ed88a031967a3012c5609add1959ea5bb6afda84479267c6c58fc2bfe61efa
verifier SHA-256  9bcf9d11dc867f95d44d80203d7d0ee5c4d01edcd3531bb066617de010767853
```

## Autonomous `-5` charge--discharge register

`unit_charge_discharge.py` implements the first amplifying phase proposed by
the energy separator.  At sign-negative hierarchy level two, compose a
length-`N` unit instruction with the one-cell instruction.  If the first
branch has exponents `p(N),q(N)` and its output executes the one-cell branch,
eliminating the intermediate core gives

```text
2^(p(N')+p(1))*h'
 =3^(q(N)+q(1))*h-(3^q(1)+2^p(1)).
```

At this level `p(1)=77`, `q(1)=57`, and

```text
3^57+2^77=5*D,
D=314038802961906688057474567.
```

The divisor `D` is coprime to the unit-register stride
`671265207750760396088265`.  Exactly one packet residue modulo `D` makes the
public register divisible by `D`; the residue is

```text
233625389414829423733081846 (mod D).
```

Restricting to that class and dividing both endpoints by `D` produces a new
invariant register

```text
G=499379675639703663139777
  +671265207750760396088265*K
```

with autonomous branch law

```text
G=2^(23N+3)g -> G'=(3^(17N+97)g-5)/2^128.          (UCD)
```

Its complete packet branch is again affine, with input stride exponent
`23N+131` and output stride `3^(17N+97)`.  The slope is strictly outward for
every `N>=1`: the exponent inequality
`3^(17N+97)>2^(23N+131)` holds at `N=1` and gains a factor
`3^17/2^23>1` per added cell.  The worker constructs every audited branch in
two independent ways: directly from (UCD) by CRT, and by composing the
original level-two length-`N` branch with its one-cell branch and restricting
the result to the displayed residue.  Both affine coefficient pairs must
agree before bounded members are replayed through the two literal unit
macros.

```bash
python3 unit_charge_discharge.py selftest
python3 unit_charge_discharge.py build unit_charge_discharge_audit.json
python3 unit_charge_discharge.py verify unit_charge_discharge_audit.json
```

The artifact checks `N=1..32`, four members per branch, and 256 original
unit-macro replays.  It is an exact finite compiler plus a symbolic
all-`N` outwardness argument.  It does not supply an infinite successful
orbit.  Such an orbit would be an outward ordinary Collatz macro-orbit and
would refute Collatz.

This coordinate is distinct from `search_shadow.py`'s bounded programs near
the signed cycle `-5 -> -7 -> -5`.  Only the debris magnitude coincides; no
conjugacy is claimed, and the register and exponent laws are different.

```text
artifact SHA-256  e7af475f153a2e444b84f91dda8f4f395f1a048abde2383f40ac48eda4bef564
verifier SHA-256  5c6cb46cec58720ef3d215651312556a05a3970a089792c3cd29ba7f3831e05a
```

## All-depth self-regenerating `-5` hierarchy

`unit_charge_hierarchy.py` applies the charge--discharge quotient to itself.
Suppose a level has

```text
G=2^(23N+3)g -> G'=(3^(17N+d)g-5)/2^e.             (UCH1)
```

Composing its length-`N` branch with its one-cell branch gives

```text
2^(2e+26)G''
 =3^(17N+d+17+d)g-5*(3^(17+d)+2^(26+e)).           (UCH2)
```

Put `D=3^(17+d)+2^(26+e)`.  When `D` is coprime to the odd register
stride, there is one packet residue for which both public endpoints in
(UCH2) are divisible by `D`.  Division reproduces (UCH1), still with
collision constant `-5`, and updates

```text
d'=2d+17,              e'=2e+26.
```

Starting from `d_0=97,e_0=128`, the closed forms are

```text
d_j=114*2^j-17,
e_j=154*2^j-26,
D_j=3^(114*2^j)+2^(154*2^j).
```

The required coprimality with
`M=671265207750760396088265` holds at every depth by a finite exact
certificate.  If a prime `r!=3` divided both `M` and `D_j`, division by
`2^(154*2^j)` modulo `r` would give

```text
(3^114/2^154)^(2^j)=-1 (mod r).
```

The multiplicative order is then divisible by `2^(j+1)`, so
`2^(j+1)<=r-1<M`.  Since `M` has 80 bits, only `j=0..78` need be tested.
All 79 exact modular gcds are one.  The omitted prime `r=3` cannot divide
`D_j` because the power of two is nonzero modulo three.  This proves
transversality for every recursive depth without factoring `M`.

```bash
python3 unit_charge_hierarchy.py selftest
python3 unit_charge_hierarchy.py build unit_charge_hierarchy_audit.json
python3 unit_charge_hierarchy.py verify unit_charge_hierarchy_audit.json
```

The artifact materializes eight levels.  For `N=1..8` it independently
constructs every level branch by direct CRT and by composing two parent
branches, restricting to the `D_j` slice, and dividing; all 64 coefficient
pairs agree.  It checks two members per branch and recursively expands one
member per level through a total of 510 original unit macros.  The deepest
materialized level has `d=14575`, `e=19686`; its selected input packet has
19,868 bits and its full lower-level expansion reaches 46,258 packet bits.

The all-depth constructor does not evade the ordinary-integer gate.  Every
positive child packet lifts as

```text
K_j=rho_j+D_j*K_(j+1)>K_(j+1).
```

Thus deeper canonical nestings strictly enlarge the root packet and cannot
eventually stabilize to one natural.  The hierarchy proves that the splash
mechanism self-regenerates at arbitrary finite scale; a counterexample still
requires an infinite autonomous orbit at one fixed finite level.

```text
artifact SHA-256      6ae387f7cc5db514a5314378121986540bda0f1741e8b97a566c7510cb643981
verifier file SHA-256 71f9d2014225ec4a937bc8e489c11307139121b7a2a01cca1c59266b62adb1b9
combined source SHA   fca4daa41545e459e2e3df26439c3423a29d1f83d0a5a01b15957b447633dcc5
```

## Fixed-form two-valuation charge bouncer

`unit_charge_bouncer.py` clears the rational fixed point of the one-cell
charge instruction.  Define

```text
A=3^114,
B=2^154,
F=(A-B)/5
 =493006936424420884140154671288273660376560866054730997,
Z=F*G-2^26.
```

The charge-register offset satisfies `F*r=2^26 (mod M)`, so `Z` is an
integer multiple of `M` on every public register state.  The one-cell branch
becomes exactly homogeneous:

```text
B*Z'=A*Z.                                           (UCB1)
```

For a defect of length `N=m+1`, direct substitution gives

```text
2^(154+23m)*Z'
 =3^(114+17m)*Z
  +2^26*A*(3^(17m)-2^(23m)).                        (UCB2)
```

At every defect source, `Z=2^26*y` with `y` positive and odd.  Conversely a
defect-phase bouncer state is characterized by

```text
y=0 (mod M),
y=-1 (mod F),
v2(y+1)=23m,       m>=1.
```

Put

```text
E=3^(17m)*(y+1)-2^(23m).
```

If

```text
v2(E)=23m+154h,    h>=1,
```

then (UCB2) executes the defect and (UCB1) executes exactly `h-1` further
background cells.  The next defect-boundary state is

```text
y'=3^(114h)*E/2^(23m+154h).                         (UCB3)
```

It continues precisely when `v2(y'+1)` is another positive multiple of 23;
literal execution preserves the two fixed register congruences.  Equations
(UCB1)--(UCB3) are an autonomous two-valuation programming language: `y`
chooses `m`, the defect collision chooses `h`, and its odd part becomes the
next state.  Every successful underlying charge instruction is strictly
outward, so an infinite accepted positive `y`-orbit would refute Collatz.

The transition is exactly reversible.  Since the bracket `E` is not divisible
by three, an accepted output has

```text
h=v3(y')/114,
q=y'/3^(114h),
m=v3(1+2^(154h)q)/17,
y=2^(23m)*(1+2^(154h)q)/3^(17m)-1.                 (UCB4)
```

The verifier applies (UCB4) to every bounded member and requires the recovered
predecessor to match exactly.  The two opcode scales are nearly rank one but
not quite:

```text
114*23-154*17=4,
D^154=B^23,
A^23=3^4*C^154.
```

This determinant-four resonance is a concrete formula-family target: one
large exchange cancels the binary scale exactly while leaving only four
ternary powers.  It does not by itself close the affine register seams.

Lean commit `5633c44` proves that freezing one defect opcode `m` forever is
impossible by the affine fixed-point divisibility obstruction.  The partial
map here is not that recurrence: `m` is read anew from `y`, may decrease, and
each block switches from its defect law to `h-1` homogeneous background laws.
The bounded artifact deliberately contains every ordered `m -> m'` pair in
`1..4`; this validates variable routing but does not prove an infinite route.

```bash
python3 unit_charge_bouncer.py selftest
python3 unit_charge_bouncer.py build unit_charge_bouncer_audit.json
python3 unit_charge_bouncer.py verify unit_charge_bouncer_audit.json
```

For `m,m'=1..4` and `h=1..4`, the artifact builds the complete affine family
which executes defect `m+1`, then `h-1` backgrounds, and enters defect
`m'+1`.  Its 64 families and two members each are checked by the fixed-form
map and literally replayed through 320 charge macros and 640 original unit
macros.  This bounded family audit validates the compiler seam; it is not an
infinite orbit or an exhaustive search over bouncer states.

```text
artifact SHA-256      5f2d6bfdcc6c48692e40e000ad8550262ac74b102c1e0b06238ab9783efbd4c2
verifier file SHA-256 c434c7ddf57b15f271b7c22be66d6614199a76f41cc7ba36346ca53f7a2df754
combined source SHA   7e21ee2fdb570e0ac5e2325c957bbf6ad5a96ecdc13a6ed3f795cbba00ccd16d
```

## Perfect-23rd-power reproduction rail

`unit_charge_power_quine.py` attacks closure inside the autonomous bouncer,
instead of compiling another prescribed clock.  Write one accepted transition
in radix form:

```text
C^m*u=1+B^h*q,
D^m_next*u_next=1+A^h*q,
A=3^114, B=2^154, C=3^17, D=2^23.
```

Because the fixed register requires `F | u`, the encoding

```text
u=F*r^23,       u_next=F*r_next^23
```

is the first simple payload type that can reproduce its own address.  The
23rd power turns `v2(r_next)` into exactly one integral number of next defect
cells because `D=2^23`.  Eliminating the collision quotient gives the necessary
quine equation

```text
A^h*C^m*r^23-B^h*D^m_next*r_next^23=(A^h-B^h)/F.   (UCPQ1)
```

For the shortest recharge `h=1`, use `A-B=5F` and absorb all complete 23rd
powers.  Every closure would solve one of

```text
3^e*X^23-2^16*Y^23=5,
e=(114+17m) mod 23.                                 (UCPQ2)
```

Complete finite-field enumeration is very sharp:

```text
mod 47:  e in {4,6,15}
mod 139: e in {6,15}
mod 461: e in {15}.
```

Thus only `e=15`, equivalently `m=5 (mod 23)`, survives, leaving the single
Thue equation

```text
3^15*X^23-2^16*Y^23=5.                              (UCPQ3)
```

The artifact exactly reconstructs the bouncer constants, the squarefree prime
factorization of `F`, all 23rd-power residue sets, and every survivor set.  Lean
commit `5fbacf5` independently proves the reduction and that any accepted
shortest-recharge transition supplies a solution of (UCPQ3).  PARI/GP 2.15.4
then closes (UCPQ3): the checked script reports irreducibility, attached
tentative class number one, and complete Thue solution list `[]`.  PARI's
documentation says that the class-number-one flag-zero case is unconditional.
This last claim trusts PARI's Bilu--Hanrot implementation; it is not a kernel
proof.  Therefore the `h=1`, `u=F*r^23` rail is impossible.  Higher recharge
and other payload types remain open, and no infinite orbit is claimed.

```bash
PYTHONPATH=. python3 unit_charge_power_quine.py selftest
PYTHONPATH=. python3 unit_charge_power_quine.py build unit_charge_power_quine_audit.json
PYTHONPATH=. python3 unit_charge_power_quine.py verify unit_charge_power_quine_audit.json
ssh akdeniz.lan.cmu.edu 'gp -fq' < unit_charge_power_quine_thue.gp
```

```text
artifact SHA-256      c60741d605a1c669bd89fe3a0b4d06d1dd883ec0a03792d3e44aab5331d474eb
verifier file SHA-256 da18a787a4dd3e1fd1f56ae9eadb1fa7010594b9ba8e1764d7c9d395529496b2
GP audit SHA-256       c4541ea4c0cdcac65d2738bef9fffd378ae0fe4c7495409b46be08cd80d76e48
```

## Recharge-23 determinant-four resonance

`unit_charge_power_resonance.py` checks the first higher-recharge case where
the hardware itself aligns with the 23rd-power payload.  At `h=23`,

```text
A^23=3^4*C^154,       B^23=D^154,
(A^23-B^23)/F=5*Phi_23(A,B).
```

The fixed divisor `F` is coprime to `Phi_23(A,B)`.  Complete residue
enumeration modulo `47`, `139`, and `461` leaves all 23 coefficient classes,
in sharp contrast to `h=1`.  This is only a three-prime diagnostic: the
independent Lean sieve at `277`, `599`, `829`, and `1151` collapses the
uncorrected single rail to `e=15`, equivalently `m=9 (mod 23)`, and the one
global equation `3^15 X^23-Y^23=5 Phi_23(A,B)`.  The 1,198-digit forcing and
residual `3^4` remain live inputs for a correction rail, which can change that
equation.  These identities do not construct such a rail or even one accepted
transition.

```bash
PYTHONPATH=. python3 unit_charge_power_resonance.py selftest
PYTHONPATH=. python3 unit_charge_power_resonance.py build unit_charge_power_resonance_audit.json
PYTHONPATH=. python3 unit_charge_power_resonance.py verify unit_charge_power_resonance_audit.json
```

```text
artifact SHA-256      db7e620c936bcb9b126a70e183f33ad0880159942329e5c04476c7035fdcfe9c
verifier file SHA-256 7ae1c74962306fa89ce4cc98f4520548c1185a10b9f3fd48fe143adc83a5b8b5
```

The exact global survivor can be launched with
`unit_charge_power_resonance_thue.gp`.  It solves

```text
3^15 X^23-Y^23=5 Phi_23(A,B)
```

using PARI's complete degree-23 Thue routine and prints the irreducibility and
class-number gates before the solution list.  The 1,198-digit right-hand side
makes this a long-running external-PARI computation, not a Lean proof.

## Public-state 23rd-power reproduction

`unit_charge_state_power_quine.py` checks the stronger public-state type

```text
y=s^23,  h=23*ell,  q=t^23,
y'=(A^ell*t)^23.
```

It reconstructs the exact transition equation, all 23 coefficient
normalizations, the fixed-register 23rd-root conditions, and the integer
inequalities used by the pure coefficient no-go.  Lean commit `4c56925`
proves the `m=0 (mod 23)` class impossible; commits `f61f569` and `9f00894`
kernel-check the scaled norm equation, the valuation-preserving cyclotomic
cofactor balance, its gcd-at-23 constraint, and the additional hidden register
modulo `F`.

For a nonzero coefficient `e`, the worker also records the exact bridge

```text
0 < Y/X-3^(e/23) < 3^(e/23)/s^23,    q_reduced < s^2.
```

This would give exponent 11 and, by Roth's theorem, exclude an infinite run
wholly inside the pure public-power type.  Lean commit `07352a9` now
kernel-checks the real inequality, growth, residual-class bookkeeping, and
exponent-11 conversion.  Roth remains external, and the sequence-level
reduced-rational/finiteness consumer is not yet checked; the route therefore
does not exclude isolated transitions or corrected/multi-rail encodings.

```bash
PYTHONPATH=. python3 unit_charge_state_power_quine.py selftest
PYTHONPATH=. python3 unit_charge_state_power_quine.py build unit_charge_state_power_quine_audit.json
PYTHONPATH=. python3 unit_charge_state_power_quine.py verify unit_charge_state_power_quine_audit.json
```

```text
artifact SHA-256      8a297e55a7691a8c611ecb1daba7abc0e841b405050fbc90fe9f91c7c3e90a08
verifier file SHA-256 aa4749e1b3a51cb04b080a9b1ed79226e5abcbbf33c77004eba273f8ae020d9d
```

## Writable hidden-`F` register

`unit_charge_hidden_register.py` continues the public-power cofactor law at
the fixed divisor `F`.  If

```text
s+1=D^m F w,       B^ell*t+1=C^m F v,
```

then the exact collision lift is unique through every `F`-adic precision and
starts

```text
v=w+11F(C^m-D^m)w^2                    (mod F^2).
```

The output quotient `w'` has the first-digit instruction

```text
B D^m' w'=B C^m w-5ell                 (mod F).
```

Because all displayed coefficients are units modulo `F`, the recharge length
`ell` can write an arbitrary next value of this 179-bit register.  The audit
Hensel-lifts the collision through `F^3`, checks the nonlinear second digit,
and synthesizes five unrelated target writes whose least positive recharge
lengths have up to 54 decimal digits.  Separate CRT rows prove that the public
register does not force a second factor of `F`.

This is an exact necessary-state transducer, not an accepted bouncer
transition.  The still-missing compiler obligation is to make the chosen
`ell` equal the exact 2-adic collision valuation in a positive integer.  Lean
commit `34e166b` independently proves the universal Taylor/carry spine,
geometric output law, first-digit divisibility, and unique recharge class
modulo `F`.

```bash
PYTHONPATH=. python3 unit_charge_hidden_register.py selftest
PYTHONPATH=. python3 unit_charge_hidden_register.py build unit_charge_hidden_register_audit.json
PYTHONPATH=. python3 unit_charge_hidden_register.py verify unit_charge_hidden_register_audit.json
```

```text
artifact SHA-256      e04f1c829e28fe4621507755cc7f0b6dfbf59f920f02baf961e87f042ddc7f08
verifier file SHA-256 58c35526dfdba88268f1821b9a439db54bb2f3242ba3674e1603e35c8494ba19
```

## Hardware-matched quadratic norm type

`unit_charge_quadratic_norm.py` replaces the rigid one-coordinate power by a
literal two-rail type

```text
N_d(x,u)=x^2+d*u^2.
```

It reproduces for every recharge, because

```text
B^h N_d(t,v)=N_d(2^(77h)t,2^(77h)v),
A^h N_d(t,v)=N_d(3^(57h)t,3^(57h)v).
```

The obvious `d=1` choice is universally impossible: every accepted public
state and collision quotient is `7 (mod 8)`, while a sum of two squares is
never `3 (mod 4)`.  The corrected audit uses

```text
d_hw=13*(C-D)=5*13*19*1271069=7 (mod 8).
```

This discriminant ramifies every non-ternary prime forced by the public
register.  Exact CRT witnesses show, separately, that `N_d` contains legal
inputs with `m=1,2,5` and collision quotients whose scaled outputs have next
opcodes `m'=1,3,5`.  A PARI-discovered vector is replayed by integer arithmetic
as a nonzero-last-coordinate rational point on the `m=h=1` homogenized
collision quadric.  Thus the endpoint syntax and rational core have no
obstruction in this type.

The endpoints have not been coupled.  The remaining equation is the integral
rank-four quadric

```text
C^m*(x^2+d*u^2+1)=D^m*(1+B^h*(t^2+d*v^2)),
```

together with the public-register congruences.  Solving that equation in a
way which maps one coordinate pair to the next forever is the live closure
problem; no transition or orbit is claimed here.  Lean commit `2743350`
independently proves the universal recharge identities and the complete
accepted-semantics mod-8 obstruction for `d=1`.  Commit `90c9b6c` proves that
an already accepted typed step satisfies the displayed quadric and regenerates
the displayed output coordinates; the converse compiler obligation remains
open.

```bash
PYTHONPATH=. python3 unit_charge_quadratic_norm.py selftest
PYTHONPATH=. python3 unit_charge_quadratic_norm.py build unit_charge_quadratic_norm_audit.json
PYTHONPATH=. python3 unit_charge_quadratic_norm.py verify unit_charge_quadratic_norm_audit.json
```

```text
artifact SHA-256      bb04d5fb5d05ce6c5e22765d00029430e626aabaf7c5970b12867ebca465c9b5
verifier file SHA-256 8dddae25c33895e948bff98b94361e32fb0586abf1263797a98184b4c0340e57
```

## Quadratic norm opcode sieve and closure boundary

`unit_charge_norm_opcode.py` corrects the discriminant choice above and
connects it to literal accepted transitions.  If a prime `p` divides
`R=C-D` once and `-d` is nonsquare modulo `p`, then `p` dividing an `N_d`
value forces `p^2` to divide it.  Applying this at both sides of the accepted
collision forces `p|m`.  The complete squarefree list `d=7,15,23,31` shows
that `d=31` is the first parity-compatible candidate in this range without an
inert register prime; `d=7` forces `95|m`.  The selected type has the exact
hardware identity

```text
C-D = 7706^2+31*1407^2.
```

Writing consecutive public states and quotients as

```text
y=A^g(C-D)r,       q=(C-D)r',
```

cancels the register and gives

```text
2^(23m+154h)r' = 3^(17m+114g)r + H_m,
H_m=(C^m-D^m)/(C-D).
```

The artifact replays one literal 184-digit to 193-digit outward transition
whose input, quotient, and output are all `N_31` values.  It also checks why
this is not closure: the output's next collision valuation is 153, so after
its 23-bit defect the putative recharge has remainder `130 (mod 154)`.

The same artifact treats opcode chaining symbolically.  With

```text
J_m=[[C^m,H_m],[0,D^m]],
```

it checks `J_n J_m=J_(m+n)` and the general upper-triangular product formula
for decorated finite opcode chains.  The recharge-free algebra is therefore
an additive clock.  The live object is a public, self-synchronizing relation
among recharge-decorated matrices, as specified in
[`kontorovich-closure-principles.md`](../../docs/notes/kontorovich-closure-principles.md).

```bash
PYTHONPATH=. python3 unit_charge_norm_opcode.py selftest
PYTHONPATH=. python3 unit_charge_norm_opcode.py build unit_charge_norm_opcode_audit.json
PYTHONPATH=. python3 unit_charge_norm_opcode.py verify unit_charge_norm_opcode_audit.json
```

```text
artifact SHA-256      fbf757f3884cb190c852b530a7aa0799225ab630b133a4d83b38489da2351d2c
verifier file SHA-256 dcbac93c1b51a3eb4573f62ee74bf570ce419b9f764d52bd6952087b17bf8724
```

`unit_charge_norm_chain.py` exactly compiles two accepted blocks and can force
its middle residual to be a principal form along a quadratic parameter.  Its
selftest passes, but its prime/form search emitter is deliberately not being
run as a large job: a hit would be only a finite typed chain, not the required
depth-independent public update.

## Canonical public-cofactor transducer

`unit_charge_public_cofactor.py` removes the noncanonical norm coordinates
from the programming interface.  At defect opcode `m`, every legal public
state has one unique presentation

```text
y=D^m*w-1,
w=w_m+S*t,       S=2*F*M,       t>=0,
```

where `w_m` is the least positive odd solution of

```text
F|w_m,       D^m*w_m=1 (mod M).
```

For one branch `(m,h,m')`, exact collision/output elimination gives

```text
A^h(C^m*w-1)=B^h(D^m'*w'-1).
```

Substituting the canonical bases produces the literal mixed-radix
instruction

```text
2^(154h+23m')*t'=3^(114h+17m)*t+kappa,
t=rho+2^P*u  ->  t'=sigma+3^Q*u.
```

The state `(m,t)` is uniquely decoded from the normalized public integer
`y`; it is not a chosen certificate coordinate.  Positive odd endpoint
cofactors make the collision quotient odd, so the equality recovers the exact
normalized valuation and bouncer output.  The bounded arithmetic artifact
reconstructs every branch with
`1<=m,h,m'<=3`, replays two members per branch through the public bouncer and
its reverse decoder, and checks 54 exact transitions.  At each tested control
state it also checks all 36 pairs of source cylinders disjoint.  The complete
positive-opcode code has the exact geometric Kraft mass

```text
sum_(h,m'>=1) 2^-(154h+23m')
  = 1/((2^154-1)(2^23-1)),
```

so one instruction consumes at least 177 low binary bits and the accepted
language is extraordinarily sparse.  This does not make closure impossible:
when `m'=m`, the exact output coefficient satisfies
`3^(114h+17m)>2^(154h+23m)`, leaving scale with which a self-writer could
replenish its address.  The artifact supplies no
invariant tail language or infinite orbit.  That invariant language—an exact
binary-reader/ternary-writer feedback—is now the constructive target.
Each replay also exposes the complementary canonical ternary rail
`r'=q/(C-D)` and checks the two `S`-unit ladder faces

```text
C^m*w=1+B^h(C-D)r',
D^m'*w'=1+A^h(C-D)r'.
```

The cofactor recurrence and normalized payload recurrence are therefore two
projections of one exact square; a future renormalization must return the
whole square, not merely preserve one arithmetic representation.
Lean commit `5a9324b` independently proves coordinate uniqueness, the
converse from the public balance to the arithmetic `ChargeBouncerStep`
surrogate, and the forward balance from every such step in these coordinates.
It does not alone connect the normalized state to `WordLegal` Collatz
semantics; the separate compiler below audits that descent on bounded members.

```bash
PYTHONPATH=. python3 unit_charge_public_cofactor.py selftest
PYTHONPATH=. python3 unit_charge_public_cofactor.py build unit_charge_public_cofactor_audit.json
PYTHONPATH=. python3 unit_charge_public_cofactor.py verify unit_charge_public_cofactor_audit.json
```

```text
artifact SHA-256      2a12e1d9c3493e5cfbdb0fe903f3d5aec445e7c2b99b52edfbd44f1fb422e2d7
verifier file SHA-256 89030b15382b3ad469869b69dc3aeff7859898ef3b0631140e501464a2bcd32b
```

## Bounded literal charge-bouncer semantic compiler

`unit_charge_semantic_compiler.py` repairs the final semantic seam.  The
normalized `y` is not itself the Collatz state, and the glider worker's
historical `ordinary_start` field is still the intermediate breakoff state
`k`.  The complete coordinate chain is

```text
y -> charge packet -> unit packet -> level-two packet
  -> level-one packet -> breakoff k -> literal odd Collatz state.
```

The finite substitution grammar is

```text
charge cell N      -> unit cells [N,1]
level-two cell N   -> level-one gliders [1,2,1^N]
level-one glider N -> breakoff gates [E,H,E^N].
```

The final gate layer calls `router_breakoff.literal_step` and concatenates
its valuation words.  A separate direct accelerated replay recomputes every
`v2(3*x+1)` and endpoint without trusting the hierarchy labels.  The default
artifact covers all 27 branches with `1<=m,h,m'<=3`, two members each: 756
glider macros, 4,968 breakoff macros, and 14,057 accelerated instructions.
All 54 literal endpoints equal the router-decoded target and are strictly
larger.  This is bounded exact regression, not a universal Lean composition
theorem or an infinite orbit.

```bash
PYTHONPATH=. python3 unit_charge_semantic_compiler.py selftest
PYTHONPATH=. python3 unit_charge_semantic_compiler.py build unit_charge_semantic_compiler_audit.json
PYTHONPATH=. python3 unit_charge_semantic_compiler.py verify unit_charge_semantic_compiler_audit.json
```

```text
artifact SHA-256      8311baf98156759a3a7d3cb8e898deb240afab01ad435efdb46143c01da9b17c
verifier file SHA-256 4c8c73605b9d809919fb50a839f8c504a4cbca8f483a43b97a9ea3acacb84f30
```

## Determinant-four resonant phase conjugacies

`unit_charge_resonant_conjugacy.py` uses the exact exponent resonance

```text
(m,h,m') -> (m+2622k,h-391k,m'+2618k).
```

It preserves the public-tail exponents `P,Q` but displaces source and target
defect phases by `4k`.  Parallel branches
`F_i(t)=(3^Q*t+kappa_i)/2^P` admit an integral affine conjugacy
`E(t)=s*t+c` whenever

```text
gcd(kappa_a,3^Q-2^P) | kappa_b.
```

The artifact exactly constructs the first phase-down pair
`(1,392,1) -> (2623,1,2619)` and phase-up pair
`(1,392,5) -> (2623,1,2623)`.  Their embeddings have 21,330-digit slopes and
intercepts.  It checks the conjugacy identity, source-cylinder and output-tail
embeddings coefficientwise, then replays two members of all four branches
through the arithmetic bouncer formula.  This is a genuine public-tail
glider cell, not a telescoping self-map, literal semantic theorem, or infinite
orbit.  Fixed periodic bouncing is already obstructed.  Lean commit `466e381`
also closes every constant positive phase-up jump: the linked public cofactor
ray is a Väänänen--Wallisser partial-theta value and is nonordinary under that
inspected 1989 external theorem.  The open problem is a genuinely variable,
payload-generated direction/jump rule whose forced 2-adic debris series
telescopes to an integer.

The natural coboundary has a strict opcode type.  In cofactor coordinates,
with `tau_m=3^(-17m)`, `beta_m=2^(-23m)`, every public step is

```text
w-tau_m = (2^(154h+23m')/3^(114h+17m))*(w'-beta_m').
```

Thus both the up and down cells are ternary-entry to binary-exit operations;
they are not complementary merely because their phase motions have opposite
signs.  Every internal word boundary pays
`tau_m-beta_m<0`, the normalized defect polynomial `-H_m`.  The next useful
computation is therefore an affine-conjugacy or paired-rail **adapter** which
supplies the opposite correction, not a blind enumeration of four-letter
jump words.

```bash
PYTHONPATH=. python3 unit_charge_resonant_conjugacy.py selftest
PYTHONPATH=. python3 unit_charge_resonant_conjugacy.py build unit_charge_resonant_conjugacy_audit.json
PYTHONPATH=. python3 unit_charge_resonant_conjugacy.py verify unit_charge_resonant_conjugacy_audit.json
```

```text
artifact SHA-256      e3db4d58871f3a8b0493969405ad4f29ca1e2f4e988eda0038eb578f78a333b1
verifier file SHA-256 70666b9ff3a47436a3fd45003af37b631c7c592b913ee94201f0fdc24deb362c
```

## Two-opcode phase-swap conjugacy

`unit_charge_phase_swap_conjugacy.py` implements the first word-level answer
to the resonant separation loss.  For

```text
W_r=[(r,h0,L-r),(L-r,h1,r+d)],
```

the consecutive words `W_r,W_(r+d)` differ at their boundary phases by
`(+d,-d,+d)` and have exactly the same total tail gains

```text
Q=114*(h0+h1)+17*L,
P=154*(h0+h1)+23*(L+d).
```

The internal sign reversal means the two charts cross, then recover their
original separation at the exponent level; this is the minimal escape from
the one-cell `2622k -> 2618k` contraction.  The default artifact constructs

```text
W_1 : 1 -> 3 -> 2,
W_2 : 2 -> 2 -> 3,
W_3 : 3 -> 1 -> 4
```

with `L=4,d=h0=h1=1`.  Both adjacent pairs have `P=423,Q=296` and composite
constant gcd one against `3^296-2^423`.  The verifier exactly compiles each
nested two-branch source cylinder, constructs a positive integral affine
conjugacy, checks both cylinder faces coefficientwise, and replays sixteen
arithmetic bouncer steps.

The same artifact now checks why these squares are not yet a glider handoff
*along the conjugacy*.  For both comparisons, the conjugacy-selected next
input is

```text
rho_next+2^P*(v0+s*u),
```

while the current output is `sigma_current+3^Q*u`; both the constant
difference and the coefficient difference `2^P*s-3^Q` are strictly positive.
Thus the parallel embeddings are not consecutive states of one orbit.

The two word-rays themselves are not disjoint.  The direct handoff equation

```text
sigma_current+3^Q*u = rho_next+2^P*v
```

has a coprime solution lattice
`u=u0+2^P*t`, `v=v0+3^Q*t`.  The version-two artifact constructs positive
base solutions for both adjacent pairs and replays two members of each,
adding sixteen linked arithmetic-bouncer steps.  These are finite CRT
compiler layers, not conjugacies or a self-reproducing address mechanism.
The artifact does not prove universal literal semantics, a typed adapter, a
turnaround, an infinite orbit, or a counterexample.

```bash
PYTHONPATH=. python3 unit_charge_phase_swap_conjugacy.py selftest
PYTHONPATH=. python3 unit_charge_phase_swap_conjugacy.py build unit_charge_phase_swap_conjugacy_audit.json
PYTHONPATH=. python3 unit_charge_phase_swap_conjugacy.py verify unit_charge_phase_swap_conjugacy_audit.json
```

```text
artifact SHA-256      1dcd6feacc137fc04db60de43d3ea70bab1253220e2708bbed4ce5af05acd5ab
verifier file SHA-256 4352e4d7a6637e4e8407c28c916a63dc84ac966e66ebd28839cbf3e09af90f9b
```

## Three low-description aperiodic bouncer clocks

`unit_charge_morphic.py` tests whether merely replacing a fixed opcode by a
familiar aperiodic binary word solves the ordinary-address problem.  Its
three clocks are Thue--Morse, period doubling, and the Fibonacci substitution
fixed word `0 -> 01, 1 -> 0`.  The symbols are mapped injectively to all
ordered distinct pairs among the 16 bouncer opcodes

```text
(m,h),       1<=m,h<=4.
```

For every coding and every prefix through 48 transitions, the worker compiles
the literal charge-macro word, links the endpoint to the next defect selected
by the word, and computes the canonical least positive fixed-form address
`y`.  Consecutive canonical addresses must eventually become equal if the
infinite nested cylinders are realized by one ordinary natural.

```bash
python3 unit_charge_morphic.py selftest
python3 unit_charge_morphic.py build unit_charge_morphic_audit.json
python3 unit_charge_morphic.py verify unit_charge_morphic_audit.json
```

The audit checks

```text
3 sequences * 240 injective codings * 48 prefixes = 34,560 prefixes.
```

It finds zero address stabilizations.  The closest event is period doubling
with `0 -> (4,4)`, `1 -> (3,4)` at depth 48: consecutive addresses share
33,128 low bits but grow from 33,386 to 34,092 bits.  This is an exact bounded
failure of three named fixed two-opcode clocks.  It is not a seed census and
does not exclude larger alphabets, other morphisms, unbounded substitutions,
or arithmetic opcodes generated by the odd payload itself.

```text
artifact SHA-256      6beff79aa6fe363f4bbe7cd84a42d7cd69c232bbb13ac1d610201dd4927c52dc
verifier file SHA-256 c823867bccbc2001c4a3d3c58d4dbd32741f362eced027ed16a5fb7cbf7893b3
combined source SHA   8103734360b9d601a3f2032a283bed30fc84ae3930eb661cf564e3c53cf0ccfb
```

## Zero-extension audit for the charge bouncer

`unit_charge_zero_lift.py` tests the exact seam between a finite bouncer word
and one more block.  If the compiled word is

```text
K=R+2^P*t -> K'=S+3^Q*t
```

then linking a next input progression restricts the old tail to
`t=rho+2^E*u`.  The case `rho=0` says that the current canonical output `S`
already belongs to the next block's input progression, so the least ordinary
address survives one more extension unchanged.  Lean proves that an ordinary
infinite realization would require this zero case eventually.

```bash
python3 unit_charge_zero_lift.py selftest
python3 unit_charge_zero_lift.py build unit_charge_zero_lift_audit.json
python3 unit_charge_zero_lift.py verify unit_charge_zero_lift_audit.json
```

The artifact exhausts all bouncer words through depth four over the 16
opcodes `(m,h)` with `1<=m,h<=4`, and tests every next opcode:

```text
prefixes by depth:          16, 256, 4,096, 65,536
extension tests by depth:  256, 4,096, 65,536, 1,048,576
total prefixes:            69,904
total extension tests:     1,118,464
zero extension lifts:      0
```

The closest nonlift is the word
`[(1,3),(3,3),(4,1),(4,2)]` followed by `(1,1)`; it shares 16 low
bits while the next input requires 177.  The maximum terminal public
valuation by depth is `3,9,13,16`.  This is an exact finite grammar audit,
not an all-depth nonzero-lift theorem, and the growing valuations rule out
claiming a simple fixed-modulus mismatch from these data.

```text
artifact SHA-256      1c6f863dbe2c83adda3821bcd7f1f082c2e08e0880b708630640196af3568988
verifier file SHA-256 b71feafab1c56e80b27e8e006eae640056831a249ab9cb427113e52526bbd33f
combined source SHA   89c9042bec42ee3662f947d738262512518ce2a92134fe99a3d8058476e80da6
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

## Ether-counter successor dynamics and finite zero-tail transition

`breakoff_ether_dynamics.py` links the autonomous branches without hidden
gate metadata.  If the length-`n` branch tail is `q`, intersecting its output
packet with the length-`m` input cylinder gives the exact all-parameter law

```text
q  = a_(n,m) + 2^(8m+15)*t,
q' = b_(n,m) + 3^(6n+11)*t.
```

For a whole prefix the worker maintains

```text
initial tail = A+2^B*u,
current tail = C+3^P*u.
```

An extension with new address digit zero means that the canonical member
`u=0` already executes the next branch.  For an ordinary natural, however,
extension digits must eventually be zero merely because its binary expansion
ends.  One zero digit is therefore not evidence of counter writing.

The default artifact constructs and coefficient-checks all `160^2=25,600`
branch-pair cylinders at tails zero and one.  It then exhausts all
`160^3=4,096,000` canonical three-branch prefixes for a zero-cost extension
to the minimum-width branch one.  There is exactly one:

```text
branches        115 -> 59 -> 9 -> 1
address widths  487, 87, 23
address digits  253011375082594840946181492673896274035460390409773499439088332045860417958511512792922515817364797677003558821916246716044707729607838737010028739,
                103202970569942805738160702,
                0
```

The edge multipliers provide exact expanding tail slopes:

```text
edge       floor(log2 multiplier)   address width   log-scale excess
115->59             1111                 487               624
 59->9               578                  87               491
  9->1               103                  23                80
```

The resulting initial packet has 455 decimal digits and its public register
has 463.  The verifier executes the public partial map, reconstructs every
branch tail, and independently calls the returning-glider replayer.  The four
steps expand into 192 linked affine members and 384 literal gate macros.  The
ordinary endpoints link exactly.  The next public register has `v2=2`, so the
ether counter halts after branch one.

The initial tail has bitlength `574=487+87`; the 23-bit zero address begins
exactly after its last nonzero bit.  It is binary padding at source exhaustion,
not independently regenerated storage.  The exact finite path is not an
infinite orbit, and the bounded uniqueness statement excludes neither other
next branches nor longer prefixes.  A real ordinary escape requires an
infinite deterministic itinerary after the canonical address digits become
permanently zero.

```bash
python3 breakoff_ether_dynamics.py selftest
python3 breakoff_ether_dynamics.py build breakoff_ether_dynamics_audit.json
python3 breakoff_ether_dynamics.py verify breakoff_ether_dynamics_audit.json
```

Artifact SHA-256:
`a2b0eeddb2667c0eb74305405585f479e2a861923cb01a7fc117c9c13a14395f`.
Verifier SHA-256:
`f5c93af8af44fd7f789feaa92dd738d253c9a8e0d916a0040a29c947855f7497`.

## Arithmetic ether counters and the partial-theta obstruction

`breakoff_ether_linear_theta.py` tests the most direct unbounded public
counter: prescribe `n_t=n_0+k*t` with fixed `n_0,k>=1`.  If

```text
Y_t=2^(8n_t-5)h_t,
```

then the autonomous public map gives exactly

```text
2^(8n_(t+1)+15)h_(t+1)=3^(6n_t+11)h_t+51.
```

Backward unrolling produces the unique 2-adic candidate

```text
h_0=-51/3^(6n_0+11) *
    F(2^(8k)/3^(6k), 2^(8(n_0+k)+15)/3^(6(n_0+k)+11)).
```

The coefficient identity

```text
F(2^(8k)/3^(6k),z)
 = f_(3^(6k)/2^(8k))((3^(6k)/2^(8k))*z)
```

turns the paper argument into the `k`-independent rational

```text
alpha=2^(8n_0+15)/3^(6n_0+11).
```

The Väänänen--Wallisser full-source theorem applies with
`ell=1,sigma=0,p=2`.  Its elementary hypotheses are uniform: the theorem base
is reduced and has 2-adic absolute value `2^(8k)>1`; `alpha` is nonzero; and
the exact size chain uses

```text
2^8>3^5,
3*8=4*6,
45<64.
```

Accepting the cited theorem, the candidate is irrational in `Q_2`, hence not
an ordinary integer.  The external theorem is not reproved here.

The default artifact separately compiles and executes all 16 schedules with
`1<=n_0,k<=4` through eight transitions.  It checks their exact public
odd-part recurrence, finite rational partial-theta identity, and terminal
2-adic residue.  The symbolic theorem audit compares 4,096 coefficients and
applies to every `n_0,k>=1`.

```bash
python3 breakoff_ether_linear_theta.py selftest
python3 breakoff_ether_linear_theta.py build breakoff_ether_linear_theta_audit.json
python3 breakoff_ether_linear_theta.py verify breakoff_ether_linear_theta_audit.json
```

Artifact SHA-256:
`9190bf6ea1a85d3bffc81c9f066a3af8e96529fc75267b147096c3e2c2491dc2`.
Verifier SHA-256:
`1a53504df1091e65054c5647b6ef59ff2ed04f4ca58840604de277469821b7a5`.

## Periodic-increment ether counters

`breakoff_ether_periodic_theta.py` moves from a constant-rate branch counter
to a repeated word of integer increments.  After one successful public step,
the odd part is exactly `3*u`, and the literal recurrence becomes

```text
2^(8*n_(t+1)+15)u_(t+1)=3^(6*n_t+11)u_t+17.
```

For a period-`L` increment word with positive cycle sum `K`, including words
with down-steps inside a cycle, the backward term at `j=L*q+r` splits as

```text
T_(L*q+r)=T_r Q^choose(q,2) R_r^q,
Q=2^(8*K*L)/3^(6*K*L),
R_(r+1)/R_r=2^(8*K)/3^(6*K).
```

The corresponding `L` paper arguments are pairwise separated modulo powers
of the common theta parameter.  For the ether exponent ratio, the exact
Väänänen--Wallisser size audit passes at period two,

```text
gamma<1/6<Gamma(2,0),
```

but fails already at period three:

```text
Gamma(3,0)<5/32<gamma.
```

Thus period three is the first escape from this particular sufficient
external theorem; it is not evidence for an ordinary orbit.  Companion commit
`11eaba0` kernel-checks the generic period-two EC17 bridge and its exact
external independence seam.  Accepting the cited theorem, every
positive-mean period-two increment tail is impossible.

The bounded artifact compiles and literally executes 15 public schedules,
including positive-mean words with negative increments, through nine EC17
transitions.  It checks every finite rational and 2-adic backward identity
and 624 residue/theta coefficients.

```bash
python3 breakoff_ether_periodic_theta.py selftest
python3 breakoff_ether_periodic_theta.py build breakoff_ether_periodic_theta_audit.json
python3 breakoff_ether_periodic_theta.py verify breakoff_ether_periodic_theta_audit.json
```

Artifact SHA-256:
`2d1e80094f494776f6a6fb3338a41403e806695db34b8feffab98ce391962f68`.
Verifier SHA-256:
`e0c29f74b3c4b34513309f056428a4767faa9d30e860177be9a570b8689e65cc`.

## Exact period-three ordinary-core sieve

`breakoff_ether_period3_sieve.py` tests the necessary ordinary-stabilization
condition at the first theta-theorem escape.  It does not scan unrelated
Collatz seeds.  For every prescribed period-three increment word, EC17 has
one forced initial residue `r_P modulo 2^P`.  If an ordinary core were smaller
than `2^P`, it would equal the least representative `r_P` exactly.  The worker
therefore executes that representative with exact integers; a failed required
division rules out every ordinary core below `2^P` on that schedule.

The default committed artifact was run and independently re-verified on the
32-core Akdeniz host.  It exhausts all genuine period-three words with
increment components in `-8..8`, positive cycle sum, and positive schedules
starting at branches `1..32`, at precision 4,096 bits:

```text
period-three increment words     2,340
positive start/word schedules   72,156
least-residue failure steps       7..47
largest leading-zero run             16 bits
ordinary-core lower bound          2^4096
```

All 72,156 least representatives fail.  The lower-bound bridge has also been
sent to the companion Lean worker as QM57--QM59.  The result is finite and
boxed: a larger core, a word outside the bounds, or a non-periodic controller
is not excluded, and no counterexample is claimed.

```bash
python3 breakoff_ether_period3_sieve.py selftest
python3 breakoff_ether_period3_sieve.py verify \
  breakoff_ether_period3_sieve_audit.json --jobs 32
```

Artifact SHA-256:
`bd7cf4b64a68c8146a6144c37d3a20098e2b84285a75bec2d2f393944f71848b`.
Verifier SHA-256:
`82ac3a9e463a95c573c4f8f30aa66eac420cf89bd85de40869a5e10fd2908d56`.

## Normalized period-three residue and CRT audits

The normalized workers replace raw precision widening by the kernel-checked
sharp quadratic bit budget.  For a positive-gain period-three schedule put

```text
A(q)=q*(462*B+2235+K*(693*q-3141)),
U(q)=ceil(A(q)/306).
```

`breakoff_ether_period3_normalized_margin.py` computes the future-forced
residue at precision `U(q)+R`, with `R=2*q+32`.  Its exact replay failures
invoke QM104: every checked failure forces the one fixed initial-core bit
length to exceed `R`.  `breakoff_ether_period3_normalized_crt.py` instead
uses precision `U(q)` and combines the future residue with the immediate
predecessor congruence modulo `3^(6*n_previous+11)`.  A failed canonical CRT
replay invokes QM106 and forces that whole ternary exponent below the fixed
initial bit length.  The replay-free CRT margin is separately bounded by the
same initial bit length (QM108).

The committed artifacts use the theorem-relevant dyadic horizon
`q=5,8,16,32,64,128,256,512`.  They exhaust the nine genuine positive-gain
words in `[-1,1]^3` and every positive start through branch eight:

```text
positive schedules                                 71
exact rows per artifact                           568
all normalized future residues failed replay      yes
weakest schedule-wide residue lower bound        1,057 bits
all normalized CRT representatives failed replay  yes
weakest schedule-wide CRT lower bound            3,084 bits
smallest schedule-maximum CRT margin             4,885 bits
largest measured CRT margin                      9,832 bits
counterexample                                    null
```

Both artifacts were generated and independently reconstructed on Akdeniz;
the verification commands recompute every integer rather than trusting row
hashes.  This is finite evidence only.  It neither proves that the failures
continue cofinally nor constructs an ordinary orbit.

```bash
python3 breakoff_ether_period3_normalized_margin.py selftest
python3 breakoff_ether_period3_normalized_margin.py verify \
  breakoff_ether_period3_normalized_margin_audit.json --jobs 30

python3 breakoff_ether_period3_normalized_crt.py selftest
python3 breakoff_ether_period3_normalized_crt.py verify \
  breakoff_ether_period3_normalized_crt_audit.json --jobs 30
```

Normalized-margin artifact SHA-256:
`2c51f510e4b86f0fafae489df8ad54749eb78e4aadf70511dcf5b0bcd073b720`.
Normalized-margin verifier SHA-256:
`934579c9d5253a3c40d662c98e8a8c663b461e0cc78927dafe8a1b0d9e4de345`.

Normalized-CRT artifact SHA-256:
`f0754083c04d5912b7719f6f7c72455905d7eb23d265efde2eeb9b5d612da20c`.
Normalized-CRT verifier SHA-256:
`3e4e4e89ae6e072f07529a690bb3cd40535585b65f1d7752c6a83eaf3b03079b`.

### Tight 971-budget raw-residue audit

`breakoff_ether_period3_tight_residue.py` implements the cheaper endpoint
made available by companion commits `5a3413a` and `78a6d05`.  The exact
separator `3^971<2^1539` defines

```text
G1(q)=q*(1466*B+7092+K*(2199*q-9967)),
V(q)=ceil(G1(q)/971).
```

Lean proves that a hypothetical ray eventually has `core(3q)<2^U`, so its
normalized CRT lift must eventually be zero.  Lift zero is equivalent to the
raw `U`-bit future residue satisfying the immediate predecessor congruence.
The worker therefore needs no product-modulus CRT construction.  It computes
one residue at precision `P=U+2*q+32`, masks its low `U` bits, and tests both
representatives directly against

```text
2^(8*n_q+15)*residue = 17 (mod 3^(6*n_previous+11)).
```

On the same 71-schedule, 568-row dyadic box through `q=512`, every normalized
and every padded residue fails the full predecessor congruence.  Among the
normalized residues, 350 already fail the necessary first-trit test
`residue=1 (mod 3)` and 218 match that trit but fail at a higher ternary
digit.  The padded counts are 367 failures and 201 matches.  QM116 turns the
finite failures into the uniform schedule-wise lower bounds below:

```text
weakest normalized lower bound     9 bits
weakest padded lower bound     1,065 bits
counterexample                    null
```

The normalized full-congruence failures are precisely finite nonzero-lift
rows.  They do not prove that nonzero lifts recur arbitrarily late.  The
artifact was independently reconstructed on Akdeniz with 30 workers.

```bash
python3 breakoff_ether_period3_tight_residue.py selftest
python3 breakoff_ether_period3_tight_residue.py verify \
  breakoff_ether_period3_tight_residue_audit.json --jobs 30
```

Artifact SHA-256:
`c964e93d7290832cb61f3beac17892b148b8319096411865e07c9dbb46c2832a`.
Verifier SHA-256:
`e433a8b37ef2273ab91a182d074c16de49f186174f7e7e5616c0e309e98efe41`.

### Fixed-depth phase and normalized-carry audits

Companion commit `a9ed874` proves that the predecessor congruence may be
reduced to any fixed modulus `3^d`, and that its required coefficient has
clock period dividing `3^(d-1)` in the cycle index.  Cofinal failures in one
fixed window exclude the entire prescribed ray.  The exact worker
`breakoff_ether_period3_fixed_depth.py` therefore groups canonical `U(q)`-bit
future residues by these proved clock phases; it does not scan Collatz seeds.

The dense Akdeniz artifact covers all 71 positive schedules in the
`[-1,1]^3`, start-through-eight box and every `q=5..256`, for 17,892 exact
rows.  It was independently reconstructed with 30 workers:

```text
depth  modulus  clock  matches  failures  zero-match cells  schedules w/ no-match
  1       3       1     6,025    11,867          0                  0
  2       9       3     2,014    15,878          0                  0
  3      27       9       635    17,257        218                 69
  4      81      27       217    17,675      1,709                 71
  5     243      81        76    17,816      5,676                 71
counterexample                                                   null
```

Thus modulus 27 is the first discriminating finite window in this box.  It
is not a proof of cofinal failure.  The two schedules with no zero-match
mod-27 phase are `(0,1,1)` from branch 8 and `(1,1,0)` from branch 6; both
acquire many zero-match phases at modulus 81.  QM118 separately proves why a
periodic target alone cannot justify an automaticity or rationality claim:
one sufficiently wide free binary block can hit any prescribed fixed-depth
class.

```bash
python3 breakoff_ether_period3_fixed_depth.py selftest
python3 breakoff_ether_period3_fixed_depth.py verify \
  breakoff_ether_period3_fixed_depth_audit.json --jobs 30
```

Fixed-depth artifact SHA-256:
`c4c93e5db3320803e8f434441bd555601f3ab439638a9b0a82c02adbac91c512`.
Fixed-depth verifier SHA-256:
`b289da2010090ce04cde87efb124fab91c06f247e03dbbbeb28a496b4568b3c8`.

Companion commits `40f4265` and `2e8010c` expose the canonical same-cycle
extension carry.  If `r_(U+D)` is the padded future residue, then

```text
carry_D(q)=r_(U+D) // 2^U.
```

Every hypothetical period-three ray forces this carry to be eventually zero,
for arbitrary covered `D(q)`.  The extension-carry worker measures the first
nonzero bit above `U`; a finite nonzero row is only a direct measurement of
that theorem object, not an irrationality proof.

On the same dense 17,892-row box, the first extension bit is nonzero in 8,869
rows, while every row has a nonzero bit among the first 18.  The longest zero
run above `U` is 17 bits, at word `(0,1,0)`, start branch 3, `q=167`; the next
largest is 16 bits at word `(0,0,1)`, start branch 4, `q=31`.  Thus all 71
schedules have every observed row nonzero by depth 18.  The independently
reconstructed artifact records all 24 extension depths and the exact anomaly
rows.  These finite zero-run statistics do not bound future zero runs.

```bash
python3 breakoff_ether_period3_extension_carry.py selftest
python3 breakoff_ether_period3_extension_carry.py verify \
  breakoff_ether_period3_extension_carry_audit.json --jobs 30
```

Extension-carry artifact SHA-256:
`f05b656c0297a9af416f28f4da5df34d081a281636cf45f3379ae6dc90239978`.
Extension-carry verifier SHA-256:
`4412e1e0db6d79c623809e106b97999c259e1858cb6b2188c2064025bbebd2f6`.

### Consecutive-cycle and balanced construction carries

The fixed-depth block scans are not construction criteria: exact composition
shows that modulo `3^d` a long block retains only its final consecutive carry.
The construction-facing object instead compares adjacent normalized residues.
If `r_q` is the canonical residue at the sharp budget `U(q)`, compose one
three-step cycle as

```text
2^m(q)*y_q=3^Q(q)*r_q+D(q),
p(q)=U(q)-m(q)>0,
r_(q+1)-y_q=2^p(q)*C_q.
```

The exact worker `breakoff_ether_period3_cycle_carry.py` checks the compact
formula, all three literal valuations, canonical low-bit consistency, and the
independent reverse predecessor congruence on every row.  It records backward
transition counts and covered binary mass for every residue; four deterministic
residues per schedule, plus every anomaly, are also reconstructed by an
independent forward-series evaluator.  Companion commit `daae4a8` proves bare
residue reduction/splitting without assuming an orbit and kernel-checks the
generic endpoint that compatible positive three-step factors glue to an
infinite EC17 orbit.  Commit `40835c0` proves the strict defect bound and
abstract balanced-carry equivalence, and `5769c85` proves the exact long-block
last-carry no-go; `122680b` supplies the canonical upper-block range bounds.
Commit `f79192e` proves the displayed three-step identities, specializes zero
carry to the exact replay factor, and constructs an infinite positive EC17
orbit from any eventual zero-carry tail.  Commit `4516a03` promotes the result
to the project's literal period-three `Ray`, and `fff0dec` formalizes the
canonical range gate under which full ternary divisibility forces exact zero
carry.  Commit `732da20` specializes it to the worker's actual logarithmic
precision.  The construction implication and finite-row gate are
kernel-checked; the finite workers simply contain no hit to feed into them.

Companion commits `2cad6e1`/`b518d2b`/`a2e940e` also identify any literal
period-three ray's completed backward series with exactly three
paper-normalized 2-adic theta values and prove that their linear independence
together with `1` excludes the ray.  The relevant published 1989 sufficient
criterion counts three theta values, but its threshold inequality fails here
in the strict reverse direction.  Its parameter orientation and functional
equation are now pinned, so a useful analytic continuation needs a genuinely
sharper special-argument estimate rather than another finite scan.

The dense Akdeniz scan covers all 71 positive `[-1,1]^3`, start-through-eight
schedules and every `q=14..256`, the first common interval with `p(q)>0`:

```text
exact consecutive-cycle rows                         17,253
independent series checkpoint residues                  284
exact zero carries                                        0
full 3^Q predecessor divisibilities                       0
rows with |C| < 3^Q                                  16,870
rows satisfying the zero-forcing exponent gate        8,339
positive / negative carries                     8,748 / 8,505
maximum observed v3(C)                                    8
counterexample                                          null
```

The exact zero-forcing gate is

```text
2^(U(q+1)-p(q)) <= 3^Q(q).
```

Since `D(q)<3^Q(q)`, a carry divisible by `3^Q` cannot be negative; on a gate
row it is also strictly below `3^Q`, so full predecessor divisibility would
force `C_q=0`.  Nearly half the rows therefore reduce to one theorem-facing
full congruence.  None hits it.  The result is a bounded negative construction
audit, not proof that a zero tail cannot begin later.

```bash
python3 breakoff_ether_period3_cycle_carry.py selftest
python3 breakoff_ether_period3_cycle_carry.py verify \
  breakoff_ether_period3_cycle_carry_audit.json --jobs 30
```

Consecutive-cycle artifact SHA-256:
`18e65eb08d8d9960cacd88868779d17fdcca8f6912c97530c76fd91c851b951e`.
Consecutive-cycle verifier SHA-256:
`bb7f53a312a6e7a7362c08743b962a17c516e9a13a250f5bfd6fe04d7640cfed`.

The separate balanced worker makes every hit constructive rather than using
the exclusion budget `U`.  Starting at `P_q=m(q)+h`, it transports

```text
ell_q=floor(log2(3^Q(q))),
P_(q+1)=P_q-m(q)+ell_q.
```

Both high blocks in the carry difference are then strictly below `3^Q`, so
the full congruence

```text
2^m(q)*r_(q+1)=D(q) (mod 3^Q(q))
```

is equivalent to exact `C_q=0`.  A consecutive all-future hit tail would
therefore splice into an infinite orbit.  The exact artifact checks 1,136
precision paths (`h=1..16`) across the same 71 schedules and every
`q=14..60`, for 53,392 rows.  There are zero full-congruence/zero-carry hits,
maximum hit run zero, and `counterexample:null`.  Misses on this deliberately
chosen precision path do not exclude a ray.

```bash
python3 breakoff_ether_period3_balanced_carry.py selftest
python3 breakoff_ether_period3_balanced_carry.py verify \
  breakoff_ether_period3_balanced_carry_audit.json --jobs 12
```

Balanced-carry artifact SHA-256:
`6a619989230c623cecdc8c10b8fb963c1f395568a1e5867d0e0186031cef9187`.
Balanced-carry verifier SHA-256:
`3ffb7f0163b9f73662f9ae43b2a614306741bcdddd30caa1f7ef7658f957d60d`.

Finally, `breakoff_ether_period3_rational_reconstruction.py` probes the actual
2-adic initial values rather than another fixed ternary clock.  At the `q=0`
boundary for all 71 schedules, it reconstructs the canonical residues at
2,048 and 4,096 bits and searches for a repeated reduced pair

```text
a = b*r (mod 2^P),  |a|<=2^512,  0<b<=2^512,  b odd.
```

The exact uniqueness gate `2AB<2^P` holds in every row, and backward and
direct-series residues agree.  There are zero single-precision reconstructions
and zero repeated rational or positive-integer candidates.  This excludes only
the displayed finite height box; it is not an irrationality theorem.

```bash
python3 breakoff_ether_period3_rational_reconstruction.py selftest
python3 breakoff_ether_period3_rational_reconstruction.py verify \
  breakoff_ether_period3_rational_reconstruction_audit.json
```

Rational-reconstruction artifact SHA-256:
`356994f129961e385b0dd6b0423d8ea96c96411c15a19ce501559c1d315bab93`.
Rational-reconstruction verifier SHA-256:
`4dc374208dae1fc21d413c1a9c26569205e37c7d3a06d9e65027a268d6f5c3bb`.

Companion commit `6b96f89` kernel-checks the strongest mod-27 cell's exact
EC17-specific block reduction.
For word `(1,1,0)`, start branch 8, compose nine cycles from a source
`q=0 mod 9`.  With

```text
M=432q+4221,   Q=324q+3051,
2^M*y_q=3^Q*r_q+D9(q),
```

exact reduction gives `2^M=-1`, `D9=14`, and hence `y_q=13 mod 27`, exactly
the required class at cycle `q+9`.  For `q>=99`, put
`p=U(q)-M>0` and

```text
C_q=(r_(q+9)-y_q)/2^p.
```

Then `r_(q+9)=13 mod 27` if and only if `C_q=0 mod 27`.  The exact
`breakoff_ether_period3_nine_cycle_carry.py` artifact verifies the composition,
future-residue consistency, and this equivalence at all 17 sources
`q=99,108,...,243`; the carries modulo 27 are

```text
14,11,5,24,16,3,22,23,12,3,6,19,13,17,18,14,5.
```

Their nonzeroness is still finite evidence.  Algebraically the block carry is
an invertible rescaling of the target-residue discrepancy, so this reduction
identifies an exact all-`q` theorem target but does not itself supply the
missing induction.  Companion commit `6f05ff5` also kernel-checks the analogous
27-cycle/mod-81 budget and carry interfaces for both schedules without a
zero-match mod-27 phase; it does not assert their missing cofinal premises.

```bash
python3 breakoff_ether_period3_nine_cycle_carry.py selftest
python3 breakoff_ether_period3_nine_cycle_carry.py verify \
  breakoff_ether_period3_nine_cycle_carry_audit.json
```

Nine-cycle artifact SHA-256:
`c8358802829067b98fac11d7cc798de5d914cc59f79c219625fce2052fa537c3`.
Nine-cycle verifier SHA-256:
`431483494d073b4bbb7f344ab0bfbd81b96d63512c0d6a840b5d9d502c977522`.

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

## YAH mixed-base loop and morphic-glider certificates

yah_context_loop.py pins the 11 ASCII rules in the primary
Yolcu--Aaronson--Heule artifact and checks two finite nontermination objects:

    u ->+ L u R

    u ->+ L sigma(u) R,
    sigma(lhs_rule) ->+ sigma(rhs_rule) for every rule.

The first derivation repeats by ordinary context closure.  In the second,
every rule-image simulation is required to be nonempty, so applying the
nonerasing morphism sigma produces another nonempty derivation at every
scale.  Either object would prove nontermination of their rewriting system;
their Theorem 3.17 is the explicit external seam from that fact to a false
Collatz conjecture.  Commit `1b3459d` kernel-checks both generic constructions,
including the productive morphic case.  Commit `b733caa` pins the exact
seven-symbol, 11-rule carrier in Lean and specializes both consumers to it.
Commit `442826d` connects traces over this carrier to the context-collapse
filter once the checker-supplied flank equalities are replayed.
No concrete certificate is present.

There is a structural warning on the first form.  For the one-`/`,
one-later-`.` word class, the worker records slash count, dot count,
left-of-slash offset, and right-of-dot suffix length.  All 825,708 raw rule
applications in the complete length-at-most-eight graph preserve these four
diagnostics.  Lean commit `ef1b888` proves generically that a context embedding
which preserves them has empty left and right contexts.  The universal
rule-level bridge is still separate, but this retires proper whole-word outer
growth as the main construction target.  A live glider must rewrite an
internal template, alter its delimiter chart, or reproduce morphically inside
the fixed outer frame.

The worker independently replays the paper's mixed-base trajectory
12 -> 6 -> 3 -> 5 -> 8 -> 4 -> 2 -> 1, checking all 13 literal rewrites,
value preservation at auxiliary steps, and the shortcut-Collatz update at
each dynamic step.  Its first structural audit then gives three exact,
bounded or ansatz-class failures:

- the identity is the unique rule-simulating map among all
  5^5=3,125 delimiter-fixing letter morphisms;
- no rule simulation exists among all 25^5=9,765,625 uniform two-symbol
  digit-block morphisms; exact constraint propagation covers this whole class;
- the induced graph of all 513,916 one-delimiter-pair words of length at most
  eight is acyclic across 694,458 exact edges, and no literal context loop is
  reachable in at most 20 steps from any of the 10,791 cores of length at most
  six while intermediate length is at most 14.

The finite graph is nevertheless highly spatial: its longest path has 299
rewrites, including 52 dynamic steps, and carries the canonical mixed-base
word for 834 to one for 1079 without exceeding eight symbols.  This is a tiny
delay line, not reproduction.  The next language class should be
variable-width, delimiter-changing, or multi-block; simply widening the
literal-word bound is not the primary attack.

For widths at least three, Lean commit `b4a48a6` independently checks the
arithmetic endpoint of the uniform-block no-go:
`eval_3(block)<=2*3^w<4^w=2^(2w)`.  It does not yet prove the preceding
rewrite-theoretic statement that a rule-simulating uniform morphism forces
the relevant image to have exactly that block shape.

    python3 yah_context_loop.py selftest
    python3 yah_context_loop.py build yah_context_loop_audit.json \
      --max-graph-length 8 --max-seed-length 6 \
      --max-steps 20 --max-path-length 14
    python3 yah_context_loop.py verify yah_context_loop_audit.json
    python3 yah_context_loop.py check-loop candidate.json

    artifact SHA-256  6056acc0571af5199aebbe98fff34fe43ec512a5a71b00c4ed087e816c2aac2b
    worker SHA-256    fd3bb7aff3922d4c5f8a927166deed462c557d2216302ac66e0d52efc04c89ab

## YAH carry defect and two-block counter opcode

`yah_carry_opcode.py` isolates a near-symmetry hidden by the first loop audit.
Complementing both binary digits and the outer ternary digits, while fixing
ternary one, permutes the six auxiliary A-rules exactly.  At the terminal
boundary the complemented even rule would require

    bin1 V  ->  V bin0.

If `V` has affine pair `(s,t)`, the two sides have the same slope but intercept
difference `s-t`.  Every finite digit word satisfies `s-t>=1`; equality holds
exactly for a word of maximal digits.  The default artifact exhausts all
488,281 words of length at most eight and checks both facts exactly.  The
general inequality is an elementary induction, not inferred from that bound.

For a saturated ternary buffer, the one-unit defect becomes a literal counter
instruction:

    bin1 tri2^n . ->+ tri2^(n+1) .

Together with the left boundary it gives

    / tri0^k tri2^n . ->+ / tri1^(k-1) tri2^(n+1) .

for `k>=1`.  The second macro uses exactly one dynamic step, implements
`2*y=3*x+1`, and is strictly outward.  The artifact replays every run through
128 and every `1<=k<=32, 0<=n<=32`, along with the zero-run pass and the
two-dynamic identity

    / tri1 tri2^n . ->+ / (tri0 tri2)^ceil(n/2) .

There are 1,443 exact bounded macro cases.  These are executable instructions,
not closure: the increment spends a left `tri0` token and phase-changes the
remaining block.  A counterexample still needs a contextual recharge which
regenerates that token from the incremented right counter.

    python3 yah_carry_opcode.py selftest
    python3 yah_carry_opcode.py build yah_carry_opcode_audit.json \
      --max-affine-length 8 --max-run 128 --max-transfer 32
    python3 yah_carry_opcode.py verify yah_carry_opcode_audit.json

    artifact SHA-256  2f1fa472db827f5eeec746d31c993dd1806a7ea9510b4ad4055c5850ad11d9b8
    worker SHA-256    bcf2549d767db12be3e769eca9d9e7f3fa2a89768367cbd5a78c2e2f675f675c

## YAH queue macros and the nonlocal reproduction type

`yah_queue_macro.py` independently factors a complete left-boundary macro
into a two-state base-three quotient transducer.  Writing `Q_c` for a sweep
with incoming carry `c`, including the terminal `2` deposit when its outgoing
carry is one, the three head opcodes are

    M(0v)=Q_1(v),
    M(1v)=Q_0(Q_0(v)),
    M(2v)=Q_0(Q_1(v)).

The worker implements this table directly and also constructs the same macro
one literal B/A/DT rewrite at a time.  Its default artifact compares both
semantics on all 88,572 nonempty ternary words of lengths one through ten.
At every word it independently checks the represented shortcut-Collatz
values, terminal parities, and exact space balance

    len(M(w))-len(w) = number_of_odd_sweeps-1.

For all `3^m` words of a fixed trit length `m>=1`, the resulting exact census
is

    shrink  = 3^(m-1),
    neutral = (3^m+1)/2,
    grow    = (3^(m-1)-1)/2.

Thus only asymptotic density `1/6` reproduces a cell, and the uniform mean
length change is `-1/6-1/(2*3^m)`.  The artifact checks these closed counts at
each of its ten exhaustive lengths; the all-length formula is a residue-count
induction rather than a statistical estimate.

This yields a nonlocal instruction type.  A zero head never grows.  A head
one or two grows by one exactly when the represented value is `3 mod 4`.
Because `3=-1 mod 4`, that enable bit is the alternating signed checksum of
all trits, including the slash's implicit leading one.  The opcode is therefore
a local head combined with information spread across the entire digit span.

The worker also checks the exact recharge ledger.  With

    Battery(w)=2*len(w)+v2(value(w)+1),

every growing macro conserves `Battery`: its new trit consumes exactly two
units of `v2(value+1)`.  The non-growing head/residue cases have changes

    v2(D+1)-3,  -1,  v2(D+3)-4,
    v2(3D+2)-3,  or  v2(D+1)-2,

with `D=value+1`, as recorded by the artifact.  Those exceptional divisibility
events are the only literal recharge sites.  This turns “regenerate the
reservoir” into an exact potential inequality rather than a visual metaphor.

The same artifact literally replays 16,769 members, through coordinate 64,
of the carry-transfer and chained comb identities.  In particular,

    M(1^(2q) 2^n)   = (01)^(q-1) 0 1^(n+1),
    M(1^(2q+1) 2^n) = (01)^q (02)^ceil(n/2).

Thus the spent zero reservoir becomes a distributed alternating comb; it is
not simply erased.  This is a structural opcode compiler, not closure.  A
counterexample still needs a type cycle that repeatedly restores a nonzero
head and checksum three with positive net space charge.

One further macro is already a finite four-phase packet compiler.  On the
family `2 (0012)^s (01)^q`, each input block advances a public phase modulo
four.  At phases `0,1,2,3`, block `0012` emits respectively
`0210,1112,2022,0001`, block `01` emits `02,11,21,00`, and the final carry
suffix is `1,2,22,empty`.  The macro therefore grows exactly when
`s+q=2 mod 4`.  This is an exact chained opcode with a distributed block-count
address, but its output blocks do not yet close back to the input alphabet.

    python3 yah_queue_macro.py selftest
    python3 yah_queue_macro.py build yah_queue_macro_audit.json \
      --max-length 10 --max-coordinate 64
    python3 yah_queue_macro.py verify yah_queue_macro_audit.json

    artifact SHA-256  865cf4fffcc00fbfbf722dae309a32056b2d140da31e77f78751c12c652f3f09
    worker SHA-256    dd31ba052f11102ad0b9cc6dc13278c0254c8366ddb39f5b01c96a519b305745

## YAH recharge amplifier and lossless lift register

`yah_recharge_amplifier.py` specializes the phase-one packet to

    P(q)=2(01)^q.

For a requested finite gain `G>=1`, put `K=4G+1`.  There is one address
`q=q0 mod 2^(K+2)` satisfying

    41*9^q+15 = 0 mod 2^(K+5),

and its low bits give `q=1 mod 4`.  The packet macro is therefore neutral in
length, while its endpoint has `v2(N+1)>=K`.  Follow the maximal sequence of
whole queue macros which uses only odd shortcut steps.  It contains at least
`K-1=4G` odd steps.  If its ternary-length gain were at most `G-1`, comparison
of the endpoint scale `(3/2)^J` with the canonical ternary intervals would
give

    3^(4G) < 2^(4G+1)*3^(G-1),

contradicting `2*16^G <= 3*27^G`.  Thus arbitrarily large *finite* program
space can be regenerated by formula.  This is not an infinite orbit.

The unused congruence lift is a genuine nonlocal register.  With
`L=2^(K+2)`, define

    A_K(t)=3*(41*9^(q0+L*t)+15)/2^(K+5).

LTE gives the exact identity

    v2(A_K(t)-A_K(u))=v2(t-u).

Hence `t -> A_K(t)` permutes every finite binary residue ring: the amplifier
does not erase its free address.  A counterexample compiler would have to
decode this surviving register into the next packet address autonomously.

There is also an exact spatial output.  Since `q>=1`,
`v3(41*9^q+15)=1`; hence the normalized endpoint defect has `v3=2`.  After
`J` safe odd shortcut steps its defect has `v3=J+2`, so its ternary word ends
in exactly `J+2` maximal trits.  The finite worker checks this exact reservoir
length at every displayed trace.  The live decoder may therefore use both an
arbitrary prefix register and a clean right-hand `2` reservoir.

The default artifact constructs 32 exact symbolic addresses.  For each of
the first four it exhausts all 1,024 lift residues modulo `2^10`.  It also
replays the exact queue transducer on packets of 35, 547, 41,507, and 369,187
trits, guaranteeing gains 1--4 and observing gains 2, 3, 5, and 6.  The
all-parameter scale and LTE statements are algebraic proof schemas pending
independent Lean replay; the stated word traces and finite permutations are
the artifact's machine-checked scope.

    python3 yah_recharge_amplifier.py selftest
    python3 yah_recharge_amplifier.py build yah_recharge_amplifier_audit.json \
      --max-symbolic-growth 32 --max-literal-growth 4 --register-bits 10
    python3 yah_recharge_amplifier.py verify yah_recharge_amplifier_audit.json

    artifact SHA-256  3969fab7fc0b5ed38972afc7b3ed6a9cabfcb4ae1447b27db4093afb8aa54c3d
    worker SHA-256    6100b2c33f35f26e0fc7874c7981829f9733a234c60576739e1fc6fa41637a75

## YAH lift-register bit decoder

`yah_lift_decoder.py` resolves the first post-amplifier decoder instruction
at the smallest nontrivial address depth.  Set

    q=17+128*t,
    P_t=2(01)^q.

Exact composition of the two-state quotient transducer gives

    M^4(P_t)=U V^t Z,

where the generated lasso has prefix/block/suffix lengths `31,256,6`.  The
block length is not accidental: `ord_(2^10)(3)=256`.  Each of the four
symbolic macro compositions checks that its repeated block fixes the entering
carry, which is a finite-state certificate of the identity for every natural
`t`.

The endpoint defect is

    D(M^4(P_t))=3^7 R(t),
    R(t)=(41*9^(17+128*t)+15)/(3*2^10).

The register isometry makes `R(t)=t mod 2`.  The fifth macro has head zero and
is therefore an exact LSB-first branch:

    R=2r:    3^7 R-1 -> 3^8 r-1,
    R=2r+1:  3^7 R-1 -> (3^7 R-1)/2.

On zero, the terminal carry is one, the length is neutral, and the clean
right reservoir grows from seven to eight twos while the register shifts.
On one, the terminal carry is zero, one cell is lost, and the reservoir is
consumed in a chart-changing collision.  The repeated 256-trit block flips
the sweep carry, so the worker constructs the exact parity split

    t=2s   -> U_0 V_0^s Z_0,   lengths 30,512,7,
    t=2s+1 -> U_1 V_1^s Z_1,   lengths 286,512,6.

The default artifact independently materializes and checks every parameter
`0<=t<=64`: 33 zero branches and 32 one branches, including exact integer
values, carries, length charges, trailing-reservoir sizes, and word hashes.
The finite-state block identities are all-parameter proof schemas; Lean replay
has been requested.  A thin bit-one cylinder is routed back to recharge by the
restorative worker below, but the full branch and recurrent type graph remain
open; this is an instruction decoder rather than a counterexample.

    python3 yah_lift_decoder.py selftest
    python3 yah_lift_decoder.py build yah_lift_decoder_audit.json \
      --max-parameter 64
    python3 yah_lift_decoder.py verify yah_lift_decoder_audit.json

    artifact SHA-256  7ca77895ea65644857c920835fecbba5b35520416867b04960b2e4ff0d1b01a5
    worker SHA-256    db4b19a53c40e7d7c5b250b71e938741ed9b1ee68d3a11248f416b17c9f8ca10

## YAH restorative bit-one opcode

`yah_restorative_decoder.py` continues the decoder's bit-one branch on the
exact source cylinder

    t=91+256*u,
    s=45+128*u,
    q=11665+32768*u.

Here the incoming stripped register satisfies `R=151 (mod 256)`.  Since
`3^6*151+1=0 (mod 256)`, the bit-one collision is followed by a neutral
recharge with returned register

    R_next=(3^6*R+1)/2^8.

The recharge state has defect `9*2^5*R_next`.  Three subsequent safe queue
macros use five odd shortcut steps and return with defect `3^7*R_next`.
Relative to the incoming decoder state, the complete five-macro instruction
gains exactly one ternary cell, returns to head zero, and rebuilds exactly
seven trailing `tri2` symbols.  The macro terminal carries are

    [0], [0,1], [1], [1,1], [1,1].

The worker constructs every stage as an all-parameter finite-state lasso.
Their prefix/block/suffix lengths are

    incoming       23327,65536,6
    bit-one        23326,65536,6
    recharge       23325,65536,7
    safe-1         23324,65536,8
    safe-3         23323,65536,10
    returned       23322,65536,12

The 65,536-trit block at the return is not the incoming block.  Thus this is
an exact regenerative instruction, but not a recurrent type cycle.  Companion
commit `f96e621` goes further: it kernel-checks that the returned register lies
strictly between two consecutive registers of the original decoder chart, so
no reindexing can identify the two families.  Commit `0da1058` also proves
that no positive ordinary register can eventually repeat only the affine
update `256*R_next=729*R+1`; any recurrent chart component needs more than
this single edge map.

The default artifact independently materializes and verifies `u=0,...,4`,
including exact integer values, carries, defects, word lengths, seven-trit
reservoirs, and hashes.  Its all-parameter component is the generated lasso
certificate plus the modular source-cylinder identities; a finite recurrent
chart graph and an infinite ordinary Collatz orbit remain open.

    python3 yah_restorative_decoder.py selftest
    python3 yah_restorative_decoder.py build yah_restorative_decoder_audit.json \
      --max-parameter 4
    python3 yah_restorative_decoder.py verify yah_restorative_decoder_audit.json

    artifact SHA-256  2346f0b87c15d8a7c336be2b7f5dbcb2003c58bc2435d88344715ff27054638a
    worker SHA-256    2f8e835e100a5041b17a07db8fd86b92aa0e5a549fa06f08d7963ddcce5d54ba

## Compressed returned-chart bursts

`yah_returned_burst.py` replaces explicit multiplication of the restorative
chart's 65,536-trit block by an exact straight-line program.  Each literal,
concatenation, and repetition node carries the complete two-input-state
summary of the quotient sweep.  Summary composition and binary powering
therefore certify a restricted lasso for every natural value of its remaining
parameter without expanding the repeated block.

For `g=1,...,4`, let `a_g` be the unique checked residue at which the returned
register vanishes modulo `2^(3g)`.  The artifact proves the following finite
table:

```text
g   a_g mod 2^(3g)   macro heads   odd sweeps   net cells   trailing twos
1   3 mod 8           01                 3          +1           10
2   27 mod 64         0102               6          +2           13
3   411 mod 512       010202             9          +3           16
4   2971 mod 4096     01020210          12          +4           19
```

Thus every certified row has `D'=(27/8)^g D`.  The repeated blocks have
lengths `2^(16+3g)`, reaching 268,435,456 trits in the fourth row while
remaining compressed.  Separate literal regressions materialize the least
source at `g=1,2`, replay every queue macro independently, and pin each stage
by SHA-256.

This is deliberately a bounded word theorem.  The observed heads do not obey
either tempting extrapolation `(01)^g` or `01(02)^(g-1)`.  The register
isometry supplies an all-depth arithmetic root tower, but its compatible
addresses cannot eventually be one ordinary natural parameter.

The first collision after a depth-one burst does produce a second restorative
edge.  Restrict the returned chart to `u=35+2048*w`.  The exact seven-macro
schedule is

```text
heads    0       1       0       2       0       2       1
carries [1]    [1,1]   [0]     [1,1]   [1]     [1,1]   [1,1]
```

The first two macros are the `g=1` burst.  The third is an even collision;
the remaining four spend seven odd sweeps and restore the seven-trit
reservoir.  The full instruction gains three cells.  With incoming register
`R` and returned register `T`, its exact affine law is

```text
2048*T = 59049*R + 8.
```

The repeated SLP block has length 134,217,728.  The independent regression
materializes only the least 2,317,094-trit member, replays all seven literal
queue macros, and records every SHA-256.  The endpoint is not identified with
an earlier chart.  If one nevertheless postulates a periodic alternation with
the original restorative edge, the composite expands by `3^16/2^19`; the
kernel-checked periodic affine gate in companion commit `2037f54` rules out
such a positive natural register orbit.  Closure still needs a nonperiodic
dispatcher or a different composite.

```bash
python3 yah_returned_burst.py selftest
python3 yah_returned_burst.py build yah_returned_burst_audit.json --max-depth 4
python3 yah_returned_burst.py verify yah_returned_burst_audit.json
```

Artifact SHA-256:
`e6c9aae7b804f616a1fb5b9640f693f641156d995666e5e275f4d641680d6293`.
Worker SHA-256:
`f552fb0a4fa754ef4313f678dcfb4b45448de6d21fc05312ea6d6994def569fa`.

## YAH abstract chart clock and fixed-lasso gate

`yah_chart_clock.py` continues the second restorative endpoint without
materializing its 134,217,728-trit block.  At macro boundaries its normalized
leading scale begins at `rho=269001/262144` and follows

```text
head 0,  1 <= rho < 4/3:   rho' = 3*rho/2
head 1,  4/3 <= rho < 5/3: rho' = 3*rho/4
head 2,  5/3 <= rho < 2:   rho' = 3*rho/4.
```

The resulting abstract head prefix is `01020210102101020210...`.  An
eventually periodic tail would multiply a bounded positive `rho` by one fixed
`3^p/2^q` on every period, forcing `3^p=2^q`.  This proves aperiodicity of the
abstract clock.  It is not by itself an infinite literal-word theorem: the
additive correction could cross a head boundary.  The worker supplies exact
gap inequalities only for the five phases used below.

On `w=249+256z`, the incoming second-edge register is `T=221 (mod 256)`.
The exact five-macro schedule is

```text
heads    0       1       0       2       1
carries [0]    [1,1]   [1]     [1,1]   [1,1].
```

It uses eight quotient sweeps and seven odd sweeps, gains two cells, restores
seven trailing twos, and writes

```text
256*U=3^7*T+1.
```

The output register inherits the exact two-adic isometry and satisfies
`U(z)=z (mod 2)`.  The artifact checks the unique source residue, every finite
correction gap and carry, and bounded low-bit/isometry regressions through
`z=32`.

For any segment with `M` macros, `S` quotient sweeps, `J` odd sweeps, and
space gain `G=J-M`, the worker checks the exact factorization

```text
3^J/2^S = 3^G * rho_end/rho_start.
```

The universal algebra implies that positive space gain has slope greater than
`3/2`; the default artifact includes 27,796 finite identity regressions.

The same artifact falsifies a proposed counter-writing reblock.  Across all
19 quotient layers, one 65,536-trit atom acts on the carry state by

```text
f(r)=(262145*r+449133) mod 2^19,
f^2(r)=r+111834 mod 2^19.
```

Since `v2(111834)=1` and odd iterates have odd return difference, every state
has exact period `2^19`.  The third nominal block contains precisely `2^19`
base atoms and therefore traverses one full carry-state cycle; it has no
smaller atom-aligned repetition.  The worker checks the general LCG
hypotheses through 24 layers and exhausts every cycle through 18.  The
all-depth full-period/reblocking generalization is a theorem request, not yet
a kernel-checked claim.

```bash
python3 yah_chart_clock.py selftest
python3 yah_chart_clock.py build yah_chart_clock_audit.json
python3 yah_chart_clock.py verify yah_chart_clock_audit.json
```

Artifact SHA-256:
`2c55cec21f81b563f181803a26ef5dc7489e13c668317af17438ace6220a29ab`.
Worker SHA-256:
`6cd98e32a22c47432d5d22d31a551afed0c5175f9abd094b7cea36385191d8ab`.

## KL-calibrated minus-one escape tax

`kl_minus_one_escape_tax.py` turns the original Krasikov--Lagarias
predecessor system into a construction diagnostic.  At an exact positive
critical eigenvector, every edge retained by the minimizing policy satisfies

```text
lambda^w*c(target) <= c(source).
```

Multiplication around a cycle cancels `c`, so every selected-policy cycle has
nonpositive total time shift; irrationality of `log_2(3)` makes the KL
inequality strict.  Thus the critical policy is supported by branching
entropy rather than one outward ray.  If a chord uses a non-minimal lift, its
factor `d=c_alt/c_min` gives the calibrated full-cycle constraint

```text
lambda^(sum w) <= product d.
```

Companion commit `9f307a9` kernel-checks both generic statements as QM127,
including strict negativity for KL selected-policy cycles.  Commit `ddff8d7`
adds the arbitrary-path condition-number form QM130, and `7aa7c0d` packages
the selected-path corollary: if `cmax/cmin<=lambda^B`, every selected path has
total shift at most `B`, independent of its length.

The exact finite worker tests the distinguished positive-shift self-loop at
the 3-adic state `-1`.  It SHA-checks the stored KL certificate/vector inputs
at every level `k=12..19`, extracts the three integer values in the fiber over
`-1`, and compares the exact deviation factor

```text
c(-1)/min_fiber(c)
```

to the certificate's rational class-8 weight `B8/SC_W`.  All eight exact
cross-products are strictly positive.  More specifically,

```text
k                         12                 19
deviation / weight   1.00491098975441   1.00029914602351
```

and all eight exact ratios decrease strictly with `k`.  This is bounded
evidence that the nonordinary `-1` self-loop saturates the escape-tax bound,
not an asymptotic theorem.

For the pathwise form of the tax, the worker also takes the exact minimum and
maximum of each certified feasible subeigenvector.  The condition numbers
increase strictly from `146.967160601293` at `k=12` to
`2782.61599307298` at `k=19`.
At any one level this is only a fixed endpoint factor, independent of path
length; its growth with level means that no precision-uniform path estimate is
being claimed.  Companion commit `cc9f441` separately proves that a natural
matching the exact `-1` residue at depth `k` must satisfy `3^k<=n+1`, so only a
growing diagonal sequence can chase the exceptional spine.

The paired exact rail regression checks, for every `L,t<=64`,

```text
T^L(2^L*t-1)=3^L*t-1.
```

The universal algebra shows why this outward wire is finite: splicing the
next pure wire subtracts its positive length from the payload counter
`v_2(t)`.  A fixed positive payload cannot support infinitely many such
discharges.  Companion commit `9f307a9` connects this exact counter exhaustion
to the literal Syracuse semantics.  A viable construction must therefore
contain an autonomous recharge phase; fresh high lift digits describe only a
3-adic stack.

```bash
python3 kl_minus_one_escape_tax.py selftest
python3 kl_minus_one_escape_tax.py verify \
  kl_minus_one_escape_tax_audit.json
```

Artifact SHA-256:
`b6204c3964b880e3c5857114f7bcd112e2e1592ca3653ad79445ce470dc14577`.
Worker SHA-256:
`5e8a2be5e31cc7beea536b871e86813b00b4954a193d0a7c5a28ef30b606af29`.

The mathematical interpretation and original-source audit are in
[`docs/notes/kl-calibrated-escape.md`](../../docs/notes/kl-calibrated-escape.md).
`counterexample:null`.

## KL tax on the three standard negative-cycle templates

`kl_negative_cycle_tax.py` extends the same exact finite calibration from the
fixed point `-1` to the signed shortcut-Collatz cycles through `-5` and `-17`.
It does not discover or classify cycles: the three templates are supplied
explicitly, then checked against the signed Syracuse rule and against their
positive-center KL predecessor presentations:

```text
1 -> 1
7 -> 10 -> 7
25 -> 34 -> 136 -> 91 -> 61 -> 82 -> 55 -> 37 -> 25.
```

Their class counts give the exact outward separators `3>2`, `3^2>2^3`,
and `3^7>2^11`.  At each stored level `k=12..19`, the worker SHA-checks the
certified feasible subeigenvector, extracts every prescribed chord lift, and
forms

```text
product(c_prescribed/minFiber) / product(certified edge-weight lower bounds).
```

All 24 rational ratios are strictly larger than one.  Each of the three
eight-level sequences decreases strictly, and `-1` is exactly the smallest
in every row:

```text
template                 k=12              k=19
-1 fixed point        1.00491098975441   1.00029914602351
-5 cycle             1.14003194854355   1.06409075514007
-17 cycle            1.86455471354517   1.48129516352954
```

These are finite diagnostics from independent feasible vectors, not
critical-eigenvector identities, a coherent tower, or limiting theorems.
They justify signed cycles as comparison controllers, not as an equality set;
the `-17` surplus in particular remains `1.4813` at level 19.  An autonomous
construction still has to pay for increasingly precise switches or resets
between finite shadow blocks.
Companion commit `e15c6f0` kernel-checks the only immediate product-level
corollary: if all `q` chord deviations are at most `M`, the calibrated cycle
weight is at most `M^q`.  Individual edges may exchange which one carries the
tax across levels.

The companion's subsequent controller theorem removes finite legality as a
search discriminator.  Commits `8c20163`/`54eb749` prove that a controller
word's numerator slope is a power of two, giving one input class for every
finite ternary target and automatic mixed dyadic/ternary CRT compatibility.
Commit `961c692` proves that for every word with `r>0` divided letters,

```text
LegalWord(w,h) <-> A*h+B = 3^r (mod 3^(r+1)),
```

and constructs the unique positive legal input class reaching every target
`g=1 mod 3` at every finite precision.  A bounded worker that merely finds
such legal target hits is therefore testing an automatic cylinder theorem,
not approaching a counterexample.  Future workers must test coherence of one
ordinary payload across resets and the real KL outward budget.

Commits `2acceaa`/`d8d8337` supply the matching dyadic accumulator for that test.  A
finite reset program has data `(S,P,D)` with
`2^S*m_end=3^P*m_start+D`, hence one initial class modulo `2^S`; an infinite
program whose cumulative `S` is unbounded has at most one ordinary initial
payload.  The terminal congruence reconstructs every intermediate integer
quotient, and a large enough cylinder shift makes all payloads in any finite
program positive.  Workers should therefore report the coherent sequence of
accumulated classes and its exact extension carries: a natural payload
requires the canonical representative to stabilize, so every newly written
high-bit block must eventually be zero.  Commits `2963a8d`/`ca8dc5c`
kernel-check this stabilization criterion and the exact bounded carry law,
including the no-chain consumer for carries that are nonzero arbitrarily
late.  Counts of independent finite reset, integrality, or positivity hits
carry no promotion evidence.  Commit `18b8c93` proves the complete interface:
an exact eventual zero-carry tail is equivalent to existence of a
nonnegative ordinary integer reset chain.  Workers must still certify strict
positivity of all later quotients and literal outward Collatz semantics.
Commit `302ce3b` supplies an abstract finite-table consumer for exactly those
extra fields, but intentionally has no signed-Syracuse bridge.  Do not search
total outward tables: the live computational target is a proper thin language
of compatible cylinders and its exact carry behavior.

```bash
python3 kl_negative_cycle_tax.py selftest
python3 kl_negative_cycle_tax.py verify kl_negative_cycle_tax_audit.json
```

Artifact SHA-256:
`f52afeca61dc4bd0683a2ab72e285377355e86edd5e52fec85e89a84ab534249`.
Worker SHA-256:
`6372c07d1b4cf289b44c624496e3813af7c2ceb901cd6d7ff27af9d5c60d2774`.
`counterexample:null`.

## Proper signed-controller thin language

`kl_signed_thin_residue.py` extracts the minimal outward shortcut-parity
language in the exact bounded controller box `c in [-96,-1]`, `1<=N<=8`.
It verifies the four-word prefix code, its exact Kraft masses, every
odd-affine pullback modulo `2^8`, and literal positive reset growth.  Its
finite prefix tree reports exact extension lifts; it does not promote a long
zero-lift suffix to an infinite address.

```bash
python3 kl_signed_thin_residue.py selftest
python3 kl_signed_thin_residue.py verify kl_signed_thin_residue.json
```

Default results: 768 modes, 246 outward modes, code
`{1,011,001111,010111}`, ordinary mass `21/32`, tilted mass `1905/2048`, and
41,328 literal growing reset checks.  The strongest finite zero-lift run is
eight blocks and then fails.  Companion commit `1aa3e52` rules out all
periodic and ultimately periodic infinite paths in this code.  A genuinely
aperiodic eventually-zero-carry path is not decided.  `counterexample:null`.

## EC17 boundary clock versus KL edges

`breakoff_ether_period3_kl_bridge.py` is a deliberately negative semantic
audit.  It proves by exact modular enumeration that the EC17 normalized core
clock is an odometer but that almost every boundary pair is not a KL
full-lift edge.  It also exhausts 29,524 KL words through length nine against
the sharp defect bound `D>=3^r-2^r`.

```bash
python3 breakoff_ether_period3_kl_bridge.py selftest --max-word-length 8
python3 breakoff_ether_period3_kl_bridge.py verify \
  breakoff_ether_period3_kl_bridge_audit.json
```

For the `(-1,1,1)` schedule, every phase has exactly one class-2 and one
class-8 KL chord over the full odometer orbit, with 7 nonedges at depth 3 and
25 at depth 4.  A normalized EC17 core step has defect 34 at divided count at
least 17, far below `3^17-2^17=129009091`, so it cannot itself be a KL word.
The actual packet compiler is not ruled out.  The artifact records
`tax_ready:false` and `counterexample:null`.

## Literal returning-glider KL bridge

`breakoff_ether_glider_kl_bridge.py` performs the corrected semantic
compilation which the core-boundary audit deliberately refuses.  It expands
the actual returning glider through linked breakoff steps and literal Collatz
states, samples `2 mod 3` visits, reverses them to KL full-lift edges, exactly
re-verifies the stored KL certificate, and checks every edge and path-product
potential inequality before reporting a tax row.

```bash
python3 breakoff_ether_glider_kl_bridge.py selftest \
  --maximum-ether-cells 3
python3 breakoff_ether_glider_kl_bridge.py verify \
  breakoff_ether_glider_kl_bridge_audit.json
```

The default artifact covers ether lengths `1..6`, tail zero, at KL level 12.
All paths are outward and contain only chord edges; their `(R2,R8)` counts are
`(6,9),(8,13),(10,18),(12,22),(14,25),(16,29)`.  Every exact edge inequality
and telescoped product passes.  This is finite packet-level calibration only;
it does not supply an infinite macro schedule, a precision-uniform KL bound,
or a Collatz counterexample.  Companion commit `82c01dd` separately proves
that successive `2 mod 3` Syracuse visits always give KL principal edges;
the worker's remaining finite obligations are compiled macro linkage and the
certificate-specific tax.  `counterexample:null`.

## Linked glider tail chart and deterministic KL ether cycle

`breakoff_ether_glider_kl_tail_chart.py` resolves the free-tail versus linked-
tail distinction left open by the literal KL bridge.  It first verifies the
true packet chart

```text
Z=2^35*K-358513857,
r=v_3(Z),
C+1=3*2^(r+1)*(Z/3^r).
```

Free `q mod 3^d` has an exact geometric rail histogram because its coefficient
in `Z` is a 3-adic unit.  A genuine linked successor is not free: substitution
of EC17 gives

```text
2^(8m+30)u'-9591553
 =3^12*(2^15*3^(6n-1)u-17),
```

so every positive-branch successor has `r'=2`.  It also verifies
`v_3(473*C'+881)=6n` and fixed-target synchronization of `q' mod 3^d` for
every `d<=6n+1`.

```bash
python3 breakoff_ether_glider_kl_tail_chart.py selftest
python3 breakoff_ether_glider_kl_tail_chart.py verify \
  breakoff_ether_glider_kl_tail_chart_audit.json
```

The default artifact checks free branches `n=1..12` modulo `3^5`, 192 lifted
links with both branch lengths in `1..8`, synchronization through depth 49,
1,200 piecewise-affine chart instances, and literal router skeletons for
`n=1..4`, tails `0..8`.  Every linked post-initial length-`n` macro has
`(R2,R8,S)=(2n+4,4n+7,0)`.  The repeated ether cell is the exact KL cycle
`F_E(x)=(729*x+881)/256` at `x=-881/473`.  At the reverified level-12
certificate, linked macros `n=2..6` have exact factorization
`Dev(n)=Dev_base*Dev_E^n`, with one selected and five nonselected lifts per
ether cell.  This is a fixed-precision calibration and supplies no infinite
EC17 chain.  `counterexample:null`.

`kl_rational_ether_cycle.py` independently isolates the same rational cycle
without replaying a glider macro.  It derives its six rational centers,
SHA-checks the stored certificate manifests and sidecars at `k=12..19`,
memory-maps the large vectors, reconstructs every chord fiber, and compares
the exact cycle deviation `D_E` with
`W_E=(B2/SC_W)^2*(B8/SC_W)^4`.

```bash
python3 kl_rational_ether_cycle.py selftest
python3 kl_rational_ether_cycle.py verify kl_rational_ether_cycle.json
```

All eight exact ratios `D_E/W_E` exceed one and decrease strictly from
`1.217522341...` at level 12 to `1.051569573...` at level 19; each comparison
is certified by a positive integer cross-product.  The artifact independently
matches the level-12 literal tail-chart factor.  It records
`finite_evidence_only:true`, `limit_theorem:null`, and `counterexample:null`.

## Self-writing KL/EC17 two-rail coordinate

`breakoff_ether_self_writing_kl.py` turns the rational ether center into a
global deterministic packet coordinate.  Every genuine packet has

```text
Z(q)=494251421+(473*2^20)q,
W(q)=83499104+(473*3^11)q,
3^11 Z(q)+17=2^20 W(q).
```

The current branch is stored in `v_3(Z)=6n`.  A target branch is decoded by
`v_2(W)=8m-5`; writing `h=W/2^(8m-5)`, the fixed packet-return test and output
are

```text
729^m h = 494251421+(473*2^20)q'.
```

Thus the binary delay is written back as `v_3(Z(q'))=6m`.  In the centered
coordinate `Z=473R+4`, the same step is

```text
D(R)=(3^11 R+1221)/2^15,
E(R)=(729R+4)/256,
R'=E^m(D(R)).
```

Under the literal boundary change `C=2^18R+2215`, `E` is exactly the KL ether
map `(729C+881)/256`.  For each fixed `m`, CRT reconstructs the complete
affine source/output family with strides `2^(8m+15)` and `3^(6m+11)`.

```bash
python3 breakoff_ether_self_writing_kl.py selftest
python3 breakoff_ether_self_writing_kl.py verify \
  breakoff_ether_self_writing_kl_audit.json
```

The v2 artifact checks all target families through `m=32`, 4,096 literal
linked packet transitions, and 1,024 color-zero positive bare EC17 steps.
For a bare step it certifies the promotion identity

```text
3^11*(3^(6n)u-Z0)=2^20*(2^(8m-5)u'-W0).
```

Thus the `2^20` rail factor is automatic; packet color zero supplies the
remaining `473`, and the exact height window makes the packet coordinate
nonnegative.  A positive bare ray plus color zero at one state already
promotes to the full self-writing rail.  Every accepted step has `q'>q`.
The artifact does not find an infinite accepted orbit; `counterexample:null`.
Companion commit `7ca6d4f` kernel-checks the determinant identity and proves
strict payload growth and branch aperiodicity for every supplied infinite
self-writing orbit.  Companion commit `d4a8edf` independently packages the exact public
program `2^(8m+15)q'=3^(6m+11)q+delta_m`: eventual-zero canonical carry for
that branch-only program constructs a shifted self-writing orbit, and every
supplied orbit has eventual-zero public carry.  This is the preferred search
interface because it already includes color and packet-rail semantics.
Companion commit `ded9c30` completes QM148 and proves the sharper bare-ray iff:
color zero at one state is equivalent to promotion of the one-step tail.

## Branch pressure and the EC1 unit component

`breakoff_ether_branch_pressure.py` eliminates the affine tail from every
fixed target branch:

```text
2^(8m+15)q'=3^(6m+11)q+delta_m,
delta_m=(3^(6m)W0-2^(8m-5)Z0)/473>0.
```

The exact target cylinders form an LSB-first prefix code with lengths
`23,31,39,...`, Kraft mass `1/(255*2^15)`, and schedule generating function
`(1-x^8)/(1-x^8-x^23)`.  The corresponding pressure root satisfies
`x^8+x^23=1`, giving the diagnostic dimension
`0.07065929109419928758...`.  The standard dimension interpretation is not
part of the executable certificate; the code, recurrence, Kraft identity,
and rational root bracket are.

The same worker isolates an invariant component `q=17r`:

```text
Zbar(r)=29073613+495976448r,
Wbar(r)=4911712+83790531r,
3^11*Zbar(r)+1=2^20*Wbar(r).
```

On accepted packet states this reduces EC17 to

```text
2^(8m+15)v'=3^(6n+11)v+1,   v,v'=2 (mod 3).
```

The exact residue transport

```text
r'-14=6*(-2)^(m-1)*(r-1) (mod 17)
```

proves that consecutive normalized cores can never both contain `17^2`:
`min(v17(u),v17(u'))=1`.  This all-depth filter leaves every finite branch
pair CRT-solvable, so it narrows but does not close the live component.

The v4 audit also certifies the complete shallow graph and eight invariant
rails

```text
m mod 8:       1  2  3  4  5  6  7  0
r=q/17 mod17: 12  2 13  3 15  6  9  0.
```

For `m=1+8j`, `r=12+17s`, the next digit is
`s'=6s+10j+13 (mod17)`; all other rails likewise have a unit branch-digit
coefficient.  At depth `17^k` this becomes an exact branch clock modulo
`8*17^(k-1)`.  The per-rail code has generating function
`(1-x^64)/(1-x^64-x^(8j+15))`; the maximal diagnostic dimension is
`0.0250459467556681664...`.  These are exact selectors for a canonical-carry
analysis, not evidence that an ordinary infinite address exists.

Version 3 added the exact KL/Tschakaloff telescope for the public-payload
address.  With `alpha_m=2^(8m+15)/3^(6m+11)`,
`R_j=product_(i<j)alpha_(m_i)`, and

```text
A=83499104/(473*3^11),
B=494251421/(473*2^20),
epsilon=A-B=17/(473*2^20*3^11),
```

every finite public chain satisfies

```text
q_0+A+epsilon*sum_(1<=j<N)R_j=R_N*(q_N+B).
```

The artifact verifies this identity on all 1,278 stored prefix cylinders.  An
ordinary infinite orbit would force the single variable-exponent theta value
`Theta=sum_(j>=1)R_j` to equal `-2^20*W(q_0)/17` in `Q_2`.  This recovers the
closed fixed-rate partial-theta cases but makes no irrationality claim for a
nonlinear payload-written exponent sequence.

Version 4 adds the exact two-place height gate.  Put

```text
M_N=sum_(i<N)m_i, D_N=11N+6M_N, V_N=15N+8M_N.
```

If the theta value is a negative integer `-K`, then the exact valuation of
the first omitted term and the positive real partial sum give

```text
2^V_(N+1) < (K+1)*3^D_N.
```

Combining this with `3^41<2^65` bounds
`328m_N-62M_N-100N+615`.  In particular a schedule whose fresh branch is
superincreasing relative to its entire past cannot work.  This is a universal
growth sieve, not a proof against slow nonlinear rulers.  The same certificate
checks the mod-473 constants used in the converse: one exact hit
`Theta=-2^20*Wbar(r)` recursively supplies integral suffixes and preserves the
full reduced packet lattice.

The same version checks 83,521 Legendre block identities behind the slow
valuation ruler `m_n=j+8*v17(n+1)`, verifies all eight rational Mahler
specialization points, and records the exact 17-Mahler functional equation.
It also uses the quadratically amplified ruler as a negative control for the
height gate.  These coefficient checks do not certify irrationality of the
resulting `Q_2` value.

Version 5 adds the source-audited value-theorem application that was missed in
version 4.  With `kappa=16/27`, the slow-ruler function has the stronger form

```text
G(x)=sum_(n>=0)kappa^(-s17(n))*x^n
    =product_(k>=0)P_17(x^(17^k)/kappa),
G(x)=P_17(x/kappa)G(x^17).
```

Its product zeros approach the complex unit circle densely, giving a natural
boundary and, after rational-coefficient scalar descent, transcendence over
`C_2(x)`.  Wang's 2006 p-adic Mahler theorem applies with `rho=17`, functional
degree one, `M0=17`, and size condition `17<17^2`.  At each of the eight exact
arguments `x_j`, its nonvanishing polynomial is positive in the real
embedding.  The published theorem therefore makes `G(x_j)` transcendental in
`Q_2`, excluding its required ordinary-integer value.  The artifact checks
the digit-sum conversion, argument valuations, and elementary Wang
parameters; it cites rather than re-proves the analytic theorem.

Version 6 records the structurally different place-value ruler
`m_n=j+8*17^v17(n+1)`.  For
`A_n=sum_(1<=t<=n)17^v17(t)`, the exact block law

```text
A_(17n+r)=17A_n+16n+r
```

gives the bivariate equation

```text
H(C,Z)=P_17(CZ)H(C^17,C^16Z^17),
1+Theta=H(c,z_j).
```

The checker verifies 83,521 block cases, the digit-position formula through
`17^4`, 65 iterates of `T(C,Z)=(C^17,C^16Z^17)`, all eight prime-exponent
determinants `16`, and the boundary identity
`A_(17^k-1)=16k17^(k-1)` through eight symbolic rows.  This is a genuine
rank-two Jordan system; Wang's univariate theorem does not apply, while the
cumulative `k17^k` depth makes the public height gate asymptotically slack.
The artifact identifies a multivariate `Q_2` value theorem as the live seam
and makes no irrationality claim for `H(c,z_j)`.

```bash
python3 breakoff_ether_branch_pressure.py selftest
python3 breakoff_ether_branch_pressure.py verify \
  breakoff_ether_branch_pressure_audit.json
```

The default artifact checks target families through `m=64`, 1,278 distinct
schedule cylinders through 160 source bits, and the higher 17-adic branch
clock through precision 12.  It has `counterexample:null`.

Version 7 also records the exact valuation of every polynomial monomial along
the defective Jordan orbit.  Lexicographically distinct exponent pairs have
eventually distinct valuations, and the worker constructs an explicit depth
after which a chosen finite polynomial has a unique least-valuation monomial.
This is a rigorous zero-estimate input for a possible direct multivariate
`Q_2` auxiliary-function argument; it is not itself a special-value theorem.

### Minimal raw outward first-passage code

`outward_first_passage.py` removes the YAH/tag compiler from the construction
search and audits the canonical shortcut-parity system directly.  A word is a
codeword exactly when its affine slope `3^O/2^S` first exceeds one at its last
bit.  Every outward word has one such prefix, so this is the maximal outward
prefix-free code.  Its first layers are exactly the previously audited thin
language

```text
1, 011, 001111, 010111.
```

The worker counts states by `(length,odd_count)`, not by enumerating words.
It checks the ordinary stopped mass `P_N+A_N=1`, the slope-tilted martingale
identity `Q_N+R_N=1`, and the overshoot bracket

```text
P_N+(2/3)R_N <= P <= P_N+R_N.
```

At the default exact depth 256 this gives the rational bounds rendered as
`0.713684569145118094... < P < 0.713684640996637644...`; the remaining tilted
mass is `0.000000215554558648...`.  The full tilted mass is one by the
positive-drift stopped-martingale argument recorded in the artifact.  This is
critical ensemble conservation, not an ordinary survivor.

Schema v3 also scans the exact monotone construction variable, not an
unstructured seed record.  It replays every positive source through `300000`
to the terminal cycle and thereby certifies `h_n` through block depth 36 and
the strict lower bound `h_37>300000`.  The successive record sources are

```text
1, 3, 7, 15, 27, 703, 4255, 4591, 31911, 77671,
113383, 159487, 270271.
```

The final source completes 36 blocks before reaching the `1--2` cycle.  Its
canonical address is already fixed after block eight, so the remaining 28
blocks are genuine zero-carry renewals.  The more informative nested
visualizer object replays

```text
3698459 -> 8216025965
```

in 72 accelerated steps and 27 post-address complete extensions.

The worker also compresses every completed boundary as `x=3H-1`.  Even `H`
forces a one-letter block and drains one factor of two.  A nontrivial recharge
word has

```text
2^S K=3^O H+e_w,   e_w>0, 3|e_w,
R(H)=3^a K/2^a,    a=v_2(K), v_3(R(H))>=a+1.
```

The record orbit's 36 blocks become 13 exact recharge rows.  The shallow
`011` branch is separately checked as
`2^(c'+2)u'=3^(c+1)u+1`, including the finite exponent return
`7 -> 2 -> 12 -> 7` on source `159487`; neither finite trajectory survives.

Every certified minimum address is odd.  Its forced first block gives the
exact triadic-slice reduction

```text
h_(n+1)=(2m_n-1)/3,
m_n=min {y completing n blocks : y=2 mod 3}.
```

All rows through `h_36` are audited.  More generally, the artifact records
the theorem target that nonzero extension carry forces
`rho_(n+1)>=2^n`; sub-`2^n` canonical-address growth therefore suffices for
eventual zero carry.  Companion commit `e48bd60` kernel-checks this carry
threshold.  The odd-charge identities and QM158's full min-plus 3-adic class
recurrence remain formalization targets.

```bash
python3 outward_first_passage.py selftest
python3 outward_first_passage.py verify outward_first_passage_audit.json
```

The construction target is the monotone minimum canonical address `h_n`.
Boundedness/eventual constancy of `h_n` is equivalent to an ordinary infinite
strictly growing shortcut orbit.  Companion commit `8959436` kernel-checks the
finite-window compactness and minimum-start equivalence for literal shortcut
executions.  The next search should propagate triadic class minima or iterate
the odd-charge map, not widen the seed bound.  Diffuse critical flow fails the
gate; the artifact makes no orbit claim and stores `counterexample:null`.

### Directed carry lifts of the 36-block prefix

`outward_carry_lift.py` searches the exact next cylinder above the failed
record prefix, rather than unrelated starting integers.  At block 36 the
source `270271` is canonical at cumulative parity length 124.  Its zero-carry
continuation dies, so every seed preserving the prefix is

```text
270271+2^124*ell, ell>=1.
```

The committed artifact exhausts `1<=ell<=1000000` with exact integer replay
to the terminal cycle.  The first maximum of 73 blocks is carry `636503`,
source

```text
13536921712017380925614270484633922618793919.
```

Carry `719011` ties it.  Both terminate.  The champion's address stabilizes at
block 50, followed by 23 further complete blocks.  This demonstrates genuine
post-address renewal at a 144-bit source, but remains finite.

```bash
python3 outward_carry_lift.py selftest
python3 outward_carry_lift.py --processes 8 verify \
  outward_carry_lift_audit.json
```

The `probe` command performs one exact scan without writing an artifact;
promote a diagnostic only by rebuilding and verifying a stated bound.

### Triadic min-plus profile operator

`outward_minplus_profile.py` checks the exact inverse renewal on residue-class
minima.  If every execution of word `w` is

```text
(x,y)=(r+2^S*t,b+3^O*t),
```

then source phase `a mod 3^k` fixes `t=c mod 3^k` and target phase
`d=b+3^O*c mod 3^(O+k)`.  The worker evaluates the resulting min-plus formula
and compares it with literal Collatz block counts.

The default artifact uses `B=50`, target bound `C(B)=74`, depths through six,
and all phases through exponent three.  Its complete word table is
`{1,011,010111}` and all 240 profile equalities pass.  It also checks every
available nonzero-carry target against `y<=3B-1`.

Companion commit `a0e460d` proves the exact dual-residue family for every
literal word, and `8d79424` proves the finite active-code min-plus minimum
formula.  Commit `4c39f8d` proves the growing-phase equivalences and the
phase-refined finite active-code minimum.  Commit `1aec3fc` proves the
residue-two predecessor equivalence, and `5448445` proves odd-part
monotonicity and the unconditional scalar slice law.

```bash
python3 outward_minplus_profile.py selftest
python3 outward_minplus_profile.py verify \
  outward_minplus_profile_audit.json
```

This finite checker exposes rather than hides the inverse-limit obstruction:
no fixed phase precision closes the unbounded operator, because the update
for word `1` already asks for one more ternary digit.  At finite height, a
complete word table and a precision `3^K>C(B)` do close exactly.  The artifact
has `counterexample:null`.

### Power-charge return and Hensel exponent cylinders

`outward_power_charge_return.py` starts only from `H=3^C`, the exact landing
family of the kernel-checked resonant word.  It iterates the deterministic
compressed odd-charge map and checks for a return to either a pure power or
the resonant family.

The artifact checks every `12<=C<=10000` on Akdeniz.  All 9,989 cases reach a
terminal orbit before the declared recharge and shortcut limits.  No return
is found; `C=700` is the unique maximum with 11 completed recharges.  The
worker stores hashes rather than enormous decimal charges and reconstruction
replays all arithmetic exactly.

More importantly, it certifies the first exponent cylinder symbolically.
The word `010111` occurs exactly for `C=12 mod16`, with

```text
a=v2(3^(C+2)+7)-6,
R=3^(a+2)*(3^(C+2)+7)/2^(a+6).
```

An exact 64-bit Hensel tower constructs the unique nested class with `a>=k`
at every `k`.  This supplies arbitrarily deep finite recharge classes without
claiming that their 2-adic limit is a natural exponent.  Commit `7826516`
proves that the residues cannot eventually stabilize to any natural exponent.

```bash
python3 outward_power_charge_return.py selftest
python3 outward_power_charge_return.py --processes 8 --chunk-size 100 verify \
  outward_power_charge_return_audit.json
```

The artifact records `counterexample:null`.  The interval bound is a finite
calibration; the exponent-cylinder formulas are the reusable search state.

### Primitive-coordinate invariant architecture CEGIS

`outward_primitive_invariant_cegis.py` is separate from the next-word beam.
It writes `H=3^c*u`, binds the exact unbounded drain, and audits the
LOW/HIGH/RESONANT defect normalization for every defined displayed recharge.
Its finite guard-architecture loop adds memory, prior carry, a dyadic unit
residue, and an exponent residue only in response to exact feature
ambiguities.  None is promoted to an invariant without universal
definedness, target inclusion, and root coverage.

The default reconstructible artifact uses only the directed root family
`C=12 mod16`, tests `C<=1000`, keeps one coherent nested exponent cylinder,
and records an `(H,D,P)` ledger for the `C=700` champion.  It also checks the
mod-nine resonant-return lemma on the complete first-passage word table
through length 24.  The unbounded primitive normalization, chart-rank
obstruction, and word lemma are requested from the companion Lean worker as
QM162--QM163.

The same artifact contains a theorem-directed writer--decoder outer loop.
For each displayed counter `c<=5`, it solves the unique base-nine Hensel
logarithm making a pure-power `010111` output legal for the resonant word
`0^(2*3^c)1^o`.  Counters `2,3,4,5` are compatible; the least ordinary root
exponent is `7848752615831324`.  Every coefficient, exact drain, target charge
exponent, and output primitive chart is stored.  A size comparison rejects an
immediate third decoder edge for all four rows, so this is a two-edge
architecture witness with a named next failure, not invariant closure.

```bash
python3 outward_primitive_invariant_cegis.py selftest
python3 outward_primitive_invariant_cegis.py verify \
  outward_primitive_invariant_cegis_audit.json
```

The artifact records `universal_invariant:null` and `counterexample:null`.
The coherent cylinder is a bounded 2-adic diagnostic unless its canonical
ordinary exponent stabilizes.
