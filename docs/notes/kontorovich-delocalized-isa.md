# The delocalized Collatz instruction set

Status: active research map, 2026-07-21.  Exact identities are separated from
proposed certificate shapes.  This note contains no counterexample.

## 1. Scale changes the object we should search for

Barina's current published computation verifies convergence for every seed
below `2^71`.  That is already about 21 decimal digits.  If an exceptional
seed instead has roughly 10,000 decimal digits, its bit length is about
33,220.  Searching the intervening integers is not a meaningful strategy.
The target must be a **short generator for a huge seed**, accompanied by a
finite certificate which proves what the generator does without expanding an
unbounded orbit.

This is the useful lesson from ultra-small languages and Busy Beaver
"bouncers."  Tiny syntax does not imply easy behavior.  More importantly, a
nonhalting computation can sometimes be certified by a formula configuration
and a bounded shift rule

```text
C(n)  ->+  C(f(n)),       f(n)>n,
```

where one checked period crossing lifts to every `n`.  A Collatz disproof of
this form would start at one canonical finite positive integer `C(n0)` and
make every macrostep literal Collatz arithmetic.  It would not require the
specific `3x+1` map to be a universal computer.

## 2. Simon's nonlocality hypothesis

Simon Dedeo suggested using Brainfuck, tag systems, FRACTRAN, and other
ultra-simple languages as sources of programming-language ideas, but also
warned that their usual spatial locality may be the wrong assumption.  A
Collatz "instruction" might be spread over the entire digit span.

That warning is mathematically natural.  Multiplication by `3` propagates
carries; division by the maximal power of `2` reads an arbitrarily long
suffix; conversion between binary and ternary changes the meaning of every
digit position; and a congruence can couple the low address of a number to an
arbitrarily large high payload.  The working unit should therefore be allowed
to be a **relation**, not a substring.

This is a hybrid rather than an anti-spatial model.  Kontorovich's separated
bits and zero gaps are still literal packets and delay lines.  The revised
claim is that the *junction* which schedules or replenishes them can be a
whole-number congruence.  We should search for spatial wires connected by
delocalized gates.

| Exact presentation | Candidate instruction unit | Where it is nonlocal |
|---|---|---|
| Kontorovich--Sinai valuation stream | one exact `v_2(3x+1)` value | the first `N` values select one whole residue class modulo an exponentially growing power of two |
| Mersenne packet recurrence | a dyadic address / triadic next-phase bridge | a fixed low suffix transforms the complete high payload, while the next packet is constrained modulo `3^m` |
| Yolcu--Aaronson--Heule mixed-base rewriting | motion of the binary/ternary boundary | a local rewrite in mixed base represents whole-word carry and base conversion in ordinary binary |
| De Mol's 2-tag encoding | left-end symbol plus appended right-end word | control and output occur at opposite ends of an unbounded word |
| Colussi convergence grammar | rotation, length, and order of a repetend | a "block" is a phase of a periodic word whose admissibility is coupled to all other orders by congruences |

Brainfuck contributes the discipline of looking for macros, loops, counters,
and invariants in a minimal machine.  FRACTRAN is the closer semantic analogy:
divisibility of the whole integer, rather than a nearby opcode, chooses the
transition.  Neither analogy is evidence of universality.

## 3. An exact dyadic--triadic packet gate

The Lean-checked Mersenne endpoint reduces one disproof lane to positive odd
packets satisfying, at counter level `m`,

```text
2^e (2^(m+1) h' - 1) = 3^m h - 1.                    (1)
```

There is a forward "instruction decoder" hidden in (1).  Fix positive `m,e`
and put

```text
W = m+e+2,       M = 2^W,
r = 3^(-m) (1 - 2^e + 2^(m+e+1))  (mod M),  0<r<M,
s = (3^m r + 2^e - 1)/2^(m+e+1).
```

Here the inverse exists because `3^m` is odd.  The defining extra bit in the
congruence makes both `r` and `s` odd.  Direct substitution gives the exact
affine family

```text
h  = r + 2^(m+e+2) q,
h' = s + 2*3^m q,                                  (2)
```

for every nonnegative payload `q`.  Conversely, every positive odd renewal
with literal collision valuation `e` lies in (2).  Thus the low `W` binary
digits are an address, but the operand is the entire arbitrarily long prefix
`q`; the instruction multiplies that payload by `2*3^m`.

The same equation gives the opposite-place scheduler

```text
2^(m+e+1) h' = 2^e-1  (mod 3^m).                    (3)
```

One instruction is therefore a bridge between a dyadic suffix of the current
packet and a triadic phase of the next.  It is better represented by
`(m,e,r_2,r_3,affine payload map)` than by a contiguous bit word.

Lean commit `7370489` supplies a complementary global rigidity statement: a
fixed infinite extra stream has at most one ordinary positive packet
realization.  It also proves the exact finite backward affine-series identity
for every truncation.  Thus a symbolic controller is not hiding many ordinary
seeds; it selects at most one.  Proving that the controller's unique 2-adic
candidate is or is not a nonnegative integer becomes a separate arithmetic
gate, and may rule out an entire controller family without seed enumeration.
Commit `b205e40` now proves that the canonical series converges in `Q_2` for
every schedule and equals `-(x_0+1)` whenever an ordinary renewal exists.  The
remaining task is only to exclude embedded negative naturals for a useful
schedule class.

[`packet_gate.py`](../../experiments/kontorovich/packet_gate.py) computes these
gates with exact integers.  Its current self-test checks the coefficient
identities and literally replays 8,192 gate/payload pairs (`1<=m,e<=8`,
`0<=q<128`).  A separate exhaustive converse pass recovers all 16,316 literal
renewals among odd `h<2^16` at levels `1..8`, including valuations outside the
displayed `e<=8` test rectangle.  These bounded checks test the implementation;
Lean commit `f1cb0e2` proves the unbounded affine family, unique payload,
literal valuation, and triadic scheduler universally.

## 4. A scale-matched periodic background

Colussi gives an exact binary grammar for the convergence classes
`G_k={x:R^k(x)=1}`.  Its order-`h` seed `s_h` has padded length

```text
2 lambda_h,       lambda_h=3^(h-1),
|s_h| = (4^lambda_h-1)/3^h.
```

Every member of `G_k` is a concatenation of finite extracts from periodic
rotations of `s_k,...,s_1`, with an explicit congruence scheme for their
phases and lengths.  This is an exact grammar of known-halting programs, not
a divergence certificate.

It nevertheless supplies a strikingly well-scaled "ether."  The order-10
seed has padded length 39,366 bits; its integer has 39,351 significant bits
and 11,846 decimal digits.  It is generated by a one-line formula rather than
an 11,846-digit literal.  Moreover

```text
|s_(h+1)| = |s_h| (1+B+B^2)/3,       B=2^(2 lambda_h),
```

so `s_(h+1)` is obtained by globally dividing three aligned copies of `s_h`
by `3`.  That division is precisely the kind of carry transduction for which
a spatially small defect can have a nonlocal phase effect.

The lead discovery target is consequently a **defect bouncer**:

```text
C_h = (order-h repetend background, finite defect, mixed-base phase)
C_h ->+ C_(h+1),
```

where the rewrite is a literal Collatz macro, the defect description stays
bounded, and the represented positive integer grows.  The background may be
specified by rotations and congruences rather than expanded bits.  A verified
transition from every `h>=h0`, together with one checked finite start, would
be the desired finite nontermination certificate.

### First spatial primitive: an 11,846-digit wire

The order-10 background already contains a striking exact delay line.  Let

```text
a_10=(4^19683-1)/3^10.
```

The finite valuation header

```text
(1,1,2,1,1,1,5,1,4,1)
```

has ten steps, total halving count 18, and affine offset `2^18+1`.  Therefore
literal replay gives

```text
T^10(a_10)=1+2^39348.
```

For the next 19,673 accelerated steps there is no need to simulate:

```text
T^t(1+2^39348)=1+3^t 2^(39348-2t),    0<=t<=19673,
```

and every one of the first 19,673 valuations is exactly two.  The high packet
moves two bit positions toward the low `1` per tick while its payload is
multiplied by three.  It then collides with valuation three and endpoint
`(1+3^19674)/2`.

[`colussi_delay.py`](../../experiments/kontorovich/colussi_delay.py)
reconstructs the 11,846-digit seed from the formula, checks the compressed
header, literally replays the full delay as an independent regression, and
continues the seed exactly to `1` after 95,146 accelerated steps.  The first
1,024 post-collision states regenerate no zero gap wider than 10 bits.  Thus
the unmodified background is a verified wire but a failed bouncer.  The
concrete synthesis problem is to add a distributed defect which changes the
collision endpoint into a new state `1+q'2^J'` with `J'>39348` (or into a
multi-packet state which later does so).

### Simon's gap splash and the two-rail correction

Simon suggested aligning other bits so that, when the high packet reaches the
boundary, their carries “eat” the dirty collision output and regenerate a
wide gap.  This can be written exactly.  Start with an odd payload `Q` on the
`+1` rail,

```text
X=1+2^(2r+2)Q.
```

After `r` valuation-two ticks it is `1+4*3^r Q`.  Ask the collision to emit
`Y=1+2^(2r'+2)Q'` with extra valuation `a`.  The entire splash condition is

```text
3^(r+1) Q + 1 = 2^a (1+2^(2r'+2) Q').              (4)
```

For every positive `r,r',a`, the coefficient of `Q'` is invertible modulo
`3^(r+1)`.  Equation (4) therefore selects one residue class for `Q'`; choosing
its odd lift gives a positive `Q`, and adding `2*3^(r+1)z` to `Q'` gives an
infinite affine family of splashes.  The small regression

```text
r=1, r'=2, a=1:   Q=185, Q'=13,
2961 -> 2221 -> 833
```

increases the empty gap from four to six bits.  At the order-10 scale, the
same construction can increase 39,348 bits to 39,350 bits in one generated
78,700-bit state.  [`splash_gate.py`](../../experiments/kontorovich/splash_gate.py)
checks the coefficient identities and literally replays 15,360 bounded family
members.

There is also a universal energy warning.  A pure `+1` splash uses `r+1` odd
steps and `2r+2+a` halvings, so its leading multiplier is

```text
3^(r+1)/2^(2r+2+a) = (3/4)^(r+1)/2^a < 1.
```

Indeed (4) directly gives `Y<X` for every positive member.  Gap cleanup is
real, but the `+1` rail cannot be the engine.

The proposed machine therefore has two spatial phases:

```text
-1 rail:  -1+2^J Q -> -1+3^t 2^(J-t) Q    (k=1, amplifier),
+1 rail:  +1+2^J Q -> +1+3^t 2^(J-2t) Q  (k=2, timer/cleaner).
```

Delocalized phase-switch congruences connect the rails.  The exact synthesis
target is a return circuit whose `-1` amplification exceeds its `+1` cleanup
loss, whose outgoing precisions are larger, and whose sacrificial payload
bits are produced again by the same finite relation.

That finite return circuit now exists.  With `r` amplifier ticks, `s` cleanup
ticks, collision extras `a,b`, and outgoing gap `L`, the two switches are

```text
3^(r+1)P - 1 = 2^a(1+2^(2s+2)Q),
1 + 3^(s+1)Q = 2^b(-1+2^L P').                 (5)
```

For every fixed shape, modular inversion gives the complete affine family of
positive odd triples `(P,Q,P')`.  The standard shape

```text
s=1, a=b=1, L=r+2
```

has valuation word `[1]^r ++ [2,2,3]` and moves the `-1` gap from `r+1` to
`r+2`.  At `r=4`, one exact member is

```text
-1+2^5*2961 = 94751  ->  101183 = -1+2^6*1581.
```

Thus the pump can pay for the cleanup loss and move outward.  Consecutive
gate families are arithmetic progressions in their payloads, so Chinese-
remainder intersection compiles a whole finite circuit without enumerating a
seed interval.  [`two_rail_gate.py`](../../experiments/kontorovich/two_rail_gate.py)
uses `r_i=4+i` and constructs a depth-247 seed with 33,351 significant bits
(10,040 decimal digits).  Literal exact replay certifies 247 strict outward
rounds, 32,110 accelerated steps, gap growth `5 -> 252`, and a 15,397-digit
endpoint.  Full continuation nevertheless reaches `1` after 155,190
accelerated steps.

This separates the two hard parts cleanly.  The finite hardware has genuine
wires, amplification, carry cleanup, and regeneration.  What it lacks is one
ordinary program: adding the 248th gate changes the least canonical seed.
The affine-family index gives the missing instruction semantics.  If a source
output family is `c+2*3^R z` and a target input family is `a+2^D w`, exact
linkage reads

```text
3^R z + (c-a)/2 = 2^(D-1)w.
```

There is one accepted low-bit address `z=rho mod 2^(D-1)`; after deleting it,
the residual tape obeys `w=w0+3^R u`.  This is a literal variable-length tag
instruction whose address and data are spread across the full payload rather
than stored in adjacent binary cells.  Lean commits `4789a80` and `1076954`
prove whole affine links and compatible two-instruction handoffs for every
natural residual tail.  Commit `2f2e24e` supplies a sound conditional endpoint
for an affine self-link—but the older periodic-word theorem makes every
outward instance impossible.  Repeating one fixed gate route repeats one fixed
nonempty valuation word.  On affine coefficients a word with `N` odd steps
and total valuation `S>0` would force the return slope to be
`3^N/2^S`, which cannot be a natural integer.

Lean commits `b741a14` and `26f3584` prove this for fixed affine circuits and,
more generally, for every eventually periodic stream of macro-words.  Commit
`560fcc5` adds the finite-memory consequence: a payload-independent controller
with any finite effective state eventually becomes periodic and is therefore
impossible.

The branch is nevertheless deterministic once the unbounded payload is
included.  For fixed amplifier length `r`, a shape `(s,a,b,L)` accepts one odd
payload residue modulo

```text
2^E,  E=a+b+2s+L+3.
```

The accepted residues form an LSB-first prefix code: the literal payload
uniquely reveals `a`, then `s`, then `b`, then `L` through successive exact
2-adic valuations.  Its Kraft mass among odd 2-adic payloads is

```text
sum_(a,b>=1,s>=0,L>=2) 2^(-(E-1)) = 1/6.
```

Thus one-sixth of the 2-adic tape cylinders encode a complete next splash,
while the handoff writes the surviving tail by a power of three plus an
offset.  The instruction is literally “sparse binary prefix read, global
ternary write.”  [`two_rail_prefix_code.py`](../../experiments/kontorovich/two_rail_prefix_code.py)
audits the bounded prefix tree and literal decoder.

That `1/6` language was not the whole hardware.  It silently rejected odd
intermediate `+1`-rail gaps and outgoing gaps of one bit.  Simon's suggestion
that another aligned packet could eat the bad collision gives the exact
parity-dual branch.  At an odd gap `2s+1`, the last state is

```text
1+2*3^s Q,
```

and its next accelerated step has valuation one and endpoint

```text
2+3^(s+1)Q = -1+2^L P'.                         (6)
```

The congruence `3(1+3^s Q)=2^L P'` is the promised sacrificial alignment:
the low payload bits absorb the dirty constant and regenerate the `-1` rail.
Allowing `L=1` means the next rail has zero free ticks but a perfectly legal
immediate collision.  The even cleanup family, now also with `L>=1`, has
Kraft mass `1/3`; the odd catcher has mass `2/3`.  Their sum is one.

This is not only a measure calculation.  For every nonnegative rail length
and every positive odd payload, the first collision either reaches `1` or
its `+1` gap has exactly one parity.  The corresponding terminal collision
then has a unique positive outgoing gap `L>=1`.  Hence every nonhalting
payload decodes into exactly one parity-complete splash instruction.  The
[exact checker](../../experiments/kontorovich/complete_splash_isa.py) builds
both affine families, literally replays their words, and audits the combined
prefix tree.  The remaining challenge is no longer instruction coverage; it
is to find one ordinary decoded tape avoiding the explicit halt with positive
long-run drift.  Lean commits `afb86a5`/`f7ac880` certify the odd catcher's
exact word, endpoint, affine cylinders, and cross-branch disjointness,
including `r=0,L=1`.  Commit `78d1048` proves total existence: every positive
odd payload has a certified halt, generalized even-cleanup, or odd-catcher
outcome.  Commit `92f237c` proves that proof-carrying outcome unique.  The
parity-complete decoder semantics are now kernel-closed.

Lean commits `88e2577`/`b023700` turn those semantics into the canonical
partial map on public states `(r,P)`: halt maps to `none`, while either splash
maps to its unique outgoing `(L-1,P')`.  A surviving strictly outward orbit of
that map kernel-compiles to `¬Collatz`.  Hence the mathematical target no
longer includes hidden gate certificates—only a public payload recurrence.

The splash must therefore regenerate a **rewritten instruction tape**, not the
same schedule.  The live target is a finite controller which branches on the
changing residual tail and thereby emits a genuinely aperiodic gate sequence,
or an unbounded shape parameter such as an increasing rail length.  This is
closer to a true tag system than to an oscillator.

The standard increasing-length schedule's necessary recurrence reduces its
ordinary-integer gate to the 2-adic Tschakaloff value derived in
[`standard-two-rail-theta.md`](standard-two-rail-theta.md).  The full-source
Väänänen--Wallisser theorem audited there proves that value irrational, so
this rigid schedule is now closed.  A branching schedule remains open.

## 5. Three exact machines to mine for a bouncer

### Mixed binary--ternary rewriting

Yolcu, Aaronson, and Heule give an 11-rule string rewriting system over
`{f,t,0,1,2,/,.}` whose termination is equivalent to Collatz.  The auxiliary
rules preserve the represented integer while swapping adjacent base-2 and
base-3 positions; the two dynamic rules implement the shortcut map.  This
presentation localizes binary whole-word carries at a moving mixed-base
boundary and is the best carrier for formula-tape certificates.

Search object: a valid canonical configuration family, allowing repeat
segments, arithmetic counters, rotated Colussi tracks, and congruence fields,
with a bounded rewrite proof `C(h)->+C(h+1)`.  The auxiliary subsystem is
terminating, so a candidate must contain infinitely many certified dynamic
steps rather than merely churn representations.

### De Mol's 2-tag system

De Mol encodes the problem by a deletion-2 tag system on three symbols,

```text
0 -> 12,       1 -> 0,       2 -> 000,
```

started at the unary word `0^n`; reaching `0` is equivalent to convergence of
`n`.  A production reads the left edge, appends at the remote right edge, and
deletes two symbols.  It therefore exposes the exact head--tail nonlocality
Simon anticipated.  Literal words are enormous, but run-length formulae can
be small.  The search target is a run-length bouncer whose one-period crossing
can be lifted by induction.  The small rule set is not claimed to be
universal.

Cocke and Minsky prove universality for the *class* of deletion-two tag
systems, not for every small member and not for De Mol's three-rule system.
Their construction makes the missing operation precise: the simulated Turing
tape is a state plus two binary stacks `(Q,M,N)`; a head move pops the low bit
of one stack (`N -> floor(N/2)`) and pushes a bit onto the other
(`M -> 2M+b`), then changes `Q`.  A tag word realizes this by deleting at one
end and appending at the remote other end.

The delay link (21) has a complete bounded ternary write alphabet, but it does
not yet implement that queue geometry: it divides a binary address and then
multiplies the surviving *same integer* by a power of three.  Mixed-radix
reinterpretation can create nonlocal carries, but “all 243 output words” is
not a universality result.  A sharper spatial compiler target is therefore a
pair of separated packet registers with exact pop/push and state-transition
macros.  Regeneration must move the collision boundary between those packets
without consuming an infinite preloaded address.

### Dyadic--triadic arithmetic gates

Equation (2) is already a formula configuration.  Instead of enumerating
packets, search for a finite controller and symbolic payload family
`q=Q(m,z)` such that the gate maps `Q(m,z)` to `Q(m+1,F(z))`.  The controller
may inspect residues at both `2` and `3`; it need not be a local or periodic
function of `e`.  Proposed relations are falsified on exact integers before a
universal algebraic proof is attempted.

### Rational-base tapes and the spatial grid

Two exact presentations make the spatial metaphor less speculative.  Stérin
and Woods' quasi-cellular automaton draws Collatz iterates as binary rows while
ternary columns simultaneously perform base conversion.  The least-
significant-bit bootstrap is nonlocal, but the interior update is a finite
two-dimensional transducer.  A glider could therefore be a repeating diagonal
defect or boundary signal in this binary/ternary spacetime, provided it is
translated back to a canonical positive integer.

Eliahou and Verger-Gaugry's rational-base-`3/2` presentation supplies a second
tape.  Shortcut Collatz appends a rightmost digit `1`; on saturated words over
digits `{1,2}`, their auxiliary map appends `1` or `2` and is divergent.  This
does not transfer divergence to Collatz.  It gives a concrete compiler target,
and the first block now exists.  The two-rail shapes

```text
(5,0,2,1,2) -> (1,0,2,1,2)
```

link their family indices by

```text
95+128t -> 1640+2187t = U^7(95+128t),
```

executing the append block `[1,1,1,1,1,2,1]` for every `t>=0`.  The saturated
orbit reaches this cylinder at time 41.  The linked target then shrinks and
does not renew, so this is one instruction compiler, not a simulation of the
whole divergent `U` orbit.  The attack now seeks a payload-selected chain of
such blocks.  This preserves Kontorovich's spatial delay-line intuition while
allowing Simon's instruction to be a global boundary/carry condition.

A second exact bridge is longer and exposes the value of the complete
catcher.  Coefficientwise affine iteration gives

```text
U^12(1023+4096t)=132860+531441t
```

with ten appended `1`s followed by `[2,1]`.  It links the shapes
`(10,0,4,2,11)` and `(10,2,1,3,2)`, and both families are universally
outward.  At the saturated orbit's first entry, time 622, the next payload
has odd intermediate gap one.  The old grammar stopped; equation (6) decodes
the catcher `(r,s,a,L)=(1,0,3,6)`.  That catcher shrinks.  Continuing the
total decoder gives 290 exact macros, 101 outward, and then the explicit
halting collision `5->1`.  So “splash the splash” repairs the syntax but has
not yet repaired the energy budget.

The first complete bridge-graph audit now quantifies what the odd catcher
buys.  In the source box `r<=15,s<=4,a,b<=4,L<=16`, 11,312 of 25,600
parity-complete source families are universally outward.  Exhausting all
2,751,680 coefficient-compatible target shapes yields 18 exact saturated
bridges—14 with odd-catcher sources and four with even-cleanup sources.  Eleven
linked target subfamilies remain universally outward.  The simplest new compiler instruction is

```text
U^3(7+8t)=26+27t,
odd (1,0,1,1) -> odd (0,0,1,1),
```

with both selected sides outward.  But every one of those 11 target shapes is a dead end:
its complete next-target list, 718 candidates in total, contains no second
saturated bridge.  This closes depth two only for the 18 first edges found in
the stated source box.

There is nevertheless a universal three-gate outward *Collatz* cascade.  In
the `U^12` bridge, impose the nonlocal tail address `t=0 mod 16`.  The two
compiler gates then feed the outward odd catcher `(1,0,1,2)` for every
remaining natural tail.  The least member is

```text
2199021754367 -> 2229023590399 -> 5083728186203 -> 8578791314219.
```

It reaches `1` after 133 accelerated steps.  This is exactly Simon's aligned
“splash the splash,” now with net gain through three gates; it is not yet a
renewing instruction or evidence that a finite refinement stabilizes to an
ordinary infinite program.

Allowing ordinary splash gates between saturated blocks separates two
different obstructions.  With exactly one ordinary relay, the 11 two-outward
compiler nodes have 22 exact affine transitions but only one directed cycle,
a fixed self-loop.  Every infinite shape path in that restricted graph is
eventually periodic and is therefore closed by the existing valuation-word
theorem.

With two ordinary links, however, there is a universal spatial router.  For
arbitrary `r>=0,L>=1`, take the odd catcher

```text
R_(r,L)=(r,0,1,L),       word=[1]^r ++ [2,1].
```

It uses `r+2` odd steps and `r+3` halvings.  The exact inequality

```text
3^(r+2)>2^(r+3)
```

follows from `9>8` and induction, so every legal member is outward.  Its
outgoing gap `L` is arbitrary.  Given compiler edge `A->B` and desired next
edge `C->D`, choose `r=B.outputGap-1` and `L=C.inputGap`; coprime affine
intersection then compiles

```text
A -> B -> R_(r,L) -> C -> D.
```

[`complete_u_router.py`](../../experiments/kontorovich/complete_u_router.py)
checks all 121 ordered pairs of the current 11 nodes.  Every five-gate family
is universally outward, so the two-relay node graph is complete and can emit
arbitrary finite branching words.  This is a genuine programming-language
advance: finite control flow and spatial routing are solved in this ISA.  It
does not solve self-reference.  An infinite chosen node word still specifies
nested dyadic cylinders and usually only a 2-adic initial tail; the next object
must make that tail an ordinary positive integer by a public payload
recurrence, not by compiling longer prefixes.

Lean commit `fedb5ca` makes the two qualifications kernel-level.  It proves
the router outward for arbitrary `r,L` and every legal payload, and proves that
an ordinary natural realizing dyadic cylinders of unbounded precision forces
their canonical residues eventually to stabilize at that natural.  A changing
infinite address stream therefore needs genuine payload feedback; compactness
of the corresponding 2-adic cylinders is not enough.

There is a particularly small feedback core.  If every selected gate is a
router, put `r_n` for its amplifier length, `P_n` for its input payload, and
choose its outgoing gap as `L_n=r_(n+1)+1`.  The two router balance equations
collapse exactly to

```text
2^(r_(n+1)+3) P_(n+1) = 3^(r_n+2) P_n + 3.       (7)
```

Conversely, positivity and oddness together with (7) give the exact powers of
two required by the router word `[1]^r ++ [2,1]`.  Equation (7) forces every
output payload to be divisible by three.  Hence, after the first gate, write
`P_n=3H_n` and obtain

```text
2^(r_(n+1)+3) H_(n+1) = 3^(r_n+2) H_n + 1.   (8)
```

Lean commit `e9f791b` proves the converse and the all-level endpoint: positive
odd public payloads satisfying (7) construct the unique canonical router,
force strict endpoint growth, and refute Collatz if supplied forever.  No
hidden gate witness or extra outwardness assumption remains.  Commit
`c10e5b5` proves from (7) that `3|P_(n+1)` and kernel-identifies the next
`r,H` with the maximal power of two and odd part of the displayed numerator.

The two registers reduce to one.  Set

```text
y_n = 3^(r_n+2) H_n,
e_n = v_2(y_n+1).
```

Because `H_(n+1)` is odd, (8) makes `e_n=r_(n+1)+3`; because
`y_n+1` is nonzero modulo three, `3` does not divide `H_(n+1)`.  Therefore

```text
F(y) = 3^(e-1) * (y+1)/2^e,       e=v_2(y+1),      (9)
```

and `r_(n+1)=v_3(F(y_n))-2`.  The invariant window is

```text
9 | y,                    y = 7 (mod 8).
```

It guarantees `e>=3`, the output is automatically divisible by nine, and
`F(y)>y` since `3^(e-1)/2^e >= 9/8`.  A step survives precisely when
`F(y)=7 (mod 8)` again.  Thus the smallest current “hardware as software”
model is a one-register partial radix swap: remove the complete binary-zero
suffix of `y+1`, then install one fewer ternary zeros.  An infinite positive
orbit in this window is exactly the target; finite traces and 2-adic limit
points are not.

There is an equivalent symbolic description.  Expanding an accelerated
valuation `k` into shortcut parity bits `1 0^(k-1)`, the router word
`[1]^r ++ [2,1]` becomes

```text
1^(r+1) 0 1.
```

Across consecutive blocks, every two zeros are separated by at least two
ones; equivalently the parity stream avoids `00` and `010`.  This is a regular
constraint language, not a finite-state controller: its aperiodic choice must
still be made forever by the changing ordinary payload.  It gives the
Stérin--Woods spatial grid and mixed binary/ternary rewriting a sharply
defined diagonal-defect target.

Mahler's 1968 break-off algorithm is a close but nonidentical warning sign.
For odd `G`, it forms `H=(3G+1)/2`, puts `a=v_2(H)`, and replaces `G` by
`3^a H/2^a`; indefinite continuation is a necessary condition for a
Mahler `Z`-number, and none is known.  In our coordinate `z=y/3`, the Mahler
output is exactly `F(y)`, while the next router coordinate is
`z'=F(y)/3`.  Thus the router is a stricter, factor-three-reserving cousin of
Mahler's algorithm, not a reduction to or from the `Z`-number problem.  The
analogy says that raw long-survivor search is likely to hit the same
individual-orbit wall; the new opportunity is the additional invariant
`z=0 (mod 3)` and the exact Collatz spatial interpretation.

One last affine coordinate removes even the explicit invariant window.  Put
`y=8k-1`.  Then `9|y` is simply `k=8 (mod 9)`.  Write `k=2^j u` with `u` odd;
the next value is determined by

```text
B(k) = (3^(j+2)u+1)/8.                           (10)
```

If the division is integral, `B(k)=8 (mod 9)` automatically and
`B(k)>k`; moreover `8B(k)-1=3^(j+2)u`, so the next delay and payload are
literally `j` and `u`.  The legality test is only

```text
u=7 (mod 8) when j is even,
u=5 (mod 8) when j is odd.
```

Thus the pure-router disproof problem has become: find one ordinary
`k=8 (mod 9)` whose partial orbit under (10) never fails this three-bit test.
This statement is equivalent only to the router subclass, not to the whole
Collatz conjecture, but every surviving transition is already an outward
Collatz macro.

Lean commit `0b12d44` proves the all-level version in this coordinate.  Its
`BreakoffCounterOrbit` asks only for the binary and ternary factorizations
`k=2^j u`, `8k=3^(r+2)H+1` and the handoff `(r',H')=(j,u)`.  Lean derives
`k=8 (mod 9)`, strict growth, the public router recurrence, and finally
`¬Collatz`.  The same commit proves the necessary interior filter
`H=23 (mod 24)` for even `r` and `H=13 (mod 24)` for odd `r`.  The theorem is
conditional: it supplies the checker, not an infinite `k`.

Lean commit `7293975` closes the executable seam as well.  It defines the
partial map using the actual maximal binary valuation and odd part of `k`,
proves `breakoffNext k = some k'` equivalent to (10), reconstructs all
proof-carrying registers from an executable orbit, and obtains `¬Collatz`
from an infinite successful orbit.  Thus a formula-generated 10,000-digit
candidate need not ship hidden gate metadata; the remaining obligation is a
generic proof that its ordinary `k_t` formula survives the executable map for
every `t`.

For a fixed opcode `j`, the simultaneous mod-8 and mod-9 tests select one odd
residue `u_j (mod 72)`.  Writing `u=u_j+72t` turns (10) into the exact affine
tag instruction

```text
k = 2^j(u_j+72t),
B(k) = b_j + 3^(j+4)t.
```

The residues repeat with period six,
`u_j=71,13,47,37,23,61 (mod 72)`, because powers of two modulo nine do.  The
[exact checker](../../experiments/kontorovich/router_breakoff.py) constructs
these complete branches and translates literal members back through the
canonical splash decoder.  Its committed artifact lists `j=0..64` and
replays 64 tails per opcode.  Those 4,160 replays are bounded regressions; the
displayed coefficient identities and Lean router theorems carry the universal
semantics.

### 5.10 A collision can consume and regenerate a spatial gap

Simon's “splash the gap” question has a literal answer in the `k` coordinate.
For `q>=1`, define a clean delay-line state

```text
k = 9*2^(3q)c-1.                                      (11)
```

It is odd and is a legal opcode-zero state.  One application of (10) gives

```text
9*2^(3q)c-1  ->  9*2^(3(q-1))(9c)-1.                 (12)
```

Thus one instruction consumes exactly three clean binary gap bits while the
nonlocal coefficient is multiplied by nine.  After `q` ticks, the low packet
meets the coefficient at the collision state

```text
3^(2q+2)c-1 = 2^j u,          u odd.                  (13)
```

The dirty odd part `u` is not merely debris.  If it is aligned so that

```text
3^j u+1 = 2^(3(q'+1)) c',     c' odd, q'>=1,          (14)
```

then the collision instruction emits

```text
9*2^(3q')c'-1,                                        (15)
```

another clean delay line.  This is precisely the proposed sacrificial
cleanup: the collision's distributed odd bits absorb the carry and install a
new all-zero region farther across the binary word.

The construction is complete at the level of one finite gate.  Eliminating
`u` from (13)--(14) gives

```text
2^(j+3q'+3)c' = 3^(j+2q+2)c + 2^j - 3^j.             (16)
```

For every `q,q'>=1` and `j>=0`, exactness of the output valuation selects the
unique class

```text
c = 3^(-(j+2q+2))
      * (3^j-2^j+2^(j+3q'+3))
      (mod 2^(j+3q'+4)).                              (17)
```

All powers of three are invertible modulo the displayed power of two.  If
`c=c_0+2^(j+3q'+4)t`, the corresponding `u` and `c'` are affine with strides

```text
2^(3q'+4) 3^(2q+2),        2*3^(j+2q+2),              (18)
```

respectively.  The smallest useful regression at `(q,j,q')=(1,2,1)` has
`c=13,u=263,c'=37` and

```text
935 -> 1052 -> 2663.
```

The first step consumes its one delay cell; the second performs the collision
and restores one.  The ordinary seed nevertheless later reaches `1`.

[`breakoff_delay_gate.py`](../../experiments/kontorovich/breakoff_delay_gate.py)
constructs these affine classes and replays each delay tick and collision
through the canonical Collatz router.  Its audit covers all 1,088 triples
`q,q' in 1..8`, `j in 0..16`, with eight tails each (8,704 literal macro
replays).  This establishes a finite regenerative instruction family, not an
infinite orbit.  The unresolved seam is global and nonlocal: the outgoing
coefficient `c'` of every gate must itself lie in the input cylinder of the
next gate for one fixed ordinary integer.  Lean commit `a1a5fd0` proves that
the resulting collision-opcode sequence cannot even become periodic; a
successful “program” must continually generate fresh arithmetic information.

Lean commit `eac55d3` now removes the bounded audit from the semantic trust
path.  It proves the compressed `q`-tick delay identity for every positive
coefficient, reconstructs the executable collision registers from (13),
proves the renewal (15), composes the whole run, and proves it strictly
outward.  The coefficient-residue existence formula (17) remains
research-side exact algebra; any supplied instance needs only its two small
factorizations to use the kernel theorem.

### 5.11 The linked gate is a binary-read/ternary-write instruction

Take two gates whose boundary delay agrees, and require the second collision
opcode to be positive.  The first gate's output coefficient and the second
gate's input cylinder have forms

```text
c_out = o + 2*3^A t,
c_in  = r + 2^(m+1) s,                              (19)
```

where both `o` and `r` are odd.  Consequently the linking equation always
reduces to one invertible congruence

```text
3^A t = (r-o)/2          (mod 2^m).                 (20)
```

Choose its least solution `t_0` and lift by a whole period if needed to make
`s_0` nonnegative.  Every linked pair is then

```text
t = t_0 + 2^m v,
s = s_0 + 3^A v,          0 <= s_0 < 3^A.           (21)
```

This is a literal mixed-radix tag instruction.  It reads and deletes the
`m` low binary address bits of the nonlocal tail, then appends the fixed
`A`-digit base-three word `s_0` to the residual `v`.  The units of the
program are therefore neither neighboring bits nor fixed-size symbols: the
read address and the written trits span different, state-selected digit
boundaries, exactly as Simon anticipated.

The artifact checks all 4,608 ordered link shapes with three delay parameters
in `1..4`, first opcode in `0..8`, and second opcode in `1..8`; two affine
members per link give 18,432 literal gate-macro replays.  A separate complete
alphabet audit fixes the dispatcher `(q,j,q')=(1,1,1)`, for which `A=5`.
Among next gates with opcode at most 34 and output delay at most 44, it records
an exact binary address for every `s_0 in 0..242`: all 243 possible five-trit
write words occur.  This is bounded completeness of one instruction alphabet,
not universality of the Collatz map.  A reusable program still needs a return
path to a dispatcher and, ultimately, one ordinary initial tail whose
aperiodic execution continues forever.

Lean commit `1711620` proves both directions between the two collision/renewal
factorizations and the subtraction-free form of (16).  Commit `54e506f`
formalizes affine delay families and pairwise tail links: base and stride
identities imply (21), exact ordinary endpoint/start equality, a composed
two-gate executable run, and strict outwardness for every `v`.  These theorems
do not infer an infinite chain from pairwise links.

Commit `5254194` supplies the decisive acceptance test.  A link whose first
tail stride is `2^m` accepts exactly one dyadic address cylinder.  For a
sequence of such cylinders with unbounded precision, if one ordinary natural
tail belongs to every cylinder, then the canonical residues eventually equal
that natural literally.  Therefore a dispatcher whose addresses change
forever is only describing a 2-adic tape.  An ordinary program must eventually
stop reading previously unspecified bits of its *initial* tail; its later
aperiodic control must instead be generated by the payload already written by
the hardware.  This is the exact point at which finite instruction-set
completeness falls short of a counterexample.

### 5.12 Immediate ordinary stabilization is sparse

The ordinary-tail theorem suggests an extreme acceptance strategy: stop
requesting new initial bits immediately.  For a shape `(q,j,q')`, take the
least coefficient `c_0` in (17), execute its gate, decode the next shape from
the output coefficient, and require that coefficient to equal the next
shape's own least representative.  This is a tail-zero or **base-to-base**
edge.

Canonical spatial representation matters.  If `8|c`, then

```text
9*2^(3q)c-1 = 9*2^(3(q+1))(c/8)-1,                  (22)
```

so the purported source has merely hidden another whole delay cell in its
coefficient.  It is the same ordinary state with a nonmaximal gap label.
`search_delay_base_graph.py` separates these aliases before counting programs.

Its exact artifact exhausts the rectangular shape class

```text
1<=q,q'<=100,       0<=j<=100.                       (23)
```

Of 1,010,000 shapes, 992,129 do not emit another clean delay, 17,861 emit a
next gate only in a positive-tail subcylinder, seven tail-zero hits are
noncanonical by (22), and three canonical base edges remain:

```text
(1,1,90) -> (90,5,1),
(1,2,61) -> (61,4,1),
(2,2,61) -> (61,4,1).                                (24)
```

The target of every edge in (24) fails its next renewal, giving maximum
canonical chain length one in (23).  Every source and target macro is
literally replayed.  Exact full continuation sends the corresponding 85-,
59-, and 59-digit starts to `1` in 330, 1,272, and 1,277 ordinary steps.  This
closes only the simplest immediate-stabilization dispatcher in the displayed
box.  A viable ordinary program can still stabilize its *initial* address
while later gates branch on nonzero payload manufactured by earlier steps.

There is also a narrow algebraic warning for the two-stack analogy.  A direct
affine delay link writes its surviving parameter with coefficient `3^A`,
`A>0`.  A binary push by `p` places would require coefficient `2^p`.
Coefficient comparison makes those unequal: for `p>0` one is odd and the
other even, while for `p=0` the latter is one and the former is greater than
one.  Formalization has been requested.  Consequently a Cocke--Minsky stack
cannot be represented by the current *single affine residual parameter* with
one fixed instruction.  The live escape is precisely a nonlinear two-packet
encoding or a payload-selected collision turnaround.

### 5.13 A remote packet can amplify a sacrificial gap

There is now an exact positive form of Simon's proposal that bits distributed
across the word might eat a collision's dirty part and regenerate its gap.
Use the complete five-trit dispatcher, whose link instruction has write
stride `3^5`, and select the word

```text
b_L=3^5-2^L,             1<=L<=7.                    (25)
```

Every `b_L` lies in its certified 243-word alphabet.  Give the instruction a
residual packet with a low Mersenne boundary,

```text
v=K*2^L-1.                                             (26)
```

The native mixed-radix write (21) becomes

```text
b_L+3^5v = 2^L(3^5K-1).                              (27)
```

This is a literal sacrificial carry.  The `L` terminal one-bits in (26)
collide with the complement word (25) and emerge as `L` zero-bits.  The
regenerated gap is controlled nonlocally: for any `D>=1`, choose the unique
odd class

```text
3^5K = 1+2^D  (mod 2^(D+1)).                         (28)
```

Then `v_2(3^5K-1)=D`, so (27) has exactly `L+D` trailing zero-bits.  Bits of
the remote packet `K`, not just symbols adjacent to the collision, determine
the extra gap length.

`splash_gap_amplifier.py` selects the actual certified target gate for every
word (25), reconstructs its link, and checks (27)--(28).  Its artifact covers
all seven `L` and `D=1..32`: 224 linked members and 448 literal gate macros.
The formulas themselves are unbounded; formalization of their factorization
form has been requested.

This does not yet regenerate the *public* delay coordinate `q`.  The zeros in
(27) are nested inside the residual tail, behind the target gate's fixed
address.  The new architectural target is therefore a two-stroke turnaround:
a later instruction must expose this nested gap, retain the odd part of
`3^5K-1`, and rewrite it into another packet of form (26).  Achieving that
would turn a finite carry amplifier into a gap bouncer; no such returning
family is presently known.

### 5.14 A regenerative finite ether and a defect

The gap amplifier can be centered at a periodic 2-adic background rather than
at zero.  Let `E` be the delay gate `(q,j,q')=(1,2,1)`.  Its exact self-link
in tail coordinates is

```text
t=20+2^8v  ->  t'=57+3^6v.                           (29)
```

The affine fixed point of (29) is `tau=-12/473`, and eliminating `v` gives

```text
2^8(473t'+12)=3^6(473t+12).                          (30)
```

Because the odd factor `3^6` changes no binary valuation, a positive ordinary
tail with

```text
v_2(473t+12)=8n                                      (31)
```

executes exactly `n` self-links, losing eight bits of ether precision at each
one, and then exposes its boundary.  An infinite repetition of `E` is the
already-forbidden periodic 2-adic program.  Formula (31) instead describes an
arbitrarily long *finite* periodic background on which a defect can travel.

There is an exact defect writer.  Put `H=(1,136,1)`.  The links `E -> H` and
`H -> E` meet after the residual substitution

```text
v=177+2^8u,       w=504+3^6u.                        (32)
```

For the Mersenne-coded packet `u=2^8K-1`, their returned `E` tail has the
factorization

```text
473t+12=2^8(r+AK),                                   (33)
```

where the fixed `r` and `A` recorded by the artifact are both odd.  Therefore
for every `D>=1` there is one odd class of `K` modulo `2^(D+1)` satisfying

```text
r+AK = 2^D  (mod 2^(D+1)),                           (34)
```

and its returned tail has exact ether precision `8+D`.  Setting `D=8n-8`
constructs any prescribed finite `n`-cell ether.  This is the desired spatial
picture: a two-gate defect emits a periodic delay medium whose length is
selected by an unbounded, nonlocal packet.

`breakoff_ether_defect.py` reconstructs both defect links, checks (29)--(34),
and literally replays every ether cell.  Its artifact covers `n=2..32`, 589
linked members, and 1,178 gate macros.  Formalization of the two universal
factorizations has been requested.

The `j=136` defect does not itself receive that boundary: its `E` input
address is even, whereas (31) exposes an odd tail.  This is an all-level parity
obstruction, not a bounded miss.  The compatible odd defect and its complete
return are described next.

### 5.15 A returning finite ether glider ISA

For an immediate defect `E -> H_j -> E`, every `j>=2` forces the input
coefficient of `H_j=(1,j,1)` to be `1 mod 4`; since `E`'s output base is also
`1 mod 4`, the corresponding `E`-tail address is even.  The sole
parity-compatible opcode is `j=1`.  Put `H=(1,1,1)`.  Its exact links are

```text
E -> H:  67+2^7v -> 381+3^6v,
H -> E: 151+2^8w -> 144+3^5w.                       (35)
```

They meet under

```text
v=170+2^8u,       w=485+3^6u.                       (36)
```

Substituting the sacrificial packet `u=2^5K-1` makes the returned `E` tail
especially small:

```text
t=5668704K-59148,
473t+12=2^5(83790531K-874281).                       (37)
```

For every `n>=1`, one odd class of `K` modulo `2^(8n-4)` makes the second
factor in (37) have exact valuation `8n-5`.  Hence the return emits exactly
`n` cells of the ether (29).  After those cells, the boundary is odd.  Solving
one more congruence places it in the next copy of the same defect family,
whose `E` input tail is

```text
X(K')=2^20K'-10941.                                  (38)
```

Eliminating the internal packet and boundary parameters gives a complete
affine macro for every length:

```text
K=R_n+2^(8n+15)q -> K'=S_n+3^(6n+11)q.              (39)
```

Every member of (39) executes `E -> H -> E`, crosses `n` ether self-links,
and ends at the next state (38), ready to execute the same defect again.  This
is a literal finite glider instruction: a defect writes a periodic medium,
travels across it, and returns to its own instruction family.  Fixed `n`
cannot repeat forever because that would give an eventually periodic outward
valuation schedule, but a payload-generated aperiodic sequence of lengths is
not covered by that obstruction.

`breakoff_ether_glider.py` constructs (39), checks both affine coefficients,
and replays `n=1..32` at two tails each: 1,184 linked members and 2,368 gate
macros.  A separate exact audit tests the most stringent ordinary controller.
For every `n=1..128`, link `n -> n+1` and set the remaining higher macro tail
to zero.  The generated `(n+1)` tail misses the `n+2` cylinder in every case;
the maximum chain is two macros.  This closes only the exhausted-tail
staircase, not nonzero generated state.

The disproof target is now the native macro language (39).  Find one natural
sequence `(n_i,K_i,q_i)` with unbounded or otherwise aperiodic `n_i` such that
each output packet is the next input packet.  Pairwise compilation of an
externally specified infinite `n_i` is insufficient by the ordinary-tail
theorem.  The sequence of lengths must be computed from the transformed
finite payload itself—for example by a Mersenne/carry relation on `q_i`, a
branching finite-state transducer whose data register is unbounded, or a
second nested ether level.

### 5.16 The glider ISA collapses to one autonomous register

The macro bases in (39) look enormous because they encode two affine changes
of coordinates and a finite ether traversal.  They disappear in the register

```text
Y=83790531K-874281.                                  (40)
```

For an executable length-`n` macro,

```text
Y=2^(8n-5)h,       h odd,                            (41)
```

and the exposed-boundary congruence is simply

```text
3^(6n+11)h+51 = 0  (mod 2^20).                       (42)
```

The next register is

```text
Y'=(3^(6n+11)h+51)/2^20.                             (43)
```

The small constant is not fitted numerically.  The defect calculation has

```text
2^20*(-874281)-3^11*(-5175081)=51,                   (44)
```

which converts the boundary quotient directly into (43).

In Simon's spatial language this is a rigorous "splash the gap" rule: the
collision leaves the finite debris `51`, and the pre-positioned, nonlocal
bits selected by (42) absorb that debris into twenty zero bits, exposing the
next clean interface.  The central problem is now whether that regenerated
interface can contain the instructions for its own next regeneration.

Moreover

```text
Y=-874281  (mod 83790531),                            (45)
```

is preserved.  The modulus is `83790531=473*3^11`; its factors encode the
ether fixed point and the defect's ternary stride.

For fixed `n`, (45) selects `h` modulo `83790531` because powers of two are
invertible there, while (42) selects `h` modulo `2^20` because powers of three
are invertible there.  CRT therefore gives one odd class

```text
h=h_n + 83790531*2^20*q.                              (46)
```

Substituting (46) into (41)--(43) yields exactly (39), including both bases
and strides.  The input cylinders are disjoint because their exact valuations
`8n-5` differ.  Their total dyadic mass is

```text
sum_(n>=1) 2^-(8n+15)=1/(255*2^15).                  (47)
```

This is a direct quantitative version of Kontorovich's sparse-software
warning: the returning instruction language occupies about one part in 8.36
million of its packet address space even before asking for a second macro.

`breakoff_ether_counter.py` implements (40)--(43) as a public executable
partial map.  Its artifact checks `n=1..128`, four tails per CRT branch, and
proves by exact coefficient comparison that every branch equals the compiled
returning macro.  Literal macro replay is repeated through `n=32`.

An infinite successful orbit of (43), subject to (41)--(42) and (45), would
compile through (39) to an infinite outward Collatz glider.  No orbit is
supplied.  The new synthesis target is nevertheless much smaller than the
original map: a one-register valuation machine with exponent class
`3 mod 8`, fixed division exponent `20`, constant `51`, and a preserved odd
congruence.  Search should now emphasize symbolic invariant families for
(43), not raw Collatz stopping times.

### 5.17 Splashing the gap produces a recursive super-ether

The factor of three in (40) is invariant and exact.  Dividing it out gives
the primitive first-scale register

```text
Z=-291427+27930177K,
Z=2^(8n-5)g  ->  Z'=(3^(6n+11)g+17)/2^20.            (48)
```

Now regard the `n=1` branch `B=M_1` as a background *super-cell*.  It is

```text
K=3520715+2^23q -> K'=54200376+3^17q.                (49)
```

Writing `D=2^23`, `P=3^17`, `C=50679661`, and `G=P-D`, its self-link is

```text
q=4844785+Dv -> q'=74584052+Pv,                      (50)
F(q)=Gq+C,              D F(q')=P F(q).              (51)
```

Thus every background self-link consumes exactly 23 binary bits of `F` and
multiplies the remaining odd packet by `3^17`.

A literal exhaustion is the wrong operation.  If `F(q)` is odd, then (51)
forces `q` even because `G,C` are odd.  On the other hand, every first-scale
macro has odd input packet, so after executing `B` its source tail for a link
to any next macro has the opposite parity.  This closes the fully exhausted
recursive ether for the whole current glider alphabet.

Simon's proposed "splash the gap" overhang evades the obstruction sharply:
retain three bits rather than zero.  The two-cell macro supplies the defect

```text
B -> M_2: q=70933817+2^31v -> q_2=4265645+3^17v,
M_2 -> B: q_2=7704077+2^23w -> q'=86460874100+3^23w. (52)
```

The bridges meet at

```text
v=8279328+2^23u,       w=127457829+3^17u.             (53)
```

With `u=K-1`, the defect input and returned fixed form are

```text
q_in=-234676942119623+2^54K,
F(q_ret)=3^7*(-8744697538656344367967
              +671265207750760396088265K).           (54)
```

Let the primitive expression in parentheses be `V`.  Choosing its exact
valuation to be `23N+3` writes `N` background cells and leaves a three-bit
cap.  At the exposed boundary, `F=8 (mod 16)`.  Since `G=3 (mod 16)` and
`C=13 (mod 16)`, (51) gives `q=9 (mod 16)`, exactly the residue of `q_in`.
The remaining 50 binary address bits are therefore one ordinary modular
inverse, and the boundary re-enters (54).

The resulting autonomous second-scale machine is

```text
V=2^(23N+3)g  ->  V'=(3^(17N+40)g-17)/2^51,          (55)
K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t.             (56)
```

The sign flip is another exact cancellation, not a fitted recurrence:

```text
2^54*(-8744697538656344367967)
 -3^33*(50679661+120751555*(-234676942119623))
=-2^3*17.                                             (57)
```

`breakoff_superether.py` checks (48)--(57), constructs 64 branches with four
members each, and literally expands 32 super-macro members through 336
returning glider macros, 1,040 lower links, and 2,080 delay-gate macros.  This
is still finite.  Its significance is recursive: a nonlocal cap has absorbed
the collision debris while preserving the collision constant, changing only
`+17` to `-17` and the binary/ternary scales.  The next kill test is whether
the sign-flipped ISA nests again and, if it does, whether the nested addresses
can describe one ordinary natural rather than a nonterminating 2-adic word.

### 5.18 Finite sign-alternating renormalization hierarchy

The sign-flipped ISA does nest again.  The calculation is uniform enough to
state as a finite renormalization scheme.  Suppose one certified level is

```text
V=r+mK,
V=2^(an+b)g -> V'=(3^(cn+d)g+s*17)/2^e.              (58)
```

Its complete branch has input width `an+b+e` and output stride `3^(cn+d)`.
Let branch one be `B`, branch two be `H`, and write

```text
B: K=R+2^Aq -> K'=S+3^Cq,
F(q)=(3^C-2^A)q+(S-R).                               (59)
```

Compose `B -> H -> B`, factor the returned `F` by its exact inherited power
of two and common power of three, and retain

```text
cap=a+b                                                     (60)
```

bits after the background traversal.  Two finite identities are the kill
tests.  First, the boundary phase computed from

```text
q_boundary=((2^cap)-(S-R))/(3^C-2^A) mod 2^(cap+1)   (61)
```

must equal the defect-input phase.  Second, after division by `2^cap`, the
normalized collision numerator must be exactly

```text
-s*17.                                                (62)
```

When both pass, direct defect composition constructs every child branch and
agrees coefficientwise with CRT applied to a new register of the form (58).
The parameter update visible without the large affine offsets is

```text
a_new=a+b+e,
b_new=a+b-r0,
c_new=c+d,
d_new=3c+2d,
e_new=2a+b+2e+r0,
s_new=-s,                                             (63)
```

where `r0` is the exact inherited binary valuation of the shifted defect
return.  The offset and odd stride are the primitive coefficients remaining
after the common ternary factor is removed.

Branch one is not essential.  If branch `j>=1` is the background and the
adjacent branch `j+1` is the defect, retain `aj+b` bits.  The corresponding
visible update is

```text
a_new=aj+b+e,
b_new=aj+b-r0,
c_new=cj+d,
d_new=c(2j+1)+2d,
e_new=a(j+1)+b+2e+r0,
s_new=-s.                                             (63a)
```

The same phase and normalized-numerator checks decide the large hidden
coefficients.  The artifact evaluates every level-one `j=1..64`: all 64
adjacent defects return and give normalized constant `-17`.  It also checks
the nonconstant background words `(2,2,2,2)`, `(3,1,4,2)`, and `(8,5,3,1)`
through four renormalizations, with signs `+,-,+,-,+`.  Hence the spatial
hierarchy has a bounded verified meta-alphabet, not merely one substitution.
No all-`j`, all-level induction is claimed.

A first finite-quine test uses this alphabet directly.  For a meta-word
`(j_1,...,j_L)`, compile the length-`j_L` top branch with zero remaining tail
and expand it to the first-scale packet.  The construction makes the
depth-`L` macro word a prefix of the depth-`L+1` word.  Equality of consecutive
first-scale packets would therefore be an ordinary canonical-seed
stabilization, not merely a linked affine family.

The complete tree `1<=j_i<=8`, `L<=3` has `8+64+512=584` nodes.  Exact
arithmetic finds zero stabilizations and zero decreases: all 576 extensions
strictly increase.  The closest extensions are `(1,1)` and `(1,1,1)`, with
23 and 155 shared low bits, so variable syntax has not escaped the same 2-adic
address phenomenon at this bound.  This closes only the zero-top-tail quine
ansatz by itself; the identity below subsumes it for all positive child
payloads.  A serious next candidate must use an autonomous relation at one
fixed compiler level or a different defect grammar.

In fact the constructor itself supplies the all-payload kill test.  Let
`E=E_B+E_H` be the sum of the parent background and defect input exponents,
let `q_raw>0` be the raw defect input, and let `r0>=0` be the inherited binary
valuation.  The normalized child defect has input constant

```text
X=q_raw-2^E,
I=E+r0.
```

Consequently every positive child packet `K` enters its parent at tail

```text
q=X+2^I K
 =q_raw+2^E(2^r0 K-1)>0.                             (63b)
```

The inequality is unconditional once the adjacent-defect step exists:
`2^r0 K>=1`, and `q_raw` is positive by construction.  Thus no added
hierarchy level can expand to the canonical parent packet with tail zero.
The canonical dyadic addresses of an infinite nested tower change forever;
the ordinary-tail theorem therefore says that such a tower describes only a
2-adic program, never one ordinary natural.  The bounded meta-quine tree is a
useful calibration but is now subsumed by (63b).

This does not close the hierarchy's real computational residue.  At any fixed
finite level, an evolving nonzero packet can repeatedly use the same public
register without adding nesting depth.  Equation (63b) therefore redirects
the search from deeper spatial towers to autonomous fixed-level packet maps,
especially the unit-debris law in Section 5.19.

Exact arithmetic passes five such renormalizations:

```text
level       1      2       3        4         5          6
s           +      -       +        -         +          -
a           8     23      77      254       839       2771
b          -5      3      24      100       354       1192
c           6     17      57      188       621       2051
d          11     40     131      433      1430       4723
e          20     51     153      485      1578       5189
r0          0      2       1        0         1       --
cap         3     26     101      354      1193       --
```

The double construction is important: for every step and child length
`N=1..8`, `breakoff_renormalization.py` independently computes the public CRT
branch and the branch obtained by `B -> H -> B`, `N` background cells, and
the capped boundary.  All 40 coefficient pairs agree; 80 members expand
through 520 parent blocks.  This is a bounded six-level certificate, not a
proof that (61)--(62) continue forever.

There is now a concrete morphic program to reject.  Choosing length one and
zero remaining tail at every level expands by

```text
sigma(n)=1,2,1^n.                                    (64)
```

The depth-six word has 360 first-scale glider macros.  Exact expansion gives
a 6,708-digit ordinary start and replays 1,189 lower links and 2,378 gate
macros.  But the first-scale packet does not stabilize.  Its decimal lengths
at depths one through six are

```text
7, 46, 177, 606, 2021, 6698,                         (65)
```

and consecutive differences have exact binary valuations
`23,155,589,2013,6715`.  The low bits converge while the natural values grow:
the canonical tower is behaving exactly like a 2-adic program, not one
ordinary seed.  This is the central lesson of the hierarchy.  Further depth
alone is not an attack, and (63b) now rules it out as one.  A useful next
construction must stay at a fixed finite compiler level and evolve its packet
autonomously; adding another spatial nesting level can never make the lower
ordinary packet literal.

### 5.19 An invariant unit-debris sublanguage

The magnitude `17` can be removed on an invariant finite-index slice.  At any
certified level write its primitive register as

```text
V=r+mK,                                               (66)
```

where `m` is odd and, for the six constructed levels, coprime to `17`.  There
is exactly one class

```text
K=k_0=-r*m^(-1) (mod 17)                              (67)
```

with `17|V`.  Put `V=17H`.  If an executable branch has
`V=2^(an+b)g`, then `g=17h`, and the public law divides identically by `17`:

```text
H=2^(an+b)h -> H'=(3^(cn+d)h+s)/2^e,  s=+1 or -1.   (68)
```

In particular `17|V'`, so (67) is preserved without another address filter.
The nonlocal collision has reduced its residual from `±17` to the indivisible
unit `±1`.  This is algebraically adjacent to the repository's Mersenne and
negative-cycle-shadow coordinates, but (68) has different branch exponents;
no equivalence of their orbit problems is claimed.

Scaling once exposes the actual instruction.  Put

```text
p=an+b+e,   q=cn+d,   W=2^e H.
```

Then (68) is precisely

```text
W =2^p h,
W'=3^q h+s.                                          (68a)
```

The core `h` is coprime to six on every legal branch: oddness makes the
binary valuation exact, and the affine register phase makes the displayed
ternary valuation exact.  Thus (68a) is a reversible-looking FRACTRAN
instruction with an additive write bit: read the complete dyadic scale,
preserve the delocalized core, replace it by a triadic scale, and write `s`.
The next collision is the nonlocal test of whether `3^q h+s` contains another
legal binary instruction word.

There is an exact comparison with the earlier router.  Center the source and
target at the written sign,

```text
y=W-s,   y'=W'-s=3^q h,
```

and define the signed router expression

```text
R_s(y)=3^(p-1)*(y+s)/2^p=3^(p-1)h.
```

Therefore

```text
R_s(y)=3^delta y',   delta=p-1-q.                    (68b)
```

All six compiled levels have a strictly positive trim:

```text
level  s   p                 q                 delta
  1    +   8n+15             6n+11             2n+3
  2    -   23n+54            17n+40            6n+13
  3    +   77n+177           57n+131           20n+45
  4    -   254n+585          188n+433           66n+151
  5    +   839n+1932         621n+1430          218n+501
  6    -   2771n+6381        2051n+4723         720n+1657.
```

Equation (68b) is a coordinate comparison, not a claim that division by
`3^delta` is itself a Collatz macro.  It identifies the exact resource lost
relative to the router: a successful feedback architecture must bank a
variable ternary-zero packet of length `delta(n)` and re-inject it.  This is a
sharper two-rail target for Simon's splash metaphor than another clean binary
gap.  The Mersenne rail is a natural first bank because each separated tick
already transports a factor of three, but no exact bank/return composition is
yet supplied.

`breakoff_unit_slice.py` constructs (68) independently and intersects every
parent affine branch with (67).  For the six-level hierarchy and `n=1..32`,
all 192 input/output coefficient pairs agree; four members per branch give
768 public-map checks and 768 checks of (68a)--(68b), including exact ternary
valuation.  At level one, 32 members expand through 336 lower links and 672
literal gate macros.  The successive packet residues are

```text
k_0 = 3,16,0,2,6,8  (mod 17).                        (69)
```

Every constant-rate bank clock fails at the ordinary-integer gate.  Suppose
at one fixed level that

```text
p(n)=an+b+e,   q(n)=cn+d,
n_t=n_0+kt,                 k>=1 fixed.
```

Backward unrolling of (68a) gives the unique 2-adic core

```text
h_0=-s/3^(q(n_0)) *
    F(2^(ak)/3^(ck), 2^(p(n_0+k))/3^(q(n_0+k))),    (69a)
F(r,z)=sum_(j>=0) r^(j(j-1)/2)z^j.
```

Coefficientwise,

```text
F(2^(ak)/3^(ck),z)
 =f_(3^(ck)/2^(ak))((3^(ck)/2^(ak))z),               (69b)
```

where `f_q` is exactly the Väänänen--Wallisser theta function used to close
the earlier standard two-rail schedule.  Their 1989 theorem applies for every
`n_0>=1`, every fixed integer `k>=1`, with `ell=1`, `sigma=0`, `p=2`, theorem
parameter `3^(ck)/2^(ak)`, and

```text
alpha=2^(p(n_0))/3^(q(n_0)).
```

The argument is nonzero rational, is independent of `k`, and the
multi-argument ratio condition is vacuous.  Its only delicate uniform size
condition follows exactly from

```text
2^8>3^5,   3a>=4c,   45<64.
```

Indeed these give `a log(2)/(c log(3))>5/6` and hence
`1-a log(2)/(c log(3))<1/6<(3-sqrt(5))/2`.  Also
`3^c>2^a>1`; taking the `k`th powers preserves the inequalities, the
logarithmic ratio is unchanged because `k` cancels, and the 2-adic norm of
`3^(ck)/2^(ak)` is `2^(ak)>1`.  The published theorem therefore makes (69b),
and hence (69a), irrational in `Q_2`.  No constant-rate `n_t=n_0+kt` unit
schedule can have an ordinary integer initial core.

`unit_linear_theta.py` verifies finite unrolling against eight linked unit
transitions at each level for the step-one regression, checks the generalized
function conversion coefficients and all elementary theorem hypotheses, and
reaches 172,972 bits of terminal 2-adic precision at level six.  The
irrationality step remains a cited external theorem, not a reproof.  This
no-go matters architecturally: because
`delta(n+k)-delta(n)=(a-c)k`, every fixed-rate Mersenne bank is exactly a clock
just excluded.  A viable factor bank must let its unbounded ordinary contents
select a nonlinear, aperiodic length change.  In Simon's spatial formulation,
the second rail must be sacrificial and regenerative at once: its distributed
bits cancel the dirty collision suffix, but the surviving packet must select
and recreate the next clean gap.  A fixed periodic placement cannot do this.

That sacrificial mechanism is now exact at the unit level.  Fix three
successive positive branch lengths `n,m,l`.  Put `p=p(m)`, `q=q(n)`, and let
`C` be the unique low `L=p(l)+1`-bit word for which

```text
v_2(3^(q(m))*C+s)=p(l).                              (69c)
```

The extra bit in `L` records exactness, rather than divisibility alone.
Because `3^q` is invertible modulo every power of two, there are a unique
correction `A mod 2^(p+L)` and an integer carry `B` such that

```text
3^q A+s=2^p C+2^(p+L)B.                             (69d)
```

Now prescribe any `D>=1`.  A second inversion gives the unique sacrificial
word `z mod 2^D` and integer `B_2` satisfying

```text
B+3^q z=2^D B_2.
```

Hence, identically for every remaining tail `u`,

```text
A+2^(p+L)(z+2^D u)
  -> C+2^(L+D)(B_2+3^q u).                          (69e)
```

This is Simon's “other bits eat the bad parts” picture without metaphor.
`A` is the low collision circuit which emits the complete next instruction
`C`; `z` is a `D`-bit disposable packet which cancels its carry; the output
has a literal `D`-bit zero interval above `C`; and the untouched nonlocal
packet survives as `B_2+3^q u`.  Restricting `u` once modulo the odd register
stride makes (69e) an unbounded affine family of genuine linked unit macros.

[`unit_gap_regenerator.py`](../../experiments/kontorovich/unit_gap_regenerator.py)
checks (69c)--(69e), register invariance, exact valuations, and two compiled
unit branches.  The artifact reconstructs 486 families across all six finite
levels, triples `n,m,l=1..3`, gaps `D=1,4,12`, and two tail members, for 972
linked two-branch replays.  The construction itself is symbolic for arbitrary
positive lengths and `D`; those numbers scope only the executable regression.

The sacrificial word can itself be chosen to regenerate the collision carry.
Assume the canonical carry in (69d) is positive and smaller than `3^q`, put

```text
r=v_3(B),   e=q-r,   D=ord_(3^e)(2),
z=B(2^D-1)/3^q.                                    (69e+)
```

Then `z` is a positive finite `D`-bit word and

```text
B+3^qz=2^D B.                                      (69e++)
```

Thus (69e) becomes a literal carry translator: the low copy of `B` is eaten,
`D` zero bits open, and the identical `B` is deposited at the far boundary.
[`unit_carry_repetend.py`](../../experiments/kontorovich/unit_carry_repetend.py)
checks the concrete multiplicative orders and embeds the canonical one-cell
header in all three true register phases at six compiled levels.  The six
gap-length integers have `8,28,90,297,979,3231` decimal digits, while the
verifier never expands `2^D`.

This is Kontorovich's glider picture in a precise but finite form: `B` travels
unchanged through a rational-repetend ether cell.  Concatenating finitely many
catcher blocks gives an arbitrarily long finite delay line.  Preloading
infinitely many blocks is only a 2-adic tape, so the open **reseed** problem is
to make a finite ordinary end cap append the next catcher from the surviving
payload.  The likely architecture is two-ended: one rail pops a catcher at
the active low boundary while a charge phase pushes its formula description
onto the remote end.

There is a formula-compressed specialization which restores Kontorovich's
very long spatial wire.  Let an odd marker `C` and exponent `T` satisfy

```text
2^T C=s (mod 3^q),
R=(2^T C-s)/3^q.                                    (69f)
```

Then `R` is a positive ordinary integer and, for every `D>=1,K>=1`,

```text
3^q(R+2^(T+D)K)+s
  =2^T(C+2^D 3^q K).                                (69g)
```

This time the disposable packet is not stored as an arbitrary `D`-bit word:
it is one complete rational repetend generated by (69f).  Collision consumes
the whole rail, emits `C`, and recreates `D` clean positions before the remote
packet.  To make this a legal nonlinear unit jump, also require

```text
T=p(n')=a n'+b+e.
```

The exact order `ord_(3^q)(2)=2*3^(q-1)` places `T` in one discrete-log class;
CRT with `T=b+e (mod a)` supplies `n'`.  This succeeds at all six finite
levels for source length one.  Levels two through six use `C=1`; level one's
parity obstruction to `C=1` is repaired by `C=5`.  Its smallest audited jump
has

```text
q=17,  T=105734623,  n'=13216826.
```

Thus the first correction rail alone has about 31.8 million decimal digits.
At the six levels the decimal lengths of `T` are respectively
`9,29,91,299,980,3235`.  [`unit_repetend_splash.py`](../../experiments/kontorovich/unit_repetend_splash.py)
checks the exact orders, the level-one discrete logarithm, every CRT,
divisibility by `3^q`, and both odd-register phases using modular powers.  It
never expands `2^T`.  The artifact records gaps `D=1,64` at each level.

Equation (69g) is a genuine answer to the scale objection and a sharp new
test, not renewal.  Its emitted core `C+2^D3^qK` must itself enter another
repetend family.  Solving that handoff by another independently preselected
congruence simply hides an infinite 2-adic tape in `K`; a useful solution must
make the ordinary packet select and reconstruct the next `(C,T)`.

At the sign-negative second level, the emitted marker renews once by an exact
3-adic stability law.  Define

```text
c_m=(2^(3^(m-1))+1)/3^m.
```

Writing the numerator base as `-1+3^m c_m` and cubing gives

```text
c_(m+1)=c_m-3^m c_m^2+3^(2m-1)c_m^3.               (69h)
```

Thus `c_(m+1)=c_m (mod 3^m)`.  Once `m>=P`, the residue is frozen modulo
`3^P`.  For the first level-two splash,

```text
q_0=57,
T_0=21457252954121782025753972361,
n_1=932924041483555740250172709,
q_1=15859708705220447584252936093.
```

The register has `v_3(M)=33`, so take `P=q_0+33=90`.  If `c` is the stable
residue, exact CRT produces the odd multiplier

```text
k=376213925255524775706446580991916826376956379
```

with `kc=1 (mod 3^90)` and
`3^(q_1-1)k=54 (mod 23)`.  Put

```text
T_1=3^(q_1-1)k,
R_i=(2^T_i+1)/3^q_i,
A=(R_1-1)/(2*3^q_0).
```

The binomial expansion of `(-1+3^q_1 c)^k`, with `q_1>=90`, proves
`R_1=1 (mod 3^90)` and makes `A` integral through the complete register
conductor.  For a suitable ordinary class of positive `L`, the exact chain is

```text
R_0+2^(T_0+1)(A+2^(T_1+D-1)L)
 -> R_1+2^(T_1+D)3^q_0 L
 -> 1+2^D 3^(q_0+q_1)L.                            (69i)
```

[`unit_double_repetend.py`](../../experiments/kontorovich/unit_double_repetend.py)
checks the 89 finite quotient recurrences, constructs `k`, computes the
unmaterialized `R_1` modulo the coprime register conductor factors, and checks
all three public phases for `D=1,64`.  Exponent reduction uses the exact
Carmichael exponent of the level-two register.  `T_1` itself has about
`7.57*10^27` decimal digits.

Equation (69i) is genuine renewal through two nonlinear splashes, but it also
exposes the next trap.  Backward nesting a third independently selected
repetend changes another dyadic address of the initial core.  Iterating that
compiler produces a coherent 2-adic stack, not automatically one natural
program.  A live third step must be chosen by the fixed free packet `L`
already present in (69i), so that the canonical ordinary address does not
keep changing.

There is a stronger obstruction to making (69i) the whole program.  For any
sign-negative marker-one full repetend,

```text
T=(2j+1)3^(q-1).
```

When `q>=3`, exact induction gives `3^(q-1)>=2q+1`, and therefore

```text
2^T >= 2^(2q+1)=2*4^q>2*3^q.                       (69j)
```

The recurrence `2^T h'=3^q h-1` now gives `h>2h'`.  Thus `N` consecutive
full-order erasures force `h_0>2^N h_N>=2^N`; no fixed positive integer core
can execute infinitely many.  [`unit_repetend_energy.py`](../../experiments/kontorovich/unit_repetend_energy.py)
audits the exact exponent classes at sign-negative levels `2,4,6` and the
integer inequalities.  This closes the pure repetend staircase even if its
addresses could somehow be written autonomously.

The architectural correction is important.  The giant spatial wire is a
**discharge**, not an ether cell: it spends more than half the odd core to
relocate a marker across an immense binary gap.  A viable bouncer must insert
a sufficiently amplifying **charge phase** between such discharges.  That
phase must do two jobs at once—restore real core magnitude and synthesize the
next correction prefix.  Sparse repetend splashes inside an aperiodic
charge--discharge controller remain open; consecutive ones do not.

The finite unit ISA itself supplies an exact charge--discharge primitive.
At sign-negative level two, compose a length-`N` instruction with the
one-cell instruction.  Eliminating the intermediate core gives

```text
2^(p(N')+p(1)) h'
 =3^(q(N)+q(1))h-(3^q(1)+2^p(1)).                  (69k)
```

Here `p(1)=77`, `q(1)=57`, and

```text
3^57+2^77=5D,
D=314038802961906688057474567.                     (69l)
```

Because `gcd(D,M)=1` for the level-two register stride `M`, there is a unique
packet class on which the register is divisible by `D`; (69k) preserves that
class.  Dividing both endpoints produces

```text
G=499379675639703663139777
  +671265207750760396088265K,
G=2^(23N+3)g -> G'=(3^(17N+97)g-5)/2^128.          (69m)
```

The complete branches of (69m) have dyadic stride exponent `23N+131` and
triadic stride `3^(17N+97)`.  Since
`3^(17N+97)>2^(23N+131)` for every `N>=1`, each successful branch is strictly
outward.  [`unit_charge_discharge.py`](../../experiments/kontorovich/unit_charge_discharge.py)
constructs the branches both directly from (69m) and by restricting the
literal two-unit composition; its artifact compares `N=1..32` and replays
four members of each.

Equation (69m) is a notably smaller disproof target than the original unit
machine: any infinite successful positive orbit is already an outward
ordinary Collatz macro-orbit.  It is not such an orbit.  Its `-5` should also
not be conflated with the old signed-cycle shadow grammar: the latter shadows
negative periodic states, whereas (69m) is a positive quotient register
derived from two exact finite-level unit instructions.

That regenerative test succeeds uniformly.  At a recursive level with
ternary offset `d` and division exponent `e`, composing a length-`N` branch
with the one-cell branch produces fixed debris

```text
5D,             D=3^(17+d)+2^(26+e).               (69n)
```

On the unique packet class divisible by `D`, quotienting reproduces (69m)
with

```text
d'=2d+17,                 e'=2e+26.                 (69o)
```

Starting from `d_0=97,e_0=128`, this gives

```text
d_j=114*2^j-17,
e_j=154*2^j-26,
D_j=3^(114*2^j)+2^(154*2^j).                       (69p)
```

These divisors are coprime to the fixed stride
`M=671265207750760396088265` at every depth.  The proof needs only 79 exact
gcds.  If a prime `r!=3` divided `M` and `D_j`, then

```text
(3^114/2^154)^(2^j)=-1 (mod r),
```

so the order of the ratio would be divisible by `2^(j+1)`.  Therefore
`2^(j+1)<=r-1<M`.  Since `M` has 80 bits, only `j=0,...,78` can fail; all
those gcds are one.  The prime three is excluded directly by (69p).
[`unit_charge_hierarchy.py`](../../experiments/kontorovich/unit_charge_hierarchy.py)
performs this all-depth certificate, materializes eight levels, compares 64
direct/composed branches, checks 128 members, and expands selected members
through 510 original unit macros.

This is the strongest form yet of Simon's splash metaphor: the collision
debris is eaten and the same `-5` interface is regenerated at arbitrarily
large finite spatial scales.  It also supplies its own ordinary-address kill
test.  A positive child packet lifts as

```text
K_j=rho_j+D_j K_(j+1)>K_(j+1).                     (69q)
```

Thus deeper canonical nestings strictly enlarge the root packet and cannot
stabilize to one natural.  The recursive hierarchy is a formula-generated
finite compiler, not the desired infinity.  Its useful outputs are the
outward autonomous machines at each fixed finite level; a packet-selected
aperiodic orbit inside one of those levels remains live.

The rational fixed form of the base charge level turns that live problem into
a compact valuation bouncer.  Put

```text
A=3^114,              B=2^154,
F=(A-B)/5,
Z=FG-2^26.                                             (69r)
```

The register identity `Fr=2^26 (mod M)` makes `Z` integral on the whole
public register.  The one-cell branch is exactly homogeneous:

```text
B Z'=A Z.                                              (69s)
```

For a defect length `N=m+1`, the difference-of-powers term is exposed:

```text
2^(154+23m) Z'
 =3^(114+17m)Z
  +2^26 A(3^(17m)-2^(23m)).                           (69t)
```

Every defect boundary has `Z=2^26y`, where `y` is positive odd and

```text
y=0 (mod M),             y=-1 (mod F).                (69u)
```

The state reads its defect opcode and recharge count by

```text
m=v_2(y+1)/23,
E=3^(17m)(y+1)-2^(23m),
h=(v_2(E)-23m)/154.                                   (69v)
```

When `m,h>=1` are integers, (69t) followed by `h-1` copies of (69s) returns

```text
y'=3^(114h) E/2^(23m+154h).                           (69w)
```

The block renews precisely when `v_2(y'+1)` is another positive multiple of
23; literal register execution preserves (69u).  This is an autonomous
one-register language with two unbounded state-read opcodes, not an external
schedule.  Every accepted block is strictly outward, so an infinite positive
orbit of (69u)--(69w) is already an ordinary Collatz counterexample.
[`unit_charge_bouncer.py`](../../experiments/kontorovich/unit_charge_bouncer.py)
checks 64 complete `(m,h,m')` transition families in the box
`m,m'<=4,h<=4`, two members each, through 320 charge macros and 640 original
unit macros.  No infinite accepted orbit is supplied.  The fixed-form
bouncer, rather than a ninth nested charge level, is now the primary
formula-family target.

Accepted transitions also carry an exact reverse decoder.  Since the odd
quotient in (69w) is not divisible by three, write

```text
h=v_3(y')/114,
q=y'/3^(114h).
```

Then

```text
m=v_3(1+2^(154h)q)/17,
y=2^(23m)(1+2^(154h)q)/3^(17m)-1.                 (69x)
```

Equation (69x) recovers the unique predecessor.  The opcode matrix has the
small determinant

```text
114*23-154*17=4,                                   (69y)
```

or equivalently `2^(23*154)=2^(154*23)` while
`3^(114*23)=3^4*3^(17*154)`.  This makes the resonance rays
`(m,h)=(154t,23t)` and `(114t,17t)` the first formula-scale bouncer targets:
one radix cancels exactly and the other leaves only a fourth power.  The
remaining affine seam is essential; (69y) alone is not a transition or an
orbit.

Lean commit `5633c44` closes the frozen-opcode specialization.  For any fixed
`m`, the positive affine-gain recurrence has a fixed-point defect satisfying
`B delta'=A delta`; coprimality would force arbitrarily large powers of `B`
to divide one positive natural.  This does not instantiate on (69v)--(69w):
`m` may decrease or oscillate, and one block deliberately changes from its
`m`-defect law to `h-1` homogeneous background laws.  The artifact includes
all ordered pairs `m,m'<=4`, including strict decreases; no monotonic opcode
rank is assumed.

Three canned aperiodic clocks also fail their first bounded ordinary-address
test.  [`unit_charge_morphic.py`](../../experiments/kontorovich/unit_charge_morphic.py)
checks Thue--Morse, period doubling, and the Fibonacci substitution word;
every injective two-symbol coding by `(m,h)` with `1<=m,h<=4`; and all
prefixes through 48 transitions.  None of 34,560 consecutive canonical
addresses stabilizes.  This is a scoped grammar failure, not a theorem about
general morphic control.  It pushes the PL target from “emit an aperiodic
clock” to “make the odd payload perform the counter update or zero-test which
chooses the clock.”

The formal ordinary-address obstruction is now smaller than “show every
canonical address changes.”  For a prefix affine map followed by one more
dyadic input filter, write the old-tail restriction as

```text
t=rho+2^E*u.                                          (69z)
```

Lean commits `af1a934`/`ba121d9` prove that realization by one ordinary
natural forces `rho=0` eventually.  Hence it suffices to prove `rho!=0` at an
unbounded sequence of scales.  [`unit_charge_zero_lift.py`](../../experiments/kontorovich/unit_charge_zero_lift.py)
exhausts all words through depth four over the 16 small bouncer opcodes and
all next blocks: zero of 1,118,464 extensions have `rho=0`.  This is finite
evidence only.  The terminal two-adic agreement grows with depth, so no fixed
mod-`2^c` separator is asserted.

Simon's proposed **gap splash** should therefore be treated as a distributed
code rather than one collision.  Place several bit islands across an immense
zero gap so that their carry waves arrive in phases: a strike opens the main
collision, a scrub island cancels or absorbs its bad residue, and a reseed
island survives as the header of the next delayed configuration.  The
instruction is nonlocal in precisely Simon's PL sense: its operands are
spread over the entire digit span, while their spatial separations are clock
delays in Kontorovich's picture.  After fixing the valuation word each phase
is affine, so simultaneous phase alignment is a CRT problem.  What must be
synthesized is a parameterized catcher vector `C(n)` with an exact return
`C(n)->+C(f(n))`, not merely one beautifully clean finite splash.

The remaining obstruction is now a programming-language condition rather
than a missing collision gadget.  Reading (69e) from right to left, one
instruction pops the required low binary word `z` and pushes a power-of-three
affine carry onto the residual packet.  Repeating with externally prescribed
`z` words compiles any finite program but selects a 2-adic stack in the
infinite limit.  A counterexample needs a quine-like residual update: the
surviving ordinary packet must write the next sacrificial word before it is
needed, and its own low bits must select the next branch length.  This is the
precise mixed-base pop/push target for the next search.

A static odd-payload quine is closed immediately.  If one branch sent
`h` to the same `h` at another branch, then

```text
h*(2^B-3^A)=s.                                       (70)
```

Thus `h=1` and two nontrivial powers would differ by one; the hierarchy's
large exponent pairs are not the exceptional small solutions.  Periodic
payload/branch schedules were already closed more generally.  The live unit
problem is an evolving odd packet whose exact valuation-selected branch word
is aperiodic.

## 6. Ranked attack and kill tests

1. Implement the mixed-base rules and mine structured, formula-generated
   Colussi backgrounds for repeat crossings.  Anti-unify traces into proposed
   formula-tape rules; do not rank candidates by stopping time.
2. Build a symbolic `Div3` transducer for three rotated `s_h` tracks plus a
   finite defect.  Classify defects that die, translate, split, or reproduce
   as `h` increases.  Only the last two classes can support a bouncer.
3. Search exact closures of the packet gate on arithmetic relation families,
   not on packet intervals.  GPU code is retained only to falsify a proposed
   relation over a large bounded domain.
4. Treat (21) as the native mixed-radix tag instruction.  Search for a
   returning dispatcher or one-counter bouncer which uses the complete
   five-trit writer.  More stringently, compile Cocke--Minsky's two-stack
   primitives `N -> floor(N/2)` and `M -> 2M+b` into two separated packets;
   reject a writer that lacks remote-end queue semantics.  The tail-zero base
   graph is now closed through (23), so require nonzero state produced by
   earlier instructions or a nonlinear packet pairing.  Identity (27) is the
   first exact payload-generated gap amplifier; search for a turnaround that
   promotes its internal `2^(L+D)` factor to the next delay and reconstructs
   (26).  The returning macros (35)--(39) now solve finite ether, boundary
   exposure, and defect return.  Prioritize an autonomous nonzero-tail
   recurrence in this macro ISA over enlarging either replay bound.  Use the
   autonomous registers (48) and (55) as the primary search and proof
   interfaces.  Infinite recursive renormalization is now closed by (63b),
   and every constant-rate fixed-level clock is closed by (69a)--(69b); search a
   packet-selected nonlinear bank for the signed radix swap instead of
   widening either replay bound.
   Compare
   survivors
   with the run-length-accelerated three-symbol tag system and translate them
   back to a canonical positive integer before treating them as Collatz
   evidence.
5. Use the parity-complete splash decoder as a deterministic variable-length
   machine.  Search for a finite symbolic invariant of its natural payload
   map with genuinely aperiodic branch sequence and positive long-run drift;
   reject fixed return routes because their valuation words are periodic.
6. Extend the exact seven- and twelve-append rational-base bridges into a
   payload-selected block compiler.  Two ordinary catcher links now route
   every current compiler node to every other, so stop enlarging the finite
   graph as a primary tactic.  Search instead for a self-describing payload
   recurrence whose decoded node word is aperiodic and whose nested cylinders
   stabilize to one ordinary integer.  In parallel, search the Stérin--Woods
   spacetime for a diagonal defect implementing the same
   binary-address/ternary-write transitions.

Every candidate is rejected unless all of the following are explicit:

- a finite ordinary positive starting integer, preferably given by a short
  generator and exact digit-count metadata;
- exact valuation legality or value-preserving mixed-base rewrites at every
  macrostep;
- a universal induction parameter, not a long finite trace;
- infinitely many genuine Collatz dynamic steps and no visit to `1`;
- outward motion, or another well-founded reason the configurations never
  repeat into a halting state;
- the known residue-coverage obligations: a nonconvergent ordinary Collatz
  trajectory must visit every class modulo `4`, and in particular classes
  `2,3,4,6` modulo `8` (the remaining modulo-8 cases are not all known).

## Sources

- A. V. Kontorovich and Ya. G. Sinai, [*Structure Theorem for
  `(d,g,h)`-Maps*](https://arxiv.org/abs/math/0601622), 2002.
- D. Barina, [*Improved verification limit for the convergence of the Collatz
  conjecture*](https://doi.org/10.1007/s11227-025-07337-0), 2025.
- L. Colussi, [*The convergence classes of Collatz
  function*](https://doi.org/10.1016/j.tcs.2011.05.056), 2011; [author's
  repository copy](https://www.research.unipd.it/retrieve/e14fb267-5e97-3de1-e053-1705fe0ac030/TCS8412.pdf).
- L. De Mol, [*Tag systems and Collatz-like
  functions*](https://biblio.ugent.be/publication/436211), 2008.
- J. Cocke and M. Minsky, [*Universality of Tag Systems with
  `P=2`*](https://doi.org/10.1145/321203.321206), 1964.
- E. Yolcu, S. Aaronson, and M. J. H. Heule, [*An Automated Approach to the
  Collatz Conjecture*](https://arxiv.org/abs/2105.14697), 2023.
- T. Stérin and D. Woods, [*The Collatz process embeds a base conversion
  algorithm*](https://arxiv.org/abs/2007.06979), 2020.
- S. Eliahou and J.-L. Verger-Gaugry, [*The number system in rational base
  `3/2` and the `3x+1` problem*](https://arxiv.org/abs/2504.13716), 2025.
- K. Väänänen and R. Wallisser, [*Zu einem Satz von Skolem über lineare
  Unabhängigkeit von Werten gewisser
  Thetareihen*](https://gdz.sub.uni-goettingen.de/download/pdf/PPN365956996_0065/LOG_0016.pdf),
  1989; its p-adic linear-independence theorem applies exactly to the standard
  two-rail Tschakaloff value after the audited parameter substitution.
- [Reverse-mined Busy Beaver bouncer certificate
  semantics](../REVERSE-MINING.md#2b4-bouncers-formula-tapes--verified-shift-rules),
  with the distinction between a finite experiment and a universally checked
  shift rule retained here.
