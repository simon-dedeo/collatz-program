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
   five-trit writer, and compare it with the run-length-accelerated
   three-symbol tag system.  Translate any survivor back to a canonical
   positive integer before treating it as Collatz evidence.
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
