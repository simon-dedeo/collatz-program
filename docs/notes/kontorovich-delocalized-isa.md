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
does not transfer divergence to Collatz.  It gives a concrete compiler target:
implement the missing “append `2`” operation as a bounded exact two-rail or
mixed-base macro, then seek a self-generating saturated word.  This attack
preserves Kontorovich's spatial delay-line intuition while allowing Simon's
instruction to be a global boundary/carry condition.

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
4. Run-length accelerate the three-symbol tag system and look for a
   head--tail bouncer.  Translate any survivor back to a canonical positive
   integer before treating it as Collatz evidence.
5. Build a branching affine two-rail transducer.  Each instruction consumes a
   low-bit address and must choose the next gate shape from the residual tape;
   reject fixed return routes because their valuation words are periodic.
   Search for an invariant natural tape orbit with a genuinely aperiodic shape
   sequence or an unbounded rail-length counter.
6. Compile the rational-base saturated-map instruction “append `2`” into the
   mixed-base or two-rail ISA, and search the Stérin--Woods spacetime for a
   diagonal defect that implements the same return.

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
