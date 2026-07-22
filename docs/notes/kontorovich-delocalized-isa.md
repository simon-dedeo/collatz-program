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

[`packet_gate.py`](../../experiments/kontorovich/packet_gate.py) computes these
gates with exact integers.  Its current self-test checks the coefficient
identities and literally replays 8,192 gate/payload pairs (`1<=m,e<=8`,
`0<=q<128`).  A separate exhaustive converse pass recovers all 16,316 literal
renewals among odd `h<2^16` at levels `1..8`, including valuations outside the
displayed `e<=8` test rectangle.  These bounded checks test the implementation;
the algebra above is a research derivation pending the requested Lean theorem.

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
- [Reverse-mined Busy Beaver bouncer certificate
  semantics](../REVERSE-MINING.md#2b4-bouncers-formula-tapes--verified-shift-rules),
  with the distinction between a finite experiment and a universally checked
  shift rule retained here.
