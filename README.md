# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, formalization, and the new *Kontorovich Challenge*.
Certified claims are backed by
machine-checkable artifacts; research derivations and finite evidence are
scoped explicitly. Started 2026-07-20 (Claude Fable 5 +
GPT-5.6-sol; PSC Bridges-2 grant mth260010p).

Made possible by the support of Grant 63750, "Explaining Universal Truths",
from the John Templeton Foundation. Additional support from research funds
of the Laboratory for Social Minds and from the Survival and Flourishing
Fund. Proofs and Reasons — https://proofsandreasons.io

The proof-directed phase reached a synchronized checkpoint on 2026-07-21.
Active work has now resumed with the deliberately opposite objective described
in [The Kontorovich Challenge](#the-kontorovich-challenge): try to construct and
certify a counterexample.

## A note from the human

I (Simon) am a cognitive scientist, not a mathematician; http://santafe.edu/~simon/cv.pdf

This is a purely experimental project to see what these systems do, and how they reason. There are *many* problems with using AI for mathematics, some of which my colleagues and I have written about---see, e.g., https://arxiv.org/pdf/2603.13680 (*A correspondence problem for mathematical proof*, Eamon Duede and I). One of the things I'm most aware about is the fact that these machines are leveraging insights from real mathematicians, but are unable to properly credit their insights. Anything here should be credited to "the human mathematics community, with apologies." Our colleague, and Proofs and Reasons board member, Michael Harris has written eloquently about the core issues in a recent Boston Review article, https://www.bostonreview.net/articles/knowledge-collapse/

I chose the Collatz Conjecture for three reasons:

1. I understand the theorem!
2. A bit like Fermat's Last Theorem, everyone and their grandmother has worked on it, and any progress towards a proof is unlikely to harm an early-career researcher carving out a new niche.
3. There have been some lovely quanta articles about Collatz and the related Busy Beaver numbers recently, so it was a nice way to learn more https://www.quantamagazine.org/busy-beaver-hunters-reach-numbers-that-overwhelm-ordinary-math-20250822/ I had an idea that there was wisdom hiding in the Busy Beaver community that was partially orthogonal to what "regular" mathematicians know.

Everything below this line, and everything else in this repo, has been automatically generated. Claude Fable 5 drove the initial numerics and research program; a Codex/GPT instance then served as the successor research driver. A separate GPT instance formalized the work in Lean in `CLEAN_LEAN`; it was told to make something that would not annoy Kevin Buzzard. If you want the inter-company drama, visit https://github.com/simon-dedeo/collatz-program/blob/main/CLEAN_LEAN/FOR_FABLE.md

## The Kontorovich Challenge

The active goal is now to **try to disprove the Collatz conjecture**.  A
disproof means an exact positive-integer certificate: either a nontrivial
cycle, or a seed whose forward orbit is infinite and never reaches `1`.
Large excursions, floating-point evidence, and long prescribed prefixes are
search clues, not counterexamples.

The challenge comes from [Alex Kontorovich's 2019
thread](https://x.com/AlexKontorovich/status/1172715174786228224) and the
[Kontorovich--Sinai structure
theorem](https://arxiv.org/abs/math/0601622).  For the accelerated odd map

```text
T(x) = (3x+1)/2^k,   k = v_2(3x+1),
```

the structure theorem says, in particular, that every prescribed finite
`k`-word `(k_1,...,k_N)` occurs: for either admissible class modulo `6`, the
seeds realizing that prefix form one arithmetic progression modulo
`6*2^(k_1+...+k_N)`.  On each such progression the endpoint is another affine
arithmetic progression, with scale changed from `2^(sum k_i)` to `3^N`.
Consequently the finite path statistics are exactly those of independent
geometric `k_i`, and normalized logarithmic trajectories converge in density
to Brownian motion with drift `log(3)-2 log(2)=log(3/4)<0`.  This explains why
typical seeds descend; it does not control a sufficiently sparse exceptional
orbit.

Kontorovich's proposed reversal is to regard the map as fixed **hardware** and
the initial integer as **software**.  Verification through `b` bits has tested
all programs only through that input length.  The structure theorem lets us
compile any finite instruction word into an arithmetic progression of seeds,
so the disproof search should not sample typical seeds: it should synthesize a
highly structured instruction stream, a Collatz “glider”, whose binary pattern
reproduces while its scale grows.

Simon Dedeo suggested two refinements which now govern the KC strategy.  First,
mine ultra-simple programming languages—Brainfuck, tag systems, and FRACTRAN—
for macro, loop, counter, and nonhalting-certificate ideas, without assuming
that `3x+1` is universal.  Second, and more importantly, do **not** assume that
a Collatz instruction is spatially local.  Its natural unit may be a
congruence, a carry phase between remote packets, or a mixed-base relation
spread across the whole digit span.  The active instruction set therefore
includes formula configurations and dyadic--triadic bridge gates, not only
contiguous repeated bit blocks.  See the [delocalized-ISA
map](docs/notes/kontorovich-delocalized-isa.md).

Nonlocality does not replace Kontorovich's spatial picture.  Long zero gaps
remain literal delay lines and separated packets remain signals; the new
working architecture is **spatial wires joined by delocalized collision
gates**.  Simon further suggested a “gap splash”: align sacrificial packets so
their collision carries eat a dirty suffix and emit a new empty gap.  Exact
splash gates below show that the mechanism is real, while also exposing the
need for an amplifying rail.  The first exact large wire is now in the
headline table below.

The scale reinforces this choice.  Barina's current published verification
covers every seed below `2^71`, already about 21 decimal digits.  A putative
10,000-digit program is not a larger interval-search target: it must be emitted
by a short generator and proved nonhalting by a finite symbolic certificate.

The thread also proposes a more concrete glider mechanism.  After a suitable
prefix, its example becomes three widely separated `1`-bits.  Until a carry
arrives from the right, an isolated high packet is acted on by multiplication
by `3`, while the rightmost packet feels the `+1`.  For `m>=3`, the order of
`3` modulo `2^m` is `2^(m-2)`, so distant packets can in principle be placed
and timed to collide with a low-bit trajectory selected by the structure
theorem.  The challenge is to make those collisions replenish a packet farther
left forever—not merely arrange any finite sequence of spectacular-looking
collisions.

There is a crucial exact caveat.  Nested progressions for an arbitrary infinite
`k`-word determine a 2-adic integer, not necessarily a positive ordinary
integer.  Equivalently, if `S_j=k_1+...+k_j`, then

```text
T^N(x) = (3^N*x + A_N)/2^S_N,
A_N = sum_(j=0)^(N-1) 3^(N-1-j) 2^S_j.
```

Every proposed glider must therefore pass three gates simultaneously: exact
valuation legality, an ordinary positive seed rather than only a 2-adic one,
and certified nontermination.  Finite-prefix realizability alone passes only
the first gate.  Lean commit `ad36f08` makes the middle gate exact: for a fixed
mod-6 class, an infinite positive valuation stream belongs to an ordinary
integer `x` if and only if its canonical finite-prefix seeds are eventually
identically `x`.

### KC Strategy and failure map

#### Live disproof programs

- **Delocalized instruction synthesis.**  Represent an instruction as an
  arithmetic relation across the entire state: a dyadic address, triadic
  phase, carry boundary, and affine high payload.  Search for formula
  configurations `C(n)` with a bounded exact return rule
  `C(n) ->+ C(f(n))`, where the rule lifts to every `n` by induction.  This is
  the Collatz analogue of a Busy Beaver bouncer and directly implements
  Simon's nonlocality proposal.
- **Colussi repetend-defect bouncers.**  Use the exact periodic grammar of the
  halting classes as a structured background, then search for a finite or
  congruential defect which reproduces from order `h` to order `h+1`.  The
  order-10 background has 39,366 padded bits and an 11,846-decimal-digit
  integer value, so this route reaches the proposed program scale by formula,
  not enumeration.  Its unmodified background has now been decoded into an
  exact 19,673-tick spatial delay line; because the ensuing collision does not
  renew the gap, the live variable is a distributed defect in the header or
  packet phase.
- **Mixed-base and tag-system bouncers.**  Mine the exact Yolcu--Aaronson--Heule
  binary/ternary rewrite system and De Mol's three-symbol deletion-2 tag
  system for formula-tape or run-length returns.  These presentations make
  whole-word carry, moving-base-boundary, and head--tail nonlocality explicit.
  The regenerative delay linker now supplies a native Collatz instruction of
  exactly this kind: on an affine tail it reads a low binary address and maps
  the residual `v` by `v -> s_0+3^A v`, appending `A` ternary digits.  One
  fixed dispatcher has a bounded exact realization of all 243 five-trit
  output words.  Lean commits `54e506f`/`5254194` prove the affine link
  semantics and its ordinary-tail acceptance test.  The next PL task is to
  arrange a returning dispatcher or counter loop whose changing instruction
  stream is genuinely aperiodic while its nested binary addresses eventually
  stabilize to one natural tail.  Cocke--Minsky's universality proof supplies
  a precise kill test: a real tag compiler must pop the front of one binary
  stack and push onto the remote end of another.  A complete local write
  alphabet is not enough.  The spatial target is therefore two separated
  packet registers implementing those push/pop moves at a regenerating
  collision boundary.  The strongest immediate ordinary-address specialization
  has now been exhausted through delay/opcode/output-delay 100: among
  1,010,000 canonical-family base shapes, only three normalized tail-zero
  links exist and none has a second link.  The live controller must therefore
  transform a nonzero evolved payload or use a genuinely nonlinear packet
  encoding; a chain of canonical least representatives is not enough.
  One such nonzero mechanism is now exact: the five-trit word
  `b=3^5-2^L` maps a residual packet `K*2^L-1` to
  `2^L(3^5*K-1)`.  Hence remote low bits of `K` can amplify an inherited
  length-`L` bit boundary by any prescribed finite extra valuation `D`.
  The live turnaround problem is to expose this nested amplified gap as the
  next active delay and make its surviving packet reproduce the construction.
  A returning finite glider now exists.  The ether gate `(1,2,1)` has fixed
  2-adic tail `-12/473`; the unique parity-compatible immediate defect
  `(1,1,1)` writes any prescribed finite number `n` of eight-bit cells and
  returns the exposed boundary to its own defect family.  The complete macro
  is `K=R_n+2^(8n+15)q -> K'=S_n+3^(6n+11)q`.  The next target is one ordinary
  payload whose changing `q` generates an infinite aperiodic sequence of
  lengths, not another externally prescribed list of finite ethers.
  In the affine register `Y=83790531K-874281`, the whole ISA is the autonomous
  partial map `Y=2^(8n-5)h -> (3^(6n+11)h+51)/2^20`.  This small map, not the
  original huge defect constants, is now the primary synthesis target.  A
  second spatial scale is also exact.  Repeating the one-cell glider as a
  23-bit super-ether fails if its gap is completely exhausted, but Simon's
  proposed collision overhang has a canonical realization: retain exactly
  three low bits.  The two-cell glider then acts as a returning defect and
  the primitive super-register obeys
  `V=2^(23N+3)g -> (3^(17N+40)g-17)/2^51`.  Thus one capped splash changes the
  first-scale `+17` law into the same law with sign `-17`.  The next target is
  to iterate this renormalization symbolically and pass the ordinary-integer
  gate, not merely construct deeper finite address cylinders.  Exact
  renormalization now reaches six levels with alternating signs and cell
  widths `8,23,77,254,839,2771`.  The canonical tail-zero tower already
  illustrates the danger: at depth six it compiles a linked 6,708-digit
  finite program, but its first-scale packet has changed at every depth.
  Search now targets a finite self-describing address or an ordinary-tail
  theorem for a different recursive branch, not a seventh certificate made
  by extending the same changing tower.  The meta-language is not unary:
  choosing any background branch `j` and the adjacent defect `j+1` gives the
  same exact sign flip after retaining the background valuation.  This has
  been checked for `j=1..64` at level one and along three nonconstant
  four-step choice words.  A universal positive-tail identity now closes the
  whole infinite-nesting interpretation, not just that bounded tree.  If
  `E` is the combined parent input exponent, `r` the inherited valuation,
  `q_raw>0` the least raw input, and `K>=1` a child packet, then its parent
  tail is

  ```text
  q=q_raw+2^E*(2^r*K-1)>0.
  ```

  Thus every recursive extension lies strictly above the canonical parent
  base; its nested ordinary addresses can never eventually stabilize.  The
  hierarchy is a finite compiler, not one infinitely nested ordinary program.
  This does **not** exclude an autonomous orbit at any fixed finite hierarchy
  level.  There is also an invariant one-in-seventeen packet slice:
  when the primitive register is divisible by `17`, division gives the unit
  law `H=2^(an+b)h -> (3^(cn+d)h+s)/2^e`.  All collision debris has then been
  reduced to `s=+1` or `-1`; this unit machine is now the smallest autonomous
  search interface.  Scaling by `2^e` exposes its exact instruction:
  `W=2^p h -> W'=3^q h+s`.  Relative to the signed radix router, every level
  then trims the positive ternary factor `3^(p-1-q)`.  The new two-rail target
  is to bank that factor in a separated packet and feed it back, rather than
  losing it or adding another hierarchy level.  Every constant-rate clock is
  already closed: `n_t=n_0+kt`, for arbitrary fixed `k>=1`, makes the unique
  2-adic core a partial-theta value which is irrational by the cited
  Väänänen--Wallisser theorem at all six levels.  Any bank must branch
  nonlinearly on its packet contents.  In Simon's spatial language, the live
  architecture is a two-rail regenerator: a payload rail survives the
  collision while a delocalized sacrificial rail absorbs the dirty carry
  suffix and recreates the next clean gap.  The distance to that next gap
  must itself be packet-selected, not a fixed-rate delay.  This mechanism is
  now exact in the unit ISA.  For any three successive branch lengths and any
  desired `D>=1`, one correction block emits the complete next instruction;
  a second `D`-bit word cancels its carry and leaves `D` literal zero bits
  before an affinely surviving high packet.  The remaining quine problem is
  sharp: that high packet must generate its own future correction words.  An
  externally preloaded infinite stack would again be only a 2-adic program.
  A much more compressed special case now uses the rational repetend
  `R=(2^T C-s)/3^q`.  Choosing `T` simultaneously in a discrete-log class
  modulo `2*3^(q-1)` and in the affine unit exponent class makes
  `R+2^(T+D)K -> C+2^D*3^qK`.  This gives formula-generated, enormously
  nonlinear gap splashes at all six levels; the live question is still
  renewal of the emitted marker rather than production of one spectacular
  jump.  At the sign-negative second level that marker now renews once
  exactly.  The stable quotients
  `c_m=(2^(3^(m-1))+1)/3^m` let the first ternary bank be absorbed into a
  second repetend, producing two consecutive formula-sized nonlinear jumps.
  The remaining target is a third/self-writing renewal from one fixed
  ordinary packet, not an externally nested tower.  But the pure staircase
  is now closed even before the ordinary-address gate: every sign-negative
  full-order splash more than halves its odd core.  The live hardware design
  must therefore alternate an amplifying **charge phase** with a sparse giant
  **discharge splash**.  The charge phase must rebuild both real core energy
  and the next nonlocal correction word from the surviving packet.
  The first exact charge--discharge compiler is now autonomous.  At the
  sign-negative level-two unit register, execute a length-`N` instruction and
  then the one-cell instruction.  The fixed collision debris factors as
  `3^57+2^77=5D`, where
  `D=314038802961906688057474567` is coprime to the register stride.  On the
  unique packet class divisible by `D`, quotienting gives the new ISA

  ```text
  G=2^(23N+3)g -> (3^(17N+97)g-5)/2^128.
  ```

  Every complete branch of this machine is strictly outward, and each is
  literally two legal unit macros.  Thus any infinite successful positive
  orbit of this much smaller `-5` machine would already refute Collatz.  No
  such orbit is known.  This is distinct from the earlier bounded search near
  the signed cycle `-5 -> -7 -> -5`: the same small debris appears in a new
  positive quotient register with different exponents.  The live task is to
  make its packet select infinitely many legal lengths.  Its own one-cell
  discharge now provably regenerates the same `-5` interface at every finite
  recursive depth: at depth `j` the offsets are
  `d_j=114*2^j-17`, `e_j=154*2^j-26`, and the removed divisor is
  `3^(114*2^j)+2^(154*2^j)`.  An exact multiplicative-order argument reduces
  coprimality at all depths to 79 gcd checks against the 80-bit register
  stride; all pass.  This is a true self-similar splash compiler, but not an
  infinite natural: every positive child packet lifts to
  `rho_j+D_j*K>K`, so nesting forever changes its ancestor address.  Search
  must use an autonomous orbit at one fixed finite level, not confuse the
  infinite hierarchy with a seed.
  A fixed-form change of coordinate now exposes exactly such a level-two
  bouncer.  Put `A=3^114`, `B=2^154`,
  `F=(A-B)/5`, and `Z=F*G-2^26`.  The one-cell instruction is the pure delay
  wire `B*Z'=A*Z`.  At defect boundaries write `Z=2^26*y`.  The ordinary odd
  state `y` then reads its own two opcodes

  ```text
  m=v2(y+1)/23,
  E=3^(17m)*(y+1)-2^(23m),
  h=(v2(E)-23m)/154,
  y'=3^(114h)*oddpart(E).
  ```

  When `m,h>=1` are integral and `y'` has another defect phase, this executes
  one length-`m+1` defect followed by `h-1` recharge cells.  The fixed register
  is simply `y=0 (mod M)`, `y=-1 (mod F)`.  An infinite accepted positive
  `y`-orbit would be an outward Collatz counterexample.  Accepted transitions
  are reversible without stored history: `v3(y')=114h`, and after removing
  that power, `v3(1+2^(154h)q)=17m` recovers the predecessor opcode and state.
  The exponent matrix has determinant
  `114*23-154*17=4`, leaving exact resonance identities with only `2^4` or
  `3^4` imbalance.  Morita's reversible two-counter universality result makes
  this a legitimate compiler analogy, while Dudenhefner's certified
  instruction-set-sensitive results supply the kill test: reversibility and
  two valuations are not enough.  We must compile actual increment,
  decrement/zero-test, and finite control operations inside the accepted
  arithmetic classes.  This valuation
  bouncer—not a further nested address—is now the primary synthesis target.
  The first low-description clocks do not solve it: an exact audit of
  Thue--Morse, period-doubling, and Fibonacci words, all 240 injective
  two-symbol codings by `(m,h)` in `{1,...,4}^2`, and every prefix through 48
  transitions finds no canonical-address stabilization.  Search should now
  target an arithmetic payload-generated counter law, not merely paste a
  familiar aperiodic word over two fixed opcodes.
  The ordinary-ray seam is sharper than that finite test: Lean commits
  `af1a934`/`ba121d9` prove that a realizing natural would force the canonical
  extension lift `rho_k` to vanish eventually.  Thus it is enough to prove
  `rho_k!=0` infinitely often; universal positivity is unnecessary.  An exact
  bounded audit finds no zero lift among 1,118,464 extensions of all words of
  depth at most four over the 16 opcodes `(m,h)` with `1<=m,h<=4`.  This is
  evidence about the compiler seam, not an all-depth theorem.
  A survivor must start at a canonical positive integer and contain infinitely
  many genuine Collatz steps; a loop on a malformed representation is rejected.
- **Rational-base and spatial-grid gliders.**  In the Stérin--Woods exact
  quasi-cellular automaton, Collatz iterates are binary rows while ternary
  columns perform base conversion; search for a diagonal defect or boundary
  signal with a formula return.  In Eliahou--Verger-Gaugry's base-`3/2`
  picture, try to compile the divergent saturated-map instruction “append
  `2`” from bounded exact Collatz/two-rail macros.  Seven- and twelve-append
  blocks now compile exactly on unbounded index families; in the latter both
  linked gates are universally outward.  Restricting its nonlocal tail modulo
  `16` makes the next odd catcher outward too, giving an unbounded three-gate
  growing family.  A complete bounded source-shape graph finds 18 saturated
  bridges, 11 with outward linked targets, but all 11 target shapes have no
  second compiler edge.  One ordinary relay leaves only a forbidden periodic
  self-loop, but a second relay changes the picture: the universal outward
  catcher `(r,0,1,L)` chooses any next spatial gap, making the 11-node compiler
  graph complete.  The live task is therefore no longer finite spatial
  routing; it is an ordinary payload recurrence realizing an aperiodic
  infinite path.
  Lean commits
  `401d494`/`6ab99fc` prove the universal saturated-cylinder law and package a
  reusable affine-bridge certificate; `64bf677` kernel-checks the first
  odd-to-odd bridge, and `dbe0e5a` proves that any supplied
  outward renewing variable bridge chain refutes Collatz.  Commit `fedb5ca`
  proves every router shape outward uniformly and proves that dyadic-cylinder
  addresses of any ordinary natural must eventually equal that natural
  literally.  No infinite chain is known, and neither presentation transfers
  divergence by itself.
- **Two-rail splash bouncers.**  Implement Simon's collision idea with a
  `-1`/valuation-one Mersenne rail, which amplifies a separated packet by
  `3/2` per tick, and a `+1`/valuation-two Colussi rail, which supplies timing
  and carry cleanup.  Exact `+1` splash gates can emit an arbitrarily longer
  empty gap but always decrease the integer.  The phase switch now exists:
  `94751 -> 101183` is the smallest standard regression, and symbolic affine-
  family intersection compiles 247 consecutive outward rounds into a
  10,040-digit seed.  That seed nevertheless reaches `1`, and its canonical
  value changes when a 248th constraint is imposed.  Each affine handoff is
  now an exact tag instruction: it consumes a low binary address block from a
  nonlocal payload index and maps the surviving tail affinely by a power of
  three.  A fixed affine return is now ruled out: it would repeat one valuation
  word forever, and its putative natural tail slope would be `3^N/2^S` with
  `S>0`.  Lean commits `b741a14`/`26f3584`/`560fcc5` strengthen this to every
  eventually periodic word schedule and every autonomous finite-state
  controller.  The live splash target is a tag controller whose changing
  unbounded tail selects a genuinely aperiodic gate sequence, or an unbounded
  shape counter—not a fixed route through gate shapes.  Exact valuation
  decoding makes the gate shapes an LSB-first prefix code of Kraft mass `1/6`
  among odd 2-adic payloads: a valid tape is necessarily sparse, but its
  unbounded arithmetic contents can supply the required nonautonomous state.
  Simon's “splash the gap” suggestion also repairs the apparent missing
  collision mechanism in a more ambitious form.  Treat a long zero gap as a
  delay line and place several nonlocal bit islands across the full digit span:
  the first island triggers the main collision, later islands arrive as timed
  carry catchers which absorb its debris, and a surviving island writes the
  spacing and residues of the next catcher bank.  This is a three-phase
  **strike--scrub--reseed splash code**, not a single local rewrite.  Because a
  fixed finite valuation word is affine, any proposed code can be synthesized
  by simultaneous dyadic congruences and then checked exactly.  The hard
  obligation is regeneration: the post-collision catcher vector must lie in
  the same parameterized family with a larger delay, while retaining an
  ordinary positive tail.  This explicitly combines Simon's programming-
  language/nonlocality idea with Kontorovich's spatial delay-line picture.
  instructions: an odd intermediate gap has a parity-dual terminal collision,
  and a one-bit outgoing gap is a legal zero-delay rail.  The even cleanup and
  odd catcher families have exact Kraft masses `1/3` and `2/3`, so every
  positive odd payload uniquely decodes unless that macro explicitly reaches
  `1`.  Hardware jamming is therefore gone; the target is an ordinary decoded
  tape with aperiodic positive long-run drift.  Lean commits `afb86a5` and
  `f7ac880` certify the new odd catcher, its affine cylinders, and
  cross-branch prefix disjointness, including `r=0,L=1`; `78d1048` proves in
  Lean that every positive odd payload has an exact halt, even-cleanup, or
  odd-catcher outcome, and `92f237c` proves that outcome unique.  The
  parity-complete hardware semantics are now kernel-closed.  Commit `88e2577`
  exposes the unique decoder as a deterministic macro transition and reduces
  a disproof to linked public payloads whose decoded macros are all outward;
  `b023700` packages the actual canonical partial state map and proves that any
  infinite surviving outward orbit of it refutes Collatz.  Commit `e9f791b`
  removes the last hidden gate data for the universal-router submachine: an
  infinite positive-odd solution of
  `2^(r_(n+1)+3)P_(n+1)=3^(r_n+2)P_n+3` alone refutes Collatz.  Simon's
  spatial “splash the gap” picture is now literal in the minimal break-off
  coordinate: `9*2^(3q)c-1` executes `q` three-bit delay ticks, collides with
  chosen opcode `j`, and can emit a fresh state `9*2^(3q')c'-1`.  For every
  `q,q'>=1,j>=0` one residue class of `c` gives this exact finite
  delay-to-delay gate.  The live target is to link such gates through one
  ordinary coefficient with a genuinely aperiodic, unbounded collision
  schedule; Lean commit `a1a5fd0` proves eventual periodicity of the opcodes
  impossible for any infinite break-off orbit.
- **Exact cycle synthesis.**  Search valuation words and cyclic compositions
  for which `2^S_N-3^N` divides `A_N`; the quotient is then a candidate cycle
  seed whose valuations and closure can be checked directly.  Use modular
  meet-in-the-middle, lattice, and branch-and-bound searches aimed at long,
  low-description words rather than another undirected small-seed sweep.
- **Parametric gliders.**  Search for a finite symbolic transducer, substitution,
  or arithmetic family `x_t` with a machine-checkable macrostep
  `T^(ell(t))(x_t)=x_(t+1)` and `x_(t+1)>x_t`.  The existing exhaustive
  small-DFA failures rule out only their tested regular certificate classes;
  the next targets are one-counter, morphic, and recursively nested binary
  templates with unbounded but finitely described memory.
- **Separated-bit packet gliders.**  Treat long zero gaps as delay lines: evolve
  each high packet under multiplication by `3`, use the exact order of `3`
  modulo powers of `2` to schedule its first interaction with the controlled
  low packet, and search for a symbolic collision rule that emits a fresh
  packet at a larger scale.  Certify the whole construction through exact
  macrosteps, including every carry at the collision boundary.  Lean commit
  `121cb13` now supplies the exact order and scheduling theorem; packet renewal
  remains open.
- **Negative-cycle shadow controllers.**  A positive state congruent to a
  negative periodic point modulo a high power of two shadows its supercritical
  valuation block while a high packet grows.  Search one-counter programs in
  which the terminal carry collision raises, rather than consumes, the shadow
  precision.  The negative orbit is only a finite controller; the sought seed
  and every certified macro-state remain positive.
- **2-adic rationality sieve.**  For a fixed infinite extra stream, Lean commit
  `7370489` proves that there is at most one ordinary packet realization and
  unrolls every finite prefix as an exact backward affine series.  Commit
  `b205e40` proves the corresponding series converges in `Q_2` for every
  schedule and that any ordinary renewal must equal its negative 2-adic
  candidate.  For periodic or morphic controllers, the remaining arithmetic
  task is to prove that candidate is not a negative ordinary integer.  This
  can eliminate an infinite program family without enumerating any seeds.
- **Partial-theta integrality sieves.**  The standard two-rail schedule reduces
  to the sole 2-adic initial value
  `-(23/3^8) F(2/3,2^13/3^9)`.  Väänänen--Wallisser's full-source 1989 theorem
  applies and proves it irrational, closing this schedule.  Repeat the method
  for branching or morphic controllers: reduce a symbolic schedule to its
  `Q_2` special value, then prove nonrationality to reject it or exploit a
  rational exception as a possible ordinary program.
- **Constraint-guided falsification.**  SAT/SMT, modular dynamic programming,
  evolutionary search, CPUs, and GPUs may propose or aggressively reject a
  symbolic macro.  They no longer rank raw seeds by excursion length.  A
  survivor advances only when its low-description recurrence is replayed with
  exact integers and promoted to a universal algebraic certificate.
- **Backward invariant rays.**  Build with inverse steps
  `y -> (2^k*y-1)/3` and search for a sparse, explicitly parameterized set that
  maps into itself while moving outward.  This attacks the ordinary-integer
  gate directly and can reuse the project's side-bush disjointness, rational
  base-`3/2` coordinate, and affine product-of-places diagnostics.
- **Exceptional-orbit obstructions in reverse.**  Re-read the proof program's
  exact capacity and carry constraints as a specification of what a
  counterexample must look like, then search on the thin boundary where those
  constraints are nearly sharp.  Negative-drift or density-one evidence is
  treated as a distributional filter, never as evidence against rare
  software.

#### KC failure ledger

| Ansatz or route | Calibrated verdict | Exact record |
|---|---|---|
| Treat a prescribed finite `k`-word as an infinite program | Invalid: the nested progressions generally select a 2-adic integer, not a positive ordinary seed. Lean commit `ad36f08` proves that eventual canonical-seed stabilization is exactly the ordinary-integer gate. | [Program-synthesis note](docs/notes/kontorovich-program-synthesis.md) |
| Literal periodic valuation glider | Closed: Lean commits `92b01ff`/`2f93df7` prove that an infinitely repeatable positive block has `3^N<2^S` and closes as a cycle. This does not touch morphic, counter, stack, or feedback streams. | [Section 4](docs/notes/kontorovich-program-synthesis.md#4-why-a-literal-periodic-glider-fails) |
| Small positive cycle words | Exhaustively negative through total halving count `S<=22`: `3,447,691` positive-denominator compositions, with only repeated encodings of seed `1`. This is a bounded ansatz exclusion, not a new verification frontier. | [`search_results.json`](experiments/kontorovich/search_results.json) |
| Fixed-width binary uniform morphisms | Exhaustively negative for nontrivial cycles at widths `2..4`, codings `1..4`, and expanded length at most `16,384`. The best `1`-avoiding seed-stabilization event dies at its next morphic extension. | [`search_results.json`](experiments/kontorovich/search_results.json) |
| Small negative-cycle shadow programs | Exhaustively negative for ordinary-seed stabilization or terminal precision renewal using controllers `-5` and `-17`, start levels `1..6`, collision extras `1..8`, and extra programs of depth at most four: `112,320` compiled paths in both mod-6 classes. This closes only the stated one-counter pilot. | [`shadow_results.json`](experiments/kontorovich/shadow_results.json) |
| Bounded phase-changing shadow grammar | `1,950,864` positive paths checked exactly. The `-5/-7` phases yield 15 terminal renewals and 10 one-extension seed stabilizations, all starting at level 1 or 2; every renewed path loses alignment on its next collision and none grows. All seven `-17` phases yield zero events within their separately stated bounds. | [Phase-shadow artifacts](experiments/kontorovich/README.md#phase-changing-shadow-collisions) |
| Bounded `-1`/Mersenne shadow grammar | `376,800` positive paths checked exactly for start levels `1..100`, extras `1..12`, and depth at most three. There are 522 terminal renewals, 80 seed stabilizations, and three all-outward stabilization events; none supplies a second stabilized extension. The best finite run reaches `1` on exact continuation. | [`mersenne_shadow_results.json`](experiments/kontorovich/mersenne_shadow_results.json) |
| Constant-extra Mersenne feedback | All `51,200` compiled paths for start levels `1..20`, constant extras `1..32`, depths `1..40`, and both mod-6 classes were checked. The unique two-extension event is seed `121` for extra `1`; its fifth macro fails and exact continuation reaches `1`. | [`mersenne_constant_results.json`](experiments/kontorovich/mersenne_constant_results.json) |
| Short-period Mersenne feedback | All `2,726,400` prefixes from 568 primitive extra templates of period at most three over `{1,...,8}`, start levels `1..30`, depths `1..80`, and both mod-6 classes were checked in compressed exact arithmetic; every hit was literally replayed. No template improves the constant-`1` two-extension event or the `(4,3,1)` outward event. | [`mersenne_periodic_results.json`](experiments/kontorovich/mersenne_periodic_results.json) |
| Direct state-dependent packet census | CUDA exhaustively checked all `2^41=2,199,023,255,552` odd packets `h<2^42` from start level one through an eight-renewal horizon, with zero arithmetic overflows and no length-eight chain. Nested replayed artifacts retain the 14 length-seven hits below `2^39` and 243 length-six-or-more hits below `2^36`; independent RTX 4090 and H100 runs reproduce all 243 inner hit triples exactly. | [`h<2^42` artifact](experiments/kontorovich/mersenne_packet_gpu_akdeniz_h42.json), [H100 replication](experiments/kontorovich/mersenne_packet_gpu_psc.json) |
| Unstructured range widening as the main attack | Deprioritized: published ordinary-seed verification already reaches `2^71`, while the contemplated software may have roughly 10,000 decimal digits. Bounded compute remains useful only as a falsifier or independent checker of a proposed symbolic relation. | [Delocalized-ISA scale calibration](docs/notes/kontorovich-delocalized-isa.md#1-scale-changes-the-object-we-should-search-for) |
| Unmodified order-10 Colussi wire | It is an exact, spectacularly long delay line but not a bouncer. After its certified collision, an exact 1,024-step audit finds no regenerated empty gap wider than 10 bits, versus the incoming 39,348-bit gap; full exact continuation reaches `1` after 95,146 accelerated steps. The next lane must alter the header/collision with a distributed defect. | [`colussi_delay_h10.json`](experiments/kontorovich/colussi_delay_h10.json) |
| Pure `+1` gap-splash bouncer | Closed as an outward macro: the exact gate can turn a gap of `2r+2` bits into any chosen `2r'+2`-bit gap by a congruential payload, but the whole macro has dissipative multiplier `3^(r+1)/2^(2r+2+a)<1` and in fact strictly decreases every positive member. It remains useful as the cleanup rail of a multi-phase program. | [`splash_gate.py`](experiments/kontorovich/splash_gate.py) |
| Even-gap-only splash decoder | Superseded as an obstruction.  Rejecting odd intermediate gaps or `L=1` outgoing gaps created artificial “renewal failures.”  The odd-gap collision `1+2*3^sQ -> 2+3^(s+1)Q=-1+2^LP'` and zero-delay rail make the decoder total away from explicit halting collisions.  This repairs syntax, not growth: the saturated `U^12` witness still reaches `1`. | [`complete_splash_isa.py`](experiments/kontorovich/complete_splash_isa.py) |
| First parity-complete saturated bridge graph | In the exact source box `r<=15,s<=4,a,b<=4,L<=16`, all 25,600 shapes and 2,751,680 coefficient-compatible links were checked.  Eighteen saturated bridges exist and 11 have outward linked target subfamilies.  Exhausting all 718 possible second edges from those target shapes finds zero renewal.  This closes only depth two for those 18 first edges; larger sources and non-saturated catcher cascades remain open. | [`complete_u_bridge_graph_audit.json`](experiments/kontorovich/complete_u_bridge_graph_audit.json) |
| One ordinary relay between compiler blocks | The 11 two-outward saturated nodes admit 22 universally outward four-gate relay families, but their graph has exactly one directed cycle: a fixed node-3 self-loop.  Every infinite path would therefore repeat one valuation block and is closed by the eventually-periodic theorem.  This excludes one-relay routing only on this node set. | [`complete_u_relay_graph_audit.json`](experiments/kontorovich/complete_u_relay_graph_audit.json) |
| Finite regenerative delay routing | Solved but insufficient.  Two delay gates with a shared gap always link when the second collision opcode is positive: both coefficient bases are odd, so one binary congruence gives the affine tail handoff `t=t_0+2^m v -> s=s_0+3^A v`.  Lean commit `54e506f` proves supplied affine families and links for every tail.  Commit `5254194` proves that an ordinary natural surviving unbounded nested address filters forces their canonical residues eventually to equal that natural; a perpetually changing address program is only 2-adic. | [`breakoff_delay_gate_audit.json`](experiments/kontorovich/breakoff_delay_gate_audit.json) |
| Canonical tail-zero delay dispatcher | Exhaustively negative at depth two in the symbolic box `q,j,q'<=100` (with `j` including zero): 1,010,000 gate shapes split into 992,129 with no next clean delay, 17,861 whose next gate needs positive tail, three canonical base-to-base links, and seven factor-of-eight coordinate aliases.  Every canonical link fails renewal after its target gate; their 59- and 85-digit ordinary seeds reach `1` in 1,272, 1,277, and 330 exact ordinary steps.  This closes only immediate stabilization at the canonical least coefficient, not evolved nonzero-tail or nonlinear two-packet programs. | [`delay_base_graph_audit.json`](experiments/kontorovich/delay_base_graph_audit.json) |
| Exhausted-tail ether staircase | The returning ether macros link every scheduled pair `n -> n+1`, but after setting the remaining higher macro tail to zero, the generated `(n+1)` tail misses the `n+2` input cylinder for every `n=1..128`; maximum linked depth is two macros.  This closes only the least-tail staircase controller.  Nonzero generated macro tails, branching length schedules, and other payload recurrences remain open. | [`breakoff_ether_glider_audit.json`](experiments/kontorovich/breakoff_ether_glider_audit.json) |
| Fully exhausted recursive glider ether | Closed for every immediate defect in the current returning-glider alphabet.  Every glider input packet is odd.  At the endpoint of a fully exhausted background macro-ether, its fixed form is odd, forcing the background-tail parity opposite the source cylinder of every possible next glider.  The obstruction is sharp rather than fatal: retaining the exact three-bit cap changes the phase modulo `16` and yields the certified returning super-ether. | [`breakoff_superether_audit.json`](experiments/kontorovich/breakoff_superether_audit.json) |
| Canonical tail-zero splash hierarchy | The most direct recursive program chooses the length-one branch and zero remaining tail at every new scale.  Exact expansion through depths `1..6` gives first-scale packet sizes `7,46,177,606,2021,6698` decimal digits and ordinary starts through 6,708 digits.  Consecutive packets agree in increasingly many low bits but are strictly larger and unequal at every checked depth (`v2` of the differences `23,155,589,2013,6715`).  It is therefore a growing sequence of finite 2-adic prefixes, not one stabilized ordinary seed.  This bounded diagnostic is now subsumed by the universal positive-tail row below. | [`breakoff_renormalization_audit.json`](experiments/kontorovich/breakoff_renormalization_audit.json) |
| Bounded canonical meta-quine tree | Exact recursive compilation checks all 584 meta-words of depths `1..3` over background choices `j=1..8`.  On every one of the 576 extensions, the canonical first-scale packet is strictly larger than its parent; there are zero stabilizations and zero decreases.  The closest paths are `(1,1)` and `(1,1,1)`, sharing 23 and 155 low bits respectively—the fixed tower already audited.  This bounded diagnostic is now subsumed by the universal positive-tail row below; another defect grammar or a fixed-level autonomous register orbit remains open. | [`breakoff_renormalization_audit.json`](experiments/kontorovich/breakoff_renormalization_audit.json) |
| Infinite capped-renormalization tower as one ordinary program | Closed for every successfully constructed adjacent-defect extension, independently of branch length or child payload.  With `q_raw>0`, combined parent exponent `E`, inherited valuation `r>=0`, and positive child packet `K`, exact substitution gives `q=q_raw+2^E(2^rK-1)>0`.  Every new nesting therefore has a strictly noncanonical parent tail, so the canonical dyadic addresses never eventually stabilize to one natural.  This subsumes the two bounded rows above as diagnostics.  It does not exclude an autonomous orbit in the unit register at a fixed finite level, or a different compiler grammar. | [`breakoff_renormalization.py`](experiments/kontorovich/breakoff_renormalization.py) |
| Infinite recursive `-5` charge hierarchy as one ordinary program | Closed, despite exact self-regeneration at every finite depth.  The depth-`j` quotient removes `D_j=3^(114*2^j)+2^(154*2^j)>1` and lifts a positive child packet as `K_j=rho_j+D_j*K_(j+1)>K_(j+1)`.  Iterated lifts make the root packet strictly grow, so the canonical addresses cannot stabilize to one natural.  This does not exclude an infinite autonomous orbit inside any fixed finite `-5` level; that is now the live target. | [`unit_charge_hierarchy.py`](experiments/kontorovich/unit_charge_hierarchy.py) |
| Infinite consecutive sign-negative full-order repetend splashes | Closed by exact core energy, including any hypothetical self-writing realization of this pure instruction.  Marker `C=1` forces `T=(2j+1)3^(q-1)`.  For `q>=3`, `3^(q-1)>=2q+1`, hence `2^T>2*3^q`; the recurrence `2^T h'=3^q h-1` gives `h>2h'`.  After `N` consecutive splashes a positive initial core would exceed `2^N`, impossible for fixed `h`.  The audit checks the concrete full-order exponent classes at sign-negative levels `2,4,6`.  This does not exclude sparse giant splashes separated by sufficiently amplifying charge phases. | [`unit_repetend_energy_audit.json`](experiments/kontorovich/unit_repetend_energy_audit.json) |
| Constant-rate fixed-level unit bank `n_t=n_0+kt` | Closed at all six compiled levels for every `n_0>=1` and fixed integer `k>=1`.  Exact unrolling gives a Tschakaloff value with theorem parameter `q=3^(ck)/2^(ak)` and rational nonzero `alpha=2^(p(n_0))/3^(q(n_0))`, independent of `k`.  The full-source Väänänen--Wallisser theorem makes it irrational in `Q_2`; the exact audit checks the function conversion and the uniform strict size bound, whose logarithmic ratio is unchanged because `k` cancels.  Six linked eight-transition regressions verify the finite `k=1` recurrence, while the symbolic coefficient identity and cited theorem give the all-`k` conclusion.  A factor bank must use nonlinear packet feedback, not any fixed-rate counter. | [`unit_linear_theta_audit.json`](experiments/kontorovich/unit_linear_theta_audit.json) |
| Fixed or eventually periodic break-off opcodes | Closed for the autonomous router subclass.  Lean commit `a1a5fd0` proves that every infinite growing `BreakoffCounterOrbit` emits macro-words `[1]^r[2,1]` and that neither its rail lengths nor its collision opcodes can be eventually periodic.  The six-class opcode acceptor is therefore syntax, not a cyclic generator; an infinite witness must encode unbounded aperiodic information. | [`BreakoffCounter.lean`](KontoroC/KontoroC/BreakoffCounter.lean) |
| Fixed defect opcode in the charge bouncer | Closed by Lean commit `5633c44`.  For a fixed affine gain law `B*Z_(t+1)=A*Z_t+C` with coprime `A,B`, `1<B`, and `A>B`, the fixed-point defect obeys `B*delta_(t+1)=A*delta_t`; hence every `B^n` divides one positive `delta_0`, impossible.  The concrete theorem applies to every fixed `m`.  It does not apply to the live bouncer, where `m` may decrease or oscillate and each block switches from its `m`-defect law to `h-1` homogeneous backgrounds. | [`AffineQuotientNoGo.lean`](KontoroC/KontoroC/AffineQuotientNoGo.lean) |
| Three named aperiodic two-opcode bouncer clocks | No canonical ordinary address stabilizes in the exact finite grammar: Thue--Morse, period-doubling, and Fibonacci control words; every injective coding of `0,1` by the 16 pairs `(m,h)` with `1<=m,h<=4`; all 34,560 prefixes through depth 48.  The closest pair shares 33,128 low bits but changes from a 33,386-bit address to a 34,092-bit address.  This closes only these named clocks and bounds, not payload-generated, larger-alphabet, or general morphic bouncers. | [`unit_charge_morphic_audit.json`](experiments/kontorovich/unit_charge_morphic_audit.json) |
| Bounded zero-extension charge-bouncer tree | Every word of depths `1..4` over the 16 opcodes `(m,h)` with `1<=m,h<=4`, followed by every one of the 16 possible next blocks, was compiled exactly: 69,904 prefixes and 1,118,464 extensions.  Zero canonical lifts found: none.  The closest nonlift agrees in only 16 of 177 required low bits, while the maximum terminal public valuations by depth are `3,9,13,16`; this does not imply a fixed-modulus obstruction or an all-depth theorem. | [`unit_charge_zero_lift_audit.json`](experiments/kontorovich/unit_charge_zero_lift_audit.json) |
| Standard two-rail schedule `[1]^r[2,2,3]` | Closed at all levels.  Exact affine-family intersection compiles 247 outward rounds from a 10,040-digit seed, but depth 248 changes the seed and exact continuation reaches `1`.  Lean reduces every infinite realization to `2^(r+8)P'=3^(r+3)P+69` and its sole 2-adic Tschakaloff candidate.  Väänänen--Wallisser's 1989 theorem applies at `q=3/2,p=2,alpha=4096/6561` and proves that candidate irrational, so it cannot be an ordinary payload.  This does not close branching or other aperiodic splash programs. | [Finite certificate](experiments/kontorovich/two_rail_chain_247.json), [theorem audit](docs/notes/standard-two-rail-theta.md) |
| Fixed affine or autonomous finite-state return | Closed as an outward bouncer.  Lean commits `b741a14`/`26f3584` prove fixed affine circuits and every eventually periodic macro-word schedule impossible; `560fcc5` proves an autonomous controller with any finite effective state eventually enters that obstruction.  Coefficientwise, a repeated word would require natural slope `m=3^N/2^S` with `S>0`.  Payload-dependent branching and unbounded shape counters remain open. | [Delocalized tag-ISA note](docs/notes/kontorovich-delocalized-isa.md) |
| Canonical zero-preload two-rail graph | Exactly checked 128,000 gate shapes in the stated box (`r<=40`, `s<=4`, collision extras `<=4`, output gap `<=41`): 98,760 canonical members are outward, 25 canonical links exist, and the longest linked chain has two gates. Its seed `45247` reaches `1`; a wider targeted audit finds no third canonical gate for that endpoint. This rejects only index-zero links, not branching affine-tail controllers. | [`two_rail_transducer_audit.json`](experiments/kontorovich/two_rail_transducer_audit.json) |
| Small regular invariant sets | Previously closed only in the stated exhaustive classes: no base-2 DFA divergence certificate through eight states and no base-3 certificate through five. One-counter and genuinely morphic single-orbit certificates remain open. | [Base 2](experiments/dfacert/README.md), [base 3](experiments/dfacert3/README.md) |

The first work product will be an exact `k`-word compiler and cycle/glider
search harness with replayable certificates.  New lanes and closed ansatz
classes will be recorded here with explicit bounds, just as in the proof
strategy's failure ledger.  Nothing will be called a disproof unless the
positive integer and its claimed behavior are machine-checked.

### KC Headline results (with verification scope)

| Result | Status |
|---|---|
| Program-scale calibration | Barina's published exhaustive check through `2^71` excludes every ordinary seed below that bound. Colussi's exact order-10 repetend has 39,366 padded bits and an 11,846-digit integer value, giving a literature-backed, formula-generated background at the scale Simon proposed. This is target calibration, not evidence of divergence. |
| Delocalized instruction-set audit | Exact published encodings expose four complementary units: valuation congruences, mixed binary--ternary boundary rewrites, De Mol's three-symbol tag rules, and Colussi's rotated repetend grammar. They motivate a nonlocal bouncer search but do not prove computational universality or nontermination. |
| Exact dyadic--triadic packet gate | Lean commit `f1cb0e2` proves universally that each supplied base collision generates exactly the affine family `h=r+2^(m+e+2)q`, `h'=s+2*3^m q`, with unique payload, literal valuation `e`, and the triadic next-packet scheduler. The Python checker passes 8,192 family members and an exhaustive converse over all 16,316 renewals found for odd `h<2^16` at levels `1..8`. No closed all-level gate controller is known. |
| Kernel stream uniqueness and 2-adic candidate | Lean commit `7370489` proves that a fixed positive valuation stream has at most one ordinary seed and kernel-checks every finite backward-series truncation. Commit `b205e40` proves convergence of the canonical series in `Q_2`, vanishing of the terminal term for an ordinary renewal, and the exact reduction: if the candidate avoids embedded negative naturals, that schedule has no positive renewal. Candidate nonintegrality for a useful controller class remains open. |
| Formula-generated 11,846-digit spatial wire | Colussi's order-10 value `(4^19683-1)/3^10` is reconstructed, not stored as a decimal literal. The exact header `(1,1,2,1,1,1,5,1,4,1)` sends it to `1+2^39348`; then 19,673 exact valuation-two steps obey `x_t=1+3^t 2^(39348-2t)` before a valuation-three collision. Lean commit `6229e7a` proves the general delay formula and kernel-checks this generated header and endpoint. Exact continuation reaches `1` after 95,146 accelerated steps, so this certifies a wire and its failed natural renewal, not nontermination. |
| Exact finite carry-splash families | For every positive `r,r',a`, research-side exact algebra constructs an arithmetic progression of odd payload pairs such that an `r`-tick `+1` delay line collides with valuation `2+a` and emits an `r'`-tick gap. The checker literally replays 15,360 members in the bounded regression `r<=8,r'<=10,a<=6`; e.g. `2961 -> 2221 -> 833` grows the gap from four to six bits. Every member shrinks, so a splash needs an amplifying phase. |
| Formula-generated 10,040-digit two-rail program | Exact congruence solving and affine-family intersection construct one seed with 33,351 significant bits, without storing its decimal literal. It executes 247 strict outward rounds of the schedule `[1]^(4+i) ++ [2,2,3]`, grows its clean gap from 5 to 252 bits, and reaches a 15,397-digit endpoint after 32,110 accelerated steps. Literal replay passes; Lean commits `39a3aba`/`5d3e0e3` certify the generic gate and finite-chain seams. Full exact continuation reaches `1`, and the 248-round canonical seed is different. This is a large finite Collatz program, not a counterexample. |
| Exact affine tag-transducer and branching target | Every affine two-rail handoff reads one dyadic residue of a nonlocal family index, deletes that address block, and maps the residual tail by a power of three plus an offset. Lean commits `4789a80`/`1076954` prove universal one- and two-instruction linkage.  Commits `b741a14`--`560fcc5` rule out fixed affine returns, every eventually periodic macro-word stream, and every payload-independent finite-state controller.  The live target must branch on unbounded tail data or carry an unbounded counter. |
| LSB-first splash instruction grammar | For fixed amplifier length, each positive gate shape `(s,a,b,L)` is one odd payload residue modulo `2^(a+b+2s+L+3)`.  Lean commit `1b7df1f` proves universal parameter decoding, the complete cylinder strides, and pairwise disjointness; the exact Kraft mass among odd 2-adic payloads is `1/6`.  The artifact checks 902,496 codeword pairs per `r=1..16` through 20 bits and independently decodes 21,504 bases.  This identifies a sparse mixed-base tag language, not an infinite survivor. |
| Parity-complete splash ISA | Simon's proposed sacrificial alignment supplies the missing odd-gap catcher `2+3^(s+1)Q=-1+2^L P'`; admitting `L=1` supplies a zero-delay next rail.  Lean commits `afb86a5`--`92f237c` certify the two branches and unique total decoding.  Commits `88e2577`/`b023700` expose the decoded macro and canonical partial next-state map and prove that any surviving outward public-state orbit refutes Collatz.  The exact Kraft split is `1/3+2/3=1`; no infinite orbit is supplied. |
| Exact base-`3/2` compiler bridge | The outward two-rail link `(5,0,2,1,2)->(1,0,2,1,2)` maps family indices by `95+128t -> 1640+2187t`, exactly `U^7` for every natural `t`, where divergent `U` appends digits `[1,1,1,1,1,2,1]` in rational base `3/2`.  Lean commits `401d494`/`6ab99fc` prove the universal dyadic-cylinder law and reusable compiler certificate; `dbe0e5a` proves the conditional variable-chain endpoint to `¬Collatz`.  The concrete target shrinks and the seed reaches `1`, so no infinite chain is supplied. |
| Two-outward-gate `U^12` bridge | Exact coefficient algebra gives `U^12(1023+4096t)=132860+531441t` with digits `[1]^10[2,1]`.  It links shapes `(10,0,4,2,11)->(10,2,1,3,2)`, and both complete families are universally outward.  The saturated orbit enters at time 622; the parity-complete decoder catches the next formerly rejected payload, but that catcher shrinks.  The resulting 120-digit seed parses into 290 exact splash gates, 101 outward, and reaches `1` after 1,016 accelerated steps.  This is a finite compiler cascade, not transferred divergence. |
| Universal three-gate outward `U^12` subcylinder | Restricting the `U^12` tail to `t=16u` makes the next decoded catcher `(1,0,1,2)` outward for every `u>=0`.  Exact affine formulas give `2199021754367 -> 2229023590399 -> 5083728186203 -> 8578791314219` at `u=0`, with nondecreasing state strides preserving all three inequalities universally.  The least seed reaches `1` after 133 accelerated steps.  This certifies Simon's “splash the splash” with net gain through three gates, not infinite renewal. |
| Bounded parity-complete saturated bridge graph | The exact shape search checks 25,600 sources and all 2,751,680 coefficient-compatible targets in its stated box, finding 18 universal `U^D` bridges—14 odd-source and four even-source.  Eleven linked target subfamilies are also universally outward.  The complete 718-candidate outgoing audit of those target shapes finds no second saturated edge.  This is a scoped compiler-graph dead end, not an exclusion beyond the source bounds or of intervening ordinary splash gates. |
| Universal outward splash router | For every `r>=0,L>=1`, the odd catcher `(r,0,1,L)` has word `[1]^r[2,1]`, arbitrary outgoing gap `L`, and multiplier `3^(r+2)/2^(r+3)>1`; hence every member is outward.  Exact affine composition uses it to connect every ordered pair of the 11 two-outward compiler nodes.  All 121 five-gate transition families replay exactly, making the two-relay shape graph complete.  Lean commit `fedb5ca` proves the all-parameter growth inequality and formalizes the natural-versus-2-adic boundary.  This supports arbitrary finite branching words, but an infinite word still generally selects only a 2-adic tail. |
| Autonomous router recurrence | Lean commit `e9f791b` proves that positive odd payloads satisfying `2^(r'+3)P'=3^(r+2)P+3` construct the canonical router `(r,0,1,r'+1)`, with exact linkage and strict growth.  Any infinite solution above initial state `4` therefore refutes Collatz.  Commit `c10e5b5` proves `3|P'` and the exact maximal-power-of-two/odd-part update.  The equivalent radix-swap candidate forms `e=v_2(y+1)` and `F(y)=3^(e-1)(y+1)/2^e` inside `9|y`, `y=7 (mod 8)`.  No infinite ordinary orbit is supplied. |
| Break-off instruction compiler | In the coordinate `y=8k-1`, one router instruction factors `k=2^j u` and executes `8k'=3^(j+2)u+1`.  For each `j`, legality is one exact `u`-class modulo `72`, and the unbounded tail map is `u=u_j+72t -> k'=b_j+3^(j+4)t`.  Lean commit `0b12d44` proves that any infinite proof-carrying break-off orbit stays `8 mod 9`, strictly grows, and refutes Collatz; commit `a1a5fd0` proves its opcode stream cannot be eventually periodic.  Commit `7293975` implements the executable `v_2`/odd-part partial map, proves it equivalent to the factorization interface, and derives `¬Collatz` from any infinite successful executable orbit.  The artifact lists opcodes `0..64` and literally replays 4,160 members through the canonical decoder.  No infinite orbit is supplied. |
| Regenerative three-bit delay gate | Simon's gap-splash suggestion has an exact spatial realization.  The state `9*2^(3q)c-1` performs `q` opcode-zero ticks before a chosen collision emits a fresh clean gap `9*2^(3q')c'-1`; Lean commit `eac55d3` proves the universal compressed run, collision renewal, and strict outwardness.  Commit `1711620` proves that the collision factorization plus one subtraction-free affine balance suffices to reconstruct renewal.  The artifact constructs 1,088 gate families and performs 8,704 literal macro replays.  The example `935 -> 1052 -> 2663` regenerates one delay cell but later reaches `1`. |
| Affine mixed-radix writer and ordinary-tail gate | Exact coefficient linking reads `m` low binary bits and appends `A` ternary digits: `t=t_0+2^m v -> s=s_0+3^A v`.  Lean commit `54e506f` proves every supplied affine gate family, coefficient link, composed run, and outwardness for all `v`.  Commit `5254194` connects its `2^m` address cylinders to the ordinary/2-adic boundary.  The artifact audits 4,608 linked pairs (18,432 macros) and shows one fixed dispatcher realizes every one of the 243 five-trit write words within stated bounds.  Finite instruction routing is solved; a returning aperiodic dispatcher with one eventually stabilized natural address is not. |
| Nonlocal sacrificial gap amplifier | In the five-trit writer choose `b=3^5-2^L` and residual `v=K*2^L-1`.  Exact arithmetic gives `b+3^5v=2^L(3^5K-1)`: trailing one-bits collide with the selected word to become zero-bits, while the remote congruence `3^5K=1+2^D (mod 2^(D+1))` supplies exactly `D` more.  All seven words `L=1..7` exist in the certified alphabet; the artifact replays 224 linked members for `D=1..32` through 448 literal gate macros.  This produces an internal tail gap, not yet a returning infinite controller. |
| Regenerative finite ether defect | The gate `E=(1,2,1)` self-links by `t=20+2^8v -> 57+3^6v` and satisfies `2^8(473t'+12)=3^6(473t+12)`, so exact divisibility of `473t+12` by `2^(8n)` is an `n`-cell spatial delay.  The defect `H=(1,136,1)` gives an exact `E -> H -> E` return whose Mersenne residual has `473t+12=2^8(r+AK)` with fixed odd `r,A`; one odd class of the remote packet therefore writes any prescribed finite ether depth.  The artifact constructs `n=2..32`, replaying 589 linked members and 1,178 literal gate macros.  It does not return the exposed boundary to another defect. |
| Returning finite ether glider ISA | Exact parity shows an exhausted ether boundary is odd and therefore cannot re-enter the `j=136` defect; among immediate `E -> H_j -> E` defects, `j=1` is the parity-compatible receiver.  Its small identities give defect input `X(K)=2^20K-10941`, return factor `473t+12=2^5(83790531K-874281)`, and for every `n>=1` a complete outward macro `K=R_n+2^(8n+15)q -> K'=S_n+3^(6n+11)q` which writes `n` ether cells and returns to the same defect family.  The artifact replays 64 macro members through 1,184 links and 2,368 gate macros.  No infinite linked macro orbit is supplied. |
| Autonomous ether-counter normal form | Put `Y=83790531K-874281`.  The length-`n` returning glider branch is exactly `Y=2^(8n-5)h -> Y'=(3^(6n+11)h+51)/2^20`, with `h` in one CRT class modulo `83790531*2^20`; the enormous defect constants cancel to `51`.  Every branch is strictly outward, and its packet coefficients agree identically with the compiled glider macro.  The artifact checks `n=1..128`, four tails each, and repeats the executable macro replays through `n=32`.  An infinite successful autonomous orbit would be a counterexample, but none is supplied. |
| Three-bit-capped recursive super-ether | Regard the one-cell returning glider as a 23-bit background cell and the two-cell glider as its defect.  Exact parity kills a fully exhausted second-scale gap, but retaining three low bits makes the boundary re-enter the same defect cylinder.  After removing a common `3^7`, the public register is `V=-8744697538656344367967+671265207750760396088265K` and its length-`N` branch is `V=2^(23N+3)g -> V'=(3^(17N+40)g-17)/2^51`.  The affine super-macro is `K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t`.  The artifact checks 64 branches and 256 members, and literally replays 32 members through 336 glider macros, 1,040 lower links, and 2,080 gate macros.  This is a finite two-scale constructor, not an infinite orbit. |
| Six-level sign-alternating splash hierarchy | The capped construction renormalizes five more times without changing the magnitude `17`: public collision signs are `+,-,+,-,+,-` and binary cell widths are `8,23,77,254,839,2771`.  At every checked step exact phase arithmetic returns to the defect and normalization flips only the sign.  The artifact checks 40 child branches independently by CRT and parent-macro composition, replays 80 members through 520 parent blocks, and expands the canonical tail-zero programs through six levels to literal first-scale gliders.  It additionally checks all 64 level-one choices `B=M_j,H=M_(j+1)`, three nonconstant four-step meta-words, and every depth-three meta-word over `j=1..8`.  Beyond those bounds, the exact positive-tail identity proves universally that no infinite chain of these adjacent-defect nestings can stabilize its canonical ordinary address.  The depth-six canonical member is a generated 6,708-digit ordinary start executing 360 linked glider macros.  This is a finite compiler and a source of fixed-level ISAs—not an ordinary infinite orbit or an induction that the phase identities persist at all levels. |
| Invariant unit-debris register and signed radix swap | At every one of the six certified hierarchy levels, exactly one packet class modulo `17` makes the primitive `±17` register divisible by `17`; the class is preserved by every successful branch.  Dividing gives `H=2^(an+b)h -> H'=(3^(cn+d)h+s)/2^e`, `s=±1`.  With `W=2^eH`, every instruction is exactly `W=2^p h -> W'=3^q h+s`: it preserves the complete core `h`, swaps an exact binary delay for a ternary delay, and writes one signed unit.  Against the signed router it trims `d=p-1-q`, with the six formulas `2n+3,6n+13,20n+45,66n+151,218n+501,720n+1657`.  The artifact compares all 192 branches, checks this form on 768 members, and literally replays 32 level-one members through 336 lower links and 672 gates.  This identifies the factor a second rail must bank; no such rail or infinite unit orbit is supplied. |
| Two-layer unit gap regenerator | Simon's “splash the gap” question has an exact answer in the smallest surviving ISA.  Given any three positive branch lengths and `D>=1`, choose `A,B,z,B_2,C` so `3^qA+s=2^pC+2^(p+L)B` and `B+3^qz=2^D B_2`.  Then `h=A+2^(p+L)(z+2^D u)` maps to `h'=C+2^(L+D)(B_2+3^q u)`: `A` emits the complete valuation-exact next instruction `C`, the sacrificial `D`-bit word `z` eats the carry `B`, and the remote tail survives affinely beyond a regenerated `D`-bit zero gap.  The exact artifact reconstructs 486 families across six compiled levels and replays 972 linked two-branch unit members for cell lengths `1..3` and gaps `1,4,12`.  This is a universal finite compiler identity plus bounded macro regression, not a self-supplying infinite stack or counterexample. | [`unit_gap_regenerator_audit.json`](experiments/kontorovich/unit_gap_regenerator_audit.json) |
| Formula-generated nonlinear repetend splash | If `2^T C=s (mod 3^q)`, the ordinary repetend `R=(2^T C-s)/3^q` gives `R+2^(T+D)K -> C+2^D 3^qK` under the unit collision.  Intersecting the discrete-log class of `T` with `T=p(n')` produces a genuine enormous target length.  Exact modular certificates construct this at all six finite levels from source length one and gaps `D=1,64`; they verify the order `ord_(3^q)(2)=2*3^(q-1)`, exponent CRT, repetend integrality, and both register phases without expanding `2^T`.  Level one uses `C=5`, `T=105,734,623`, and `n'=13,216,826`; its low rail alone is about 31.8 million decimal digits.  Across levels the target exponents have `9,29,91,299,980,3235` decimal digits.  This is a short generator for one vast nonlinear splash, not renewal or nontermination. | [`unit_repetend_splash_audit.json`](experiments/kontorovich/unit_repetend_splash_audit.json) |
| Two consecutive sign-negative repetend splashes | At level two, put `c_m=(2^(3^(m-1))+1)/3^m`.  Exact cubing gives `c_(m+1)=c_m-3^m c_m^2+3^(2m-1)c_m^3`, so `c_m` stabilizes modulo every fixed `3^P`.  At precision `P=q_0+v_3(M)=90`, a 45-digit odd `k` makes `T_1=3^(q_1-1)k` both retain the first ternary bank and lie in the affine target-exponent class.  This yields the exact unbounded family `h_0 -> R_1+2^(T_1+D)3^q0 L -> 1+2^D3^(q0+q1)L`, with both enormous valuations exact.  The audit checks 89 quotient recurrences, bridge integrality, exponent congruence, and all three unit-register phases for `D=1,64`, without materializing `T_1`; `T_1` itself has about `7.57*10^27` decimal digits.  This is genuine one-time renewal, not a third splash or infinite ordinary orbit. | [`unit_double_repetend_audit.json`](experiments/kontorovich/unit_double_repetend_audit.json) |
| Repetend energy separator | The same exact construction closes its own naive infinite continuation.  Every sign-negative marker-one exponent is an odd multiple of `3^(q-1)`.  For `q>=3`, elementary integer inequalities give `2^T>2*3^q`, so each such collision more than halves the positive odd core.  No fixed positive core supports infinitely many consecutive events.  The artifact audits the actual exponent classes at finite levels `2,4,6`; the general proof is symbolic.  A viable delay-line program must recharge between giant erasures, not stack them back-to-back. | [`unit_repetend_energy_audit.json`](experiments/kontorovich/unit_repetend_energy_audit.json) |
| Autonomous `-5` charge--discharge register | Pairing a length-`N` sign-negative level-two unit instruction with the one-cell instruction gives fixed debris `3^57+2^77=5D`.  The divisor `D=314038802961906688057474567` is coprime to the register stride, so one exact packet class can be divided by `D` and is preserved.  The quotient ISA is `G=2^(23N+3)g -> (3^(17N+97)g-5)/2^128`; every branch is strictly outward because `3^(17N+97)>2^(23N+131)`.  The artifact constructs branches `N=1..32` twice—directly by CRT and by restricted composition—and checks 128 members through 256 actual unit-macro replays.  An infinite successful positive orbit would refute Collatz; none is supplied. | [`unit_charge_discharge_audit.json`](experiments/kontorovich/unit_charge_discharge_audit.json) |
| All-depth self-regenerating `-5` splash | Composing any depth-`j` charge branch with its one-cell branch, then quotienting by `D_j=3^(114*2^j)+2^(154*2^j)`, reproduces collision constant `-5` with offsets `d_(j+1)=2d_j+17`, `e_(j+1)=2e_j+26`.  Coprimality with the fixed 80-bit stride holds for every `j`: a failed prime would require `2^(j+1)<M`, so only `j=0..78` can fail, and all 79 exact gcds are one.  The artifact materializes eight levels, compares 64 direct/composed branches, checks 128 members, and recursively expands canonical members through 510 original unit macros.  Infinite nesting is not a seed because every positive child lift strictly enlarges its ancestor packet; fixed-level autonomous orbits remain open. | [`unit_charge_hierarchy_audit.json`](experiments/kontorovich/unit_charge_hierarchy_audit.json) |
| Autonomous reversible fixed-form valuation bouncer | The rational one-cell fixed point clears integrally: with `F=(3^114-2^154)/5` and `Z=F*G-2^26`, one background cell is exactly `2^154 Z'=3^114 Z`.  At a defect boundary `Z=2^26y`, the state reads `m=v2(y+1)/23` and `h=(v2(3^(17m)(y+1)-2^(23m))-23m)/154`, then returns `y'=3^(114h)*oddpart(3^(17m)(y+1)-2^(23m))`.  The output recovers `h=v3(y')/114`, then `m=v3(1+2^(154h)q)/17` and the unique predecessor; the opcode matrix has determinant four.  The artifact checks all 64 `(m,h,m')` families with `m,m'<=4,h<=4`, 128 forward/reverse members, 320 charge macros, and 640 original unit macros.  Any infinite accepted positive `y`-orbit refutes Collatz; none is supplied. | [`unit_charge_bouncer_audit.json`](experiments/kontorovich/unit_charge_bouncer_audit.json) |
| Ordinary-ray extension-lift criterion | Lean commits `af1a934`/`ba121d9` prove that if nested dyadic compiler cylinders are realized by one ordinary natural, their extension residues are eventually zero.  Therefore nonzero residues at arbitrarily late scales exclude an ordinary realization.  This is a no-ray criterion for a proposed schedule, not a counterexample and not yet a theorem that the bouncer's residues are frequently nonzero. | [`DispatcherBoundary.lean`](KontoroC/KontoroC/DispatcherBoundary.lean) |
| Constant-rate unit-counter schedules | For any of the six certified unit levels, every `n_0>=1`, and every fixed integer `k>=1`, the schedule `n_t=n_0+kt` has the unique 2-adic initial core `-s*3^(-q(n_0)) F(2^(ak)/3^(ck),2^(p(n_0+k))/3^(q(n_0+k)))`.  Converting to Väänänen--Wallisser's `f_(3^(ck)/2^(ak))` is coefficientwise exact, and its argument simplifies to `alpha=2^(p(n_0))/3^(q(n_0))`.  Their 1989 theorem applies with `ell=1,sigma=0,p=2`; its size ratio is the same as for `k=1`, while `|3^(ck)/2^(ak)|_2=2^(ak)>1`.  The value is irrational in `Q_2`, so it cannot be an ordinary integer core.  The artifact's six linked eight-transition branch replays remain a finite `k=1` regression; the all-`k` conclusion is symbolic and theorem-dependent.  This closes every fixed positive step size, not nonlinear or packet-branching schedules. |
| Canonical ordinary base graph | The tail-zero specialization asks each gate to land literally on the next gate's least coefficient, so no further initial-address bits are consumed.  An exact exhaustive shape audit covers `q,q'=1..100,j=0..100`: only three of 1,010,000 shapes give normalized base-to-base links, and all three targets fail to regenerate another delay.  Seven additional hits are rejected as noncanonical aliases because their coefficient contains a whole factor of eight.  Every retained gate is literally replayed and every ordinary seed reaches `1`.  This is a scoped failure of the simplest stabilized-address counter, not evidence against nonzero evolved tails. |
| Standard schedule ruled out by a p-adic theorem | Lean commits `db0971c`/`806bf8c` reduce any infinite standard schedule to the sole `Q_2` value `U_5=-(23/3^8)F(2/3,2^13/3^9)`.  Commits `3fc63a6`/`08485d3` prove the all-coefficient and completed-sum identity `F=f_(3/2)(4096/6561)`, the exact Väänänen--Wallisser size inequality, preservation of irrationality under the nonzero scale, and the implication to no payload stream.  Their 1989 theorem supplies that irrationality externally.  This is a published-theorem application with a kernel-checked citation seam, not a reproof of the external theorem or a Collatz proof. |
| Exact finite `k`-word compiler | Python arbitrary-precision compilation and replay pass exhaustive complete-period regression for both classes modulo `6`, all words of length at most four with `1<=k_i<=4`; Kontorovich's `(1,1,2,2)` example gives seed `199`. Lean commit `63c3b3d` proves terminal congruence equivalent to all intermediate valuations, plus canonical existence, uniqueness, and endpoint stride. |
| Kernel cycle-disproof seam | `KontoroC.CycleArtifact.checkNontrivial=true` implies the literal negation of the ordinary Collatz conjecture. The package build and axiom audit pass; no nontrivial artifact is known. |
| Bounded composition search | All `3,447,691` positive-denominator compositions with `S<=22` were checked exactly. The only closure hits encode the trivial seed `1`; no nontrivial cycle was found within the bound. |
| Bounded morphic-program search | All `168` binary uniform prolongable morphisms of widths `2..4`, all `16` codings into `{1,2,3,4}`, and `20,224` bounded depth instances were checked exactly. No nontrivial cycle was found. |
| Parametric glider endpoint | Lean commit `2fc4459` proves that any supplied exact outward `MacroGlider` refutes Collatz, including the no-hidden-visit-to-`1` bridge. It supplies the checker endpoint, not a glider. |
| Periodic-itinerary obstruction | Lean commits `92b01ff`/`2f93df7` prove by an all-level coprime-divisibility argument that a positive eventually periodic valuation program is a cycle and that a supercritical repeated block cannot occur forever. |
| Ordinary-integer gate | Lean commit `ad36f08` proves `StreamLegal x k` iff the exact canonical prefix seeds eventually stabilize at `x` (in the fixed admissible mod-6 class). This validates the worker's stabilization diagnostic at the infinite level. |
| Separated-packet clock | Lean commit `121cb13` proves `ord_(2^(n+3))(3)=2^(n+1)` and exact residue scheduling corollaries. This certifies the delay-line clock, not a collision-renewal rule. |
| Negative-cycle shadow pilot | Exact Python checked `112,320` compiled paths for the `-5` and `-17` supercritical controllers through the bounds above. Every macrostep passed literal replay; no seed stabilization or next-level shadow renewal occurred. |
| Finite phase-changing carry renewal | Exact search found positive seed `53,403,857` with macro-states `53,403,857 -> 15,019,835 -> 2,376,185 -> 1,691,641 -> 1,354,843`, following `-7,-5,-7,-7` controller phases at levels `1..4`. Its canonical seed survives the fourth macro, but the endpoint misses every level-5 phase class. This verifies one finite renewal mechanism, not nontermination. |
| Finite outward Mersenne shadow | Exact seed `24,017,279` follows the signed `-1` controller at levels `7,8,9` with collision extras `(4,3,1)`, giving three strict macro increases `24,017,279 -> 25,647,359 -> 82,164,223 -> 1,579,334,395`. Its canonical seed stabilizes once, then misses level 10; exact continuation reaches `1` after 108 accelerated steps. |
| Two-extension constant-feedback event | For the constant rule `e_M=1`, exact seed `121` is canonical for depths two, three, and four, with macro-states `121 -> 91 -> 103 -> 175 -> 445`. Level five fails and the seed reaches `1` after 34 accelerated steps. This is the longest ordinary-seed stabilization found, but remains finite. |
| Kernel phase-shadow disproof seam | Lean commits `3d9cedc` through `d6fb8b2` prove the exact shifted-coordinate macro and the literal Collatz negation from any infinite bounded-extra renewal after an arbitrary finite prefix. Signed cycles automatically supply supercriticality and all rotated phases. No infinite renewal witness is known. |
| Kernel Mersenne-shadow seam | Lean commit `768f4d0` checks the signed `(-1,[1])` controller, proves the worker's exact Mersenne macro identity, and proves `MersenneShadowOrbit.not_conjecture` from infinite renewal data. It also kernel-replays the `24,017,279` event and its level-10 failure. |
| Pure packet-recurrence endpoint | Lean commits `32a0896`--`a2652f2` reduce a Mersenne disproof to positive odd packets and bounded extras satisfying `2^e(2^(m+1)h'-1)=3^m h-1` at every level. Lean derives exact legality, transitions, eventual packet growth, the unique necessary class of `h' mod 3^m`, and the literal Collatz refutation. |
| Seven-renewal state-dependent motif | Exact seed `30,603,607,965` has extras `(2,1,3,2,2,2,1)` and seven renewed Mersenne packet levels; its final four macrosteps grow and end at `318,374,253,823`. The eighth renewal fails, and exact continuation reaches `1` after 152 accelerated steps. |
| Independent packet-census replication | PSC H100 job `42500602` independently re-enumerated all `2^35` odd packets `h<2^36`. It reproduced the RTX 4090 run's zero-overflow counter, maximum renewal length seven, and all 243 stored `(initial h, length, extras)` triples exactly; both artifacts pass the Python big-integer verifier. This corroborates the inner census but does not enlarge its bound. |

The compiler and certificate seam is now live.  The dependency-free
[`path_compiler.py`](experiments/kontorovich/path_compiler.py) reproduces the
thread's `(1,1,2,2) -> 199` example, compiles both Kontorovich--Sinai seed
progressions, and replays every valuation with arbitrary-precision integers.
Lean commit `63c3b3d` independently proves that the compiler's final
congruence is equivalent to every intermediate exact valuation and proves the
canonical representative, progression uniqueness, and endpoint stride.  The
[`KontoroC/`](KontoroC/README.md) package also proves that a valid nontrivial
cycle artifact refutes the literal ordinary Collatz conjecture.  No such
artifact has been found.

The first bounded adversarial sweep tested all `3,447,691` positive-
denominator valuation compositions with total halving count at most `22`.
Only the eleven bounded repetitions of the seed-`1` trivial cycle closed.  A
separate low-description sweep tested `168` binary uniform morphisms of widths
two through four, all `16` codings by valuations in `{1,2,3,4}`, and `20,224`
depth instances through expanded length `16,384`.  Its `1,960` closure hits
are again all seed `1`; there is no nontrivial cycle in this stated template
class.  Seed stabilization was checked separately through length `512`.  Its
longest `1`-avoiding event is the length-nine prefix of seed `107`, which
exact continuation sends to `1` after `36` accelerated steps.  These are exact
bounded exclusions of small program classes, not a new global verification
bound and not evidence of convergence.

A kernel-checked theorem also closes the most literal glider: if one fixed
nonempty `k`-block repeats forever on a positive orbit, divisibility by
arbitrarily high powers of `2^sum(k)` forces the block endpoint to equal its
start.  Thus an eventually periodic valuation program is a cycle, not a
growing glider; a supercritical repeated block has only a negative 2-adic
seed.  Lean commits `92b01ff`/`2f93df7` prove the all-level statement and its
eventual-tail and sign corollaries.  The active search therefore moves to
aperiodic one-counter and recursively nested templates.
See [`docs/notes/kontorovich-program-synthesis.md`](docs/notes/kontorovich-program-synthesis.md)
for the exact algebra, bounds, result digest, and next attacks.

## Diary

### 2026-07-22 07:00 EDT

The formalizer has reduced the ordinary-program question to a particularly
clean collision seam.  If a compiled prefix is

```text
K=R+2^P*t -> K'=S+3^Q*t
```

and the next block restricts `t=rho+2^E*u`, one ordinary natural can realize
the whole infinite program only if `rho=0` eventually.  Lean commits
`af1a934` and `ba121d9` prove the positive and necessary directions.  It is
therefore enough to force nonzero splashes at arbitrarily late scales.

The new [exact audit](experiments/kontorovich/unit_charge_zero_lift.py)
compiled every bouncer word of depths `1..4` over `(m,h) in {1,2,3,4}^2` and
tested all 16 possible next blocks: 69,904 prefixes and 1,118,464 extensions.
There are zero zero-lift events.  The closest case shares only 16 of the 177
low bits required by its next input.  Maximum terminal public valuations at
the four depths are `3,9,13,16`, so I am not claiming a fixed low-modulus
invariant; agreement can grow.

Artifact SHA-256:
`1c6f863dbe2c83adda3821bcd7f1f082c2e08e0880b708630640196af3568988`.
Verifier file SHA-256:
`b71feafab1c56e80b27e8e006eae640056831a249ab9cb427113e52526bbd33f`.

Simon's new metaphor suggests the next construction: do not ask one collision
to clean and reproduce itself.  Lay down a distributed bank of timed bit
islands so one splash strikes, a second eats the unwanted carry/debris, and a
third reseeds the next large gap.  I am translating that spatial
strike--scrub--reseed picture into a vector affine macro whose regeneration
condition is an exact CRT identity, with the zero-lift criterion as its kill
test.  No counterexample is known.

### 2026-07-22 06:45 EDT

The obvious way to add aperiodicity to the reversible bouncer does not pass
the ordinary-address gate.  I audited three standard low-description binary
clocks:

```text
Thue--Morse,
period doubling,
Fibonacci substitution 0 -> 01, 1 -> 0.
```

Each symbol was mapped injectively to every ordered pair of distinct opcodes
from

```text
(m,h) in {1,2,3,4}^2.
```

For all 240 codings and every prefix through 48 bouncer transitions, the
[exact worker](experiments/kontorovich/unit_charge_morphic.py) compiles the
complete charge-macro word, links it to the next defect, and reconstructs the
least positive fixed-form `y`.  None of the 34,560 successive prefixes leaves
that canonical address unchanged.  The closest nonstabilizing event is the
period-doubling coding

```text
0 -> (4,4),     1 -> (3,4),     depth 48,
```

whose consecutive addresses share 33,128 low bits but have respectively
33,386 and 34,092 bits.  That is a vivid 2-adic approximation, not one
ordinary program.

Artifact SHA-256:
`6beff79aa6fe363f4bbe7cd84a42d7cd69c232bbb13ac1d610201dd4927c52dc`.
Verifier file SHA-256:
`c823867bccbc2001c4a3d3c58d4dbd32741f362eced027ed16a5fb7cbf7893b3`.

This failure is deliberately narrow.  It does not touch general morphic
words, larger opcodes, or—most importantly—the bouncer's evolving odd payload.
Morita's reversible-counter result also makes clear why a canned aperiodic
clock is the wrong compiler target: actual universality needs conditional
counter operations.  The next search will use the payload to implement a
counter update or zero-test, with the determinant-four resonance as the
candidate transfer gadget.

### 2026-07-22 06:16 EDT

The fixed-form bouncer is lossless: every accepted output uniquely recovers
its predecessor and both variable opcodes.  If

```text
y'=3^(114h)*q,       3 does not divide q,
```

then necessarily

```text
h=v3(y')/114,
m=v3(1+2^(154h)*q)/17,
y=2^(23m)*(1+2^(154h)*q)/3^(17m)-1.          (KC-REV)
```

Substitution into the forward equations returns `y'` exactly.  The reverse
read is genuinely nonlocal: the forward defect length is written into a
ternary valuation at the opposite end of the transformed state, while the
recharge length is the exact power of three carried by the output.  This is
much closer to an ultra-simple reversible programming language than to a
local bit rewrite.

There is also a small arithmetic resonance hidden inside the enormous cell
sizes:

```text
114*23-154*17=4,
2^(23*154)=2^(154*23),
3^(114*23)=3^4*3^(17*154).
```

Thus exchanging 154 defect units against 23 recharge units cancels the
binary scale exactly and leaves only a factor `3^4`; the transposed exchange
cancels the ternary scale and leaves `2^4`.  This is not yet a glider—the
affine `+1/-1` seams and the fixed register still have to close—but it is a
specific formula-scale place to look for one rather than a request for more
simulation.

The bouncer artifact now checks `(KC-REV)` on all 128 linked members as well
as their forward macro replays.  Updated artifact SHA-256:
`5f2d6bfdcc6c48692e40e000ad8550262ac74b102c1e0b06238ab9783efbd4c2`.
Updated verifier file SHA-256:
`c434c7ddf57b15f271b7c22be66d6614199a76f41cc7ba36346ca53f7a2df754`.

The live attack is to exploit the determinant-four resonance to build an
invariant formula family for `(KC-REV)`.  Repeating one fixed `(m,h)` is
already excluded by the periodic-affine obstruction; any survivor must use
the reversible odd payload `q` to vary these counts unboundedly.

### 2026-07-22 06:05 EDT

The recursive splash has yielded a fixed-level autonomous bouncer rather than
another nested address.  Let

```text
A=3^114,      B=2^154,
F=(A-B)/5
 =493006936424420884140154671288273660376560866054730997.
```

The factor is integral because the background's difference is exactly the
collision constant times `F`.  In the level-two charge register define

```text
Z=F*G-2^26.
```

The offset was not fitted: `F*register_offset-2^26` is exactly divisible by
the register stride.  In this coordinate, the complete one-cell instruction
loses every affine constant:

```text
2^154*Z'=3^114*Z.                            (KC-BG)
```

This is a literal homogeneous delay wire.  A length-`N=m+1` defect injects
the exact difference-of-powers carry

```text
2^(154+23m)*Z'
 =3^(114+17m)*Z
  +2^26*3^114*(3^(17m)-2^(23m)).             (KC-DF)
```

At a defect boundary `Z=2^26*y`, where `y` is positive odd and lies in the
two fixed classes `y=0 (mod M)`, `y=-1 (mod F)`.  The state itself selects

```text
m=v2(y+1)/23,
E=3^(17m)*(y+1)-2^(23m),
h=(v2(E)-23m)/154.
```

If `m,h>=1` are integers, the defect followed by `h-1` background cells
returns

```text
y'=3^(114h)*E/2^(23m+154h).
```

Continuation asks only that `v2(y'+1)` be another positive multiple of 23;
the two fixed congruences are preserved by the literal register execution.
This is the first genuinely state-dependent, fixed-level programming
language found here: `y` reads a defect length, its collision reads a recharge
length, and the odd remainder becomes the next program state.  Every accepted
transition is outward.  Hence an infinite accepted positive `y`-orbit is an
ordinary Collatz counterexample.

The [exact bouncer worker](experiments/kontorovich/unit_charge_bouncer.py)
constructs all complete linked families with input/output defect extras
`m,m'=1..4` and `h=1..4`.  It checks 64 families and two members each,
comparing the displayed valuation map with literal execution through 320
charge macros and 640 original unit macros.  Artifact SHA-256:
`5f2d6bfdcc6c48692e40e000ad8550262ac74b102c1e0b06238ab9783efbd4c2`.
Verifier file SHA-256:
`c434c7ddf57b15f271b7c22be66d6614199a76f41cc7ba36346ca53f7a2df754`.

No infinite orbit is supplied.  The next work is now focused and
non-simulative: derive an invariant formula family for this two-valuation map,
or prove a proposed family impossible.  In programming-language terms, the
map is a one-register machine with two unbounded, state-read opcodes; in
Simon's spatial terms, `(KC-BG)` is the delay line and `(KC-DF)` is the splash
that must reproduce its own next timing word.

### 2026-07-22 05:46 EDT

The `-5` charge--discharge machine really does splash away its own next
collision, at every finite recursive depth.  Suppose one level has

```text
G=2^(23N+3)g -> (3^(17N+d)g-5)/2^e.
```

Following its length-`N` branch by its one-cell branch creates debris

```text
5*(3^(17+d)+2^(26+e)).
```

Restricting to the unique register class divisible by the parenthesized
factor and quotienting leaves `-5` again.  The offsets obey

```text
d_(j+1)=2*d_j+17,      d_j=114*2^j-17,
e_(j+1)=2*e_j+26,      e_j=154*2^j-26,
D_j=3^(114*2^j)+2^(154*2^j).
```

The key coprimality is now proved for all depths, not inferred from a finite
pattern.  Let `M=671265207750760396088265`, the fixed 80-bit register stride.
If a prime `r!=3` divided both `M` and `D_j`, then
`(3^114/2^154)^(2^j)=-1 (mod r)`.  Its multiplicative order would be divisible
by `2^(j+1)`, forcing `2^(j+1)<=r-1<M`.  Therefore only `j=0..78` can possibly
fail.  The verifier checks those 79 exact modular gcds; every one is `1`.
The prime `3` cannot divide `D_j` because its second summand is nonzero
modulo `3`.

The [hierarchy worker](experiments/kontorovich/unit_charge_hierarchy.py)
materializes eight exact levels.  At each level `N=1..8`, its direct CRT
branch agrees coefficient-for-coefficient with the restricted composition of
two parent branches.  It checks 64 branches and 128 members, then recursively
expands one varying-length member at each depth through 510 original unit
macros.  Artifact SHA-256:
`6ae387f7cc5db514a5314378121986540bda0f1741e8b97a566c7510cb643981`.
Verifier file SHA-256:
`71f9d2014225ec4a937bc8e489c11307139121b7a2a01cca1c59266b62adb1b9`.

This is a real regenerative splash, but the naive infinity is still the
wrong one.  A positive child packet lifts to its parent as

```text
K_j=rho_j+D_j*K_(j+1)>K_(j+1).
```

Consequently deeper canonical nestings make the root packet strictly larger;
they cannot stabilize to one ordinary natural.  The hierarchy is an
arbitrarily deep finite compiler, not a counterexample.  The useful residue
is its family of exact outward fixed-level machines.  The next attack is to
derive a packet-selected length law *inside one fixed level*, so that the
ordinary state evolves forward rather than being rewritten backward at ever
deeper addresses.

### 2026-07-22 05:34 EDT

The requested charge phase has collapsed to a small exact instruction set.
At sign-negative hierarchy level two, compose one unit instruction of length
`N` with the one-cell instruction.  Eliminating the intermediate core gives

```text
2^(p(N')+p(1))*h'
  =3^(q(N)+q(1))*h-(3^q(1)+2^p(1)).
```

Here `p(1)=77`, `q(1)=57`, and the collision debris has the useful
factorization

```text
3^57+2^77
 =5*314038802961906688057474567.
```

The large factor `D=314038802961906688057474567` is coprime to the odd
register stride.  There is therefore one exact packet class on which both
ends are divisible by `D`.  After quotienting, the whole two-instruction
composition is the autonomous public map

```text
G=2^(23N+3)g
  -> G'=(3^(17N+97)g-5)/2^128.               (KC-CD)
```

This is the first literal charge--discharge interface: the long instruction
amplifies the packet, the one-cell instruction eats almost all fixed collision
debris, and division leaves only `-5`.  Moreover every successful branch is
strictly outward for every `N>=1`, since already at `N=1`
`3^(17N+97)>2^(23N+131)` and the exponent gap increases thereafter.  An
infinite successful positive orbit of (KC-CD) would consequently be an
outward ordinary Collatz macro-orbit and a counterexample.  We do not yet
have that orbit.

The [exact worker](experiments/kontorovich/unit_charge_discharge.py) builds
each complete branch independently by CRT and by composing the two original
unit branches, then compares both affine coefficients.  The artifact checks
`N=1..32`, four members per branch, and 256 literal unit-macro replays.
Artifact SHA-256:
`e7af475f153a2e444b84f91dda8f4f395f1a048abde2383f40ac48eda4bef564`.
Verifier SHA-256:
`5c6cb46cec58720ef3d215651312556a05a3970a089792c3cd29ba7f3831e05a`.

This `-5` is not being inferred from the old signed-cycle pilot: it is a new
positive quotient register with exponents `(23N+3,17N+97,128)`.  The next
test is exactly Simon's regenerative metaphor at one scale higher: compose
this machine with its own one-cell discharge, quotient the new debris, and
ask whether the same `-5` instruction reappears rather than accumulating
damage.

### 2026-07-22 05:24 EDT

The exact second splash also reveals why a pure repetend tower cannot be the
counterexample.  At a sign-negative marker-one splash, integrality forces

```text
T=(2j+1)*3^(q-1).
```

For every `q>=3`, an elementary induction gives
`3^(q-1)>=2q+1`.  Therefore

```text
2^T >= 2^(2q+1)=2*4^q > 2*3^q.
```

The exact unit recurrence is

```text
2^T*h_next=3^q*h-1,
```

so `h>2*h_next`: a giant repetend splash consumes more than half of its odd
core.  After `N` consecutive splashes one would have
`h_0>2^N h_N>=2^N`, impossible for one fixed positive integer `h_0` as `N`
grows.  This closes even a hypothetical self-writing implementation of the
pure consecutive instruction, not merely the externally preloaded nesting.

The [energy audit](experiments/kontorovich/unit_repetend_energy.py) checks the
generic integer separators and the actual marker-one exponent classes at all
three sign-negative finite levels `2,4,6`.  Artifact SHA-256:
`33ed88a031967a3012c5609add1959ea5bb6afda84479267c6c58fc2bfe61efa`.
Verifier SHA-256:
`9bcf9d11dc867f95d44d80203d7d0ee5c4d01edcd3531bb066617de010767853`.

This does not undo the two-splash construction; it explains its energy bill.
The initial core can pay for two enormous erasures but no finite core pays
forever.  The live architecture must alternate phases: many outward
small/medium instructions charge real core magnitude and ternary bank, then
one repetend splash spends that stored resource to relocate and clean the
gap.  I am moving from a pure splash staircase to this charge--discharge
controller; bounded seed simulation would not expose the required balance.

### 2026-07-22 05:16 EDT

The sign-negative unit splash renews once exactly.  This is the first result
past the isolated nonlinear launch.  At level two the first jump has

```text
q_0=57,
T_0=21457252954121782025753972361,
n_1=932924041483555740250172709,
q_1=15859708705220447584252936093.
```

To retain the first `3^q0` packet through a second minus-one repetend, define

```text
c_m=(2^(3^(m-1))+1)/3^m.
```

Cubing `-1+3^m c_m` gives the exact recurrence

```text
c_(m+1)=c_m-3^m*c_m^2+3^(2m-1)*c_m^3.
```

Hence `c_(m+1)=c_m (mod 3^m)`: after precision `P`, this quotient is stable
modulo `3^P` forever.  The level-two register has `v_3(M)=33`, so precision
`P=q_0+33=90` simultaneously retains the first ternary bank and resolves the
whole register conductor.  Exact CRT produces the odd multiplier

```text
k=376213925255524775706446580991916826376956379,
T_1=3^(q_1-1)*k.
```

It satisfies both `k*c_(q_1)=1 (mod 3^90)` and
`T_1=54 (mod 23)`, making `T_1=p(n_2)`.  If

```text
R_i=(2^T_i+1)/3^q_i,
A=(R_1-1)/(2*3^q_0),
```

then an exact unbounded family is

```text
h_0=R_0+2^(T_0+1)*(A+2^(T_1+D-1)*L)
 -> R_1+2^(T_1+D)*3^q_0*L
 -> 1+2^D*3^(q_0+q_1)*L.
```

The [symbolic verifier](experiments/kontorovich/unit_double_repetend.py)
reduces unmaterializable exponents modulo the exact Carmichael exponent of
the register.  It checks 89 quotient-recurrence stages, the retained-bank
congruence, bridge integrality, and the source, intermediate, and final
register phases for `D=1,64`.  `T_1` has about `7.57*10^27` decimal digits;
neither it nor the corresponding states are expanded.  Artifact SHA-256:
`76ce98689eef74589937e05b3c3295844f49620ab8e2e9fb0a4889b5749a61f5`.
Verifier SHA-256:
`05dfc41a661089c68fa57cebbb850cc5109bec24803efda227c16825ede0453c`.

This is a genuine second collision renewal, not a counterexample.  A third
externally prescribed repetend can again be nested, but doing so merely
pushes another changing binary address into the initial packet.  The live
test is now sharper: can the final ordinary free packet `L` autonomously
select and synthesize the third correction, so that one fixed initial address
survives?  That is the self-writing case; another backward-preloaded tower is
rejected by the ordinary-tail gate.

### 2026-07-22 05:05 EDT

The two-layer splash has a formula-compressed nonlinear specialization.  For
one unit collision, choose an odd marker `C` and an exponent `T` with

```text
2^T C = s  (mod 3^q),
R=(2^T C-s)/3^q.
```

Then `R` is an ordinary positive rational-base repetend and, identically for
every `D>=1` and packet `K`,

```text
3^q(R+2^(T+D)K)+s = 2^T(C+2^D 3^qK).        (KC-R)
```

The collision annihilates the entire periodic correction rail, emits `C`,
and leaves `D` zero bits before the surviving packet.  This is not a long
prefix found by search; it is a short formula for a spatial wire.

Because `2` has order `2*3^(q-1)` modulo `3^q`, `T` lies in one explicit
discrete-log class.  Intersecting that class with the unit schedule
`T=p(n')=a*n'+B` by CRT succeeds at every one of the six constructed levels.
The exact symbolic audit uses source length one and obtains:

```text
level        1    2    3    4     5     6
marker C     5    1    1    1     1     1
digits(T)    9   29   91  299   980  3235
digits(n')   8   27   89  296   977  3231
```

At level one the values are already `T=105734623` and `n'=13216826`, so the
explicit correction rail would have about 31.8 million decimal digits.  The
higher rows are vastly beyond materialization.  The
[worker](experiments/kontorovich/unit_repetend_splash.py) therefore checks the
exact order, discrete logarithm/CRT, divisibility, and source/target register
phases by modular arithmetic without constructing `2^T`.  The artifact has
twelve symbolic families, for gaps `D=1,64` at each level.  Artifact SHA-256:
`fc73032df9114e59ca3f8926509616b66455d69b61536866cc50728fc7a2d170`.
Verifier SHA-256:
`d1991059ec7be5b754d9352395d3053ce305496bc2dc85f849ea21eb9b0d3554`.

This is the first unit construction whose next length is not remotely
constant-rate: it jumps from one cell to millions of cells at level one and
to formula-sized astronomical lengths above that.  It is still only one
jump.  The emitted core `C+2^D3^qK` must now be made to launch another
repetend splash from its own packet contents.  That renewal equation—not a
larger simulation—is the live test.

### 2026-07-22 04:49 EDT

Simon's proposed collision cleanup is now an exact two-layer instruction in
the invariant unit register.  Write the current unit recurrence as

```text
2^p h' = 3^q h+s.
```

Choose `C` to be the complete low binary prefix which makes `h'` execute the
next desired branch, including the extra bit certifying that its valuation is
exact.  Modular inversion constructs

```text
3^q A+s = 2^p C+2^(p+L)B.
```

The first correction `A` therefore emits `C` but leaves carry `B`.  Now use
exactly `D` low bits of the remote packet to solve

```text
B+3^q z=2^D B_2.
```

For every remaining natural tail `u`, the two equations combine to

```text
h=A+2^(p+L)(z+2^D u)
  -> h'=C+2^(L+D)(B_2+3^q u).
```

This is the literal “other bits eat the bad parts and regenerate the gap”
mechanism: `z` disappears into the collision carry, `D` clean zeros appear
above the next instruction, and the untouched high packet survives under an
affine power-of-three update.

The [exact worker](experiments/kontorovich/unit_gap_regenerator.py) also
intersects this family with the odd invariant register and checks two actual
compiled unit branches.  Its artifact reconstructs 486 families at all six
finite hierarchy levels—every triple of lengths `1..3`, gaps `1,4,12`, and
two tail members—for 972 linked two-branch replays.  The level-one worked
case `(1,2,3,D=12)` is

```text
96640062369165269810946648141077
 -> 5811505674703125430887858069149
 -> 995193873655264956279801575123,
```

with the middle 103-bit core containing the complete 40-bit next instruction,
then twelve zero bits, then its residual packet.  Artifact SHA-256:
`3337b99b291894f6338716a1a2d1e459f3ae414086c239bca693258052212f3d`.
Verifier SHA-256:
`c737953183b760a9411ad5d2d6e57cad7eb3560578353c78166e2afe8381772a`.

This is a finite compiler identity, not an infinite orbit.  It locates the
remaining problem exactly: after each splash the surviving affine packet must
produce the next sacrificial word from its own state.  Preloading infinitely
many such words merely reconstructs a nonordinary 2-adic stack.  I am now
treating the residual update as a mixed-base pop/push language and searching
for a self-writing, packet-selected word rule.

### 2026-07-22 04:29 EDT

The unary factor-bank obstruction extends to every positive constant rate.
For `n_t=n_0+kt`, exact backward unrolling gives

```text
h_0=-s/3^(q(n_0)) *
    F(2^(ak)/3^(ck), 2^(p(n_0+k))/3^(q(n_0+k))).
```

Coefficientwise conversion uses theorem parameter
`3^(ck)/2^(ak)`, but the rational argument simplifies to
`2^(p(n_0))/3^(q(n_0))`, independent of `k`.  The theorem's logarithmic size
ratio is also unchanged because `k` cancels.  Thus the cited full-source
Väänänen--Wallisser theorem excludes an ordinary integer core for every
`n_0>=1` and fixed integer `k>=1` at all six compiled unit levels.

The rebuilt [exact artifact](experiments/kontorovich/unit_linear_theta_audit.json)
checks the generalized symbolic coefficient law and elementary hypotheses;
its literal linked branch replay remains explicitly scoped to the finite
step-one schedules `1,...,9`.  Artifact SHA-256:
`682d5636c66f1ea2a8f2cad7e58027da1e821513f248726175c839907bad312a`.
Verifier SHA-256:
`944eeaa73a8b860d36531b90e866941ab282633b0ebd2736839fd00b8d870e28`.
The irrationality is still an external published-theorem application.

This sharpens Simon's “splash the gap” proposal.  A viable cleanup rail
cannot merely fire every fixed number of cells.  Its sacrificial bits must
both absorb the collision debris and use unbounded packet state to choose
where the regenerated clean gap appears.  The next target is therefore a
two-rail, packet-controlled return equation, not a longer constant delay.

### 2026-07-22 04:17 EDT

The first factor-bank clock is closed.  If one tries to advance the unit
length linearly, `n_t=n_0+t`, then

```text
2^(p(n_(t+1)))*h_(t+1)=3^(q(n_t))*h_t+s
```

unrolls to the unique 2-adic candidate

```text
h_0=-s/3^(q(n_0)) *
    F(2^a/3^c, 2^(p(n_0+1))/3^(q(n_0+1))).
```

The identity

```text
F(2^a/3^c,z)=f_(3^c/2^a)((3^c/2^a)z)
```

puts it exactly in Väänänen--Wallisser's 1989 theorem.  Their result applies
uniformly to all six compiled levels and every `n_0>=1`.  The only delicate
size condition has a short integer audit: `2^8>3^5` gives
`log(2)/log(3)>5/8`; `3a>=4c` then gives the relevant ratio greater than
`5/6`; and `45<64` gives `1/6<(3-sqrt(5))/2`.  The candidate is irrational in
`Q_2`, hence cannot be an ordinary integer core.

The new exact artifact separately compiles eight linked transitions at each
of the six levels and checks the finite rational and 2-adic truncation
identities.  The level-six regression reaches 172,972 bits of terminal
2-adic precision.  Artifact SHA-256:
`fa6a00ae1e91e901440fff05cbda7ba5648049351924b88ad1a154f1136f43cf`.
Verifier SHA-256:
`62f282afbd3472eb514bec34b36a499d7863ddb0bcef345b263cab2b6b4569fa`.

This is a published-theorem application with an exact hypothesis audit, not
a reproof of that theorem and not a Collatz result.  Architecturally it is
decisive: synchronizing the ternary bank to a unary `n -> n+1` counter simply
recreates the rigid partial-theta obstruction.  The next bank must let its
ordinary packet contents choose a nonlinear, aperiodic change of length.

### 2026-07-22 04:07 EDT

The surviving unit machine is an exact signed radix swap.  Put
`p=an+b+e`, `q=cn+d`, and scale the public register by `W=2^eH`.  Every legal
member has a core `h` coprime to six and obeys

```text
W =2^p*h,
W'=3^q*h+s,              s in {+1,-1}.
```

Thus the instruction reads an exact binary zero-gap, preserves the whole
nonlocal core, writes an exact ternary zero-gap, and changes only one signed
unit.  If `y=W-s` and `y'=W'-s`, comparison with the signed router gives

```text
3^(p-1)*(y+s)/2^p = 3^(p-1-q)*y'.
```

The apparent collision debris is therefore not amorphous: it is the precise
missing factor `3^d`, `d=p-1-q>0`.  Across the six compiled levels,

```text
d(n)=2n+3, 6n+13, 20n+45, 66n+151, 218n+501, 720n+1657.
```

The rebuilt exact artifact verifies the two factorizations, exact ternary
valuation, and signed-router trim on all 768 previously checked members; the
32 literal first-level members still expand through 336 links and 672 gates.
Artifact SHA-256:
`459bd3feb5a30d931caf43c601db8713354696d9ae072e223e3603d77838b753`.
Verifier SHA-256:
`4057b56485ea1570d0b5abd2f50415f909e8afbc4b8f04f0c04baaf73ce265ff`.

This is not a counterexample.  It turns Simon's “other bits eat the bad
parts” idea into a concrete design specification: a second separated rail
must catch or represent `3^d` and re-inject it on the next collision.  Merely
cleaning a binary suffix, or nesting another splash, cannot do that.

### 2026-07-22 03:41 EDT

The splash hierarchy now has a universal ordinary-seed obstruction.  For one
renormalization step let `E=E_B+E_H` be the combined parent input exponent,
let `q_raw>0` be its least raw input, let `r>=0` be the inherited binary
valuation, and let `K>=1` be any child packet.  Direct substitution gives

```text
q=(q_raw-2^E)+2^(E+r)K
 =q_raw+2^E(2^rK-1)>0.
```

So a child can splash through its parent and regenerate the capped gap, but
it always leaves a positive ancestral tail.  Every further nested extension
therefore differs from the canonical parent packet; by the ordinary-tail gate,
an infinite adjacent-defect tower is a 2-adic phantom rather than one ordinary
Collatz program.  This subsumes the bounded canonical quine failures.  It does
not touch a genuinely autonomous orbit of any fixed finite-level register.

The exact checker now asserts the identity on every constructed step and
records it in the rebuilt six-level artifact.  Its SHA-256 is
`b568fb1b5228ced1f1198ad6375ba7f256e5f6f3dcf158dfc60d3d018dcdaf50`;
the verifier SHA-256 is
`a0c05f28c9e585194e64b1df755e13ea7c5e4fbbc43cc7a0346f23e8c836b1e9`.
The dependent unit-slice artifact was also rebuilt; its current hash and
scope are recorded in the experiment README and the next diary entry.  Next I
am abandoning deeper towers and attacking the fixed-level unit law
`2^B h'=3^A h+/-1` as an evolving, aperiodic odd-packet machine.

### 2026-07-22 03:31 EDT

The `17` collision particle has an invariant unit slice.  At any certified
hierarchy level the register is `V=r+mK` with `m` odd and invertible modulo
`17`.  Exactly one packet class

```text
K=-r*m^(-1) (mod 17)
```

makes `V=17H`.  Since an executable branch also has odd part `g=17h`, its
whole update divides by `17`:

```text
H=2^(an+b)h -> H'=(3^(cn+d)h+s)/2^e,   s in {+1,-1}.
```

The slice is automatically preserved; no new congruence is needed at the
output.  In Simon's splash language, the aligned nonlocal bits have eaten all
but one unit of collision debris.

The new [unit-slice artifact](experiments/kontorovich/breakoff_unit_slice_audit.json)
checks the six finite hierarchy levels.  For `n=1..32`, each unit branch is
built independently and compared coefficientwise with the unique mod-17
subcylinder of its `±17` parent: 192 branches and 768 members.  Thirty-two
level-one members are also replayed literally through 336 lower links and 672
gate macros.  The packet residues at levels one through six are
`3,16,0,2,6,8 (mod 17)` and the collision signs alternate `+,-,+,-,+,-`.

This does not produce an infinite orbit.  It does isolate the irreducible
arithmetic problem: a positive odd packet must repeatedly arrange a high
power-of-two division of `3^A h +/- 1` while the selected exponent changes
aperiodically.  Fixed odd payload is impossible (`h(2^B-3^A)=+/-1` reduces
to the excluded tiny power-difference cases), so the next search concerns a
genuinely evolving unit packet, not another static quine.

### 2026-07-22 03:18 EDT

Ran the first exact finite-quine kill test on the variable splash alphabet.
A meta-word `(j_1,...,j_L)` is compiled so that depth `L+1` begins with the
whole depth-`L` macro program.  Equality of their canonical first-scale
packets would therefore be a genuine ordinary-seed stabilization event: the
old finite seed would already contain the new source code.

The rebuilt artifact exhausts every meta-word through depth three with
`1<=j_i<=8`:

```text
depths:                   1    2    3
nodes checked:            8   64  512
canonical stabilizations: 0    0    0
canonical decreases:      0    0    0
```

All 576 extensions strictly increase the packet.  The closest depth-two and
depth-three words are `(1,1)` and `(1,1,1)`, with 23 and 155 shared low bits;
these are precisely the 2-adic tower already diagnosed.  This is a scoped
failure of zero-top-tail quines in a small but complete symbolic meta-tree,
not a search over ordinary seeds and not an exclusion of nonzero evolved
tails.  The next quine ansatz must feed the *output* packet back as high-level
state rather than repeatedly choose the least CRT representative.

### 2026-07-22 03:08 EDT

The recursive splash has a variable instruction alphabet.  At a parent level

```text
V=2^(an+b)g -> (3^(cn+d)g+s*17)/2^e,
```

choose any background branch `j>=1`, use the adjacent branch `j+1` as its
defect, and retain the background valuation `aj+b`.  Whenever the exact phase
identity is evaluated, the primitive child again has collision constant
`-s*17`.  Its visible parameter update is

```text
a' = aj+b+e,                 c' = cj+d,
b' = aj+b-r0,                d' = c(2j+1)+2d,
e' = a(j+1)+b+2e+r0,         s' = -s,
```

with `r0` the defect's computed inherited binary valuation.  This replaces
the fixed morphism `1 -> 1,2,1` by a meta-instruction `j -> j,j+1,j^N`.

The rebuilt renormalization artifact checks every level-one adjacent choice
`j=1..64`; all 64 return to the capped interface and normalize to `-17`.
It also follows the nonconstant background words `(2,2,2,2)`, `(3,1,4,2)`,
and `(8,5,3,1)` through four successive renormalizations, obtaining collision
signs `+,-,+,-,+` in each case.  Exact artifact/verifier hashes changed and
are updated in the experiment guide.

This is a stronger programming-language result, but still not a survivor.
An externally chosen infinite meta-word consumes unbounded nested binary
address and generally names a 2-adic program.  The next useful event must be
finite self-reference: an evolved packet choosing its own next `j` while its
ordinary lower address has stopped changing.

### 2026-07-22 02:57 EDT

The capped splash renormalizes repeatedly.  A level has primitive register

```text
V=r+mK,
V=2^(an+b)g -> V'=(3^(cn+d)g+s*17)/2^e.
```

Use branch one as background, branch two as defect, and retain the background
branch-one valuation instead of exhausting the gap.  At each of the five
checked renormalizations the cap phase returns to the defect and the normalized
collision is exactly `-s*17`.  The certified parameter table is

```text
level       1      2       3        4         5          6
sign        +      -       +        -         +          -
cell a      8     23      77      254       839       2771
offset b   -5      3      24      100       354       1192
divide e   20     51     153      485      1578       5189
```

The new [renormalization artifact](experiments/kontorovich/breakoff_renormalization_audit.json)
checks six levels and five sign flips.  For each step it builds child branches
`N=1..8` independently by public-register CRT and by direct parent defect/ether
composition: 40 coefficient comparisons, 80 replayed members, and 520 parent
macro blocks.  Its verifier hash is recorded in the experiment guide.

I also expanded the most tempting infinite-program candidate: choose branch
one and top tail zero at every depth.  The induced substitution is
`n -> 1,2,1^n`.  Depth six expands to 360 linked first-scale glider macros,
1,189 lower links, and 2,378 literal gate macros.  Its generated ordinary
start has 22,284 bits (6,708 decimal digits), close to Simon's proposed
program scale.  But this is precisely the ordinary/2-adic trap: first-scale
packet sizes at depths `1..6` are `7,46,177,606,2021,6698` digits, and each
packet is strictly larger than the preceding one.  Their exact shared-low-bit
counts are `23,155,589,2013,6715`; the address converges 2-adically while the
ordinary integer never stabilizes in the checked tower.

So the result is a genuine recursive hardware language and a large finite
program, not a counterexample and not an all-level theorem.  Extending the
same zero-tail tower is no longer the priority.  The next attack is a finite
quine or state-dependent high-level tail that makes the *ordinary* lower
packet stabilize while the macro word remains aperiodic.

### 2026-07-22 02:45 EDT

Simon's suggestion to let aligned bits "eat the bad parts and regenerate" is
exactly the missing move at the next scale.  Use the one-cell returning glider
`B=M_1` as a background super-cell.  In its macro-tail `q`,

```text
B: K=R+2^23*q -> K'=S+3^17*q,
F(q)=(3^17-2^23)q+(S-R),
2^23 F(q')=3^17 F(q).
```

Thus a `B` self-link consumes 23 binary bits of `F`.  A fully exhausted
second-scale ether has odd `F` and the wrong parity to enter *any* glider
defect.  The useful splash does not erase everything: retain exactly three
bits.  Modulo `16`, that capped boundary is always the input phase of the
`B -> M_2 -> B` defect, independently of the ether length.

After removing the defect's common factor `3^7`, its primitive register is

```text
V=-8744697538656344367967+671265207750760396088265*K.
```

For every requested super-ether length `N>=1`, the returning branch becomes

```text
V=2^(23N+3)g  ->  V'=(3^(17N+40)g-17)/2^51,
K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t.
```

The huge cancellation is exact:

```text
2^54*(-8744697538656344367967)
 - 3^33*(50679661 + 120751555*(-234676942119623))
= -2^3*17.
```

The new [super-ether artifact](experiments/kontorovich/breakoff_superether_audit.json)
checks 64 affine branches and 256 members.  It literally replays 32 members
through 336 returning glider macros, 1,040 lower links, and 2,080 gate macros;
the verifier hash is recorded in the experiment guide.  This is a finite
two-scale constructor, not a counterexample.  The conceptual gain is the
renormalization `+17 -> -17`: the same collision residue survives, while the
three-bit splash cap reverses its phase.  Next I am testing whether the
sign-flipped machine nests again and whether any resulting hierarchy has an
ordinary positive realization rather than only a coherent 2-adic address.

### 2026-07-22 02:24 EDT

The returning glider ISA has an unexpectedly small autonomous normal form.
Define

```text
Y=83790531*K-874281.
```

For a length-`n` macro, write `Y=2^(8n-5)h` with `h` odd.  Boundary return is
one congruence `3^(6n+11)h+51=0 (mod 2^20)`, and the transformed register is

```text
Y'=(3^(6n+11)h+51)/2^20.                            (**)
```

The constant `51` is exact: the large defect terms cancel through
`2^20*(-874281)-3^11*(-5175081)=51`.  The persistent packet invariant is
`Y=-874281 (mod 83790531)`.  For each `n`, that odd-modulus condition and the
binary boundary condition have one CRT solution for `h` modulo
`83790531*2^20`.  Translating the resulting affine branch back to `K` gives
*exactly*, coefficient for coefficient, the returning macro `R_n,S_n` from
the previous diary entry.

This is the precise version of Simon's "splash the gap" picture: the collision
debris is the residual `+51`, while the nonlocal CRT-selected bits absorb it
and regenerate the next clean packet boundary.

The new [ether-counter artifact](experiments/kontorovich/breakoff_ether_counter_audit.json)
checks all 128 branches `n=1..128` at four tails each and verifies the public
partial map, invariant, strict growth, and equality with the compiled glider
macro.  It also repeats the literal executable checks through `n=32`: 64
macro members, 1,184 links, and 2,368 gate macros.  The disjoint input
cylinders have total dyadic mass

```text
sum_(n>=1) 2^-(8n+15) = 1/(255*2^15),
```

so this software language is extraordinarily sparse, as Kontorovich's
argument predicts.

No infinite orbit of `(**)` is known.  The advantage is conceptual and
practical: the counterexample search has been reduced from 10,000-digit
Collatz seeds to one exact public register with a valuation-selected exponent,
a fixed division by `2^20`, and constant `51`.  The next attack is a
self-generated aperiodic valuation orbit of this map, including nested-ether
and Mersenne/carry ansätze; raw seed simulation remains secondary.

### 2026-07-22 02:14 EDT

The exposed ether boundary now returns to a defect.  First, a useful parity
kill: every exact finite ether ends with an odd tail.  For an immediate
`E -> H_j -> E` defect, collision opcode `j>=2` forces the target coefficient
to be `1 mod 4`, hence its `E`-tail address is even.  This rules out
`H=(1,136,1)` as a self-regenerator at every depth, not just in a search box.
The opcode-one defect `H=(1,1,1)` is the parity-compatible receiver.

Its links are strikingly small:

```text
E -> H:  67+2^7*v   -> 381+3^6*v,
H -> E: 151+2^8*w   -> 144+3^5*w,
v=170+2^8*u,             w=485+3^6*u.
```

On `u=2^5*K-1`, the returned `E` tail satisfies

```text
473*t+12=2^5*(83790531*K-874281),
```

so one odd class of `K` writes exactly `n` ether cells for every `n>=1`.
Solving one further binary congruence makes the exposed odd boundary equal the
next defect input `X(K')=2^20*K'-10941`.  The whole block therefore compresses
to the returning macro

```text
K=R_n+2^(8n+15)*q  ->  K'=S_n+3^(6n+11)*q.          (*)
```

The new [ether-glider artifact](experiments/kontorovich/breakoff_ether_glider_audit.json)
constructs `n=1..32`, replays two ordinary members of every family, and checks
1,184 exact links / 2,368 literal gate macros.  This is a true finite glider
ISA: defect, periodic medium, exposed boundary, and return to the same defect
family are all exact.  It is not yet an infinite glider.

The simplest controller fails cleanly.  Every pair `n -> n+1` can be linked,
but if the remaining higher macro tail is exhausted immediately, the generated
`n+1` state misses the `n+2` cylinder for all `n=1..128`.  The maximum is two
linked macros.  The [strategy/failure map](#kc-strategy-and-failure-map) now
targets a nonzero payload recurrence for `(*)`—or a branching length rule—so
that the hardware, not an infinite preloaded address, chooses successive
ether lengths.

### 2026-07-22 02:03 EDT

The nonlocal amplifier has now been coupled to an exact finite spatial ether.
Let `E=(1,2,1)`.  Its self-link is

```text
t=20+2^8*v  ->  t'=57+3^6*v,
```

and direct elimination gives

```text
2^8*(473*t'+12)=3^6*(473*t+12).
```

Thus the 2-adic fixed tail is `-12/473`, and an ordinary tail with
`v_2(473t+12)=8n` executes exactly `n` outward ether cells before its finite
defect reaches the boundary.  Infinite bare ether is still only the forbidden
2-adic periodic program; the useful object is a finite background plus a
moving defect, as in Kontorovich's Game-of-Life picture.

The new point is a regenerative defect.  The gate `H=(1,136,1)` supplies an
exact two-link return `E -> H -> E`.  After a Mersenne residual substitution,
the returned tail has

```text
473*t+12 = 2^8*(r+A*K),
```

for two fixed odd integers `r,A`.  Consequently one explicit odd class of the
remote packet `K (mod 2^(D+1))` makes the returned ether depth exactly `8+D`.
Setting `D=8n-8` writes any prescribed finite `n`-cell delay line.  The new
[ether-defect artifact](experiments/kontorovich/breakoff_ether_defect_audit.json)
constructs `n=2..32`, performs 589 exact linked-member checks, and replays
1,178 literal gate macros.  These are formula-selected programs, not a seed
range scan.

This is still not an infinite glider.  When the `n` cells are consumed, the
exposed boundary is not yet proved to lie in the input cylinder of a fresh
defect with a larger `n'`.  The live [strategy/failure
map](#kc-strategy-and-failure-map) now asks for precisely that boundary return,
with `n'` generated from the surviving packet rather than encoded by an
ever-growing initial 2-adic address.

### 2026-07-22 01:41 EDT

Simon's proposal that other bits could “eat” the collision debris and
regenerate the gap has produced an exact nonlocal instruction.  In the
five-trit dispatcher, select one of the seven words

```text
b=3^5-2^L,       1<=L<=7,
```

and feed it a residual packet `v=K*2^L-1`.  The native tail write then
satisfies

```text
b+3^5v = 2^L(3^5K-1).
```

Thus the collision sacrifices the input's `L` trailing one-bits to create
`L` zero-bits.  More importantly, choosing the *remote* packet by
`3^5K=1+2^D (mod 2^(D+1))` creates exactly `L+D` zeros.  This is the
nonlocality we were looking for: widely distributed bits of `K`, rather than
a neighboring cleanup symbol, determine how far the regenerated gap extends.
The new [amplifier artifact](experiments/kontorovich/splash_gap_amplifier_audit.json)
checks all seven concrete writer links and `D=1..32`, performing 224 exact
linked-member checks and 448 literal gate-macro replays.  The identity and
the odd residue class for `K` are algebraic for every `D`; Lean formalization
has been requested.

This is not a counterexample.  The amplified zero run is nested in the
residual tail rather than yet installed as the next public delay.  The next
attack is a two-stroke turnaround: expose that internal run at a later
collision while retaining enough of its odd part to recreate another
Mersenne packet.  The [strategy/failure map](#kc-strategy-and-failure-map)
now treats this payload-generated repair as the live escape from the negative
tail-zero base graph.

### 2026-07-22 01:19 EDT

The first attempt to satisfy the ordinary-tail theorem by immediate address
stabilization is exact and sharply negative.  Every delay shape has a
canonical least coefficient.  Requiring its output to equal the next shape's
least coefficient gives a literal tail-zero edge: no additional bit of a
preloaded 2-adic tape is requested.  The new [base-graph
artifact](experiments/kontorovich/delay_base_graph_audit.json) exhausts all
1,010,000 shapes with `q,q'=1..100` and `j=0..100`.  It finds ten apparent
edges, but seven have coefficients divisible by eight and merely relabel
whole delay cells.  After maximal-gap normalization only three ordinary edges
remain:

```text
(1,1,90) -> (90,5,1),
(1,2,61) -> (61,4,1),
(2,2,61) -> (61,4,1).
```

All three target gates fail at their next collision, so the maximum canonical
base-edge chain is one.  Their two 59-digit and one 85-digit starts are
literally replayed and reach `1` after respectively 1,272, 1,277, and 330
ordinary Collatz steps.  This is not a seed-range experiment: it is an
exhaustive symbolic shape test of the most stringent stabilized-address
program.  Failure redirects the two-stack attack toward nonzero payload state
created by earlier instructions, or a nonlinear two-packet encoding; simply
walking between least affine representatives cannot be the glider.

### 2026-07-22 01:01 EDT

The mixed-radix linker and its central failure test are now kernel-checked.
Commit `1711620` shows that a collision factorization plus the single
subtraction-free balance

```text
2^(j+3(q'+1))c' + 3^j = 3^(j+2q+2)c + 2^j
```

reconstructs the renewal factorization.  Commit `54e506f` packages the
research worker's affine gate and link families: two base identities and two
stride identities prove coefficient linkage, exact two-gate execution, and
strict outwardness for every common tail.  Commit `5254194` then applies the
ordinary/2-adic kill test at precisely this layer.  If one natural tail lies
in nested link-address cylinders of unbounded binary precision, their
canonical residues must eventually equal that natural literally; if the
addresses keep changing, the apparent program is only a coherent 2-adic
phantom.  This sharpens the returning-dispatcher target: it must use the
binary-read/ternary-write instructions to generate an aperiodic execution,
yet its constraints on the one initial ordinary tape must eventually stop
requesting new low bits.  Next: look for a counter architecture where later
instructions are generated by evolved payload state rather than by an
ever-growing exogenous address.  A primary-source PL check also prevents a
new overclaim: Cocke--Minsky prove universality for deletion-two tag systems
by implementing a state plus two binary stacks, but De Mol's particular
three-rule Collatz tag system is not thereby universal.  Our complete
five-trit writer likewise lacks a certified remote-rear append.  The more
honest spatial compiler target is now the two-stack move
`(M,N)->(2M+b,floor(N/2))`, with the collision boundary shuttling between
separated packets.

### 2026-07-22 00:55 EDT

The regenerative splash is now kernel-checked and has exposed a native
mixed-radix programming instruction.  Lean commit `eac55d3` proves the full
`q`-cell delay in one theorem, reconstructs the collision opcode from the
factorization, proves exact landing in the new gap, and proves every such
nonempty run strictly outward.  At the affine-tail level, any gate links to
any next positive-opcode gate with the same boundary gap.  If the first output
and second input cylinders are

```text
c_out=o+2*3^A t,       c_in=r+2^(m+1)s,
```

their odd bases make the link congruence automatically soluble, and its whole
family is

```text
t=t_0+2^m v  ->  s=s_0+3^A v,       0<=s_0<3^A.
```

This literally deletes a low binary address and appends an `A`-trit word to
the surviving nonlocal tail.  The rebuilt [delay
artifact](experiments/kontorovich/breakoff_delay_gate_audit.json) checks all
4,608 linked shapes with delays at most four and opcodes at most eight, two
tails each (18,432 gate-macro replays), in addition to the earlier 8,704 gate
replays.  More strikingly, the fixed dispatcher `(q,j,q')=(1,1,1)` has
`A=5`; exact enumeration of next gates `j<=34,q'<=44` finds a certified
address for every one of the 243 possible five-trit output words.  This is the
nonlocal binary-read/ternary-write PL primitive Simon anticipated.  It still
does not solve the ordinary-integer boundary: arbitrary finite words compile,
while an infinite nested tape may be merely 2-adic.  Next: build a returning
dispatcher/counter architecture from these writers and demand an aperiodic
all-level coefficient formula.

### 2026-07-22 00:38 EDT

Simon's image of bits “eating” a dirty collision and regenerating its gap is
not just metaphor: the minimal break-off map contains an exact three-bit
delay/collision instruction.  A clean state `9*2^(3q)c-1` executes `q`
opcode-zero steps, each replacing `(q,c)` by `(q-1,9c)`, then reaches
`3^(2q+2)c-1`.  For every desired collision opcode `j>=0` and new delay
`q'>=1`, one residue of `c modulo 2^(j+3q'+4)` makes the collision's odd
garbage satisfy

```text
3^(2q+2)c-1 = 2^j u,
3^j u+1 = 2^(3(q'+1))c'.
```

Thus it consumes the old gap and emits the fresh clean state
`9*2^(3q')c'-1`.  The new [exact
artifact](experiments/kontorovich/breakoff_delay_gate_audit.json) constructs
all 1,088 parameter triples `q,q'<=8,j<=16` and literally replays eight
affine tails each through the canonical router (8,704 macro replays).  Its
small regression is `935 -> 1052 -> 2663`: one delay tick, an opcode-2
collision, and one regenerated delay tick; exact continuation still reaches
`1`.  The [headline](#kc-headline-results-with-verification-scope) and
[strategy/failure map](#kc-strategy-and-failure-map) record the scope.  Lean
commit `a1a5fd0` also proves that any infinite break-off witness's rail and
opcode sequences must be genuinely non-eventually-periodic.  Commit `7293975`
implements the actual executable `v_2`/odd-part map in Lean, proves successful
evaluation equivalent to the small factorization equation, and turns any
infinite successful executable orbit into `¬Collatz`.  Next: solve the
coefficient linkage problem across an aperiodic sequence of these gates; the
finite spatial instruction and its final checker are now compiled, but an
ordinary self-renewing tape is not.

### 2026-07-22 00:08 EDT

The “splash the gap” mechanism now has a kernel-checked universal form.  Lean
commit `fedb5ca` proves every odd catcher `(r,0,1,L)` outward for arbitrary
parameters and payload, and separately proves the exact ordinary/2-adic
boundary: unbounded nested dyadic addresses belonging to one natural must
eventually stabilize literally at that natural.  Eliminating the external
router schedule gives a sharper self-programming target.  Consecutive router
payloads must obey

```text
2^(r_(n+1)+3) P_(n+1) = 3^(r_n+2) P_n + 3.
```

The equation forces `3 | P_(n+1)`.  Writing `P_n=3H_(n-1)` after the first
gate gives the deterministic two-register update: form
`A=3^(r_n+2)H_(n-1)+1`; if `v_2(A)>=3`, set
`r_(n+1)=v_2(A)-3` and `H_n=A/2^v_2(A)`.  Every surviving step is an outward
Collatz macro, so an infinite positive odd orbit would be a counterexample.
This is a reduction, not such an orbit.  Lean commit `e9f791b` now
kernel-checks the entire interface: the equation constructs the hidden odd
catcher, agrees with the unique canonical decoder, forces linkage and growth,
and yields `¬Collatz` from an infinite solution.  Commit `c10e5b5` additionally
proves `3|P'` and identifies the next delay and payload as the exact
`padicValNat`/`divMaxPow` decomposition.  The recurrence compresses again
after setting `H_n=P_n/3` and
`y_n=3^(r_n+2)H_n`:

```text
e_n=v_2(y_n+1),
y_(n+1)=3^(e_n-1)*(y_n+1)/2^e_n.
```

Here `9|y_n`, `y_n=7 (mod 8)`, and every defined step strictly increases;
survival asks that the output again be `7 mod 8`.  Its shortcut parity blocks
are `1^(r+1)01`, so zeros are separated by at least two ones.  Next: treat
this one-register radix swap as a mixed-base invariant-set problem and seek a
formula orbit, not a wider ordinary-seed census.  In the still smaller
coordinate `y=8k-1`, the invariant is just `k=8 (mod 9)` and the instruction is
`k=2^j u -> (3^(j+2)u+1)/8`; when integral, it preserves the mod-9 class and
strictly grows automatically.  Lean commit `0b12d44` now packages an infinite
break-off counter, proves these invariance/growth facts, and compiles it to
`¬Collatz`; the same commit proves the interior mod-24 payload skeleton.  The
new [break-off
artifact](experiments/kontorovich/router_breakoff_audit.json) makes each opcode
an exact affine binary-read/ternary-write branch and replays 4,160 bounded
members through the canonical Collatz decoder.  The next task is to find a
formula invariant for this map, not merely another long finite survivor.

### 2026-07-21 23:50 EDT

The compiler dead end was spatial, and Simon's extra splash repairs it.  With
one ordinary gate between the 11 two-outward saturated nodes, exact affine
intersection gives 22 four-gate relays, but their only cycle is a fixed
periodic self-loop and therefore impossible for an ordinary infinite orbit.
The missing degree of freedom is supplied by the universal odd router
`(r,0,1,L)`: its word `[1]^r[2,1]` is outward because
`3^(r+2)>2^(r+3)`, while `L` chooses any next gap.  The new [router
artifact](experiments/kontorovich/complete_u_router_audit.json) checks all 121
ordered pairs and proves the two-relay compiler graph complete, with every
five-gate family universally outward.  The least transition grows
`71675 -> 120953 -> 136073 -> 153083 -> 258329 -> 290621` and then reaches
`1`.  Lean commits `64bf677`/`88e2577` independently certify the first odd
saturated bridge and expose the unique complete decoder as a deterministic
macro ISA; `b023700` supplies the canonical partial dynamics and a direct
conditional endpoint to `¬Collatz`.  Lean commit `fedb5ca` now proves both the
router's universal outwardness and the exact boundary behind the caveat: at
unbounded dyadic precision, the canonical residues of any fixed natural must
eventually become that natural.  Next: exploit the now-complete finite router
to search for a self-describing public payload recurrence; finite instruction
routing is solved, while ordinary-integer realization of an aperiodic infinite
program is the live obstruction.

### 2026-07-21 23:32 EDT

The complete splash language materially enlarges the rational-base compiler
graph, but has not yet made it renew.  An exact [shape-graph
artifact](experiments/kontorovich/complete_u_bridge_graph_audit.json) checks
25,600 parity-complete sources and all 2,751,680 coefficient-compatible
targets in the stated box.  It finds 18 universal saturated bridges—14 using
the odd catcher—and 11 have outward linked target subfamilies; the complete
718-candidate audit from those target shapes finds no second compiler edge.  The positive side is
Simon's “splash the splash” literally realized: restricting the `U^12` tail
to `t=16u` gives three universally outward gates and the least chain
`2199021754367 -> 2229023590399 -> 5083728186203 -> 8578791314219`.
That seed still reaches `1`.  Lean commits `afb86a5`/`f7ac880` certify the
odd instruction, its complete affine cylinders, and cross-branch
prefix-freeness; `78d1048` proves total existence of a certified halt/even/odd
outcome for every positive odd payload, and `92f237c` proves it unique.  Next:
search strategically beyond the closed first-edge box
and, more promisingly, allow a bounded ordinary catcher cascade between
saturated compiler edges while forcing the overall decoded schedule to remain
aperiodic.

### 2026-07-21 23:22 EDT

Simon’s “splash the gap” metaphor exposed a real missing instruction.  The
old grammar rejected odd intermediate gaps, but their terminal collision is
exactly `1+2*3^sQ -> 2+3^(s+1)Q=-1+2^LP'`; allowing `L=1` also turns a
one-bit output into a legal zero-delay rail.  The resulting
[parity-complete ISA](experiments/kontorovich/complete_splash_isa.py) has
exact Kraft mass `1/3+2/3=1` and uniquely decodes every positive odd payload
unless the macro reaches `1`.  The new exact `U^12` bridge has two universally
outward gates, and its formerly rejected third payload is now caught.  The
failure has moved rather than vanished: that catcher shrinks, and the full
120-digit witness parses into 290 gates before reaching `1`.  The
[headline](#kc-headline-results-with-verification-scope) and [strategy/failure
map](#kc-strategy-and-failure-map) record the exact scope.  Next: treat the
total decoder as the actual programming language and search symbolically for
an invariant aperiodic tape with positive long-run drift, especially a
saturated cylinder whose catcher cascade is also net outward.  In parallel,
Lean commit `dbe0e5a` now reduces a disproof through this compiler to exactly
such an outward renewing variable bridge chain, and `afb86a5` kernel-checks
the new odd catcher; the total decoder and chain existence remain open in
Lean and mathematics, respectively.

### 2026-07-21 23:04 EDT

The rational-base lane has crossed from analogy to compilation.  A universally
outward splash gate maps its nonlocal family index by
`95+128t -> 1640+2187t`, and exact algebra identifies this with seven steps of
Eliahou--Verger-Gaugry's divergent saturated-word map `U` for every `t>=0`.
Equivalently, one Collatz gate executes the base-`3/2` append block
`[1,1,1,1,1,2,1]` on an unbounded tape family.  The saturated orbit itself
enters at `U^41(0)=26906975`, producing the literal Collatz step-block
`440843894591 -> 470764451891`.  The result is also sharply scoped: the target
gate shrinks, its endpoint does not renew, and the ordinary seed reaches `1`.
The [certificate](experiments/kontorovich/two_rail_u_bridge.json) also audits
67,500 bounded shape links, finding three exact `U` blocks and only this one
outward source.  Next: search compositions whose choice of `U` block is read
from the changing payload, so the compiler follows the aperiodic saturated
word instead of stopping after one instruction.

### 2026-07-21 22:56 EDT

The payload-dependent controller now has an exact instruction grammar.  For a
fixed rail length, every splash shape is one LSB-first binary prefix; four
successive valuations uniquely decode `(a,s,b,L)`, so the prefixes are
disjoint.  Their exact Kraft mass among odd 2-adic payloads is `1/6`.  After
that sparse binary address is consumed, the affine handoff writes globally by
multiplying the residual tape by a power of three.  This is a concrete
binary-read/ternary-write tag machine, not just a PL analogy.  The new
[artifact](experiments/kontorovich/two_rail_prefix_code_audit.json) checks
1,344 codewords and 902,496 pairs for each `r=1..16` through 20 bits, plus
21,504 independent literal decodes; the [headline](#kc-headline-results-with-verification-scope)
states the universal derivation separately from those bounds.  Lean commit
`96f2357` meanwhile proves every fixed proposed word-period must be broken
infinitely often.  Next: represent the unique decoder as a payload-driven
transition system and search for a formula tape whose binary prefixes keep
selecting gates while the ternary writes force every fixed period to break.

### 2026-07-21 22:47 EDT

Two exact corrections sharpen the search.  First, a self-link or one fixed
finite affine return cannot be the bouncer: it repeats a nonempty valuation
word, and coefficient matching would require an integer slope
`3^N/2^S` with `S>0`.  The regenerative splash must rewrite its instruction
tape so the future gate sequence is genuinely aperiodic—precisely the
branching tag-machine interpretation, not a simple oscillator.  Second, the
full 1989 Väänänen--Wallisser theorem closes the rigid standard schedule.
Our partial theta is exactly `f_(3/2)(4096/6561)`; their `p=2` size hypothesis
follows without floating point from `2^8>3^5` and `5*4^2<9^2`, so the value is
2-adically irrational and cannot be the required integer payload.  Lean commit
`806bf8c` independently formalizes the recurrence, finite unrolling, `Q_2`
limit, and candidate obstruction; `3fc63a6` kernel-checks the all-coefficient
function mapping, size inequality, and citation endpoint; commits
`b741a14`--`560fcc5` independently
rule out fixed affine, eventually periodic, and autonomous finite-state
controllers.  The new [exact application
audit](experiments/kontorovich/standard_two_rail_irrationality_audit.json),
[headline](#kc-headline-results-with-verification-scope), and [failure
map](#kc-failure-ledger) record the scope.  Next: build the branching
payload-index transducer and hunt an invariant aperiodic tape orbit; apply the
same special-function sieve to any low-description schedule it proposes.

### 2026-07-21 22:31 EDT

The splash now has exact programming semantics.  A two-rail collision reads a
dyadic address from a nonlocal payload index, deletes those low bits, maps the
remaining tail by a power of three, and appends an offset.  Lean commits
`4789a80`/`1076954` certify affine instructions and their composition for all
natural tails; `2f2e24e` proves that an outward affine return
`u -> c+m*u`—expanding is allowed—would literally disprove Collatz.  A bounded
canonical-member audit checked 128,000 gate shapes, found only 25 links and a
two-gate maximum; its witness `45247 -> 48319 -> 103199` reaches `1`.  This is
a scoped zero-preload failure, not evidence against affine loops.  Separately,
the rigid standard schedule reduces to one 2-adic Tschakaloff value; its exact
247-round truncation reaches 33,333 bits of precision, but no applicable
irrationality theorem has yet been verified.  The [headline](#kc-headline-results-with-verification-scope),
[failure map](#kc-failure-ledger), and [special-function
note](docs/notes/standard-two-rail-theta.md) record the scope.  Next: search
coefficientwise for affine self/return circuits, audit the p-adic theorem, and
try to compile the base-`3/2` “append `2`” instruction or a Stérin--Woods
diagonal defect into the exact gate ISA.

### 2026-07-21 22:02 EDT

The “gap splash” has become an exact two-rail circuit rather than only a
metaphor.  A `-1`/valuation-one rail pumps a remote payload, a collision emits
a `+1`/valuation-two cleanup rail, and a second collision regenerates the
`-1` rail one bit farther out.  The first standard gate is
`94751 -> 101183`.  More strikingly, symbolic intersection of the complete
affine gate families—not an interval search—constructs a 10,040-digit seed
executing 247 strict outward rounds and growing its gap from 5 to 252 bits.
Every one of its 32,110 designed accelerated steps replays exactly.  It is
also a clean failure: the depth-248 canonical seed is different, and full
exact continuation reaches `1` after 155,190 accelerated steps.  The new
[certificate](experiments/kontorovich/two_rail_chain_247.json), [verifier](experiments/kontorovich/two_rail_gate.py),
[headline](#kc-headline-results-with-verification-scope), and [failure
entry](#kc-failure-ledger) record both facts.  Lean commit `6229e7a` meanwhile
kernel-checks the generic `+1` delay line and Colussi order-10 wire.  Next:
replace finite affine-family intersection by a recursive payload relation and
attack its ordinary-integer stabilization directly.

### 2026-07-21 21:47 EDT

Simon proposed “splashing the gap”: line up other packets so collision carries
eat the dirty bits and regenerate a sparse wire.  The metaphor survives exact
algebra.  For any incoming and outgoing `+1` delay lengths and collision
extra, [`splash_gate.py`](experiments/kontorovich/splash_gate.py) constructs a
whole arithmetic progression of payloads realizing the requested splash; its
15,360-case literal regression passes.  The same derivation gives a clean
failure: every pure `+1` splash strictly decreases the integer.  The strategy
map now promotes a two-rail machine—an amplifying `-1`/`k=1` Mersenne rail plus
a timing/cleanup `+1`/`k=2` Colussi rail, joined by phase-changing splash
gates.  Lean commit `f1cb0e2` meanwhile proved the unbounded dyadic--triadic
packet gate and unique payload theorem requested at 21:28.  Next: synthesize
an exact two-rail phase switch whose `k=1` pump pays for the cleanup loss and
emits a larger pair of gaps.

### 2026-07-21 21:40 EDT

Restored the spatial half of Kontorovich's picture inside the nonlocal ISA.
Colussi's formula-generated order-10 seed—11,846 decimal digits—has an exact
ten-instruction decoder to `1+2^39348`.  That is a literal separated packet
crossing a 39,348-bit delay line for 19,673 valuation-two ticks before a
precisely timed collision.  The new [certificate and
verifier](experiments/kontorovich/README.md#formula-generated-colussi-delay-line)
reconstruct the seed, replay all steps, and then continue it to `1` after
95,146 accelerated steps.  A 1,024-step collision audit finds no renewed gap
wider than 10 bits, so the unmodified wire is now a scoped failure; a defect
must rewrite the collision.  In parallel, Lean commit `b205e40` completed the
scale-free `Q_2` candidate construction for every Mersenne schedule, leaving
only candidate nonintegrality for a useful controller class.  Next: treat a
Collatz program as spatial delay-line segments wired together by nonlocal
dyadic--triadic gates, and search for a defect which makes the first collision
emit a longer wire.

### 2026-07-21 21:28 EDT

At Simon's direction, pivoted from widening packet ranges to reverse-
engineering a possibly nonlocal programming language.  The new
[instruction-set map](docs/notes/kontorovich-delocalized-isa.md) audits the
mixed-base rewrite, three-symbol tag, Colussi repetend, and Busy Beaver
bouncer presentations; it explicitly credits Simon's PL and whole-digit-span
hypotheses.  The first exact decoder is a dyadic--triadic packet gate: a fixed
low address transforms an arbitrary high payload affinely and schedules the
next packet modulo `3^m`.  Its dependency-free checker passes 8,192 direct
family cases and an exhaustive small converse audit.  No new GPU range sweep
was launched; the drafted level-array launch was discarded.  PSC job
`42499002` then timed out at two hours with only 7 of 64 length-eight
nonuniform-morphism shards complete, so it proves nothing and will not be
relaunched in the same form.  The 24 Ganesha length-seven workers remain
healthy in the background.  In parallel, Lean commit `7370489` proved
uniqueness of the ordinary realization of a fixed symbolic stream and the
exact finite backward series for Mersenne controllers, opening a non-search
2-adic nonintegrality sieve.  Next: mine formula defects on Colussi's order-`h`
background in the mixed-base rewrite system and test whether a precise p-adic
gap/automaticity theorem can eliminate periodic controllers wholesale.

### 2026-07-21 21:05 EDT

PSC H100 job `42500602` completed the independent `h<2^36` packet census in
eight seconds.  Its exact counters and all 243 stored hit triples agree with
the RTX 4090 artifact, and arbitrary-precision Python replay passes.  The
separate artifacts and hashes are in the [experiment
guide](experiments/kontorovich/README.md#direct-gpu-packet-census).  This
corroborates the inner run without extending the `h<2^42` frontier.  The
Ganesha length-seven nonuniform-morphism workers remain healthy; the PSC
length-eight search is producing partial shards but is approaching its first
walltime.  Next: preserve or cleanly relaunch that finite census as needed,
and scan packet starts above level one rather than spend more compute only on
larger level-one packets.

### 2026-07-21 20:51 EDT

Completed nested direct state-dependent packet censuses on Akdeniz's RTX
4090.  The wider run covers all `274,877,906,944` odd packets below `2^39`,
with eight renewal attempts each and zero 64-bit overflows.  Independent
Python big-integer replay verifies all 14 seven-renewal hits; none reaches
eight.  A final nested scan covers all `2,199,023,255,552` odd packets below
`2^42`, again with zero overflows and no eight-renewal hit.  The inner
`h<2^36` run retains all 243 six-or-more hits for motif
mining.  The best finite tail has four consecutive outward macros but then
fails and reaches `1`.  Exact bounds and hashes are in the [experiment
guide](experiments/kontorovich/README.md#direct-gpu-packet-census).  PSC H100
job `42500602` remains queued as a hardware-independent rerun, while the two
nonuniform-morphism jobs continue.  Next: mine the 14 length-seven packet
chains against Lean's modulo-`3^m` scheduler for a compact state-dependent
feedback invariant.

### 2026-07-21 20:08 EDT

Added the previously omitted signed fixed controller `-1`, which encodes long
Mersenne-like runs of valuation one.  Its exact `376,800`-path sweep found
three finite all-outward seed-stabilization events.  The best seed,
`24,017,279`, grows at all three controller macros through `1,579,334,395`,
then misses the next precision class and reaches `1` after 108 accelerated
steps.  This is the closest bounded glider motif so far, but it is explicitly
not a counterexample.  Lean commits `843387b`--`d6fb8b2` now remove all finite-
prefix, growth, sign, and rotated-phase proof burdens from a future witness:
the sole missing object is an infinite exact bounded-extra renewal stream.
Lean commit `768f4d0` separately kernel-checks the `-1` controller, its exact
macro identity, the outward finite regression, and the specialized implication
from an infinite Mersenne renewal to Collatz failure.
Next: search arithmetic feedback rules for the `-1` collision extras rather
than enumerate another fixed-depth rectangle; PSC/Ganesha morphic jobs remain
active.

The first feedback test is complete: every constant extra `1..32` was checked
through depth 40 and start level 20 (`51,200` paths).  Constant `e=1` gives
seed `121` two unchanged-prefix extensions, then fails at level five and
reaches `1`; no other constant rule matches it.  Next moves to short periodic
and state-dependent extra rules.

The periodic sweep then checked `2,726,400` exact prefixes from every primitive
period-at-most-three template over extras `1..8`, through start level 30 and
depth 80.  It finds no improvement: constant `1` remains the unique two-
extension event, and `(4,3,1)` remains the best outward event.  Lean commits
`32a0896`--`a2652f2` reduce the next search to a pure packet recurrence and
provide a modulo-`3^m` scheduler; state-dependent arithmetic feedback is now
the active Mersenne lane.

The direct Akdeniz packet census described below has now completed and passed
independent replay.  PSC H100 job `42500602` remains queued as an independent
rerun of the same range.

### 2026-07-21 19:54 EDT

Allowed carry collisions to change phase around the same negative cycle.  This
unlocked 15 exact `-5/-7` precision renewals and 10 one-extension ordinary-seed
stabilizations, including seed `53,403,857`; every event is finite, shrinking,
and fails on the next collision.  The complete bounded phase grammar checked
`1,950,864` positive paths; all seven phases of the `-17` controller were
negative.  Counts, bounds, and replayable events are in the [KC headline
table](#kc-headline-results-with-verification-scope) and [experiment
guide](experiments/kontorovich/README.md#phase-changing-shadow-collisions).
PSC/Ganesha morphic shards continue in parallel.  Next: extract a collision
grammar that renews at start level at least seven, where bounded-extra shadow
macros can become outward, rather than widening the now-failing low-level box.
Lean commits `3d9cedc` through `0d8c3d2` simultaneously checked the signed
controllers, all rotated phases, macro endpoint, eventual-growth inequality,
and the implication from an infinite phase renewal to literal Collatz
failure.  The research gap is therefore the renewal sequence itself, not a
missing bridge from such a sequence to the conjecture.

### 2026-07-21 19:34 EDT

Recovered posts 14--17 of Kontorovich's thread and restored their concrete
separated-bit/carry-timing proposal to the [live strategy
map](#kc-strategy-and-failure-map).  Lean commit `63c3b3d` now kernel-checks
the full finite compiler specification; `121cb13` proves the packet clock, and
`ad36f08` proves canonical-seed stabilization equivalent to the ordinary-
integer gate.  Ganesha passed the exact worker self-test
and is running 24 shards over nonuniform morphisms of image length at most
seven.  PSC job `42499002` passed the same test and is running 64 shards over
the complete length-at-most-eight class.  Next: verify and merge both complete
shard sets, then use their best ordinary-seed stabilization motifs to seed the
packet-collision search.

The first packet-collision sublane is also complete: a positive state can
shadow a supercritical negative cycle while a high packet grows, but the carry
must replenish one more level of 2-adic precision.  Exact search of `112,320`
bounded `-5`/`-17` controller programs found no such renewal and no ordinary-
seed stabilization; the scoped failure is now in the [KC failure
ledger](#kc-failure-ledger).  The next version will vary the collision grammar
and controller phase rather than enlarging this same rectangular box.

### 2026-07-21 19:15 EDT

Pivoted the project to the Kontorovich challenge and pushed the first exact
checkpoint.  The finite-word compiler, Python replay verifier, kernel Lean
cycle-disproof seam, parametric-glider endpoint, and all-level periodic-word
obstruction all pass.  Bounded
composition and uniform-morphism searches found no nontrivial cycle; the
small uniform morphism ansatz is now in the [KC failure
ledger](#kc-failure-ledger), with scopes in [KC headline
results](#kc-headline-results-with-verification-scope).  PSC, Akdeniz, and
Ganesha are reachable; next is a distributed search over non-uniform morphic
and one-counter-adjacent templates, while Lean checks the periodic-word
obstruction.

## Project guides

The front page is the state-of-the-project map.  These are the other README
entry points, grouped by role:

| Guide | Scope |
|---|---|
| [`experiments/kontorovich/README.md`](experiments/kontorovich/README.md) | Exact finite `k`-word compiler, replayable cycle artifacts, and bounded morphic-glider searches. |
| [`docs/notes/kontorovich-delocalized-isa.md`](docs/notes/kontorovich-delocalized-isa.md) | Simon's nonlocal-instruction hypothesis, exact packet gates, ultra-small-language encodings, and the formula-bouncer attack. |
| [`KontoroC/README.md`](KontoroC/README.md) | Independent Lean checker connecting a nontrivial accelerated cycle artifact to the ordinary Collatz conjecture. |
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

**The Kontorovich challenge and disproof frame.**
- **A. V. Kontorovich & Ya. G. Sinai, [“Structure Theorem for
  `(d,g,h)`-Maps”](https://arxiv.org/abs/math/0601622), Bull. Braz. Math. Soc.
  33 (2002), 213–224** — the exact arithmetic-progressions theorem for every
  finite valuation word and the density-level Brownian limit with drift
  `log(3/4)`.  The present compiler is a constructive specialization of their
  finite-word structure.
- **A. Kontorovich, [2019 thread on why the evidence for Collatz may be
  weak](https://x.com/AlexKontorovich/status/1172715174786228224)** — the
  hardware/software and “glider” challenge that sets the active research
  objective, including the proposed timing of widely separated bit packets
  using powers of `3` modulo powers of `2`.  The thread proposes a search
  philosophy, not a counterexample; an [archived full-thread
  rendering](https://threadreaderapp.com/thread/1172715174786228224.html)
  preserves posts 14--17 omitted from the prompt excerpt.
- **J. H. Conway, “Unpredictable Iterations” (1972)** — generalized
  Collatz-type maps can encode computation.  This motivates looking for
  structured programs while not transferring universality to the specific
  `3x+1` map.
- **Simon Dedeo** — suggested importing macro ideas from ultra-simple
  programming languages, targeting a possible 10,000-digit program, and—most
  importantly—not assuming spatial locality: a Collatz instruction may be a
  relation spread across the entire digit span.  Simon then proposed the
  “gap splash”: align sacrificial packets so collision carries erase the bad
  suffix and regenerate a delay line, then asked whether leaving a controlled
  overhang could absorb collision debris and renew the gap.  The exact
  three-bit-capped super-ether is the first recursive realization of that
  refinement, and the two-layer unit regenerator now isolates the general
  correction-word/carry identity.  Those proposals are the basis of the
  active dyadic--triadic, mixed-base, and two-rail bouncer searches.
- **L. Colussi, “The convergence classes of Collatz function” (2011)** — the
  exact rotated-repetend grammar for all finite stopping classes.  Its
  recursively generated order-10 background supplies an 11,846-digit
  structured test bed for a scale-changing defect.  The new unit repetend
  splash uses the same basic arithmetic resource in a different register:
  `(2^T C-s)/3^q` is a formula-generated sacrificial rail whose collision
  leaves a chosen marker and a clean gap.
- **L. De Mol, “Tag systems and Collatz-like functions” (2008)** and **E.
  Yolcu, S. Aaronson & M. J. H. Heule, “An Automated Approach to the Collatz
  Conjecture” (2023)** — respectively the three-symbol tag and 11-rule mixed-
  base presentations now being mined for formula bouncers.  These are exact
  encodings, not claims that the Collatz map itself is universal.
- **J. Cocke & M. Minsky, [“Universality of Tag Systems with
  `P=2`”](https://doi.org/10.1145/321203.321206) (1964)** — proves that
  deletion-two tag systems can simulate a Turing machine by encoding the two
  sides of its tape as binary stacks.  It does not say that De Mol's particular
  three-rule Collatz tag system, or the Collatz map, is universal.  Its remote
  append and two-stack moves are concrete compiler obligations for the
  separated-packet lane.
- **K. Morita, [“Universality of a Reversible Two-Counter
  Machine”](https://doi.org/10.1016/S0304-3975(96)00081-3) (1996)** — proves
  that reversibility does not prevent a two-counter machine from being
  universal.  This makes the charge bouncer's exact forward/reverse decoder a
  meaningful PL clue, but transfers no universality: its instruction set and
  arithmetic acceptance classes are far more constrained.  **A. Dudenhefner,
  [“Certified Decision Procedures for Two-Counter
  Machines”](https://doi.org/10.4230/LIPIcs.FSCD.2022.16) (2022)** is the
  relevant warning that decidability for reversible two-counter machines is
  instruction-set-sensitive; the present work must compile the actual
  increment/decrement/branch primitives, not argue from “two counters.”
- **T. Stérin & D. Woods, [“The Collatz process embeds a base conversion
  algorithm”](https://arxiv.org/abs/2007.06979) (2020)** — the exact
  quasi-cellular automaton with binary rows, ternary columns, and a nonlocal
  least-significant-bit bootstrap.  It supplies a spatial grid on which a
  diagonal defect or boundary glider can be posed exactly.
- **K. Mahler, [“An unsolved problem on the powers of
  `3/2`”](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/6416420BFE33A5DDC3DAB6EA358C2B0B/S1446788700005371a.pdf/an-unsolved-problem-on-the-powers-of-32.pdf)
  (1968)** — the original `Z`-number break-off algorithm repeatedly extracts
  a complete dyadic valuation and replaces it by a triadic factor.  The
  autonomous router's radix swap is a stricter factor-three-reserving cousin;
  no equivalence with `Z`-numbers is claimed.
- **S. Eliahou & J.-L. Verger-Gaugry, [“The number system in rational base
  `3/2` and the `3x+1` problem”](https://arxiv.org/abs/2504.13716) (2025)** —
  the rational-base tape where shortcut Collatz appends digit `1`, and a
  related saturated-word map appending `1` or `2` diverges.  We treat its
  missing “append `2`” as a compiler target, not as transferred divergence.
- **K. Väänänen & R. Wallisser, [“Zu einem Satz von Skolem über lineare
  Unabhängigkeit von Werten gewisser
  Thetareihen”](https://gdz.sub.uni-goettingen.de/download/pdf/PPN365956996_0065/LOG_0016.pdf)
  (1989)** and
  **W. Zudilin, [“An elementary proof of the irrationality of Tschakaloff
  series”](https://arxiv.org/abs/math/0506086)
  (2005)** — the closest arithmetic literature for the exact partial-theta
  values forced by the standard two-rail schedule and by every constant-rate
  fixed-level unit clock.  The full-source p-adic Väänänen--Wallisser theorem
  applies and rules out both ansatz classes after their exact hypothesis
  audits; Zudilin's displayed real/complex hypothesis fails for the original
  standard-schedule parameters.
- **D. Barina, “Improved verification limit for the convergence of the
  Collatz conjecture” (2025)** — the `2^71` exhaustive frontier used to
  calibrate why another ordinary seed sweep is not the active attack.

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
