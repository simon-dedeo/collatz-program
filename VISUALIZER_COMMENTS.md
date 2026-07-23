# Visualizer comments

## 2026-07-23 — initial exact raster pass

There is no counterexample. The new images are finite exact replays, and the
current bivariate Mahler/Jordan ruler is not rendered as a Collatz orbit
because it does not supply an ordinary positive seed.

The strongest visual contrast is between
`IMAGES/returning_glider_6_prefix.png` and
`IMAGES/returning_glider_6_full.png`. The certified construction controls the
first 45 accelerated steps. In that prefix every valuation is 1 or 2: there
are exactly 29 ones and 16 twos, so the mean valuation is `61/45`. The value
grows from

```text
213035522142268397688894067577
```

to

```text
272947268090994234357505277036711.
```

The repeating right-edge texture comes from the ether word. In the longer
prefixes one sees repetitions of the six-letter valuation block `112121`,
whose valuation sum is 8. Ignoring the positive affine correction, one such
cell has multiplicative factor `3^6/2^8 = 729/256 > 1`. This is the clean
visual reason the compiled strip expands.

The full image shows the actual problem. After the 45-step certified prefix,
the remaining 241 steps have valuation sum 490 and mean `490/241`; 65 of
those steps have valuation at least 3. The orbit keeps climbing to its peak at
step 72, but after that peak the remaining mean valuation is exactly
`454/214 = 227/107`, well above `log_2(3)`. The left boundary then forms the
large white wedge visible in the full raster, and the orbit reaches 1 at step
286. The construction is not failing because its ether cell is locally weak;
it fails because it does not autonomously write the next low-valuation cell.

This suggests a more targeted image-analysis program than global black-pixel
density. The high-order bulk is visually close to a mixed carry field, while
the self-writing gate is stored in the low-order address. Future diagnostics
should align successive ether-cell boundaries and compare only the rightmost
`8m+15` columns, then rasterize the XOR/carry residual from one cell to the
next. A persistent low-complexity residual would be a candidate state variable
for the payload writer; a residual whose required width grows with every cell
would visualize the existing canonical-address obstruction.

For clean handoff to the visualizer, new exact artifacts should expose a JSON
object containing `collatz_source`, `collatz_target`, and `accelerated_steps`.
The monitor verifies that triple under the accelerated odd map before making
an unreviewed bitmap. Symbolic schedules, 2-adic residues, and macro states are
not silently treated as ordinary Collatz seeds.

## 2026-07-23 — the small spikes in `mersenne_terminal_*`

The spikes noticed by Simon encode the controller state almost literally.
The tight raster is `IMAGES/mersenne_terminal_265296544373759_spikes.png`.
At its four macro boundaries the exact states and address depths are

```text
step   state                  v2(state+1)
0      265296544373759        10
10     7649167797229567       11
21     2584509139587071       12
33     10479081128321023      13
46     509858400321904295      3
```

For a state with `v2(n+1)=L`, the `-1` shadow forces `L-1` consecutive
accelerated valuations equal to one. Thus the visible rising faces contain
exactly 9, 10, 11, and 12 locally expanding steps. Their complete valuation
words are

```text
1^9  2
1^10 9
1^11 6
1^12 3.
```

The last valuation in each row is the cliff. Its size determines whether the
next macro is larger or smaller, but the subtler success condition is whether
the endpoint writes a still deeper `-1` address. Here the construction writes
depths 10 through 13 and then resets to depth 3 instead of reaching 14. This
turns the visual search target into a crisp one: look for a raster with an
unbounded staircase of progressively taller spikes whose post-cliff endpoints
keep increasing `v2(n+1)`, not merely for isolated high peaks.

The newly added raw first-passage code is symbolic and supplies no ordinary
infinite seed, so it is not itself rasterized as an orbit. For comparison,
`first_passage_zero_lift_prefix.png` shows the strongest stored finite
canonical zero-lift run from the earlier four-word truncation, translated to
its odd accelerated seed. `first_passage_zero_lift_full.png` shows that the
same seed reaches 1 after the controlled prefix.

## 2026-07-23 — regular texture is fuel, not renewal

Simon's warning about the EC17 images is borne out exactly. In the six-cell
returning-glider orbit, the certified motif ends at accelerated step 45. The
ordinary suffix happens to preserve the same low-valuation alphabet `{1,2}`
for 27 more steps, reaches its global peak exactly at step 72, and then hits
valuations 3 and 4. At step 76—only four steps after the texture breaks—it is
below the certified-prefix endpoint for the last time and never returns. The
isolated suffix is `IMAGES/returning_glider_6_after_prefix.png`.

The same diagnostic is even harsher elsewhere:

```text
construction                  runway to k>=3   irreversible collapse lag
EC17 returning glider n=6           27                    31
Mersenne depth staircase              6                     8
first-passage zero-lift run            0                     1
```

These values are exact finite first/last-passage statistics, recomputed by
`IMAGES/analyze_consumption.py`; they are not an all-orbit theorem.

The conceptual warning is stronger than “this example eventually went down.”
A finite dyadic address is a strip of stored instructions, and the dynamics
consume at least one address symbol per step. Making the initial seed wider
can buy an arbitrarily long regular picture without creating a writer. An
exactly periodic outward texture is also not the desired endpoint: the repo's
periodic and eventually periodic controller lanes are already closed. A
credible image of escape should therefore show **renewed but evolving**
structure—new motifs appearing at later scales before the old motif reaches
its read boundary—not one stationary stripe extended by a larger seed.

New constructions should pass a visual renewal gate at every advertised
macro boundary:

1. report the remaining exact address depth before the boundary;
2. report the newly written address depth after it;
3. require the latter not to be merely a suffix of the preloaded initial
   address; and
4. show that motif lifetime grows along one fixed ordinary seed, rather than
   across a sequence of ever-wider canonical seeds.

The raw first-passage program expresses the same issue as tightness of the
canonical addresses. In image language: if the left edge must move farther
out at time zero whenever another regular block is requested, the construction
is drawing a longer fuse, not building a self-renewing engine.

## 2026-07-23 — memory must survive the retraction

The bits to the right of the moving magnitude edge are indeed the only place
an ordinary integer can store its future. The important refinement is that
raw bit count is not yet memory: memory must mean **certified future address
depth** for the controller language. Random-looking surviving bits do not help
unless their residue forces the next macro.

For the `-1` Mersenne shadow this quantity is exact and visible without a
decoder:

```text
M(n)=v2(n+1)=number of trailing black one-bits of n.
```

At a macro start, `M(n)-1` is the length of the forced expanding run. The
post-retraction memories in the spike image are

```text
10 -> 11 -> 12 -> 13 -> 3,
delta  +1    +1    +1   -10.
```

`IMAGES/mersenne_terminal_spikes_low16.png` keeps only the exact 16 least
significant bits of every odd iterate. The growing right-edge black bars at
macro steps 0, 10, 21, and 33 are the stored future. At step 46 the bar is
destroyed: the value is still large, but its controller memory has collapsed.

This gives a stronger acceptance test for a proposed spike mechanism. Let
`D_i` be the largest dyadic address precision at the `i`th post-retraction
boundary that actually certifies the next intended behavior. A finite preload
only spends `D_i`. A writer must make `D_(i+1)` grow along the same fixed
ordinary orbit, after accounting for the bits consumed by the macro. In the
Mersenne coordinate, the simplest visible target is an unbounded sequence of
post-retraction trailing-one bars. In EC17, the analogous `D_i` must be read
from the exact public-payload/carry decoder; ordinary bit length or black-pixel
density is not an adequate substitute.

## 2026-07-23 — large visual review: how memory leaves the system

### Executive finding

The pictures now support a sharper diagnosis than “the value eventually
decreases.”  The program has repeatedly built **large integers with finite
scripts**, but it has not yet built an ordinary orbit that both executes a
macro and leaves behind more certified instructions than it consumed.  In
the strongest visual examples, the magnitude edge can keep moving while the
right-edge controller state is erased.  The later numerical collapse is a
consequence; the earlier information collapse is the warning sign.

This is a finite, exact review of the checked artifacts, not a proof about all
possible Collatz constructions and not a counterexample.

### The entropy experiment

`IMAGES/analyze_bit_entropy.py` measures exact overlapping one- and two-bit
word counts in every active binary row and fixed low-16-bit window, with
counts through four bits at marked construction boundaries.  Its output is
`IMAGES/bit_entropy_diagnostics.json`.  The decimal entropies are plotting
diagnostics derived from exact finite counts.  They are not Shannon entropies
of a proved stochastic source.

The decisive Mersenne comparison is the last certified macro boundary before
the terminal retraction:

| step | active width | exact `v2(n+1)` memory | active H1 | active delta-H2 | low-16 H1 |
|---:|---:|---:|---:|---:|---:|
| 33 | 54 | 13 | 0.950956 | 0.959955 | 0.337290 |
| 46 | 59 | 3 | 0.998134 | 0.978851 | 0.954434 |

At precisely the transition where the certified Mersenne controller loses ten
bits of future depth, both the full-row black/white balance and the incremental
two-pixel entropy estimate move **toward their maxima**.  The low-16 window
becomes dramatically more balanced as well.  The row looks richer while the
usable program becomes poorer.

So the proposed statistic is useful, but chiefly as a negative control:

- low block entropy can expose a rigid bar or ether that is being consumed;
- high block entropy certifies neither a decoder nor a next opcode;
- entropy computed after adding white left-padding is invalid because it mixes
  magnitude loss with bit balance;
- active-string entropy mostly becomes a width-weighted capacity estimate once
  the row is mixed, so it can remain high throughout a collapse;
- a unary counter such as a trailing-one Mersenne bar can store unbounded
  information with very low entropy, so balance is not necessary for scalar
  memory either.

What matters is **semantic memory**: bits that an exact public decoder turns
into certified future behavior.  A better eventual statistic is mutual
information between a public boundary state and its future opcode/address,
but that requires a specified ensemble of boundary states and an exact
decoder.  On one deterministic bit string, empirical block entropy is only
local texture complexity.

### What the principal images say

#### Mersenne terminal construction

This is the cleanest memory-loss microscope.  The spike staircase carries an
exact public counter `v2(n+1)` through depths `10,11,12,13`, then the final
retraction resets it to `3`.  The active width still rises from 54 to 59 across
that reset.  Therefore magnitude, pixel balance, and controller memory are
three genuinely different resources.

The construction should not be extended merely by adding another taller
preloaded bar.  The missing operation is a write-back that makes the
post-retraction trailing-one depth exceed the inherited depth on the *same*
ordinary orbit.

#### EC17 returning glider

The prefix is visually regular for 45 accelerated steps, followed by a long
low-valuation runway and a peak near step 72.  It then falls irreversibly below
the prefix endpoint near step 76 and reaches 1 at step 286.  Its monobit
entropy remains essentially maximal around this transition.  This reinforces
the Mersenne lesson: a balanced-looking residue can be the debris of a decoded
motif, not retained instructions.

For EC17, `v2(n+1)` is only a suffix statistic.  Any future visualization must
overlay the exact public payload/carry decoder and mark which bits certify the
next macro.  Without that overlay, a regular diagonal texture is aesthetically
suggestive but semantically ambiguous.

#### First-passage zero lift

The zero-lift prefix has a certified finite outward passage, then begins its
collapse one accelerated step after the construction boundary and reaches 1
at step 56.  This is the most severe “longer fuse” warning: extending the
horizon selects a farther initial address, but does not show a fixed seed
writing its next address.

The newer maximal outward-code record makes the same warning even cleaner.
The exact seed `270271` executes its stored 35-block odd prefix for 87
accelerated steps and reaches the prefix endpoint `8216025965`, which is also
the global peak of its whole orbit.  The very next accelerated step falls
below that boundary, never returns, and the orbit reaches 1 at step 150.
`IMAGES/outward_first_passage_270271_prefix.png`, its low-16 crop, and its
full continuation make the transition explicit.  This is a strong finite
record and a particularly sharp tape-exhaustion image, not an infinite
survivor.

It also repeats the entropy paradox.  From the boundary at step 87 to the
first post-prefix step 88, active width falls `33 -> 32`, but monobit entropy
rises `0.945660 -> 0.997180`, incremental two-block entropy rises
`0.877532 -> 0.982180`, and the low-16 monobit entropy becomes exactly `1`.
The most balanced row is already on the collapsing side of the boundary.

The correct visual companion to first-passage mass is therefore a
**canonical-seed horizon plot**.  If the least surviving residue keeps moving
right as the horizon grows, the family is diffuse.  An ordinary survivor
requires the canonical addresses to remain bounded and eventually stabilize.

### Review across the research program

The major construction families differ in notation but repeatedly meet the
same conservation law.

- The two-rail construction proves impressive finite outward motion: 247
  rounds from a 10,040-digit seed, with a growing rail gap.  At the next round
  the seed changes, and the depth-247 seed still reaches 1.  The visual issue
  is not insufficient scale; it is nonrenewal of the public address.
- The Colussi wire provides 19,673 valuation-two ticks from an 11,846-digit
  seed and then reaches 1.  Its clock is a large preloaded tape.  No checked
  writer recreates the gap that supplies the following tape segment.
- Recursive and hierarchical compilers produce arbitrary finite depth, but
  their ancestor addresses grow with the requested horizon.  The hierarchy is
  in the seed-selection procedure, not yet in one ordinary trajectory.
- The YAH/tag work has genuine opcodes and decoders.  Its missing object is a
  recurrent graph on public Collatz charts whose return map both preserves the
  data and regenerates the controller state.
- Named morphic clocks and ether candidates show finite regularity but no
  stabilizing ordinary seed.  Regular texture alone is expected to be cheap:
  finite residue prescriptions can manufacture long motifs.
- The outward first-passage lane now has a strong exact mass statement, but
  its natural tilted flow is diffuse rather than tight.  Ensemble survival is
  not an atom, just as high bit entropy is not a decoded instruction.
- The Mahler and scheduled lanes constrain several fixed symbolic schedules,
  but they do not provide a self-sustaining public register.  Scale relations
  are not control flow.
- The cycle searches remain bounded exhaustive evidence only; they have not
  supplied a nontrivial cycle.

### The resource ledger future constructions should expose

At every proposed macro return, record three separate quantities:

1. `H_i`: ordinary height or bit length;
2. `D_i`: exact public address depth certifying future intended behavior;
3. `P_i`: decoded controller/payload state, including carry and phase.

Then split address depth into inherited unread material and material freshly
written by the completed macro:

```text
fresh_i = endpoint certified depth - inherited unread suffix.
```

A promising fixed-orbit engine needs positive amortized height drift **and** a
nonnegative, preferably positive, fresh-memory drift at a recurrent public
boundary.  It need not grow on every accelerated step.  It must recover after
each retraction.  A long construction with `fresh_i <= 0` is still consuming a
finite tape.

There are two complementary asymptotic requirements that should not be
confused:

- across requested horizons, the canonical initial seed must stabilize rather
  than escape to infinity;
- along that one stabilized orbit, the public memory must keep evolving or
  growing, because a bounded finite controller eventually repeats.

This resolves a visual tension: we do not want the initial address to grow,
but we do want the internal on-orbit address resource to regenerate.

### Acceptance tests for the next generation of artifacts

Every construction artifact intended for visual review should include:

- exact `collatz_source`, `collatz_target`, and accelerated step count;
- exact macro-boundary indices;
- the public decoder and its domain, with no hidden auxiliary tape;
- depth consumed, unread depth inherited, and depth freshly written per macro;
- canonical seeds for increasing horizons;
- the ordinary continuation fate of every finite witness tested;
- explicit finite scope and `counterexample: null` unless a full certificate
  exists.

The highest-value new plots are:

- a boundary memory ledger `(H_i,D_i,P_i)` rather than only a height trace;
- least-significant-bit rasters with decoded address/payload brackets;
- an XOR residual between the predicted return word and the actual return word
  to locate carry corruption;
- motif novelty after quotienting out shifts, so repeated preloaded ether is
  separated from freshly written structure;
- canonical-seed versus requested-horizon plots;
- collapse audits that continue every finite witness to 1 or to a stated
  exact cutoff;
- one- through four-bit entropy curves retained as syntactic diagnostics, with
  semantic memory overlaid rather than inferred from them.

### Research priority suggested by the images

The most promising next unit of work is not another record-length prefix.  It
is the smallest exact **return-and-write gadget**: a public chart on which one
macro returns to the chart, preserves or advances a payload, and leaves more
certified address depth than it inherited after costs.  Even a tiny positive
fresh-memory balance would be qualitatively new.  A construction that merely
makes a taller spike, denser suffix, or more balanced raster would not address
the observed failure.

The visual bottom line is simple: the program knows how to move outward and it
knows how to execute finite tapes.  It has not yet shown an ordinary Collatz
orbit that remembers how to keep doing so after the tape is consumed.

## 2026-07-23 — 71-bit scale correction

The earlier renderer chose the smallest canvas containing each trajectory's
actual peak.  That was why the Mersenne and outward-first-passage images were
only 61 and 33 pixels wide.  It was literal, but it hid the project's most
important scale calibration.  The EC17 collection already contained natural
widths `73,74,91,101,108,115`, so this was a presentation inconsistency rather
than a shortage of large constructions.

Full-expansion images now use a minimum 71-bit canvas and remain right-aligned.
The added columns are white zero-padding.  Explicit `low16` diagnostic crops
remain 16 pixels wide.

This distinction is essential: **a 71-pixel canvas is not a 71-bit seed**.
Padding a 19-, 48-, or 60-bit state does not move it beyond the published
ordinary-seed verification frontier.  Indeed a number strictly beyond
`2^71` needs at least 72 active bits.  Sidecars and the manifest therefore
record both canvas width and active peak width.  The pictures may share a
71-bit ruler, but only the active black/white support is mathematical state.

Under the stronger and more relevant reading—“the starting integer itself
must be beyond the verified range”—the current collection does have such
images, but only in the EC17 family: the four-cell, five-cell, and six-cell
starts, plus the six-cell post-prefix state.  Their active seed widths are
`83,92,98,108` bits.  The glider-six prefix and full-continuation images share
the same 98-bit seed.  All smaller-seed pictures are retained only because
they expose controller failure modes cheaply and exactly.

<!-- visualizer-monitor:start -->
## Automated monitor status

Last change scan: `2026-07-23T19:40:52+00:00`. This block is a machine alert, not a research result.

Changed monitored files:

- `CLEAN_LEAN/FOR_FABLE.md`

Keyword alerts for visual review:

- `CLEAN_LEAN/FOR_FABLE.md`: 27: the advanced-fiber root law, the root self-loop counterexample, mixer | 28: bounds/counterexample, and rational pressure-row/Chernoff-gap checkers are | 184: ("selection") needs primitivity, and the branch residues cycle 5→2→8 (mod

<!-- visualizer-monitor:end -->
