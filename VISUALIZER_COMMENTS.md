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

<!-- visualizer-monitor:start -->
## Automated monitor status

Last change scan: `2026-07-23T19:17:02+00:00`. This block is a machine alert, not a research result.

Changed monitored files:

- `CLEAN_LEAN/FOR_FABLE.md`
- `README.md`
- `experiments/kontorovich/breakoff_ether_branch_pressure_audit.json`

Keyword alerts for visual review:

- `CLEAN_LEAN/FOR_FABLE.md`: 27: the advanced-fiber root law, the root self-loop counterexample, mixer | 28: bounds/counterexample, and rational pressure-row/Chernoff-gap checkers are | 184: ("selection") needs primitivity, and the branch residues cycle 5→2→8 (mod
- `README.md`: 18: certify a counterexample. | 38: There is still no counterexample. Simon's observation that the YAH/tag | 89: moment is ensemble conservation, not an ordinary orbit.
- `experiments/kontorovich/breakoff_ether_branch_pressure_audit.json`: 5: "claim_scope": "universal algebraic branch/unit-slice identities, exact finite prefix-tree regression at the stated bit budget, and exact 17-adic Hensel lifts through the stated pr | 6: "counterexample": null, | 186: "scope": "exact finite-polynomial orbit separation only; functional transcendence plus this zero estimate still require a new multivariate 2-adic auxiliary-value theorem before any

<!-- visualizer-monitor:end -->
