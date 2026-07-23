# Exact accelerated-Collatz bitmaps

Each PNG in this directory is a literal raster of positive odd integers under

```text
T(n) = (3n+1) / 2^v2(3n+1).
```

The seed is the top row and successive accelerated iterates run downward.
Rows are right-aligned place-value expansions, so the least significant bit is
at the right edge. A black pixel is one; a white pixel is zero or left padding.
There is exactly one image pixel per bit and one image row per odd state. The
PNG files are 8-bit grayscale containers but use only sample values 0 and 255.

`constructions.json` records the exact seed, endpoint, expected step count,
scope, and source artifact for every reviewed image. `render_collatz.py`
replays the arbitrary-precision integer dynamics, refuses an endpoint or step
count mismatch, and writes a JSON sidecar containing exact statistics and
SHA-256 hashes. Regenerate the reviewed collection with:

```bash
python3 IMAGES/render_collatz.py
```

Most images contain the full expansion. A registry entry with `low_bits`
produces an explicitly labeled least-significant-bit window while preserving
the same one-row-per-odd-iterate rule. The low-bit crop is useful for address
memory: `v2(n+1)` is exactly the trailing run length of black pixels in `n`.

The six `returning_glider_*_prefix.png` files are finite exact compiled
prefixes, not counterexamples. `returning_glider_6_full.png` continues the
same positive seed to 1 and makes the post-construction collapse visible.
The two `mersenne_*_full.png` files likewise show finite controller witnesses
whose exact ordinary continuations reach 1.

The `outward_first_passage_270271_*` files show the record minimum-address
finite witness from the maximal outward code audit. Its 87-step constructed
prefix ends at the global peak; the next accelerated step drops below that
boundary permanently, and the full orbit reaches 1 at step 150.

`monitor_repo.py` fingerprints the counterexample-search surface and can run
continuously. It updates only a delimited machine-alert block in the root
`VISUALIZER_COMMENTS.md`. A changed JSON artifact is auto-rendered only when an
object supplies an exactly replayable outward
`collatz_source`/`collatz_target`/`accelerated_steps` triple. Those unreviewed
outputs go to ignored `IMAGES/AUTO/`; a human or visualizer agent must review
and promote them before they become research evidence.

```bash
python3 IMAGES/monitor_repo.py --initialize
python3 IMAGES/monitor_repo.py --watch --interval 60
```

`analyze_consumption.py` measures the visual warning shared by the reviewed
finite controllers: how much low-valuation runway remains after the certified
motif, where the trajectory peaks, and how soon it falls irreversibly below
the motif endpoint. Its output is `consumption_diagnostics.json`.

`analyze_bit_entropy.py` records exact one- and two-pixel block counts on every
row of the active binary expansion and a fixed low-16-bit window, plus counts
through four pixels at marked construction boundaries. It also emits floating
empirical entropy diagnostics for plotting. These measure balance and local
syntactic complexity, not certified controller memory; the Mersenne example
shows why the distinction matters.
