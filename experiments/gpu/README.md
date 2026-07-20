# gpu — CUDA ports of `family` and `expsum` (RTX 4090)

CUDA ports of the two validated CPU tools in `../family` and `../expsum`,
developed for the idle RTX 4090 (24 GB, sm_89) on `akdeniz.lan.cmu.edu`
(CUDA 12.8, `/usr/bin/nvcc`). Files are mirrored to `akdeniz:~/collatz/gpu/`.

| file | contents |
|---|---|
| `family_gpu.cu` | map-census inner loop on GPU, one thread per seed, blocked by map |
| `expsum_gpu.cu` | exhaustive-over-ξ transfer-matrix DP on GPU, one thread per ξ |
| `Makefile.gpu`  | `make -f Makefile.gpu` (build), `test` (both selftests), `probe` |
| `u128_probe.cu` | device `unsigned __int128` verification kernel (see below) |
| `compare_expsum.py` | tolerance comparator for expsum TSVs (gates + informational) |

## Build

    make -f Makefile.gpu            # nvcc -O3 -arch=sm_89 (no fast-math)
    make -f Makefile.gpu test       # runs both selftests on the GPU

`--use_fast_math` is deliberately not used: `expsum_gpu` needs IEEE double
`sincospi`/`log` to hold the 1e-9 validation gate.

## family_gpu — design

Same CLI as `family.c` (`--selftest`, `anchors [N]`, `grid2 [A] [B] [N]`,
`critical [Bmax] [N]`, `grid3 [NSAMP] [N]`; env `FAMILY_STEPCAP`,
`FAMILY_NOTRAP`, plus `FAMILY_GPU_MEM` = record-buffer budget in MiB,
default 3072).

**Device side.** One thread per seed `n`, maps batched so the per-seed record
buffer stays under the memory budget (49 B/seed: cycle-min u128, excursion
u128, steps u64, cycle-len u64, kind u8). The CPU's drop-below-start memo
cannot be used across parallel seeds, so each thread runs a **segmented
direct simulation** that reproduces the memo's semantics exactly:

- The CPU resolves seed `n` by stopping at the first orbit value `x < n` and
  inheriting `fate[x]`; `fate[x]` was resolved the same way. The fate of `n`
  is therefore determined by a *chain* of segments, each one a fresh
  `classify(seg_start)` with its own Brent state and its own `STEPCAP`
  budget (the cap is per-segment, not per-orbit).
- The GPU thread simulates the orbit and opens a new segment (resetting the
  Brent tortoise and the step budget) every time the value drops below the
  current segment start. Steps and max-excursion recorded for `n` are frozen
  at the *first* drop below `n` — the CPU's truncation semantics.
- The translation-trap fast path (`a_i = d` rows) is ported verbatim and
  applied per segment; its "inherit at `fate[vdrop]`" exit becomes "open a
  new segment at `vdrop`". Overflow cap `2^100`, step cap, and the exact
  in-loop check order (overflow → trap → step → drop → cycle → Brent → cap)
  match `family.c` line for line.
- **No remaining semantic difference**: all four modes byte-compare identical
  to the CPU tool (see Validation). The one *cost* difference: the GPU
  re-simulates each seed's full chain instead of looking the tail up in the
  memo, i.e. it does strictly more raw steps and wins by throughput.

**Host side.** Cycle candidates are flagged per seed on the GPU
(cycle minimum + Brent length); the registry is resolved on the **host** by
replaying the records in ascending-seed order — provably the same order in
which the CPU registers cycles (the first seed whose *terminal* fate is a
given cycle is exactly the seed whose own Brent closes it on the CPU).
This reproduces registry indices, basin-size tie-breaks, and the `F_XCYC`
saturation path bit-for-bit, with zero device-side atomics. Registry, fate
counts, rigidity probe, drift, and row formatting are verbatim `family.c`
code, so identical per-seed records imply byte-identical TSV.

**Device u128.** `unsigned __int128` (and signed) works in device code on
nvcc 12.8 / sm_89 for `+ - * >> << ==` **and even `/ %`** — verified
bit-exact against the host on 4096 random cases (`u128_probe.cu`, built
plain and with `-DTRY_DIV128`). The hot path avoids the slow generic 128-bit
divide anyway: `d = 2` uses shifts (as the CPU does) and `d = 3` uses a
4×32-bit long division by the small divisor; the generic i128 divide remains
only on the rare trap S<0 staircase path.

## expsum_gpu — design

CLI: `expsum_gpu selftest` and `expsum_gpu exhaustive KMIN KMAX` (K ≤ 40,
signatures with M ≥ 2^62 skipped — same caps as the CPU tool). Sampled mode
is not ported (it needs u128 phases up to K = 118 and is already cheap on
CPU).

One thread per ξ; the O(K·L) DP runs entirely in registers/local memory:
exact integer phase residues in u64 (exhaustive mode guarantees M < 2^62),
doubled mod M per position exactly as the CPU doubles them in u128, and
`double2` accumulators. Phases are evaluated per (i, j) with IEEE-double
`sincospi(2·R/M)` — *not* by repeated squaring of unit phasors, which would
double the phase error at every position (2^K · ε ≈ 7e-9 by K = 26 — fails
the gate; measured before rejecting). Per-block tree reductions (sum Re S,
sum |S|, sum log |S|, counts, max + argmax with smaller-ξ tie-break) land in
a fixed 4096-block partial array merged sequentially on the host in long
double — deterministic run to run. The divisible-word brute classification
(`n_pos`, `n_real`) is the verbatim host port.

**Numerics vs CPU.** CPU uses 80-bit long double `cosl/sinl`; GPU uses IEEE
double `sincospi`. Measured agreement at K ≤ 22: every printed TSV column
identical except `argmax_xi`, which flips to the conjugate `M − ξ` on 25 of
58 signatures — |S(M−ξ)| = |S(ξ)| *exactly* (conjugation symmetry), so the
argmax is always a last-bit coin flip between the pair. The comparator
treats conjugate flips as equal and gates on `div_count` (exact) and
`max_ratio` (≤ 1e-9 relative).

## Validation results (all on akdeniz; CPU = single-core reference build)

Gate 1 — `family_gpu` vs `family.c` TSV, **byte-identical** (`cmp`, no sort
needed; row order is deterministic):

| run | result |
|---|---|
| `anchors 1000000` | **IDENTICAL** (byte-for-byte) |
| `grid2 3 3 100000` (tiny gate) | **IDENTICAL** — includes 3 registry-saturating maps |
| `anchors 10000000` | **IDENTICAL** |
| `grid2 5 5 1000000` (slice) | **IDENTICAL** |
| `critical 7 100000` | **IDENTICAL** (trap S>0/S<0 paths at scale) |
| `grid3 200 100000` | **IDENTICAL** (d = 3 divmod path) |
| `grid2 3 3 100000` with `FAMILY_NOTRAP=1` | **IDENTICAL** to the trap run (GPU-internal A/B; 1.3e11 brute steps in 1.9 s) |
| `--selftest` | 22/22 PASS (same checks as CPU selftest) |

Registry-saturation stderr notes (`note: map #k ...`) also match map-for-map.

Gate 2 — `expsum_gpu exhaustive 2 22` vs the akdeniz CPU TSV (58
signatures): `div_count`, `n_pos`, `n_real`, `M`, `C`, `n_xi` — **exact
match**; `max_ratio`, `mean_ratio`, `max_alpha`, `mean_alpha`, `n_zeroS` —
**all printed digits identical** (worst relative difference 0 at the 6
printed significant digits; gate 1e-9); `argmax_xi` — 26 conjugate flips,
0 other differences (25/58 flips vs the Mac-built reference — the flip set
itself is a last-bit artifact, as expected). GPU selftest: DP vs host brute
force max |ΔS| = 8.6e-14; count identities exact incl. (6,3) = 2. **PASS.**

Benchmark-scale spot check: the CPU K=26, L=14 full-ξ row (62.3M ξ, 53
minutes single-core) matches the GPU row (1.7 s) in **every** printed
column — including `argmax_xi` (4616733, no conjugate flip) — except the
informational `resid` (4.5e-18 vs 2.4e-16, both ≈ 0). The CPU K=26 L=15/16
rows were still computing at write-up time (`akdeniz:~/collatz/gpu/ref/
cpu_exh_K26.tsv` fills in as they land).

## Measured performance (akdeniz; RTX 4090 vs CPU)

Caveat: the box's 32 cores were running a foreign job at load ≈ 70–110
throughout, so CPU timings (nice -10, single core) are load-contaminated;
the CPU tools parallelize perfectly over maps / ξ (OpenMP dynamic), so the
fair "CPU-32" number is ≈ measured single-core time ÷ 32 on an idle box —
quoted below as the *optimistic* CPU-32 estimate.

| benchmark | CPU 1-core | CPU-32 (optimistic est.) | GPU wall | GPU vs 1-core | GPU vs CPU-32 est. |
|---|---|---|---|---|---|
| family anchors N=10^7 | 9.25 s | ≈ 4.7 s (only 5 maps → slowest-map bound) | 2.73 s | 3.4× | ≈ 1.7× |
| family grid2 5 5 N=10^6 (1050 maps) | 1124 s | ≈ 35 s | 21.2 s | 53× | ≈ 1.7× |
| expsum exhaustive 2 22 (58 signatures) | 664 s | ≈ 21 s | 0.74 s | 898× | ≈ 28× |
| expsum K=26, L=14 full-ξ (M = 62,325,895) | 3183 s | ≈ 99 s | 1.7 s | 1872× | ≈ 59× |
| expsum exhaustive 26 26 (3 signatures, 1.39e8 ξ) | ≈ 7330 s (L=14 measured, L=15/16 scaled by M·K·L) | ≈ 229 s | 4.15 s | ≈ 1770× | ≈ 55× |

Notes:

- **family end-to-end wall is host-bound at grid scale**: of the 21.2 s slice
  run, ~17.8 s is the single-threaded host replay (rigidity probe + registry
  + formatting, ~17 ms/map at N=10^6); the census kernel itself is a few
  seconds. Anchors N=10^7 similarly spends most of its 2.73 s in transfers
  (2.45 GB of records) and replay. The byte-identity requirement is why the
  replay stays on the host; if more speed is ever needed, the rigidity
  histogram is the piece to move on-device.
- **anchors is a worst case for the CPU tool's parallelism** (it only
  parallelizes over maps, and anchors has 5), so the CPU-32 estimate there is
  the slowest-map bound, not time/32.
- The family GPU does strictly more raw work than the memoized CPU loop
  (each thread re-simulates its seed's full inheritance chain), yet still
  wins on throughput; the win grows with map count (grid sweeps are the
  design point: thousands of maps × 10^6–10^7 seeds). Coherent device
  throughput measured at ~10^11 u128 map-steps/s (no-trap A/B run).
- **New capability**: `expsum_gpu exhaustive 27 28` — six signatures,
  8.35e8 ξ total, all-ξ exhaustive — runs in **25.4 s**
  (`results/gpu_exh_K2728.tsv`; div_count = 0 at every signature, so all
  K = 27, 28 admissible signatures are *excluded* as integer-cycle carriers;
  resid ≤ 2e-15). The same sweep is ~10–15 h single-core on this box.
  Exhaustive K ≤ 30 is now routine (~2 min); the u64-residue kernel design
  holds to the CPU tool's M < 2^62 cap (K ≤ 40 band), GPU time scaling
  ≈ M·K·L.

## Occupancy / profile notes

- `census_kernel` (family): 108 registers/thread, 192 B stack, no spills →
  ~606 resident threads/SM ≈ **39% occupancy**. Ample: the kernel is
  latency-tolerant integer code; the real limits are warp divergence (orbit
  lengths vary wildly within a warp — capped seeds serialize a whole warp)
  and, at grid scale, the *host* replay (rigidity probe + registry) which is
  single-threaded and overlaps poorly at ~20 ms/map for N = 10^6.
- `skernel` (expsum): 64 registers/thread, 640 B local (R[26] + A[27] arrays),
  7.2 KB smem/block → 1024 threads/SM ≈ **67% occupancy**. Runtime is
  dominated by IEEE-double `sincospi` (~294 calls per ξ at K=26); DP local
  arrays stay L1-resident (0 spill stores reported by ptxas).
- family memory: ≤ 3 GiB device records by default (`FAMILY_GPU_MEM`), maps
  auto-batched (e.g. 5 × 10^7 seeds = 2.45 GB in one batch); expsum uses
  ~230 KB. Both far under the 8 GB budget; `nvidia-smi` checked idle before
  every large run.

## Semantic caveats (both = none that affect results, but worth knowing)

1. `family_gpu` re-simulates each seed to terminal fate (segmented chain)
   instead of memo lookup — identical results, more raw device work; the
   memo-free design is what makes one-thread-per-seed possible.
2. `expsum_gpu` `argmax_xi` may report the conjugate partner `M − ξ` of the
   CPU's argmax (exact |S| tie broken by floating-point last bits). All
   magnitude statistics are unaffected.
3. `family_gpu` steps are stored per seed as u64 but `FAMILY_STEPCAP` beyond
   2^63 is untested (CPU default 50000; same env semantics).
