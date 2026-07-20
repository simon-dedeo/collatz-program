# COLLATZ

**Headline result (2026-07-20): π_a(x) ≥ x^0.9032 — the number of integers
below x whose Collatz orbit reaches any fixed a ≢ 0 (mod 3) — improving the
2003 Krasikov–Lagarias record x^0.84.** Exact-arithmetic certified at levels
k = 12..18 (`experiments/kl/RESULT.md`); k ≤ 14 chain adversarially reviewed;
γ₁₉ = 0.9094 in certification; the level-k systems are finite sections of an
adversarial transfer operator on ℤ₃ whose limit invariant the data currently
place near 1 (see `docs/notes/kl-limit-object.md`).

A research program on the Collatz (3x+1) conjecture: experiments, proof-strategy
analysis, and Lean 4 formalization. Goal: genuine progress in either direction,
with every claim backed by a machine-checkable artifact (a Lean proof or a
finitely-verifiable certificate).

## Layout

- `formal/` — Lean 4 + mathlib project. `Formal/Collatz.lean` has the conjecture
  statement and first sorry-free lemmas (descent reduction, verified ranges via
  `native_decide`, only-trivial-cycle-through-verified-numbers). Build:
  `cd formal && lake exe cache get && lake build`.
- `experiments/` — code for experiments.
  - `fate.c` — orbit-fate census for maps (x/2, Ax+B): classifies every n ≤ N as
    reaching a cycle (Brent detection, cycles auto-discovered and logged),
    overflowing 2^120 (presumed divergent), or hitting a step cap. Any new cycle
    or any non-c1 fate for 3x+1 would be disproof-grade and lands in
    `results/discoveries_*.log`.
  - `dfacert/` — BB-decider-inspired exhaustive search for a "regular divergence
    certificate": a DFA-recognizable set L ∌ 1, nonempty, with T(L) ⊆ L. Finding
    one disproves Collatz; exhausting size k proves "no k-state certificate".
- `results/` — TSVs and logs from experiment runs (synced from remotes).
- `docs/` — strategy memo and literature landscape.
- `papers/` — downloaded references.

## Remote machines

- `akdeniz.lan.cmu.edu` — 32 cores, 124 GB (fast). Experiments live in `~/collatz/`,
  long runs in tmux session `census`.
- `ganesha.lan.cmu.edu` — 32 cores, 62 GB (slow Opterons). For embarrassingly
  parallel sweeps.

## Empirical sandwich (census to 10^10, akdeniz)

| map  | fate |
|------|------|
| 3x−1 (below) | 0% divergence; 3 cycles (mins 1, 5, 17), basins ≈ 32.7/32.5/34.8% |
| 3x+1 | 100.000000% reach 1 (re-verified to 10^10 here; literature: 2^71, Barina 2025) |
| 5x+1 (above) | 99.94% presumed divergent; 3 known cycles (mins 1, 13, 17) |

The drift heuristic (odd step multiplies by A/4 on average) puts 3x+1 strictly
inside the subcritical region. The open gap is worst-case vs almost-all — hence
the certificate/automata experiments, which are worst-case-shaped.

## First certificate result (2026-07-20)

**No regular divergence certificate with ≤ 7 DFA states exists** (LSB-first
binary encoding): exhaustive, verified search over 83,968 (q≤4) + 5.1M (q=5) +
379.6M (q=6) + 32.79B (q=7) canonical DFAs; q=5,6 independently reproduced on
a second machine; q=8 running. **Base-3 (MSD-first): none with ≤ 5 states**
(34M at q≤4 + 29.28B at q=5) — a provably independent channel (see
`docs/notes/two-bases.md`: a certificate in both bases would itself be a
nontrivial-cycle witness). The infinite-semilinear case was already dead
(Monks 2006); the 2-automatic case is open in the literature. See
`docs/STRATEGY.md` §3.3 and `experiments/dfacert/README.md`.
