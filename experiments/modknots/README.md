# modknots — Collatz cycles as modular knots (Ghys dictionary)

Maps a parity necklace of shape `(K,L)` to a conjugacy class in `PSL(2,Z)`
(closed modular geodesic / Lorenz knot) and computes the Rademacher function,
Dedekind sum, trace/length, and the Böhm–Sontacchi weight `W`/defect `δ`.
Question: does any modular-knot invariant constrain cycle existence beyond the
archimedean Baker bound (which uses only `K,L`)? Verdict: **no — it collapses to
`(K,L)`**. See `docs/notes/modular-knots.md`.

- `modknots.py` — core library. `M(a)=∏ R^{a_i}L`, Rademacher via Dedekind-sum
  formula (fast O(log) Euclidean Dedekind sum), `W`, `δ`, trace, hyperbolic length.
- `verify.py` — proves `Φ(M(v)) = K−L` on all 4083 words `K≤11` (0 mismatches);
  reproduces the 5 known cycles.
- `build_tables.py` → `known_cycles.csv`, `candidates.csv` (CF-convergent /
  near-convergent band, `L≤18`; `N_δ0` = #integer-cycle words via exact DP).
- `separation.py` → `separation.csv` — within each `(K,L)` fiber, does any
  invariant separate the `δ=0` (cycle) words? Purity certificate.
- `witness.py` — the isotopy/length-descent test: exhibits two distinct
  geodesics of **equal trace** (equal length) with different `δ` — one a cycle,
  its time-reversal not. So `δ` does not factor through knot length.

Run: `python3 verify.py && python3 build_tables.py && python3 separation.py && python3 witness.py`
