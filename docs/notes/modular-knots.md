# Modular knots / Rademacher view of Collatz cycles — PARTIAL (lane killed mid-flight)

**Status: incomplete.** This lane was stopped mid-computation (2026-07-20) before
its agent wrote a final verdict. This note records the partial findings from the
data it did produce (`experiments/modknots/`: `separation.csv`, `candidates.csv`,
`fricke.csv`, `known_cycles.csv` + scripts), so nothing is lost. A successor can
resume from here.

## The setup (as built)

A cycle of shape (K halvings, L odd steps) ↔ a hyperbolic conjugacy class in
PSL(2,ℤ) (via the continued fraction of L/K ≈ 1/log₂3), hence a closed modular
geodesic / Lorenz knot (Ghys). Computed invariants per shape: the Rademacher/
Dedekind function Φ, a trace-coordinate ("trace_gap"), and a quadratic linking
pairing ("quad_gap", after C.-L. Simon). `Λ = 2^K − 3^L`.

## What the partial data shows

1. **The linear (Rademacher) invariant collapses to Baker — as CRACKS #12
   predicted.** For the actual known cycles (unit stratum |Λ|=1 and the CF
   convergents), the data has **Φ = K − L exactly** (`Phi_eq_KminusL` column) and
   all mixed/Dedekind/trace gaps = 0. Φ is linear in the CF digits — precisely the
   data Baker's linear-forms method already exploits. So the standard modular-knot
   invariant carries no information orthogonal to Baker. This is the expected
   (negative) outcome and it is now checked, not just conjectured.

2. **The QUADRATIC linking invariant shows nonzero separation on candidates —
   UNRESOLVED.** For non-cycle candidate shapes the `quad_gap` is nonzero and
   sometimes large ((6,4)/Λ=−17: 1.49; (9,6): 2.06; (12,8): 2.71; (11,7)/Λ=−139:
   0.57), while the known cycles sit at 0. This is the one place the lane was
   *not* obviously collapsing to Baker — the C.-L. Simon quadratic linking pairing
   is genuinely quadratic in the CF data, which Baker's linear forms do not see.
   **Whether this yields any cycle exclusion orthogonal to Baker was not
   determined** — the agent was mid-way through the Fricke/character-variety
   computation (`fricke.py`) when the lane was stopped.

## Honest verdict (partial)

Leaning negative for the *linear* invariant (collapses to Baker, confirmed). The
*quadratic* linking invariant is the only live residue and is **inconclusive** —
it separates cycles from non-cycles numerically on the small dataset, but no
argument was reached that this excludes anything the archimedean bound doesn't.
Priority for a successor: low-to-medium (finish the quadratic analysis, or file
the linear collapse as another confirmed CRACKS #12 negative).
