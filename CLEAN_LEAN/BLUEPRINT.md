# Formalization blueprint

## Final target

`CleanLean.Collatz.Conjecture` is the standard assertion that every positive
natural number eventually reaches `1` under the unaccelerated Collatz map.
It is deliberately defined before any proposed proof machinery.

## Status ledger

| Item | Status |
|---|---|
| Standard functional specification | Kernel checked |
| Relational specification | Kernel checked |
| Equivalence of those specifications | Kernel checked |
| Accelerated/Syracuse equivalence | Kernel checked |
| Abstract finite KL operator | Kernel checked |
| Exact min-to-fiber-average `/3` domination | Kernel checked |
| Concrete KL residue coordinates and affine transport | Kernel checked |
| Affine transport agrees with multiplication by four mod `3^k` | Kernel checked |
| Concrete branch/refinement arithmetic | Kernel checked |
| Retarded/advanced target quotient formulas | Kernel checked |
| Concrete three-lift fiber injectivity | Kernel checked |
| Concrete top/low-digit fiber equivalences and branch counts | Kernel checked |
| Abstract exact-rational KL feasibility checker and soundness | Kernel checked |
| Streaming checker for the large GPU certificate format | Planned |
| Integer-scaled GPU row format and rational soundness | Kernel checked |
| Integer proof `2^P < 3^Q` implies `P/Q < log₂ 3` | Kernel checked |
| Integer proof `3^Q < 2^P` implies `log₂ 3 < P/Q` | Kernel checked |
| Integer branch-weight lower-bound checker | Kernel checked |
| Integer branch-weight checks imply true `Real.rpow` bounds | Kernel checked |
| Scaled integer certificate implies feasibility for true KL weights | Kernel checked |
| Lean-native level-2 end-to-end certificate at `lambda=4/3` | Kernel checked |
| SHA-256/NPY streaming front end | Planned |
| KL difference-inequality transfer theorem | Planned |
| Finite weighted-tail inequality in R' | Kernel checked |
| Full abstract asymptotic R' | Kernel checked |
| Geometric pressure-gap implies tail decay | Kernel checked |
| Geometric weighted tails imply vanishing KL defect | Kernel checked |
| Transport-free local family is neutrally two-periodic | Kernel checked |
| Exact advanced-fiber minimum law | Kernel checked |
| Pure-branch root self-loop correction | Kernel checked |
| Branch-mixer range inequality and C3 counterexample | Kernel checked |
| Exact finite-cycle transport resolvent | Kernel checked |
| Generic finite restricted-pressure certificate | Kernel checked |
| Exact rational pressure-row and Chernoff-gap checkers | Kernel checked |
| Terminal-potential and block-Chernoff pressure bound | Kernel checked |
| Corrected relative charged-carrier implication | Kernel checked |
| Aligned marginal-mode obstruction to strict CL contraction | Kernel checked |
| Retarded `2 -> 2` self-lift at every residue precision | Kernel checked |
| Concrete KL oscillation identity | Kernel checked |
| Concrete annealed root: strict decrease and `s(2)=1` | Kernel checked |
| Vanishing defect implies `lambda_k -> 2` | Kernel checked |
| `lambda_k -> 2` implies `X^(1-epsilon)` counting, conditional on KL transfer | Kernel checked |
| Exact feasible sequence tending to `2` implies the same counting conclusion | Kernel checked |
| Feasible lower sequence tending to `2` squeezes exact critical suprema to `2` | Kernel checked |
| Exact Syracuse predecessor-count specification | Kernel checked |
| Critical nonlinear eigenfunction existence/selection | Planned; unnecessary for direct-feasibility route |
| Portable pressure JSON independently verified | External exact check; Lean ingestion planned |
| Restricted-pressure theorem C1' | Open mathematics |
| Original charged spine-face Lyapunov route | Falsified at its algebraic marginal mode |
| Collatz conjecture | Open mathematics |

The predecessor-counting conclusions of the KL method are milestones, not a
proof of `Collatz.Conjecture`; the dependency graph will preserve that
distinction explicitly.
