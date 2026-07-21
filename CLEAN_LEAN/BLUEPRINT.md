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
| Abstract finite KL operator | In progress |
| Exact min-to-fiber-average `/3` domination | Kernel checked |
| Concrete KL residue coordinates and affine transport | Kernel checked |
| Affine transport agrees with multiplication by four mod `3^k` | Kernel checked |
| Concrete branch/refinement arithmetic | In progress |
| Retarded/advanced target quotient formulas | Kernel checked |
| Concrete three-lift fiber injectivity | Kernel checked |
| Abstract exact-rational KL feasibility checker and soundness | Kernel checked |
| Streaming checker for the large GPU certificate format | Planned |
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
| Concrete KL oscillation identity | Planned |
| Restricted-pressure theorem C1' | Open mathematics |
| Collatz conjecture | Open mathematics |

The predecessor-counting conclusions of the KL method are milestones, not a
proof of `Collatz.Conjecture`; the dependency graph will preserve that
distinction explicitly.
