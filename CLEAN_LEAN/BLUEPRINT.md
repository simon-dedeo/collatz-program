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
| Accelerated/Syracuse equivalence | Planned |
| Abstract finite KL operator | In progress |
| KL feasibility certificate checker | Planned |
| KL difference-inequality transfer theorem | Planned |
| Oscillation identity and weighted-tail reduction | Planned |
| Restricted-pressure theorem C1' | Open mathematics |
| Collatz conjecture | Open mathematics |

The predecessor-counting conclusions of the KL method are milestones, not a
proof of `Collatz.Conjecture`; the dependency graph will preserve that
distinction explicitly.

