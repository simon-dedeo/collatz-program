# experiments/cycles — finite-place structure of Collatz cycles

Supports `docs/notes/cycle-finite-places.md`. Question: do the sporadic primes
`p | Λ = 2^K − 3^L` (unused by the Steiner→Hercher archimedean literature)
exclude cycles that Baker cannot? A length-`(K,L)` cycle needs `Λ | W(v)` for
some parity word `v` (weight `L`, `W` = Böhm–Sontacchi weight). Define
`N_m(K,L) = #{words shape (K,L) : W(v) ≡ 0 mod m}`; a **finite-place obstruction**
is a prime power `p^e ‖ Λ` with `N_{p^e} = 0`.

**Verdict: no exclusion both orthogonal to Baker AND feasible.** Obstructions are
real and computable (e.g. `(21,13)`, `Λ=502829` prime, `N_Λ=0`), heuristically
available at ~10% of near-convergents, but need a giant prime factor of a ~2^K-bit
`Λ` (infeasible where new) and are redundant where feasible (`n<2^71`, Barina).
The m=1 stratum collapses to the archimedean lower bound explicitly.

## Files
| file | what |
|---|---|
| `local_count.py` | mod-`m` transfer-matrix DP for `N_m(K,L)` (exact big-int + fast mod-`Q`). `python3 local_count.py` self-tests: `N_139(11,7)=11`, equidistribution, the `(21,13)` obstruction. |
| `local_density.py` | exact `N_p·p/C` at small prime factors `p\|Λ`, near-convergents. → `local_density.csv` |
| `factor_lambda.py` | `pplus` (full factorization, `P⁺(Λ)` vs `C`, availability) and `feas` (trial + isprime, convergents, feasibility wall). → `lambda_pplus.csv`, `lambda_feas.csv` |
| `lifting_test.py` | `N_p → N_{p^e}` lifting at `p^e ‖ Λ`, `e≥2` (valuation loophole). → `lifting_test.csv` |
| `m1_steiner.py` | m=1 reduction `Λ\|W ⟺ Λ\|(2^{K−L}−1)` and the collapse to `2^{K−L}<Λ`. → `m1_steiner.csv` |

## Reproduce
```
python3 local_count.py
python3 local_density.py 20 160
python3 factor_lambda.py pplus 20 100 && python3 factor_lambda.py feas 20 300
python3 lifting_test.py
python3 m1_steiner.py
```
Reuses the exponential-sum framing of `experiments/expsum/` (there over the full
`Λ`; here `N_m` is the mod-`m` restriction, `N_m = (1/m) Σ_ξ S_m(ξ)`).
