# Exact terminal defect statistics for the selected KL records

**Status (2026-07-21): exact finite audit for the selected feasible
certificates `k=12,...,19`.  These inequalities are regression targets and
evidence for the live terminal route, not an all-level rate or
anti-concentration theorem.**

Run the streamed audit with

```bash
python3 experiments/kl/verify_terminal_defect_statistics.py
```

The tracked output is
`experiments/kl/analysis_cache/terminal_defect_statistics_exact.csv`.  The
script verifies each certificate vector and its weight/parameter manifest
against pinned SHA-256 digests, streams the sidecar-backed levels, certifies its division bounds with exact
`uint64`-limb products, validates the provenance and quotient convention of
the existing exact Pearson cache, and independently reconstructs the complete
`k=12` Pearson interval with Python big integers.  On the current machine the
full eight-level run takes about 34 seconds with an active memory footprint of
about 312 MB.  The operating system also accounts for the memory-mapped 2.9 GB
`k=19` sidecar.

## 1. Exact quantities

For the three children of a terminal parent `r`, write

```text
P_r = x_(r,0)+x_(r,1)+x_(r,2),
m_r = min_i x_(r,i),
d_r = P_r-3m_r,
T   = sum_r P_r.
```

Under parent-mass weighting, put

```text
u_r = 1/3-min_i(x_(r,i)/P_r) = d_r/(3P_r).
```

Then

```text
delta = E[u] = (sum_r d_r)/(3T),
E[u^2]       = (1/(9T)) sum_r d_r^2/P_r.
```

The first quantity is an exact rational.  For the second, the checker computes
the exact quotient and remainder

```text
d_r^2 = q_r P_r+s_r,   0<=s_r<P_r,
```

and hence the rigorous interval

```text
sum q_r/(9T) <= E[u^2]
                < (sum q_r + #{r:s_r!=0})/(9T).
```

The interval widths are below `4.8e-15` on all eight records.  The terminal
Pearson quantity is independently enclosed by the analogous exact
quotient/remainder calculation in `verify_chi_square_envelope.py`.

It is useful to expose what the normalized ratio

```text
K = E[u^2]/delta^2
```

measures.  Normalize the parent masses by `mu_r=P_r/T`, set
`epsilon=3delta`, and, when `epsilon>0`, define

```text
theta = 1-epsilon,
q_r = m_r/sum_s m_s,
v_r = d_r/(epsilon T).
```

Direct substitution gives

```text
mu = theta q+epsilon v,
u_r = epsilon v_r/(3mu_r),
K = sum_r v_r^2/mu_r = 1+chi^2(v || mu).             (1.1)
```

Thus the missing level-uniform bound on `K` is exactly an
anti-concentration statement for the normalized excess profile `v` relative
to the parent profile `mu`; it is not merely a small-mean statement. For an
exact selected critical tower, the general renewal identity also gives

```text
chi^2(q || mu) = (epsilon^2/theta^2)(K-1).           (1.2)
```

Consequently, bounded `K` is exactly an `O(epsilon^2)` chi-square closeness
theorem for the normalized minimum profile and its renewed image. The generic
Radon--Nikodym martingale bound is only `chi^2(q||mu)<=epsilon/theta`, one
power too weak. Equation (1.2) is an audited all-level research identity, not
a consequence of this finite checker; see
`docs/notes/annealed-critical-coding.md §5.1`.

## 2. Certified finite table

The displayed decimals render rigorous rational intervals from the CSV.
`Sigma` is the true aggregate normalized KL slack, enclosed as described in
the next section.

| `k` | `lambda` | `k(2-lambda)` | `delta` | `k delta` | `E[u^2]` | `K` | terminal `chi` | `k^2 chi` | `10^7 Sigma` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 12 | 1.8064231 | 2.3229 | .0174594 | .209512 | 4.15821e-4 | 1.36411 | .00333966 | .480911 | [1.84793, 1.84956] |
| 13 | 1.8188232 | 2.3553 | .0160611 | .208794 | 3.56214e-4 | 1.38090 | .00285460 | .482428 | [2.01633, 2.01798] |
| 14 | 1.8307718 | 2.3692 | .0147548 | .206568 | 3.05067e-4 | 1.40129 | .00245346 | .480878 | [1.82198, 1.82366] |
| 15 | 1.8419679 | 2.3705 | .0135664 | .203496 | 2.62700e-4 | 1.42735 | .00210668 | .474003 | [1.76250, 1.76420] |
| 16 | 1.8522343 | 2.3643 | .0125062 | .200099 | 2.27309e-4 | 1.45334 | .00181405 | .464396 | [1.57018, 1.57191] |
| 17 | 1.8616883 | 2.3513 | .0115542 | .196422 | 1.97356e-4 | 1.47832 | .00157708 | .455775 | [1.38553, 1.38728] |
| 18 | 1.8703245 | 2.3342 | .0107046 | .192682 | 1.72358e-4 | 1.50416 | .00137410 | .445209 | [1.35587, 1.35764] |
| 19 | 1.8783127 | 2.3121 | .00993528 | .188770 | 1.51244e-4 | 1.53221 | .00119726 | .432213 | [1.35750, 1.35929] |

The checker proves the following three exact rational comparisons on every
row:

```text
delta_k < 0.21/k,
E[u^2] < 1.533 delta_k^2,
chi_terminal < 0.483/k^2.                            (2.1)
```

The constants in (2.1) were chosen after seeing these eight records.  They are
compact finite falsifiers, not confidence intervals or out-of-sample bounds.
The strongest warning is visible in the table: `K` rises monotonically from
`1.36411` to `1.53221`.  The data are compatible with a uniform constant, but
they are also compatible with slow divergence.  Conversely, `k delta` falls
from `.209512` to `.188770`, and `k^2 chi` falls after its `k=13` maximum.
This is genuine support for the paired `1/k`, `1/k^2` terminal ansatz, but it
does not decide it.

## 3. True-slack enclosure

For each certificate,

```text
Sigma = lambda^-2-1+(w_2+w_8) (sum_r m_r)/T,
w_2=lambda^(alpha-2),
w_8=lambda^(alpha-1),
alpha=log_2(3).
```

The stored rational certificate weights are rigorous lower bounds for the two
irrational weights.  For the upper endpoint, the checker proves by an exact
integer power comparison that

```text
alpha < 125743/79335,
2^125743 > 3^79335,
```

then finds the least upper weights on the certificate's `10^-15` grid and
checks them by exact integer powers.  The resulting `Sigma` intervals have
width below `1.8e-10`.

The true slack is only about five to six parts in a million of the main
`(w_2+w_8)delta` defect term.  This rules out the simple numerical concern that
the observed defect scaling is manufactured by a large feasibility slack.
It does not establish an all-level near-critical family: `Sigma` is not
monotone in this window, the certificates are selected finite feasible
subeigenvectors rather than a coherent projective family, and the largest
sidecars are not tracked by git.

## 4. What this changes, and what it does not

The audit puts both missing terminal hypotheses on one reproducible finite
dashboard.  It supports the candidate program

```text
delta_k = O(1/k),
sup_k E[u^2]/delta_k^2 < infinity,
```

which, through the sharp ternary inequality

```text
(9/2)u^2 <= chi <= 18u^2 <= 6u,
```

would give terminal `chi=O(1/k^2)` for a suitable selected all-level family.
For exact critical vectors, `delta_k->0` then forces `lambda_k->2`; selected
feasible vectors additionally require `Sigma_k->0`.

No part of this finite audit proves either all-level hypothesis.  In
particular, the rising `K` values must remain visible in future summaries, and
the fitted constants in (2.1) must not be promoted to an annealed asymptotic
or a theorem about the full feasible cone. The live structural alternative
remains a dimension-free regularity estimate or a quantitative, level-uniform
strengthening of the proved qualitative strict lift for the nonlinear
renewal-min system in `annealed-critical-coding.md`.
