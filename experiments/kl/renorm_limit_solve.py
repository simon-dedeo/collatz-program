"""Closed-form solution of the local renormalization at -1, exact checks,
and the numerical verification table (renorm_limit_table.csv).

Closed form (Theorem 1 of docs/notes/renormalization-at-minus-one.md):
  min-lift of the fiber of -1, normalized by c(-1):
      a_k = lam^(1-alpha) - lam^(-1-alpha) * c(-4)/c(-1)      (EXACT identity)
      a_infty = lam^(1-alpha)   (= 2/3 exactly at lam = 2, since 2^alpha = 3)
Pinned profile (empirical pinning c(-1) = fiber mean): (1, a, 2-a) up to the
doubling swap; sup-osc -> 2(1-a); per-shell mass ratio toward -1: lam^(alpha-1)/3
(= 1/2 exactly at lam = 2).
"""
import csv, math, os
import sympy as sp
import numpy as np
from renorm_common import ALPHA, HERE, load_C, lam_of, c_at

# ---- exact algebra (sympy) ----
lam_s, al = sp.symbols('lam'), sp.log(3, 2)
a_form = lam_s ** (1 - al)
print("a*(lam) = lam^(1-alpha);  a*(2) =", sp.nsimplify(sp.simplify(a_form.subs(lam_s, 2))),
      " (exact, via 2^alpha = 3)")
print("sup-osc limit at lam=2: 2(1-a*) =", sp.simplify(2 - 2 * a_form.subs(lam_s, 2)))
print("mass ratio/shell at lam=2: lam^(alpha-1)/3 =",
      sp.simplify((2 ** (al - 1) / 3)))
s = lam_s ** -2 + (lam_s ** (al - 2) + lam_s ** (al - 1)) / 3
print("annealed s(2) =", sp.simplify(s.subs(lam_s, 2)), "(sanity)")

rows = []
prev_spike = None
for k in [15, 16, 17, 18, 19]:
    C = load_C(k)
    lam, _ = lam_of(k)
    M1 = 3 ** (k - 1)
    c1 = c_at(C, k, -1)
    c4 = c_at(C, k, -4)
    fib = [c_at(C, k, -1 + j * M1) for j in range(3)]   # j=0 is -1
    mean = sum(fib) / 3
    a_meas = min(fib) / c1
    b_meas = max(fib) / c1
    a_star = lam ** (1 - ALPHA)
    a_pred = a_star - lam ** (-1 - ALPHA) * c4 / c1      # exact identity
    spike = c1 / c4
    row = dict(k=k, lam=round(lam, 7),
               a_star=round(a_star, 6),
               a_pred_exact=round(a_pred, 6),
               a_meas_min_over_c1=round(a_meas, 6),
               a_meas_mean_norm=round(min(fib) / mean, 6),
               pinning_c1_over_mean=round(c1 / mean, 6),
               b_meas=round(b_meas, 6),
               two_minus_a=round(2 - a_meas, 6),
               suposc_meas=round((max(fib) - min(fib)) / mean, 6),
               suposc_pred=round(2 * (1 - a_star), 6),
               spike=round(spike, 1),
               spike_growth=round(spike / prev_spike, 4) if prev_spike else "",
               lam_pow_al_minus_1=round(lam ** (ALPHA - 1), 4),
               transport_frac=f"{lam**-2 * c4 / c1:.3e}")
    rows.append(row)
    prev_spike = spike

with open(os.path.join(HERE, "renorm_limit_table.csv"), "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

for r in rows:
    print(r)

# ---- mass law check from renorm_annuli.csv ----
try:
    A = [r for r in csv.DictReader(open(os.path.join(HERE, "renorm_annuli.csv")))
         if r["center"] == "minus1"]
    print("\nper-shell mass ratio toward -1 (pred lam^(alpha-1)/3):")
    for k in ["15", "16", "17", "18", "19"]:
        ms = {int(r["j"]): float(r["mass_frac"]) for r in A if r["k"] == k}
        rats = [ms[j + 1] / ms[j] for j in sorted(ms) if j + 1 in ms and ms[j] > 0]
        lam, _ = lam_of(int(k))
        print(f" k={k}: pred={lam**(ALPHA-1)/3:.4f} measured j=1..8:",
              " ".join(f"{x:.3f}" for x in rats[:8]))
except FileNotFoundError:
    print("renorm_annuli.csv not present; skip mass check")

# ---- local dimension from renorm_window.csv ----
try:
    W = list(csv.DictReader(open(os.path.join(HERE, "renorm_window.csv"))))
    print("\nlocal count multiplier for osc>0.2 (shells j=4..9) and log3:")
    for k in ["15", "16", "17", "18"]:
        ns = {int(r["j"]): int(r["n_gt_0.2"]) for r in W if r["k"] == k}
        mult = (ns[9] / ns[4]) ** (1 / 5)
        print(f" k={k}: mult={mult:.3f}  log3={math.log(mult,3):.3f}  (global d*~0.726)")
except FileNotFoundError:
    print("renorm_window.csv not present; skip")
