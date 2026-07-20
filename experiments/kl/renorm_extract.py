"""Extract the local structure of the certified KL eigenvectors around -1.

Outputs (CSV, in experiments/kl/):
  renorm_profiles.csv   depth-nu ball profiles c(-1+u*3^(k-nu))/c(-1), nu<=4
  renorm_argmins.csv    eigen-equation decomposition + argmin for spine states
  renorm_growth.csv     annulus growth factors and transport fractions per depth
Prints a compact summary (checks against fiber-geometry.md M6).
"""
import csv, math, os, sys
import numpy as np
from renorm_common import (ALPHA, HERE, load_C, lam_of, state, cval, c_at,
                           eig_terms)

KS = [int(x) for x in sys.argv[1:]] or [15, 16, 17, 18, 19]

prof_rows, argmin_rows, growth_rows = [], [], []

for k in KS:
    C = load_C(k)
    lam, _ = lam_of(k)
    w8 = lam ** (ALPHA - 1)
    c1 = cval(C, k, 0, 1)                     # c(-1)
    c4 = c_at(C, k, -4)
    fib = [cval(C, k, j, 1) for j in range(3)]  # offsets j*3^(k-1), j=0 is -1
    mean = sum(fib) / 3
    print(f"k={k} lam={lam:.7f}  spike c(-1)/c(-4)={c1/c4:.1f}  "
          f"fiber/mean=({fib[0]/mean:.4f},{fib[1]/mean:.4f},{fib[2]/mean:.4f})")

    # ball profiles, depths 1..4, normalized by c(-1)
    for nu in range(1, 5):
        for u in range(3 ** nu):
            prof_rows.append(dict(k=k, nu=nu, u=u,
                                  val=cval(C, k, u, nu) / c1))

    # eigen-equation decomposition for all states in ball of depth <= 4
    for nu in range(1, 5):
        for u in range(3 ** nu):
            if nu > 1 and u % 3 == 0:
                continue                       # already listed at depth nu-1
            m = state(k, u, nu)
            c_m, t, br, w, jmin = eig_terms(C, k, m, lam)
            # min is over lifts of R8(x) = -1 + 2u*3^(k-nu-1) mod 3^(k-1):
            # lift j has offset 2u + j*3^nu at depth nu+1
            argmin_rows.append(dict(
                k=k, nu=nu, u=u, c_over_c1=c_m / c1,
                transport_frac=t / c_m, branch_frac=br / c_m,
                slack=(t + br) / c_m - 1, argmin_lift=jmin,
                argmin_offset=(2 * u + (jmin or 0) * 3 ** nu) % 3 ** (nu + 1)))

    # annulus growth: max/mean over annulus A_nu = {u !≡ 0 mod 3} at depth nu
    prev_max = None
    for nu in range(1, 9):
        vals = [cval(C, k, u, nu) for u in range(3 ** nu) if u % 3 != 0]
        vmax, vmean = max(vals), sum(vals) / len(vals)
        # transport fraction along the annulus (worst/typical)
        growth_rows.append(dict(k=k, nu=nu, max_over_c1=vmax / c1,
                                mean_over_c1=vmean / c1,
                                ratio_to_prev=(vmax / prev_max) if prev_max else ""))
        prev_max = vmax

for name, rows in [("renorm_profiles.csv", prof_rows),
                   ("renorm_argmins.csv", argmin_rows),
                   ("renorm_growth.csv", growth_rows)]:
    with open(os.path.join(HERE, name), "w", newline="") as f:
        wtr = csv.DictWriter(f, fieldnames=list(rows[0]))
        wtr.writeheader(); wtr.writerows(rows)
    print("wrote", name, len(rows), "rows")
