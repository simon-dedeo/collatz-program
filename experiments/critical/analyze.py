#!/usr/bin/env python3
"""analyze.py -- fit the critical-drift scaling laws from the scan CSVs.

  (c) Mother-of-Giants:  is the excursion scale ~ exp(c/|drift|) or a power law?
      Fit ln(mean_h) and max_h against 1/|drift| (linear => exp(c/|drift|))
      and against ln(1/|drift|) (linear => power law).  Report both R^2.
  (a) scale invariance:  log-log slope of the tau / tc CCDF near criticality
      (fair-walk first passage => -1/2).
  (b) certificate rank:  max_h, wtau, f_cap vs drift (worst-case DFA levels).
Outputs: results/fit_value.csv, results/fit_powerlaw.csv (stdout summary too).
"""
import sys, os, csv, math

RES = sys.argv[1] if len(sys.argv) > 1 else "results"

def load(fn):
    p = os.path.join(RES, fn)
    if not os.path.exists(p):
        return []
    with open(p) as f:
        return list(csv.DictReader(f))

def linfit(xs, ys):
    n = len(xs)
    if n < 2:
        return (0.0, 0.0, 0.0)
    mx = sum(xs)/n; my = sum(ys)/n
    sxx = sum((x-mx)**2 for x in xs)
    sxy = sum((x-mx)*(y-my) for x, y in zip(xs, ys))
    if sxx == 0:
        return (0.0, my, 0.0)
    b = sxy/sxx; a = my - b*mx
    syy = sum((y-my)**2 for y in ys)
    ss_res = sum((y-(a+b*x))**2 for x, y in zip(xs, ys))
    r2 = 1 - ss_res/syy if syy > 0 else 0.0
    return (b, a, r2)

def value_fits():
    rows = load("summary_value.csv")
    out = []
    # group logwalk by D, subcritical side (drift<0, orbits drop): fixed variance
    byD = {}
    for r in rows:
        lbl = r["label"]
        if not lbl.startswith("LW_D"):
            continue
        D = int(lbl.split("_")[1][1:])
        byD.setdefault(D, []).append(r)
    print("=== (c) exp(c/|drift|) vs power law, per fixed-D logwalk (subcritical) ===")
    fit_rows = [("D","n_pts","exp_slope_c","exp_R2","pow_slope","pow_R2","verdict")]
    for D in sorted(byD):
        sub = [r for r in byD[D] if float(r["vdrift"]) < -1e-4
               and float(r["f_drop"]) > 0.5]
        if len(sub) < 3:
            continue
        inv = [1.0/abs(float(r["vdrift"])) for r in sub]
        lninv = [math.log(1.0/abs(float(r["vdrift"]))) for r in sub]
        mh = [float(r["mean_h"]) for r in sub]
        be, ae, r2e = linfit(inv, mh)          # mean_h ~ c*(1/|mu|)  => exp scale
        bp, ap, r2p = linfit(lninv, mh)        # mean_h ~ p*ln(1/|mu|) => power
        verdict = "exp" if r2e > r2p else "power"
        print(" D=%2d  pts=%d  mean_h~%.3f/|mu| (R2=%.4f)  vs  %.3f*ln(1/|mu|) (R2=%.4f)  -> %s"
              % (D, len(sub), be, r2e, bp, r2p, verdict))
        fit_rows.append((D, len(sub), "%.4f"%be, "%.4f"%r2e, "%.4f"%bp, "%.4f"%r2p, verdict))
    with open(os.path.join(RES, "fit_value.csv"), "w") as f:
        for t in fit_rows:
            f.write(",".join(str(x) for x in t) + "\n")
    # near-critical points across D (smallest |drift| per D): the giants
    print("\n=== near-critical points (smallest |drift| per D): giant excursions ===")
    for D in sorted(byD):
        r = min(byD[D], key=lambda r: abs(float(r["vdrift"])))
        print(" D=%2d  drift=%+.4f  max_h=%s  h_p99=%s  wtau_log2=%s  f_cap=%s  blockH=%s"
              % (D, float(r["vdrift"]), r["max_h"], r["h_p99"], r["wtau"],
                 r["f_cap"], r["blockH"]))

def ccdf_slope(fn, metric, lo=2, hi=None):
    """log-log slope of CCDF vs 2^bin over [2^lo, ...]."""
    p = os.path.join(RES, fn)
    if not os.path.exists(p):
        return None
    xs, ys = [], []
    with open(p) as f:
        for row in csv.DictReader(f):
            if row["metric"] != metric:
                continue
            b = int(row["bin_log2_lo"]); cc = float(row["ccdf"])
            if b >= lo and cc > 0:
                xs.append(b*math.log(2)); ys.append(math.log(cc))
    if hi:
        xs, ys = xs[:hi], ys[:hi]
    if len(xs) < 3:
        return None
    return linfit(xs, ys)

def main():
    value_fits()
    print("\n=== (a) CCDF log-log slopes (fair-walk first passage predicts -0.5) ===")
    # value-side: near-critical logwalk tau
    for D in [4, 6, 8, 12]:
        k = D // 2
        s = ccdf_slope("ccdf_LW_D%d_k%d.csv" % (D, k), "tau")
        if s:
            print(" LW D=%d k=%d (near-crit) tau slope=%.3f R2=%.3f" % (D, k, s[0], s[2]))
    # counter-side: Hydra + LW42 at critical vs repelling
    for lbl in ["HYD_w1_-1_L1", "HYD_w2_-1_L1", "LW42_w1_-1_L1", "LW42_w2_-1_L1"]:
        s = ccdf_slope("ccdf_%s.csv" % lbl, "tc")
        if s:
            print(" %-16s tc slope=%.3f R2=%.3f" % (lbl, s[0], s[2]))

if __name__ == "__main__":
    main()
