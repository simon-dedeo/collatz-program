"""Cross-k stationarity tests on cached fiber reductions (analysis_cache/).

Tests whether the conditional refinement-pattern distribution is stationary in k:
  - conditional mean patterns per bin (parent mod 27 x parent-value decile)
  - raw and osc-standardized pattern-component histograms
  - argmin-position distribution
  - persistence of the exceptional (top-oscillation) set across k
"""
import numpy as np, json

CACHE = "/Users/simon/Desktop/COLLATZ/experiments/kl/analysis_cache"
KS = list(range(12, 20))
NQ = 10

R = {k: np.load(f"{CACHE}/reduc_k{k}.npz") for k in KS}


def tv(h1, h2):
    """total variation distance between two histograms (as prob. dists)."""
    p = h1 / h1.sum() if h1.sum() else h1
    q = h2 / h2.sum() if h2.sum() else h2
    return 0.5 * float(np.abs(p - q).sum())


print("=" * 78)
print("REFINEMENT-KERNEL STATIONARITY, consecutive k pairs")
print("=" * 78)
out = {}
for k in KS[:-1]:
    a, b = R[k], R[k + 1]
    wa = a["cnt"] / a["cnt"].sum()
    mua, mub = a["mean_pat"], b["mean_pat"]        # (90,3) conditional means
    # raw weighted L2 between conditional mean-pattern tables
    D_raw = float(np.sqrt((wa * ((mua - mub) ** 2).sum(1)).sum()))
    Dmax_raw = float(np.abs(mua - mub).max())
    # standardized: deviations measured in units of that level's median osc
    za = (mua - 1.0) / a["med_osc"]
    zb = (mub - 1.0) / b["med_osc"]
    D_std = float(np.sqrt((wa * ((za - zb) ** 2).sum(1)).sum()))
    # typical size of the deviations themselves (for scale reference)
    S_raw = float(np.sqrt((wa * ((mua - 1.0) ** 2).sum(1)).sum()))
    S_std = float(np.sqrt((wa * (za ** 2).sum(1)).sum()))
    # histogram TVs
    tv_w = np.mean([tv(a["whist"][j], b["whist"][j]) for j in range(3)])
    tv_z = np.mean([tv(a["zhist"][j], b["zhist"][j]) for j in range(3)])
    tv_osc = tv(a["osc_hist_d1"], b["osc_hist_d1"])
    # branch-conditional raw TVs
    tv_wb = np.mean([tv(a["whist_b9"][br, j], b["whist_b9"][br, j])
                     for br in range(3) for j in range(3)])
    # argmin distribution distance (weighted mean abs diff over bins)
    d_amin = float((wa[:, None] * np.abs(a["argmin_frac"]
                                         - b["argmin_frac"])).sum())
    # exceptional-set persistence (top-1000 osc fibers, class mod 3^12)
    s_a, s_b = set(a["top_r12"].tolist()), set(b["top_r12"].tolist())
    overlap = len(s_a & s_b) / 1000.0
    s_a100 = set(a["top_r12"][:100].tolist())
    s_b100 = set(b["top_r12"][:100].tolist())
    overlap100 = len(s_a100 & s_b100) / 100.0
    out[f"{k}->{k+1}"] = dict(
        D_raw=D_raw, D_std=D_std, Dmax_raw=Dmax_raw, S_raw=S_raw, S_std=S_std,
        tv_raw=float(tv_w), tv_std=float(tv_z), tv_raw_branch=float(tv_wb),
        tv_osc=float(tv_osc), d_argmin=d_amin,
        top1000_overlap=overlap, top100_overlap=overlap100)
    print(f"{k}->{k+1}:  D_raw={D_raw:.2e} (scale {S_raw:.2e})  "
          f"D_std={D_std:.3f} (scale {S_std:.3f})")
    print(f"          TV raw={tv_w:.4f}  TV std={tv_z:.4f}  "
          f"TV rawbranch={tv_wb:.4f}  TV osc={tv_osc:.4f}  "
          f"argmin={d_amin:.4f}")
    print(f"          top-osc overlap: top1000={overlap:.2f} "
          f"top100={overlap100:.2f}")

print()
print("=" * 78)
print("BRANCH-CONDITIONAL MEAN PATTERNS (parent mod 9 = 2,5,8), per k")
print("(components mu_j = mean over fibers of c(child_j)/fibermean, j=0,1,2)")
print("=" * 78)
lab = {0: "m=2(9)", 1: "m=5(9)", 2: "m=8(9)"}
bidx = (np.arange(90) // NQ) % 3
for k in KS:
    a = R[k]
    w = a["cnt"].astype(float)
    mu = a["mean_pat"]
    row = []
    for br in range(3):
        sel = bidx == br
        m = (mu[sel] * w[sel, None]).sum(0) / w[sel].sum()
        row.append(m)
    print(f"k={k}: " + "  ".join(
        f"{lab[br]}:[{row[br][0]:.4f},{row[br][1]:.4f},{row[br][2]:.4f}]"
        for br in range(3)) + f"   med_osc={float(a['med_osc']):.4f}")

print()
print("standardized deviations (mu_j - 1)/med_osc  — stationarity check:")
for k in KS:
    a = R[k]
    w = a["cnt"].astype(float)
    mu = a["mean_pat"]
    mo = float(a["med_osc"])
    row = []
    for br in range(3):
        sel = bidx == br
        m = (mu[sel] * w[sel, None]).sum(0) / w[sel].sum()
        row.append((m - 1.0) / mo)
    print(f"k={k}: " + "  ".join(
        f"{lab[br]}:[{row[br][0]:+.3f},{row[br][1]:+.3f},{row[br][2]:+.3f}]"
        for br in range(3)))

print()
print("=" * 78)
print("ARGMIN-POSITION FRACTIONS (which child is the fiber min), overall per k")
print("=" * 78)
for k in KS:
    a = R[k]
    w = a["cnt"].astype(float)
    af = (a["argmin_frac"] * w[:, None]).sum(0) / w.sum()
    print(f"k={k}: j=0:{af[0]:.4f}  j=1:{af[1]:.4f}  j=2:{af[2]:.4f}")

print()
print("=" * 78)
print("OSC BY PARENT-VALUE DECILE (mean osc, d=1) — is oscillation value-linked?")
print("=" * 78)
for k in KS:
    a = R[k]
    print(f"k={k}: " + " ".join(f"{v:.3f}" for v in a["osc_by_dec"]))

with open(f"{CACHE}/stationarity.json", "w") as fh:
    json.dump(out, fh, indent=1)
print("\nsaved", f"{CACHE}/stationarity.json")
