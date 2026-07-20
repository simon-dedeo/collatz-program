"""Figures for the eigenvector analysis. Reads analysis_cache/, writes PNGs
into the kl/ directory. Palette: dataviz reference instance (light mode)."""
import numpy as np, json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

KL = "/Users/simon/Desktop/COLLATZ/experiments/kl"
CACHE = f"{KL}/analysis_cache"
KS = list(range(12, 20))

# ---- palette (dataviz reference, light mode) ----
SURFACE = "#fcfcfb"
INK = "#0b0b0b"
SEC = "#52514e"
MUT = "#898781"
GRID = "#e1e0d9"
BASE = "#c3c2b7"
CAT = ["#2a78d6", "#008300", "#e87ba4", "#eda100",
       "#1baf7a", "#eb6834", "#4a3aa7", "#e34948"]
SEQ8 = ["#86b6ef", "#6da7ec", "#5598e7", "#3987e5",
        "#2a78d6", "#256abf", "#1c5cab", "#0d366b"]  # k=12..19 ordinal

plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE, "axes.edgecolor": BASE,
    "axes.labelcolor": SEC, "text.color": INK,
    "xtick.color": MUT, "ytick.color": MUT,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.8,
    "axes.spines.top": False, "axes.spines.right": False,
    "font.family": "sans-serif", "font.size": 10.5,
    "axes.titlesize": 11.5, "axes.titleweight": "bold",
    "legend.frameon": False, "lines.linewidth": 1.8,
})

results = json.load(open(f"{CACHE}/analysis_results.json"))
stat = json.load(open(f"{CACHE}/stationarity.json"))
R = {k: np.load(f"{CACHE}/reduc_k{k}.npz") for k in KS}
LOG_OSC_EDGES = np.linspace(-9, 1, 201)
W_EDGES = np.linspace(0.0, 3.0, 121)
Z_EDGES = np.linspace(-4.0, 4.0, 161)
LAMBDA = {int(k): v for k, v in results["lambda"].items()}

osc = {(k, d): results["oscillation"][str(k)][f"d{d}"]
       for k in KS for d in (1, 2, 3) if f"d{d}" in results["oscillation"][str(k)]}

# ================= FIG 1: oscillation =================
fig, axs = plt.subplots(1, 3, figsize=(13.5, 4.2))
ax = axs[0]
ks = np.array(KS)
for i, (name, lab) in enumerate([("mean", "mean"), ("median", "median"),
                                 ("p90", "p90"), ("p99", "p99"),
                                 ("max", "max")]):
    v = [osc[(k, 1)][name] for k in KS]
    ax.semilogy(ks, v, "-o", ms=4, color=CAT[i], label=lab)
# geometric guide through the mean
v0 = osc[(KS[0], 1)]["mean"]
ax.semilogy(ks, v0 * 0.91 ** (ks - KS[0]), "--", lw=1.2, color=MUT,
            label=r"$0.91^k$ guide")
ax.set_xlabel("level k"); ax.set_ylabel("fiber oscillation  osc(r)")
ax.set_title("(a) depth-1 oscillation statistics vs k")
ax.legend(fontsize=9, ncol=2)

ax = axs[1]
for di, d in enumerate((1, 2, 3)):
    v = [osc[(k, d)]["mean"] for k in KS if (k, d) in osc]
    kk = [k for k in KS if (k, d) in osc]
    ax.semilogy(kk, v, "-o", ms=4, color=CAT[di], label=f"depth d={d}")
    v = [osc[(k, d)]["max"] for k in KS if (k, d) in osc]
    ax.semilogy(kk, v, ":", lw=1.4, color=CAT[di])
ax.set_xlabel("level k"); ax.set_ylabel("mean osc (solid), max osc (dotted)")
ax.set_title("(b) mean and max oscillation, depths 1–3")
ax.legend(fontsize=9)

ax = axs[2]
ctr = 0.5 * (LOG_OSC_EDGES[:-1] + LOG_OSC_EDGES[1:])
for i, k in enumerate(KS):
    h = R[k]["osc_hist_d1"].astype(float)
    h /= h.sum()
    ax.plot(10 ** ctr, h, color=SEQ8[i], label=f"k={k}", lw=1.4)
ax.set_xscale("log")
ax.set_xlim(1e-4, 2)
ax.set_xlabel("osc(r)  (log scale)")
ax.set_ylabel("fraction of fibers")
ax.set_title("(c) osc distribution: bulk drifts left,\nright edge pinned")
ax.legend(fontsize=8, ncol=2)
fig.tight_layout()
fig.savefig(f"{KL}/fig_oscillation.png", dpi=160)
plt.close(fig)

# ================= FIG 2: cross-level distances =================
fig, axs = plt.subplots(1, 3, figsize=(13.5, 4.2))
pairs = [f"{k}->{k+1}" for k in KS[:-1]]
kp = np.array(KS[:-1]) + 1
cl = results["cross_level"]
ax = axs[0]
for i, proj in enumerate(["mean", "min", "canon"]):
    ax.semilogy(kp, [cl[p][proj]["rel_l2"] for p in pairs], "-o", ms=4,
                color=CAT[i], label=f"proj: {proj}")
ax.set_xlabel("level k (compared with k−1)")
ax.set_ylabel(r"$\|\hat P(c_k)-\hat c_{k-1}\|_2$ (unit-norm)")
ax.set_title("(a) cross-level L2 distance")
ax.legend(fontsize=9)

ax = axs[1]
for i, proj in enumerate(["mean", "min", "canon"]):
    ax.plot(kp, [cl[p][proj]["rel_linf"] for p in pairs], "-o", ms=4,
            color=CAT[i], label=f"proj: {proj}")
ax.set_ylim(0, 0.35)
ax.set_xlabel("level k (compared with k−1)")
ax.set_ylabel(r"$L_\infty$ distance (max-normalized)")
ax.set_title("(b) cross-level sup distance: no decay")
ax.legend(fontsize=9)

ax = axs[2]
for i, proj in enumerate(["mean", "min", "canon"]):
    ax.semilogy(kp, [1 - cl[p][proj]["corr"] for p in pairs], "-o", ms=4,
                color=CAT[i], label=f"proj: {proj}")
ax.set_xlabel("level k (compared with k−1)")
ax.set_ylabel(r"$1-\rho$ (Pearson)")
ax.set_title("(c) decorrelation, log scale")
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(f"{KL}/fig_cross_level.png", dpi=160)
plt.close(fig)

# ================= FIG 3: refinement kernel =================
fig, axs = plt.subplots(1, 3, figsize=(13.5, 4.2))
NQ = 10
bidx = (np.arange(90) // NQ) % 3
lab9 = ["2 (mod 9)", "5 (mod 9)", "8 (mod 9)"]
ax = axs[0]
for br in range(3):
    for j in range(3):
        vals = []
        for k in KS:
            a = R[k]
            w = a["cnt"].astype(float)
            mu = a["mean_pat"]
            sel = bidx == br
            m = (mu[sel] * w[sel, None]).sum(0) / w[sel].sum()
            vals.append((m[j] - 1.0) / float(a["med_osc"]))
        ax.plot(KS, vals, "-o", ms=3.5, color=CAT[br],
                alpha=(0.45, 0.75, 1.0)[j],
                label=lab9[br] if j == 0 else None)
ax.axhline(0, color=BASE, lw=1)
ax.set_xlabel("level k")
ax.set_ylabel(r"$(\mu_j-1)/\mathrm{med\ osc}$")
ax.set_title("(b1) branch-mean patterns, osc units\n(3 children per branch color)")
ax.legend(fontsize=9, title="parent branch", title_fontsize=9)

ax = axs[1]
zc = 0.5 * (Z_EDGES[:-1] + Z_EDGES[1:])
for i, k in enumerate(KS):
    h = R[k]["zhist"].sum(0).astype(float)
    h /= h.sum()
    ax.plot(zc, h, color=SEQ8[i], lw=1.4, label=f"k={k}")
ax.set_xlabel(r"$(w_j - 1)/\mathrm{med\ osc}$")
ax.set_ylabel("fraction")
ax.set_title("(b2) standardized refinement-pattern distribution")
ax.legend(fontsize=8, ncol=2)

ax = axs[2]
kp = np.array(KS[:-1]) + 0.5
ax.semilogy(kp, [stat[p]["tv_raw"] for p in pairs], "-o", ms=4,
            color=CAT[0], label="TV, raw patterns")
ax.semilogy(kp, [stat[p]["tv_std"] for p in pairs], "-o", ms=4,
            color=CAT[1], label="TV, osc-standardized")
ax.semilogy(kp, [stat[p]["D_std"] for p in pairs], "-o", ms=4,
            color=CAT[2], label=r"$D_{std}$ (cond. means)")
ax.semilogy(kp, [stat[p]["tv_osc"] for p in pairs], "-o", ms=4,
            color=CAT[3], label="TV, osc distribution")
ax.set_xlabel("pair (k, k+1) midpoint")
ax.set_ylabel("distance between consecutive levels")
ax.set_title("(b3) kernel stationarity: raw vs standardized")
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(f"{KL}/fig_kernel.png", dpi=160)
plt.close(fig)

# ================= FIG 4: coarse profile + lambda =================
fig, axs = plt.subplots(1, 3, figsize=(13.5, 4.2))
ax = axs[0]
W = 600
for i, k in enumerate(KS):
    prof = R[k]["coarse12_mean"]
    ax.plot(np.arange(W), prof[:W], color=SEQ8[i], lw=1.0,
            label=f"k={k}" if k in (12, 15, 19) else None)
ax.set_xlabel("level-12 state index p  (m = 3p+2)")
ax.set_ylabel("mean-projected value at level 12")
ax.set_title("(a) coarse (level-12) profile of $c_k$, window")
ax.legend(fontsize=9)

ax = axs[1]
ref = R[19]["coarse12_mean"]
ref = ref / np.linalg.norm(ref)
d2, dinf = [], []
for k in KS[:-1]:
    x = R[k]["coarse12_mean"]
    xn = x / np.linalg.norm(x)
    d2.append(np.linalg.norm(xn - ref))
    dinf.append(np.abs(x / x.max() - R[19]["coarse12_mean"]
                       / R[19]["coarse12_mean"].max()).max())
ax.semilogy(KS[:-1], d2, "-o", ms=4, color=CAT[0], label=r"$L_2$ to $k{=}19$")
ax.semilogy(KS[:-1], dinf, "-o", ms=4, color=CAT[5],
            label=r"$L_\infty$ to $k{=}19$")
ax.set_xlabel("level k")
ax.set_ylabel("distance of level-12 projection to k=19's")
ax.set_title("(b) Cauchy convergence of the coarse profile")
ax.legend(fontsize=9)

ax = axs[2]
lam_k = np.array([LAMBDA[k] for k in sorted(LAMBDA)])
kk = np.array(sorted(LAMBDA))
gap = 2.0 - lam_k
ax.semilogy(kk, gap, "-o", ms=4, color=CAT[0], label=r"$2-\lambda_k$")
# geometric fit on the last 5 points
z = np.polyfit(kk[-5:], np.log(gap[-5:]), 1)
rho = float(np.exp(z[0]))
ax.semilogy(kk, np.exp(np.polyval(z, kk)), "--", lw=1.2, color=MUT,
            label=fr"geometric fit, ratio {rho:.3f}")
ax.set_xlabel("level k")
ax.set_ylabel(r"$2-\lambda_k$")
ax.set_title("(c) spectral gap to 2: geometric decay")
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(f"{KL}/fig_profile_lambda.png", dpi=160)
plt.close(fig)

# lambda extrapolations printed for the summary
print("lambda_k:", dict(zip(kk.tolist(), lam_k.tolist())))
print("2-lambda ratios:", (gap[1:] / gap[:-1]).round(5).tolist())
print(f"geometric fit (last5): ratio={rho:.4f} -> lambda_inf = 2 - "
      f"{float(np.exp(np.polyval(z, 40))):.2e} at k=40 if it holds")
d1 = np.diff(lam_k)
ait = lam_k[2:] - d1[1:] ** 2 / np.where(np.diff(d1) != 0, np.diff(d1), np.nan)
print("Aitken extrapolations:", ait.round(5).tolist())
print("PLOTS DONE")
