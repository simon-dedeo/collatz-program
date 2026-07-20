"""Figure: geometry of the high-oscillation fiber set."""
import numpy as np, json, math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

KL = "/Users/simon/Desktop/COLLATZ/experiments/kl"
CACHE = f"{KL}/analysis_cache"
KS = list(range(12, 20))
TS = ["0.05", "0.1", "0.2", "0.3", "0.4"]

SURFACE, INK, SEC, MUT, GRID, BASE = ("#fcfcfb", "#0b0b0b", "#52514e",
                                      "#898781", "#e1e0d9", "#c3c2b7")
CAT = ["#2a78d6", "#008300", "#e87ba4", "#eda100", "#1baf7a", "#eb6834",
       "#4a3aa7", "#e34948"]
plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE, "axes.edgecolor": BASE,
    "axes.labelcolor": SEC, "text.color": INK,
    "xtick.color": MUT, "ytick.color": MUT,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.8,
    "axes.spines.top": False, "axes.spines.right": False,
    "font.family": "sans-serif", "font.size": 10.5,
    "axes.titlesize": 11, "axes.titleweight": "bold",
    "legend.frameon": False, "lines.linewidth": 1.8,
})

G = json.load(open(f"{CACHE}/geometry_results.json"))
LAMBDA = {12: 1.8064236, 13: 1.8188238, 14: 1.8307724, 15: 1.8419684,
          16: 1.8522348, 17: 1.8616888, 18: 1.8703250, 19: 1.8783132}
rho = json.load(open(f"{CACHE}/rho_at_2_k12-17.json"))
try:
    rho.update(json.load(open(f"{CACHE}/rho_at_2.json")))
except FileNotFoundError:
    pass
rho = {int(k): v for k, v in rho.items()}

fig, axs = plt.subplots(2, 3, figsize=(13.5, 8.4))

ax = axs[0, 0]
for i, t in enumerate(TS):
    ax.semilogy(KS, [G["tails"][str(k)][t]["haar"] for k in KS], "-o", ms=4,
                color=CAT[i], label=f"t={t}")
    ax.semilogy(KS, [G["tails"][str(k)][t]["mass"] for k in KS], "--",
                lw=1.3, color=CAT[i])
ax.set_xlabel("level k"); ax.set_ylabel("fraction of fibers with osc > t")
ax.set_title("(a) tail mass: Haar (solid) vs\neigenvector-mass (dashed)")
ax.legend(fontsize=8.5, ncol=2)

ax = axs[0, 1]
for i, t in enumerate(TS[:4]):
    lg = [math.log(G["tails"][str(k)][t]["count"], 3) for k in KS]
    sl = np.polyfit(KS[-4:], lg[-4:], 1)[0]
    ax.plot(KS, lg, "-o", ms=4, color=CAT[i], label=f"t={t}:  D≈{sl:.2f}")
ax.plot(KS, [k - 2 for k in KS], ":", color=MUT, lw=1.3, label="all fibers (D=1)")
ax.set_xlabel("level k"); ax.set_ylabel(r"$\log_3 N_k(t)$")
ax.set_title("(b) counts: box dimension of the\nhigh-osc set  (slope = D)")
ax.legend(fontsize=8.5)

ax = axs[0, 2]
for i, t in enumerate(TS):
    kk = [k for k in KS[1:] if t in G["persistence"][str(k)]]
    ax.plot(kk, [G["persistence"][str(k)][t]["cond"] for k in kk], "-o",
            ms=4, color=CAT[i], label=f"t={t}")
    ax.plot(kk, [G["persistence"][str(k)][t]["base"] for k in kk], ":",
            lw=1.2, color=CAT[i])
ax.set_ylim(0, 0.8)
ax.set_xlabel("level k")
ax.set_ylabel("P(child > t | parent > t)")
ax.set_title("(c) nesting: conditional (solid) stays up\nwhile base rate (dotted) collapses")
ax.legend(fontsize=8.5, ncol=2)

ax = axs[1, 0]
for i, t in enumerate(TS[1:4], start=1):
    ratio = [G["tails"][str(k)][t]["mass"] / G["tails"][str(k)][t]["haar"]
             for k in KS]
    ax.plot(KS, ratio, "-o", ms=4, color=CAT[i], label=f"t={t}")
ax.set_xlabel("level k"); ax.set_ylabel("mass fraction / Haar fraction")
ax.set_title("(d) eigenvector up-weights the bad set\n(but its absolute mass still decays)")
ax.legend(fontsize=8.5)

ax = axs[1, 1]
ol = G["orbit_localization"]
ax.plot(KS, [ol[str(k)]["top_mean"] for k in KS], "-o", ms=4, color=CAT[0],
        label="top-1000 osc fibers")
ax.plot(KS, [ol[str(k)]["base_mean"] for k in KS], "-o", ms=4, color=CAT[5],
        label="random fibers")
ax.plot(KS, [k - 1 for k in KS], ":", color=MUT, lw=1.2, label="max possible (k−1)")
ax.set_xlabel("level k")
ax.set_ylabel("mean 3-adic agreement depth")
ax.set_title("(e) localization on the backward\norbit of −1 (BFS, 27834 nodes)")
ax.legend(fontsize=8.5)

ax = axs[1, 2]
kk = sorted(LAMBDA)
ax.semilogy(kk, [2 - LAMBDA[k] for k in kk], "-o", ms=4, color=CAT[0],
            label=r"$2-\lambda_k$")
ax.semilogy(kk, [G["identity"][str(k)]["delta"] for k in kk], "-o", ms=4,
            color=CAT[1], label=r"$\delta_k$ (identity)")
kr = sorted(rho)
ax.semilogy(kr, [1 - rho[k]["ev"] for k in kr], "-o", ms=4, color=CAT[2],
            label=r"$1-\rho_k(2)$")
ax.set_xlabel("level k")
ax.set_ylabel("gap observables")
ax.set_title("(f) three gaps, all geometric-ish\n(ratios 0.91–0.94, drifting slowly up)")
ax.legend(fontsize=8.5)

fig.tight_layout()
fig.savefig(f"{KL}/fig_badset.png", dpi=160)
print("BADSET FIG DONE")
