"""Numerical analysis of KL Perron eigenvectors c_k, k=12..19.

Indexing (verified by brute force in verify_indexing.py against build()):
  ms_k = arange(2, 3^k, 3); index of value m is (m-2)//3; n_k = 3^{k-1}.
  The 3^d refinements {q + t*3^{k-d}} of the level-(k-d) residue q
  (parent index p=(q-2)//3) sit at level-k indices p + t*3^{k-d-1},
  i.e. c_k.reshape(3^d, n_{k-d})[:, p] is the depth-d fiber of parent p.
  Row t=0 is the canonical lift (the value q itself).
Parent branch: r = 3p+2, r mod 9 = [2,5,8][p % 3]; r mod 27 = 3*(p%9)+2.

Outputs: analysis_results.json + per-k npz reductions in ./analysis_cache/.
"""
import numpy as np, json, os, gc, sys, time

EDIR = "/Users/simon/Desktop/COLLATZ/experiments/kl/eigvecs"
CACHE = "/Users/simon/Desktop/COLLATZ/experiments/kl/analysis_cache"
os.makedirs(CACHE, exist_ok=True)

KS = [int(x) for x in sys.argv[1:]] or list(range(12, 20))

LAMBDA = {12: 1.8064236, 13: 1.8188238, 14: 1.8307724, 15: 1.8419684,
          16: 1.8522348, 17: 1.8616888, 18: 1.8703250, 19: 1.8783132}

# fixed histogram edges (shared across k so distributions are comparable)
LOG_OSC_EDGES = np.linspace(-9, 1, 201)          # log10(osc)
W_EDGES = np.linspace(0.0, 3.0, 121)             # raw normalized pattern comp.
Z_EDGES = np.linspace(-4.0, 4.0, 161)            # standardized (w-1)/med_osc
NQUANT = 10                                      # parent-value deciles


def load(k):
    c = np.load(f"{EDIR}/eigvec_k{k}.npy")
    n = 3 ** (k - 1)
    assert c.shape == (n,), f"k={k}: bad shape {c.shape}"
    assert np.isfinite(c).all() and c.min() > 0, f"k={k}: bad values"
    assert abs(c.max() - 1.0) < 1e-12, f"k={k}: max={c.max()}"
    return c


def osc_stats(osc):
    q = np.percentile(osc, [50, 90, 99])
    return dict(mean=float(osc.mean()), median=float(q[0]),
                p90=float(q[1]), p99=float(q[2]),
                max=float(osc.max()), min=float(osc.min()))


def fiber_reductions(c, d):
    """max/min/mean over depth-d fibers. Returns (fmax, fmin, fmean, osc)."""
    A = c.reshape(3 ** d, -1)
    fmax = A.max(axis=0)
    fmin = A.min(axis=0)
    fmean = A.mean(axis=0)
    osc = (fmax - fmin) / fmean
    return fmax, fmin, fmean, osc


def norm_unit(x):
    return x / np.linalg.norm(x)


results = {"lambda": LAMBDA, "oscillation": {}, "cross_level": {},
           "patterns": {}}
_rp = f"{CACHE}/analysis_results.json"
if os.path.exists(_rp):
    with open(_rp) as fh:
        old = json.load(fh)
    for key in ("oscillation", "cross_level", "patterns"):
        results[key].update(old.get(key, {}))

prev_c = None
prev_k = None
for k in KS:
    t0 = time.time()
    c = load(k)
    n = c.size
    print(f"=== k={k} (n={n}) loaded [{time.time()-t0:.0f}s]", flush=True)

    # ---------- 1. FIBER OSCILLATION, depths 1..3 ----------
    okey = str(k)
    results["oscillation"][okey] = {}
    osc_hists = {}
    fmean1 = None
    osc1 = None
    for d in (1, 2, 3):
        if k - d < 1:
            continue
        fmax, fmin, fmean, osc = fiber_reductions(c, d)
        st = osc_stats(osc)
        results["oscillation"][okey][f"d{d}"] = st
        h, _ = np.histogram(np.log10(np.maximum(osc, 1e-300)),
                            bins=LOG_OSC_EDGES)
        osc_hists[f"d{d}"] = h
        print(f"  d={d}: mean={st['mean']:.3e} med={st['median']:.3e} "
              f"p90={st['p90']:.3e} p99={st['p99']:.3e} max={st['max']:.3e}",
              flush=True)
        if d == 1:
            fmean1, osc1 = fmean, osc
            fmin1 = fmin
        else:
            del fmax, fmin, fmean, osc
        gc.collect()

    # ---------- 2a. CROSS-LEVEL PROJECTIONS vs c_{k-1} ----------
    A1 = c.reshape(3, -1)
    if prev_c is not None and prev_k == k - 1:
        cl = {}
        for name, P in (("mean", fmean1), ("min", fmin1), ("canon", A1[0])):
            x, y = norm_unit(P.astype(np.float64)), norm_unit(prev_c)
            l2 = float(np.linalg.norm(x - y))
            xm, ym = P / P.max(), prev_c  # prev_c already max-normalized
            linf = float(np.abs(xm - ym).max())
            corr = float(np.corrcoef(P, prev_c)[0, 1])
            cl[name] = dict(rel_l2=l2, rel_linf=linf, corr=corr)
            print(f"  proj {name:5s} vs c_{k-1}: L2={l2:.3e} "
                  f"Linf={linf:.3e} corr={corr:.10f}", flush=True)
        results["cross_level"][f"{k-1}->{k}"] = cl

    # ---------- 2b. REFINEMENT PATTERNS (level-k fibers) ----------
    npar = n // 3
    p = np.arange(npar, dtype=np.int64)
    f27bin = (p % 9).astype(np.int16)              # parent residue mod 27
    # parent's own c-value deciles: use c_{k-1} if available else fmean1
    parent_val = prev_c if (prev_c is not None and prev_k == k - 1) else fmean1
    qedges = np.quantile(parent_val, np.linspace(0, 1, NQUANT + 1)[1:-1])
    dec = np.searchsorted(qedges, parent_val).astype(np.int16)  # 0..9
    bins = (f27bin * NQUANT + dec).astype(np.int32)             # 0..89
    NB = 9 * NQUANT
    cnt = np.bincount(bins, minlength=NB).astype(np.int64)

    med_osc = float(np.median(osc1))
    mean_pat = np.zeros((NB, 3))
    m2_pat = np.zeros((NB, 3))
    whist = np.zeros((3, W_EDGES.size - 1), dtype=np.int64)
    zhist = np.zeros((3, Z_EDGES.size - 1), dtype=np.int64)
    whist_b9 = np.zeros((3, 3, W_EDGES.size - 1), dtype=np.int64)  # [branch,j]
    b9 = (p % 3).astype(np.int8)
    for j in range(3):
        w = A1[j] / fmean1
        mean_pat[:, j] = np.bincount(bins, weights=w, minlength=NB)
        m2_pat[:, j] = np.bincount(bins, weights=w * w, minlength=NB)
        whist[j], _ = np.histogram(w, bins=W_EDGES)
        zhist[j], _ = np.histogram((w - 1.0) / med_osc, bins=Z_EDGES)
        for br in range(3):
            whist_b9[br, j], _ = np.histogram(w[b9 == br], bins=W_EDGES)
        del w
        gc.collect()
    mean_pat /= np.maximum(cnt, 1)[:, None]
    std_pat = np.sqrt(np.maximum(m2_pat / np.maximum(cnt, 1)[:, None]
                                 - mean_pat ** 2, 0))
    amin = np.argmin(A1, axis=0).astype(np.int8)
    argmin_frac = np.array([np.bincount(bins[amin == j], minlength=NB)
                            for j in range(3)]).T / np.maximum(cnt, 1)[:, None]
    # conditional osc histograms per branch (mod 9 of parent)
    osc_hist_b9 = np.zeros((3, LOG_OSC_EDGES.size - 1), dtype=np.int64)
    lo = np.log10(np.maximum(osc1, 1e-300))
    for br in range(3):
        osc_hist_b9[br], _ = np.histogram(lo[b9 == br], bins=LOG_OSC_EDGES)
    del lo
    # branch-level (mod 9) mean patterns for the headline table
    mean_pat_b9 = np.array([
        (mean_pat[np.arange(NB) // NQUANT % 3 == br]
         * cnt[np.arange(NB) // NQUANT % 3 == br, None]).sum(0)
        / cnt[np.arange(NB) // NQUANT % 3 == br].sum()
        for br in range(3)])
    # NOTE: bins = f27bin*10+dec, f27bin = p%9; branch = p%3 = f27bin%3
    # so bin b -> branch = (b // NQUANT) % 3  -- used above.

    results["patterns"][okey] = dict(
        med_osc=med_osc,
        mean_pat_b9=mean_pat_b9.tolist(),
        argmin_overall=np.bincount(amin, minlength=3).tolist())

    # ---------- fixed-level-12 projections (aligned across k) ----------
    d12 = k - 12
    A12 = c.reshape(3 ** d12, -1) if d12 > 0 else c.reshape(1, -1)
    coarse12_mean = A12.mean(axis=0)
    coarse12_min = A12.min(axis=0)

    # ---------- exceptional set: top-oscillation fibers ----------
    NTOP = 1000
    top_idx = np.argpartition(osc1, -NTOP)[-NTOP:]
    top_idx = top_idx[np.argsort(osc1[top_idx])[::-1]]
    top_osc = osc1[top_idx]
    top_r = (3 * top_idx.astype(np.int64) + 2)   # parent residue, level k-1
    top_r12 = top_r % 3 ** 12                    # its class mod 3^12

    np.savez_compressed(
        f"{CACHE}/reduc_k{k}.npz",
        cnt=cnt, mean_pat=mean_pat, std_pat=std_pat,
        argmin_frac=argmin_frac, whist=whist, zhist=zhist,
        whist_b9=whist_b9, osc_hist_b9=osc_hist_b9,
        med_osc=med_osc, qedges=qedges,
        **{f"osc_hist_{key}": v for key, v in osc_hists.items()},
        coarse12_mean=coarse12_mean, coarse12_min=coarse12_min,
        top_osc=top_osc, top_r12=top_r12,
        # osc vs parent-value 2d: mean osc per decile
        osc_by_dec=np.array([float(osc1[dec == q].mean())
                             for q in range(NQUANT)]),
    )
    del amin, bins, dec, f27bin, b9
    prev_c, prev_k = c, k
    del fmean1, fmin1, osc1, A1
    gc.collect()
    print(f"  [k={k} done in {time.time()-t0:.0f}s]", flush=True)

with open(f"{CACHE}/analysis_results.json", "w") as fh:
    json.dump(results, fh, indent=1)
print("ALL DONE")
