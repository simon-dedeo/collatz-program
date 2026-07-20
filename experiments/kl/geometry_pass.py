"""Geometry of the high-oscillation fiber set (coordinator's priority list).

Per level k = 12..19, with osc(r) := (max-min)/mean over the depth-1 fiber:
 1. TAIL MASS: Haar fraction of fibers with osc > t, t in {0.05,0.1,0.2,0.3,0.4};
    also raw counts N_k(t) for box-dimension slopes.
 2. PARENT-CHILD PERSISTENCE: P(child fiber > t | parent fiber > t) vs base rate.
    Child fibers at level k are indexed by parent p in Y_{k-1} (0..3^{k-2}-1);
    the enclosing level-(k-1) fiber is q = p mod 3^{k-3}.
 3. LOCALIZATION: digit prefixes of top-50 fibers (k=16..19); 3-adic agreement
    depth of top-1000 fibers to candidate addresses and to the BFS backward
    orbit of -1; random baseline.
 4. WEIGHTING: eigenvector-mass-weighted tails and the exact identity
    s(lam_k) - 1 = (w2+w8) * delta_k, delta_k = sum(mean-min)/sum_m c.

Outputs: CSVs in analysis_cache/ + geometry_results.json.
"""
import numpy as np, math, json, gc

ALPHA = math.log(3, 2)
EDIR = "/Users/simon/Desktop/COLLATZ/experiments/kl/eigvecs"
CACHE = "/Users/simon/Desktop/COLLATZ/experiments/kl/analysis_cache"
KS = list(range(12, 20))
TS = [0.05, 0.1, 0.2, 0.3, 0.4]
LAMBDA = {12: 1.8064236, 13: 1.8188238, 14: 1.8307724, 15: 1.8419684,
          16: 1.8522348, 17: 1.8616888, 18: 1.8703250, 19: 1.8783132}

# ---------------- backward orbit of -1 (exact, mod 3^18) ----------------
J = 18
MJ = 3 ** J
inv4 = pow(4, -1, MJ * 9)   # work mod 3^20 to check branch conditions mod 9
inv2 = pow(2, -1, MJ * 9)
M20 = MJ * 9


def predecessors(y):
    """x with an edge x -> y in the constraint graph (classes mod 3^20)."""
    out = []
    x = (y * inv4) % M20                      # y = 4x branch (always an edge)
    out.append(x)
    x = ((3 * y + 2) * inv4) % M20            # y = R2(x), needs x=2 mod 9
    if x % 9 == 2:
        out.append(x)
    x = ((3 * y + 1) * inv2) % M20            # y = R8(x), needs x=8 mod 9
    if x % 9 == 8:
        out.append(x)
    return out


orbit = {(M20 - 1) % M20: 0}                  # -1 mod 3^20, depth 0
frontier = [(M20 - 1) % M20]
for depth in range(1, 13):
    nxt = []
    for y in frontier:
        for x in predecessors(y):
            if x not in orbit:
                orbit[x] = depth
                nxt.append(x)
    frontier = nxt
    if len(orbit) > 20000:
        print(f"orbit BFS capped at depth {depth}, {len(orbit)} nodes")
        break
orbit_mod = np.array(sorted({v % MJ for v in orbit}), dtype=np.int64)
print(f"backward orbit of -1: {len(orbit)} nodes to depth 12 "
      f"({len(orbit_mod)} classes mod 3^18)")

# candidate single addresses (value mod 3^18 if in Y, else None)
def to_class(num, den=1):
    if den == 1:
        v = num % MJ
    else:
        v = (num * pow(den, -1, MJ)) % MJ
    return v if v % 3 == 2 else None


CAND = {
    "-1": to_class(-1), "2 (fix R2)": to_class(2), "-7 (T-cycle -5)": to_class(-7),
    "-25 (T-cycle -17)": to_class(-25), "-37": to_class(-37), "-55": to_class(-55),
    "-82": to_class(-82), "-91": to_class(-91), "-136": to_class(-136),
    "-61": to_class(-61), "-34": to_class(-34), "1/5": to_class(1, 5),
    "-5": to_class(-5), "-17": to_class(-17), "-1/2": to_class(-1, 2),
}
print("candidates in Y:", {k: v for k, v in CAND.items() if v is not None})
print("candidates NOT in Y (excluded, !=2 mod 3):",
      [k for k, v in CAND.items() if v is None])


def agree_depth(r, a):
    """3-adic agreement depth: largest j<=J with r = a mod 3^j (vectorized)."""
    d = (r - a) % MJ
    out = np.full(r.shape, J, dtype=np.int64)
    nz = d != 0
    v = np.zeros(nz.sum(), dtype=np.int64)
    dd = d[nz]
    while True:
        div = dd % 3 == 0
        if not div.any():
            break
        v[div] += 1
        dd = np.where(div, dd // 3, dd)
    out[nz] = v
    return out


def orbit_agree(rs):
    """max agreement depth of each r against the whole orbit set."""
    best = np.zeros(len(rs), dtype=np.int64)
    for a in orbit_mod:
        best = np.maximum(best, agree_depth(rs, int(a)))
    return best


def base3(r, ndig):
    dig = []
    for _ in range(ndig):
        dig.append(int(r % 3))
        r //= 3
    return "".join(str(d) for d in dig)  # LSB first


rng = np.random.default_rng(0)
res = {"tails": {}, "persistence": {}, "weighted": {}, "identity": {},
       "orbit_localization": {}, "candidates": {}}
osc_prev = None
csv_tail = ["k,t,haar_frac,count,mass_frac"]
csv_pers = ["k,t,base_rate,cond_rate,enrichment"]
csv_id = ["k,lambda,s_minus_1,(w2+w8)*delta,delta,ratio,"
          "delta_haar_relosc,mean_osc"]

for k in KS:
    c = np.load(f"{EDIR}/eigvec_k{k}.npy")
    A = c.reshape(3, -1)
    fmax = A.max(0); fmin = A.min(0); fmean = A.mean(0)
    osc = (fmax - fmin) / fmean
    lam = LAMBDA[k]
    w2, w8 = lam ** (ALPHA - 2), lam ** (ALPHA - 1)
    s = lam ** -2 + (w2 + w8) / 3

    # 4. exact identity + weighting
    csum = float(c.sum())
    delta = float((fmean - fmin).sum()) / csum          # note's delta_k
    lhs = s - 1
    rhs = (w2 + w8) * delta
    relosc = (fmean - fmin) / fmean                     # (mean-min)/mean
    delta_haar = float(relosc.mean()) / 3.0             # Haar analogue of delta
    res["identity"][k] = dict(lam=lam, s_minus_1=lhs, rhs=rhs, delta=delta,
                              delta_haar=delta_haar, ratio=lhs / rhs)
    csv_id.append(f"{k},{lam},{lhs:.6e},{rhs:.6e},{delta:.6e},"
                  f"{lhs/rhs:.8f},{delta_haar:.6e},{float(osc.mean()):.6e}")

    # 1. tails (Haar and mass-weighted)
    w_mass = fmean / fmean.sum()
    tt = {}
    for t in TS:
        hi = osc > t
        cnt = int(hi.sum())
        tt[t] = dict(haar=cnt / osc.size, count=cnt,
                     mass=float(w_mass[hi].sum()))
        csv_tail.append(f"{k},{t},{cnt/osc.size:.6e},{cnt},"
                        f"{float(w_mass[hi].sum()):.6e}")
    res["tails"][k] = tt

    # 2. persistence (needs previous level's osc)
    if osc_prev is not None:
        n_par = osc_prev.size                            # 3^{k-3}
        pp = {}
        for t in TS:
            hi_c = osc > t
            hi_p = np.tile(osc_prev > t, 3)              # q = p mod 3^{k-3}
            base = hi_c.mean()
            if hi_p.any():
                cond = float(hi_c[hi_p].mean())
                pp[t] = dict(base=float(base), cond=cond,
                             enrich=cond / base if base > 0 else np.nan)
                csv_pers.append(f"{k},{t},{base:.6e},{cond:.6e},"
                                f"{cond/base:.4f}")
        res["persistence"][k] = pp

    # 3. localization: top fibers
    NT = 1000
    ti = np.argpartition(osc, -NT)[-NT:]
    ti = ti[np.argsort(osc[ti])[::-1]]
    top_r = (3 * ti.astype(np.int64) + 2) % MJ          # parent value mod 3^18
    # (parents at level k-1 have value < 3^18 for k<=19, so mod is exact)
    od = np.minimum(orbit_agree(top_r), k - 1)   # parent defined mod 3^{k-1}
    base_r = (3 * rng.choice(osc.size, NT, replace=False).astype(np.int64) + 2) % MJ
    od_base = np.minimum(orbit_agree(base_r), k - 1)
    res["orbit_localization"][k] = dict(
        top_mean=float(od.mean()), top_median=float(np.median(od)),
        top_frac_ge6=float((od >= 6).mean()),
        base_mean=float(od_base.mean()), base_frac_ge6=float((od_base >= 6).mean()))
    cd = {}
    for name, a in CAND.items():
        if a is None:
            continue
        dep = np.minimum(agree_depth(top_r, a), k - 1)
        cd[name] = dict(max=int(dep.max()), mean=float(dep.mean()),
                        frac_ge4=float((dep >= 4).mean()))
    res["candidates"][k] = cd

    if k >= 16:
        print(f"\n=== top-50 oscillating fibers, k={k} (parent value, base-3 "
              f"digits LSB->MSB, {k-1} digits) ===")
        for i in range(50):
            r_full = 3 * int(ti[i]) + 2
            print(f"  osc={osc[ti[i]]:.4f}  r={r_full:<19d} "
                  f"{base3(r_full, k-1)}  orbit_depth={od[i]}")

    osc_prev = osc
    del c, A, fmax, fmin, fmean
    gc.collect()
    print(f"[k={k} done] delta={delta:.6f} id_ratio={lhs/rhs:.8f} "
          f"tail0.2 haar={tt[0.2]['haar']:.3e} mass={tt[0.2]['mass']:.3e}")

open(f"{CACHE}/tail_mass.csv", "w").write("\n".join(csv_tail) + "\n")
open(f"{CACHE}/persistence.csv", "w").write("\n".join(csv_pers) + "\n")
open(f"{CACHE}/identity.csv", "w").write("\n".join(csv_id) + "\n")
json.dump(res, open(f"{CACHE}/geometry_results.json", "w"), indent=1,
          default=float)

# dimension slopes: log_3 N_k(t) vs k
print("\nbox-dimension estimates D(t) = slope of log3 N_k(t) in k (last 4 pts):")
for t in TS:
    lg = [math.log(res["tails"][k][t]["count"], 3) if res["tails"][k][t]["count"] > 0
          else None for k in KS]
    pts = [(k, v) for k, v in zip(KS, lg) if v is not None][-4:]
    if len(pts) >= 2:
        sl = np.polyfit([p[0] for p in pts], [p[1] for p in pts], 1)[0]
        print(f"  t={t}: log3 N = {[f'{v:.2f}' if v else 'NA' for v in lg]} "
              f"-> D ~ {sl:.3f}")
print("GEOMETRY DONE")
