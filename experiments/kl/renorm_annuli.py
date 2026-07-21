"""Renormalization measurement: fiber oscillation statistics globally and on
3-adic annuli around -1 and around the backward-4 orbit points -1/4^n.

For each level k (15..19), using the certified feasible subeigenvector
C = cert_k{k}_C.npy (int64, length 3^(k-1), state m = 2+3i), the level-k fiber over the
level-(k-1) base state r = 2+3i (i in [0, 3^(k-2))) is C.reshape(3,n)[:, i],
n = 3^(k-2).

(1) GLOBAL per-fiber stats: mean, min, max; osc=(max-min)/mean;
    u=(mean-min)/mean; mass weight nu(i)=mean_i/sum(mean).
(2) ANNULI A_j = {base r : v3((r - p) mod 3^(k-1)) = j}, j=1..10, around
    p = -1 mod 3^(k-1), enumerated as r = p + t*3^j + s*3^(j+1) mod 3^(k-1),
    t in {1,2}, s in [0, 3^(k-2-j)).
(3) Same annuli around p_n = -1/4^n mod 3^(k-1), n=1,2,3.

Outputs: renorm_global.csv, renorm_annuli.csv (in experiments/kl/).
Self-test (k=5 brute force of the annulus enumeration) runs first.
Only numpy + stdlib. Never materializes the whole float array for k=19;
all fiber passes are chunked (<= 4M fibers per chunk).
"""
import csv
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from renorm_common import load_C  # noqa: E402

CHUNK = 4_000_000          # max fibers per chunk
JMAX = 10                  # annuli j = 1..JMAX
THRESH = (0.2, 0.3)

# ---------- reference values (docs/notes/fiber-geometry.md, M7 & M3) ----------
REF_NU02 = {15: 5.97e-2, 16: 4.71e-2, 17: 3.79e-2, 18: 3.06e-2}
REF_EU = {15: 0.0407, 16: 0.0375, 17: 0.0347, 18: 0.0321}
REF_CNT02 = {15: 31703, 16: 69337, 17: 155338, 18: 351539}


def v3(x):
    """3-adic valuation of a positive integer."""
    assert x > 0
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def centers_for(k):
    """Ordered dict of annulus centers at level k-1 (all == 2 mod 3)."""
    M1 = 3 ** (k - 1)
    cs = {}
    p = M1 - 1                      # -1 mod 3^(k-1)
    assert p % 3 == 2
    cs["minus1"] = p
    for nb in (1, 2, 3):
        pn = (-pow(4, -nb, M1)) % M1        # -1/4^n mod 3^(k-1)
        assert pn % 3 == 2, (k, nb, pn)      # automatically == 2 mod 3
        assert (pn * pow(4, nb, M1)) % M1 == M1 - 1
        cs[f"inv4_n{nb}"] = pn
    return cs


def enum_annulus_chunks(k, p, j, chunk=CHUNK):
    """Yield int64 arrays of FIBER INDICES i=(r-2)/3 covering annulus A_j
    around center p, in chunks. r = p + t*3^j + s*3^(j+1) mod 3^(k-1)."""
    M1 = 3 ** (k - 1)
    S = 3 ** (k - 2 - j)
    step = 3 ** (j + 1)
    for t in (1, 2):
        base = (p + t * 3 ** j) % M1
        for s0 in range(0, S, chunk):
            s = np.arange(s0, min(s0 + chunk, S), dtype=np.int64)
            r = (base + s * step) % M1
            yield (r - 2) // 3


def selftest():
    """Brute-force check of the annulus enumeration at k=5: disjoint cover."""
    k = 5
    M1 = 3 ** (k - 1)  # 81
    for name, p in centers_for(k).items():
        brute = {j: set() for j in range(1, k - 1)}
        allr = set()
        for r in range(2, M1, 3):
            if r == p:
                continue
            d = (r - p) % M1
            j = v3(d)
            assert 1 <= j <= k - 2, (name, r, j)
            brute[j].add(r)
            allr.add(r)
        seen = set()
        for j in range(1, k - 1):
            enum = set()
            for idx_arr in enum_annulus_chunks(k, p, j):
                for i in idx_arr.tolist():
                    r = 2 + 3 * i
                    assert r % 3 == 2
                    enum.add(r)
            assert len(enum) == 2 * 3 ** (k - 2 - j), (name, j)
            assert enum == brute[j], (name, j)          # exactly A_j
            assert not (enum & seen), (name, j)          # disjoint
            seen |= enum
        assert seen == allr, name                        # cover (minus p)
    print("[selftest] k=5 annulus enumeration: disjoint cover verified "
          "for all 4 centers.", flush=True)


def sample_check_annulus(k, p, j, idx_sample):
    """Spot-check enumerated indices really have v3((r-p) mod 3^(k-1)) = j."""
    M1 = 3 ** (k - 1)
    for i in idx_sample.tolist():
        r = 2 + 3 * i
        d = (r - p) % M1
        assert v3(d) == j, (k, p, j, r)


def global_pass(k):
    """Chunked pass over all fibers. Returns (stats dict, mean_arr, osc_arr).
    mean/osc arrays are stored float64 for k<=18, float32 for k=19."""
    C = load_C(k)                      # mmap int64, length 3^(k-1)
    n = 3 ** (k - 2)
    assert C.shape[0] == 3 * n
    store_dtype = np.float32 if k >= 19 else np.float64
    mean_arr = np.empty(n, dtype=store_dtype)
    osc_arr = np.empty(n, dtype=store_dtype)

    total_mass = 0.0
    sum_min = 0.0
    sum_osc = 0.0
    cnt = {t: 0 for t in THRESH}
    mass = {t: 0.0 for t in THRESH}
    t0 = time.time()
    nchunks = (n + CHUNK - 1) // CHUNK
    for ci, a in enumerate(range(0, n, CHUNK)):
        b = min(a + CHUNK, n)
        f0 = np.asarray(C[a:b], dtype=np.float64)
        f1 = np.asarray(C[n + a:n + b], dtype=np.float64)
        f2 = np.asarray(C[2 * n + a:2 * n + b], dtype=np.float64)
        mn = np.minimum(np.minimum(f0, f1), f2)
        mx = np.maximum(np.maximum(f0, f1), f2)
        mean = f0
        mean += f1
        mean += f2
        mean /= 3.0                    # in-place; f0 no longer needed
        osc = (mx - mn) / mean
        total_mass += float(mean.sum())
        sum_min += float(mn.sum())
        sum_osc += float(osc.sum())
        for t in THRESH:
            m = osc > t
            cnt[t] += int(m.sum())
            mass[t] += float(mean[m].sum())
        mean_arr[a:b] = mean
        osc_arr[a:b] = osc
        if nchunks > 8 and (ci + 1) % 8 == 0:
            print(f"  [k={k}] global pass chunk {ci+1}/{nchunks} "
                  f"({time.time()-t0:.1f}s)", flush=True)
    stats = {
        "n": n,
        "total_mass": total_mass,
        "mean_osc": sum_osc / n,
        "nu_E_u": (total_mass - sum_min) / total_mass,
        "nu_tail": {t: mass[t] / total_mass for t in THRESH},
        "haar_cnt": cnt,
        "haar_frac": {t: cnt[t] / n for t in THRESH},
    }
    print(f"  [k={k}] global pass done in {time.time()-t0:.1f}s", flush=True)
    return stats, mean_arr, osc_arr


def annulus_stats(k, p, j, mean_arr, osc_arr, total_mass):
    """Stats over annulus A_j around p, chunked gathers from stored arrays."""
    cnt = 0
    s_mass = 0.0
    s_osc = 0.0
    s_mosc = 0.0
    cnt02 = 0
    s_mass02 = 0.0
    mx = 0.0
    checked = False
    for idx in enum_annulus_chunks(k, p, j):
        if not checked:   # spot-check first chunk's enumeration
            m = min(len(idx), 200)
            sample = idx[np.linspace(0, len(idx) - 1, m).astype(np.int64)]
            sample_check_annulus(k, p, j, sample)
            checked = True
        me = mean_arr[idx].astype(np.float64, copy=False)
        os_ = osc_arr[idx].astype(np.float64, copy=False)
        cnt += len(idx)
        s_mass += float(me.sum())
        s_osc += float(os_.sum())
        s_mosc += float((me * os_).sum())
        msk = os_ > 0.2
        cnt02 += int(msk.sum())
        s_mass02 += float(me[msk].sum())
        if len(os_):
            mx = max(mx, float(os_.max()))
    assert cnt == 2 * 3 ** (k - 2 - j), (k, p, j, cnt)
    return {
        "count": cnt,
        "mass_frac": s_mass / total_mass,
        "mean_osc": s_osc / cnt,
        "mw_mean_osc": s_mosc / s_mass,
        "p_osc_gt_02": cnt02 / cnt,
        "mass_osc_gt_02": s_mass02 / total_mass,
        "max_osc": mx,
    }


def main():
    selftest()

    gpath = os.path.join(HERE, "renorm_global.csv")
    apath = os.path.join(HERE, "renorm_annuli.csv")
    gf = open(gpath, "w", newline="")
    af = open(apath, "w", newline="")
    gw = csv.writer(gf)
    aw = csv.writer(af)
    gw.writerow(["k", "t", "nu_tail", "haar_tail_count", "haar_tail_frac",
                 "mean_osc", "nu_E_u"])
    aw.writerow(["k", "center", "j", "count", "mass_frac", "mean_osc",
                 "mw_mean_osc", "p_osc_gt_02", "mass_osc_gt_02", "max_osc"])

    for k in range(15, 20):
        print(f"[k={k}] starting", flush=True)
        st, mean_arr, osc_arr = global_pass(k)
        for t in THRESH:
            gw.writerow([k, t, f"{st['nu_tail'][t]:.6e}", st["haar_cnt"][t],
                         f"{st['haar_frac'][t]:.6e}",
                         f"{st['mean_osc']:.6e}", f"{st['nu_E_u']:.6e}"])
        gf.flush()
        print(f"  [k={k}] nu{{osc>0.2}}={st['nu_tail'][0.2]:.4e}  "
              f"nu{{osc>0.3}}={st['nu_tail'][0.3]:.4e}  "
              f"haar_cnt02={st['haar_cnt'][0.2]}  "
              f"mean_osc={st['mean_osc']:.5f}  nu_E_u={st['nu_E_u']:.5f}",
              flush=True)

        # ---- checks against fiber-geometry.md (M7, M3) for k = 15..18 ----
        if k in REF_NU02:
            ok = True
            if abs(st["nu_tail"][0.2] - REF_NU02[k]) > 0.01 * REF_NU02[k]:
                ok = False
                print(f"  [k={k}] CHECK FAIL nu02: got "
                      f"{st['nu_tail'][0.2]:.4e}, want {REF_NU02[k]:.4e}",
                      flush=True)
            if abs(st["nu_E_u"] - REF_EU[k]) > 0.015 * REF_EU[k]:
                ok = False
                print(f"  [k={k}] CHECK FAIL E[u]: got {st['nu_E_u']:.5f}, "
                      f"want {REF_EU[k]}", flush=True)
            if st["haar_cnt"][0.2] != REF_CNT02[k]:
                ok = False
                print(f"  [k={k}] CHECK FAIL count02: got "
                      f"{st['haar_cnt'][0.2]}, want {REF_CNT02[k]}",
                      flush=True)
            assert ok, f"reference checks failed at k={k}"
            print(f"  [k={k}] checks vs fiber-geometry.md PASSED", flush=True)

        # ------------------------------ annuli ------------------------------
        t0 = time.time()
        for name, p in centers_for(k).items():
            for j in range(1, JMAX + 1):
                a = annulus_stats(k, p, j, mean_arr, osc_arr,
                                  st["total_mass"])
                aw.writerow([k, name, j, a["count"],
                             f"{a['mass_frac']:.6e}", f"{a['mean_osc']:.6e}",
                             f"{a['mw_mean_osc']:.6e}",
                             f"{a['p_osc_gt_02']:.6e}",
                             f"{a['mass_osc_gt_02']:.6e}",
                             f"{a['max_osc']:.6e}"])
            af.flush()
            print(f"  [k={k}] annuli around {name} done "
                  f"({time.time()-t0:.1f}s cumulative)", flush=True)
        del mean_arr, osc_arr
        print(f"[k={k}] complete", flush=True)

    gf.close()
    af.close()
    print(f"Wrote {gpath}\nWrote {apath}", flush=True)


if __name__ == "__main__":
    main()
