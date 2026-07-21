#!/usr/bin/env python3
"""scan.py -- drive ./crit over the critical-drift map families.

modes:
  value   [N] [CAP] [OUT]   value-criticality sweep (excursion tau,h vs drift):
                            logwalk(D,k) mixing family + d=2 odd brackets
                            + exact-zero degenerate references
  counter [N] [CAP] [OUT]   counter-criticality sweep (Antihydra genre):
                            fixed mixing value map, parity-counter weights
                            swept across zero counter-drift; dumps tc CCDFs

logwalk(D,k): modulus D, up-multiplier K=D^2+1 (always coprime to D => mixing),
k residues get a=K (value x ~D), the rest a=1 (value /~D), b_i=i.  Per-step
log-value step is +-ln D; net drift mu(D,k) tunable toward 0 but never 0
(gcd obstruction).  This is a genuine deterministic Collatz-like map that
realises a multiplicative random walk of tunable drift at fixed variance.
"""
import sys, os, math, subprocess

BIN = "./crit"
HDR = ("label,d,vdrift,edrift,cdrift,cdrift_meas,p_odd,f_drop,f_escape,f_cap,"
       "f_hit,f_nohit,mean_ltau,med_tau,mean_h,mean_ltc,med_tc,blockH,condH,"
       "max_h,h_p99,wtau,tau_p99,wtc")

def run(label, d, rows, wE, wO, L, N, cap, outdir):
    args = [BIN, label, str(d)]
    for a, b in rows:
        args += [str(a), str(b)]
    args += [str(wE), str(wO), str(L), str(N), str(cap), outdir]
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write("FAIL %s: %s\n" % (label, r.stderr.strip()))
        return None
    return r.stdout.strip()

def logwalk_rows(D, k):
    """k up-residues (a=K), D-k down (a=1); b_i=i.  Returns (rows, K, drift)."""
    K = D * D + 1                      # gcd(K,D)=1 for all D
    rows = [((K if i < k else 1), i) for i in range(D)]
    drift = (k * math.log(K / D) + (D - k) * math.log(1.0 / D)) / D
    return rows, K, drift

def value_maps():
    maps = []  # (label, d, rows)
    # -- exact-zero DEGENERATE references (the (1,4)/(4,1)/(2,2) critical line) --
    maps.append(("DEG_1_4", 2, [(1, 0), (4, 1)]))
    maps.append(("DEG_4_1", 2, [(4, 0), (1, 1)]))
    maps.append(("DEG_2_2", 2, [(2, 1), (2, 1)]))
    # -- d=2 odd-multiplier mixing brackets (the coarse qx+1 axis) --
    for a0, a1 in [(1,3),(3,1),(1,5),(5,1),(1,7),(7,1),(3,3),(3,5),(5,3),
                   (1,9),(9,1),(5,5),(3,7),(7,3),(1,11),(11,1)]:
        maps.append(("d2_%d_%d" % (a0, a1), 2, [(a0, 0), (a1, 1)]))
    # -- logwalk(D,k): fine, fixed-variance drift sweep toward criticality --
    for D in [4, 6, 8, 12, 16, 24]:
        for k in range(1, D):
            rows, K, drift = logwalk_rows(D, k)
            maps.append(("LW_D%d_k%d" % (D, k), D, rows))
    return maps

def counter_maps():
    """(label, d, rows, wE, wO, L) : parity-counter weight sweep."""
    bases = [
        ("HYD", 2, [(3, 0), (3, 1)]),          # x3/2 Hydra: p_odd~1/2, short stream
        ("LW42", 4, [(17, 0), (17, 1), (1, 2), (1, 3)]),  # near-crit, long stream
    ]
    weights = [(1,-1),(1,-2),(1,-3),(2,-3),(3,-4),   # attracting (drift toward -L)
               (2,-1),(3,-1),(3,-2),(4,-3),(5,-4)]   # repelling  (Antihydra genre)
    Ls = [1, 2, 4]
    out = []
    for bl, d, rows in bases:
        for wE, wO in weights:
            for L in Ls:
                out.append(("%s_w%d_%d_L%d" % (bl, wE, wO, L), d, rows, wE, wO, L))
    return out

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "value"
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 5_000_000
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 200_000
    outdir = sys.argv[4] if len(sys.argv) > 4 else "results"
    os.makedirs(outdir, exist_ok=True)
    rows_out = [HDR]
    if mode == "value":
        for lbl, d, rows in value_maps():
            # DEG_2_2 is the pure-additive translation trap (100% step-cap by
            # construction: value never drops below start nor overflows); it
            # only serves as a rigid/zero-entropy reference, so cap it small.
            c = 3000 if lbl.startswith("DEG_2") else cap
            r = run(lbl, d, rows, 1, -1, 1, N, c, outdir)
            if r:
                rows_out.append(r)
                sys.stderr.write(lbl + " ok\n")
        fn = os.path.join(outdir, "summary_value.csv")
    elif mode == "counter":
        for lbl, d, rows, wE, wO, L in counter_maps():
            r = run(lbl, d, rows, wE, wO, L, N, cap, outdir)
            if r:
                rows_out.append(r)
                sys.stderr.write(lbl + " ok\n")
        fn = os.path.join(outdir, "summary_counter.csv")
    else:
        sys.stderr.write("unknown mode\n"); sys.exit(1)
    with open(fn, "w") as f:
        f.write("\n".join(rows_out) + "\n")
    sys.stderr.write("wrote %s (%d maps)\n" % (fn, len(rows_out) - 1))

if __name__ == "__main__":
    main()
