#!/usr/bin/env python3
# run_scan.py — drive ./crit over families of maps, collect summary.csv.
# Usage: run_scan.py <mode> <N> <STEPCAP> <OUTDIR>
#   mode = value | counter | fine
import sys, subprocess, math, itertools, os

HDR = ("label,d,vdrift,edrift,cdrift,cdrift_meas,p_odd,f_drop,f_escape,f_cap,"
       "f_hit,f_nohit,mean_ltau,med_tau,mean_h,mean_ltc,med_tc,blockH,condH")

def drift(a, d):
    return sum(math.log((x if x else 1)/d) for x in a)/len(a)

def run(label, d, rows, wE, wO, Lb, N, cap, outdir):
    # rows = list of (a_i,b_i)
    args = ["./crit", label, str(d)]
    for a,b in rows: args += [str(a), str(b)]
    args += [str(wE), str(wO), str(Lb), str(N), str(cap), outdir]
    out = subprocess.run(args, capture_output=True, text=True)
    if out.returncode != 0:
        sys.stderr.write("FAIL %s: %s\n" % (label, out.stderr.strip())); return None
    return out.stdout.strip()

def value_maps():
    maps = []
    # d=2 odd-multiplier sweep (mixing, high variance)
    for a0,a1 in [(1,3),(3,1),(1,5),(5,1),(1,7),(7,1),(1,9),(1,11),(1,13),(1,15),
                  (3,3),(3,5),(5,3),(5,5),(3,7),(5,7)]:
        maps.append(("d2_%d_%d"%(a0,a1), 2, [(a0,0),(a1,1)]))
    # d=2 naive-critical DEGENERATE line (arithmetic obstruction demo)
    maps.append(("DEG_1_4", 2, [(1,0),(4,1)]))
    maps.append(("DEG_4_1", 2, [(4,0),(1,1)]))
    maps.append(("DEG_2_2", 2, [(2,0),(2,1)]))
    maps.append(("DEG_2_2b",2, [(2,1),(2,1)]))
    # d=4 high-variance mixing: all length-4 multisets of odd {1,3,5,7,9}
    for combo in itertools.combinations_with_replacement([1,3,5,7,9], 4):
        lbl = "d4_" + "".join(str(c) for c in combo)
        rows = [(combo[i], i) for i in range(4)]
        maps.append((lbl, 4, rows))
    return maps

def counter_maps(base_rows, d):
    # sweep counter weights & boundary on a fixed value map (the parity source)
    ws = [(1,-1),(2,-1),(1,-2),(3,-2),(2,-3),(3,-1),(1,-3),(2,-2),(4,-3),(3,-4),
          (1,1),(4,-5),(5,-4)]
    Ls = [1,2,4]
    out = []
    for (wE,wO) in ws:
        for Lb in Ls:
            lbl = "c_%d_%d_L%d" % (wE,wO,Lb)
            out.append((lbl, d, base_rows, wE, wO, Lb))
    return out

def main():
    mode = sys.argv[1]; N = int(sys.argv[2]); cap = int(sys.argv[3]); outdir = sys.argv[4]
    os.makedirs(outdir, exist_ok=True)
    rows_out = [HDR]
    if mode == "value":
        for lbl,d,rows in value_maps():
            r = run(lbl,d,rows,1,-1,1,N,cap,outdir)
            if r: rows_out.append(r); sys.stderr.write(lbl+" done\n")
        fn = os.path.join(outdir,"summary_value.csv")
    elif mode == "counter":
        # base = a near-fair, long-runway subcritical mixing map (chosen from value scan)
        base = [(3,0),(3,1),(5,2),(5,3)]   # d=4 (3,3,5,5): p_odd~0.35, f_escape~0
        for lbl,d,rows,wE,wO,Lb in counter_maps(base,4):
            r = run(lbl,d,rows,wE,wO,Lb,N,cap,outdir)
            if r: rows_out.append(r); sys.stderr.write(lbl+" done\n")
        fn = os.path.join(outdir,"summary_counter.csv")
    else:
        sys.stderr.write("unknown mode\n"); sys.exit(1)
    with open(fn,"w") as f: f.write("\n".join(rows_out)+"\n")
    sys.stderr.write("wrote %s (%d maps)\n" % (fn, len(rows_out)-1))

if __name__ == "__main__":
    main()
