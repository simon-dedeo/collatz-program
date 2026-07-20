#!/usr/bin/env python3
"""compare_expsum.py CPU.tsv GPU.tsv — validation-gate comparison for expsum
exhaustive TSVs.

GATES (hard fail):
  - same signature set (K, L); M, C, n_xi identical
  - div_count identical (exact); n_pos, n_real identical
  - max_ratio relative difference <= 1e-9
INFORMATIONAL (reported, not gated):
  - mean_ratio / max_alpha / mean_alpha deviations, n_zeroS,
    argmax equality (exact or conjugate xi <-> M - xi)
"""
import sys

def load(path):
    rows = {}
    with open(path) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for line in f:
            c = dict(zip(hdr, line.rstrip("\n").split("\t")))
            rows[(int(c["K"]), int(c["L"]))] = c
    return rows

def relerr(a, b):
    a, b = float(a), float(b)
    if a == b: return 0.0
    return abs(a - b) / max(abs(a), abs(b), 1e-300)

cpu, gpu = load(sys.argv[1]), load(sys.argv[2])
fail = 0
if set(cpu) != set(gpu):
    print("FAIL: signature sets differ:", set(cpu) ^ set(gpu)); fail = 1

worst_max, worst_mean, worst_alpha = 0.0, 0.0, 0.0
argmax_conj, argmax_diff, nzero_diff = 0, 0, 0
for key in sorted(set(cpu) & set(gpu)):
    a, b = cpu[key], gpu[key]
    for col in ("M", "C", "n_xi", "div_count", "n_pos", "n_real"):
        if a[col] != b[col]:
            print(f"FAIL {key}: {col} CPU={a[col]} GPU={b[col]}"); fail = 1
    r = relerr(a["max_ratio"], b["max_ratio"])
    worst_max = max(worst_max, r)
    if r > 1e-9:
        print(f"FAIL {key}: max_ratio rel diff {r:.3g} (CPU={a['max_ratio']} GPU={b['max_ratio']})")
        fail = 1
    worst_mean = max(worst_mean, relerr(a["mean_ratio"], b["mean_ratio"]))
    for col in ("max_alpha", "mean_alpha"):
        worst_alpha = max(worst_alpha, abs(float(a[col]) - float(b[col])))
    if a["argmax_xi"] != b["argmax_xi"]:
        M = int(a["M"])
        if int(a["argmax_xi"]) + int(b["argmax_xi"]) == M:
            argmax_conj += 1
        else:
            argmax_diff += 1
            print(f"note {key}: argmax CPU={a['argmax_xi']} GPU={b['argmax_xi']} (not conjugate)")
    if a["n_zeroS"] != b["n_zeroS"]:
        nzero_diff += 1
        print(f"note {key}: n_zeroS CPU={a['n_zeroS']} GPU={b['n_zeroS']}")

n = len(set(cpu) & set(gpu))
print(f"compared {n} signatures")
print(f"worst max_ratio rel diff : {worst_max:.3g}   (gate 1e-9)")
print(f"worst mean_ratio rel diff: {worst_mean:.3g}  (informational)")
print(f"worst alpha abs diff     : {worst_alpha:.3g} (informational)")
print(f"argmax: {argmax_conj} conjugate flips, {argmax_diff} other diffs, n_zeroS diffs: {nzero_diff}")
print("GATE: " + ("FAIL" if fail else "PASS"))
sys.exit(fail)
