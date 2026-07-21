"""Factorization structure of Lambda = 2^K - 3^L at near-convergent (K,L), and
what it says about the FEASIBILITY of a finite-place (single prime power)
obstruction to the necklace congruence Lambda | W(v).

Key inequality (docs/notes/cycle-finite-places.md):
  #admissible words C(K,L) ~ 2^{0.95K};  heuristically N_{p^e} ~ C/p^e.
  A single-prime-power obstruction (N_{p^e}=0, an exclusion orthogonal to Baker)
  therefore needs  p^e >~ C ~ Lambda^{0.95}  (in the positive window Lambda~2^K).
So the finite-place route is only *available* at (K,L) where Lambda has a prime
(power) factor exceeding Lambda^{0.95} -- i.e. Lambda is "nearly prime".

Two modes:
  pplus  KMIN KMAX  : FULL factorization (small K); records P+(Lambda) and the
                      event P+(Lambda) > Lambda^{0.95} (obstruction available).
                      Compares its frequency to the Dickman prediction ~5%.
  feas   KMIN KMAX  : trial-divide to 1e5 + isprime(cofactor) (any K, incl.
                      convergents); records smooth part, cofactor bits, and
                      whether cofactor is a proven prime > Lambda^{0.95}.
"""
import sys, csv, signal
from math import comb, log
from sympy import factorint, isprime

LOG2, LOG3 = log(2.0), log(3.0)
ALPHA = 0.95  # obstruction-availability threshold exponent (~ log2 C / log2 Lambda)

CONVERGENTS = [(2,1),(3,2),(8,5),(19,12),(65,41),(84,53),(485,306),(1054,665)]

def pplus_row(K, L):
    Lam = 2**K - 3**L
    if Lam <= 1:
        return None
    C = comb(K, L)
    f = factorint(Lam)
    primes = sorted(f)
    pplus = primes[-1]
    pplus_bits = pplus.bit_length()
    # log_Lambda(P+) and log_Lambda(largest prime POWER)
    lg = lambda x: log(x) / log(Lam)
    maxpp = max(p**e for p, e in f.items())
    a_pplus = lg(pplus)
    a_maxpp = lg(maxpp)
    available = int(maxpp > C)          # prime power exceeds word count
    return dict(K=K, L=L, Lam_bits=Lam.bit_length(), C_bits=C.bit_length(),
                nfactors=len(primes), pplus_bits=pplus_bits,
                a_pplus=round(a_pplus, 4), a_maxpp=round(a_maxpp, 4),
                maxpp_bits=maxpp.bit_length(), obstr_available=available,
                factorization=";".join(f"{p}^{e}" if e > 1 else str(p)
                                       for p, e in sorted(f.items()))[:120])

def feas_row(K, L):
    Lam = 2**K - 3**L
    if Lam <= 1:
        return None
    C = comb(K, L)
    n = Lam
    smooth = {}
    d = 2
    while d < 100000 and d * d <= n:
        while n % d == 0:
            smooth[d] = smooth.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    cof = n
    cof_prime = (cof > 1 and isprime(cof))
    smooth_bits = (Lam // cof).bit_length() if cof > 1 else Lam.bit_length()
    # available iff a proven prime power exceeds C
    maxpp = max([p**e for p, e in smooth.items()] + [1])
    if cof_prime:
        maxpp = max(maxpp, cof)
    return dict(K=K, L=L, Lam_bits=Lam.bit_length(), C_bits=C.bit_length(),
                smooth_bits=smooth_bits, cofactor_bits=(0 if cof == 1 else cof.bit_length()),
                cofactor_prime=int(cof_prime),
                a_maxpp=round(log(maxpp) / log(Lam), 4) if maxpp > 1 else 0.0,
                obstr_available=int(maxpp > C))

def main():
    mode = sys.argv[1]
    kmin, kmax = int(sys.argv[2]), int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else f"lambda_{mode}.csv"
    rows = []
    for K in range(kmin, kmax + 1):
        L = int(K * LOG2 / LOG3)
        r = pplus_row(K, L) if mode == "pplus" else feas_row(K, L)
        if r:
            rows.append(r)
        print(f"K={K} done", file=sys.stderr, flush=True)
    if mode == "feas":
        for (K, L) in CONVERGENTS:
            r = feas_row(K, L)
            if r:
                r["note"] = "convergent"
                rows.append(r)
    cols = list(rows[0].keys())
    if "note" not in cols:
        cols.append("note")
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            r.setdefault("note", "")
            w.writerow(r)
    navail = sum(r["obstr_available"] for r in rows)
    print(f"[{mode}] rows={len(rows)}  obstr_available (maxpp>C) = {navail} "
          f"({100*navail/len(rows):.1f}%)")
    if mode == "pplus":
        import statistics
        aps = [r["a_pplus"] for r in rows]
        print(f"  a_pplus=log_Lambda(P+): mean={statistics.mean(aps):.3f} "
              f"median={statistics.median(aps):.3f} max={max(aps):.3f}")
    print(f"wrote {out}")

if __name__ == "__main__":
    main()
