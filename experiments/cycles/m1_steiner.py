"""The m=1 (Steiner) stratum at finite places: a concrete 'collapse to Baker'.

An m=1 cycle has all L odd steps contiguous: word 1^L 0^{K-L}, so
    W = 3^L - 2^L      (telescoping; docs/notes/dynamical-hasse.md Sec 3).
A positive m=1 cycle exists iff  Lambda=2^K-3^L  divides  W=3^L-2^L  (with n>=1).
Steiner 1977 proved this never happens (except trivial) -- historically the
FIRST Baker/linear-forms application to Collatz.

Finite-place reduction (elementary, exact): since 3^L == 2^K (mod Lambda) and
Lambda is odd,
    Lambda | (3^L - 2^L)  <=>  Lambda | (2^K - 2^L) = 2^L(2^{K-L}-1)
                          <=>  Lambda | (2^{K-L} - 1).
So the m=1 cycle is EXCLUDED at finite places as soon as
    0 < 2^{K-L} - 1 < Lambda = 2^K - 3^L,                        (*)
a pure size comparison, NO linear-forms-in-logs.  This script verifies the
reduction and (*) across near-convergents.

The catch (the collapse): (*) is 2^{K-L} < 2^K - 3^L, i.e. a LOWER BOUND on
|2^K - 3^L|.  For fixed K it is a finite integer check (unconditional).  But a
UNIFORM guarantee that (*) holds for all large K is exactly a Baker-type bound
|2^K - 3^L| > 2^{K-L} ~ 2^{0.37K}: were log2(3) Liouville, Lambda could be tiny
and (*) could fail.  Thus the finite-place m=1 exclusion is unconditional PER K
but needs Baker for a uniform theorem -- it collapses to the archimedean input.
"""
import csv
from math import log, comb

LOG2, LOG3 = log(2.0), log(3.0)

def main():
    rows = []
    nontrivial_hits = []      # Lambda>1 with Lambda|W  (would be a genuine cycle)
    bound_fail = []           # Lambda>1 with 2^(K-L)-1 >= Lambda
    min_slack = 10**9
    for K in range(2, 4001):
        L = int(K * LOG2 / LOG3)          # near-convergent, smallest Lambda>0
        Lam = 2**K - 3**L
        if Lam <= 0:
            continue
        W = 3**L - 2**L
        R = 2**(K - L) - 1
        div_W = (W % Lam == 0)
        assert div_W == (R % Lam == 0), (K, L)   # the reduction, verified exactly
        bound = (0 < R < Lam)             # elementary exclusion (*)
        slack_bits = Lam.bit_length() - R.bit_length()
        if Lam > 1:
            if div_W:
                nontrivial_hits.append((K, L, Lam))
            if not bound:
                bound_fail.append((K, L))
            min_slack = min(min_slack, slack_bits)
        if K <= 200 or K % 200 == 0:
            rows.append((K, L, Lam.bit_length(), R.bit_length(), int(div_W),
                         int(bound), slack_bits))
    with open("m1_steiner.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["K", "L", "Lambda_bits", "R=2^(K-L)-1_bits", "Lambda_divides_W",
                    "size_bound(*)_holds", "slack_bits"])
        w.writerows(rows)
    print("K=2..4000 near-convergent m=1 (Steiner) stratum, Lambda>1:")
    print(f"  nontrivial cycles (Lambda|W): {nontrivial_hits}  (empty = all excluded)")
    print(f"  size bound (*) 2^(K-L)-1 < Lambda fails at: {bound_fail}  (empty = always holds)")
    print(f"  min slack of (*): {min_slack} bits  (Lambda exceeds 2^(K-L)-1 by >= this)")
    print("  only unit-stratum trivial cycle (2,1)/Lambda=1 divides W; excluded elsewhere.")
    print("  wrote m1_steiner.csv")

if __name__ == "__main__":
    main()
