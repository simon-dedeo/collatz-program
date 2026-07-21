"""Local (mod m) counts of admissible Collatz cycle words.

For a signature (K,L): a "word" is v in {0,1}^K with exactly L ones.  Its
Boehm-Sontacchi weight is
    W(v) = sum_{j: v_j=1} 2^j * 3^{c_j},   c_j = #{ones strictly right of j}
      = sum_{i=0}^{L-1} 3^{L-1-i} 2^{b_i},  b_0<...<b_{L-1} the one-positions.
A length-(K,L) integer cycle exists  =>  Lambda=2^K-3^L divides W(v) for some v
(the necklace congruence; docs/notes/dynamical-hasse.md Thm 2/3).  This module
counts, for a modulus m,
    N_m(K,L) = #{words of shape (K,L) : W(v) == 0 (mod m)}
by the transfer-matrix DP already used in experiments/expsum (there over
Lambda; here over any divisor m).  Two backends:
  * count_mod_prime_field(...) -> exact N_m via big-int DP (feasible small m,K)
  * nonzero_mod_Q(...)         -> whether N_m>0, via DP over F_Q (Q a big prime);
                                  N_m mod Q != 0 certifies N_m>0 (no obstruction).

A "local obstruction at m" is N_m == 0: NO word of shape (K,L) is divisible by
m, hence no cycle -- an exclusion located at finite places, invisible to the
archimedean (Baker/CF) method.  See docs/notes/cycle-finite-places.md.
"""
import numpy as np
from math import comb

# right-to-left DP.  State rho = ones placed so far (all lie to the right of
# the current position, so a one placed now has c_j = rho).  dp[rho, w] counts
# suffix choices with rho ones and partial weight == w (mod m).
def _dp_counts(K, L, m, dtype=object):
    dp = np.zeros((L + 1, m), dtype=dtype)
    dp[0, 0] = 1
    p2 = 1  # 2^j mod m, j starts at K-1 going down; we track 2^j incrementally
    # precompute 2^j for j=K-1..0 : easier to iterate j from 0..K-1 with pow.
    pow2 = [pow(2, j, m) for j in range(K)]
    pow3 = [pow(3, r, m) for r in range(L + 1)]
    for j in range(K - 1, -1, -1):
        two_j = pow2[j]
        for rho in range(L - 1, -1, -1):
            if not dp[rho].any():
                continue
            shift = (two_j * pow3[rho]) % m
            dp[rho + 1] = dp[rho + 1] + np.roll(dp[rho], shift)
    return dp

def count_mod(K, L, m):
    """Exact N_m(K,L) as a Python int (uses big-int object array)."""
    dp = _dp_counts(K, L, m, dtype=object)
    return int(dp[L, 0])

def _dp_field(K, L, m, Q):
    """DP with counts reduced mod prime Q (fast int64). Returns N_m mod Q."""
    dp = np.zeros((L + 1, m), dtype=np.int64)
    dp[0, 0] = 1
    pow2 = [pow(2, j, m) for j in range(K)]
    pow3 = [pow(3, r, m) for r in range(L + 1)]
    for j in range(K - 1, -1, -1):
        two_j = pow2[j]
        for rho in range(L - 1, -1, -1):
            row = dp[rho]
            if not row.any():
                continue
            shift = (two_j * pow3[rho]) % m
            dp[rho + 1] = (dp[rho + 1] + np.roll(row, shift)) % Q
    return int(dp[L, 0] % Q)

_BIGQ = 2305843009213693951  # 2^61 - 1, Mersenne prime

def nonzero_mod_Q(K, L, m, Q=_BIGQ):
    """True if N_m(K,L) mod Q != 0  =>  N_m>0 (no local obstruction at m).
    (If it returns False, N_m is a multiple of Q -- almost surely 0, but
    re-test with a second Q to be sure before claiming an obstruction.)"""
    return _dp_field(K, L, m, Q) != 0

if __name__ == "__main__":
    # sanity: the trivial-cycle carrier (K,L)=(2t,t), Lambda=2^{2t}-3^t.
    # and the (11,7)/139 hit.
    import sys
    # (11,7): 139 | W has exactly 11 solutions (one necklace), per dynamical-hasse.
    n = count_mod(11, 7, 139)
    print("N_139(11,7) =", n, "(expect 11: the -17 necklace, all rotations)")
    # cross-check exact vs mod-Q
    print("nonzero_mod_Q(11,7,139):", nonzero_mod_Q(11, 7, 139))
    # small equidistribution: N_p * p / C(K,L) ~ 1 for small p, no divisibility of C.
    for (K, L, p) in [(30, 19, 5), (30, 19, 7), (40, 25, 11), (60, 38, 13)]:
        N = count_mod(K, L, p)
        C = comb(K, L)
        print(f"(K,L)=({K},{L}) p={p}: N_p={N}  C/p={C/p:.3e}  N_p*p/C={N*p/C:.4f}")
    # a COMPUTABLE single-prime finite-place obstruction: (21,13), Lambda=502829
    # is PRIME and < C, and N_Lambda=0 -- shape (21,13) excluded with no Baker.
    K, L, m = 21, 13, 502829
    N = _dp_field(K, L, m, _BIGQ)
    assert N == _dp_field(K, L, m, _BIGQ - 2)  # confirm ==0 mod two primes
    print(f"(21,13) Lambda=502829 (prime), C={comb(21,13)}: N_Lambda={'0 => finite-place OBSTRUCTION' if N==0 else N}")
