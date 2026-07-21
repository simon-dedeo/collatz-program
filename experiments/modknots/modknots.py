"""
Core library: parity necklace (K,L) -> PSL(2,Z) conjugacy class,
Rademacher function Phi, Dedekind sum, Boehm-Sontacchi weight W, defect delta.

Conventions (matches docs/notes/dynamical-hasse.md):
  T(x)=x/2 (even) or (3x+1)/2 (odd). A parity word v in {0,1}^K has L ones
  (=odd steps). K = word length = total power of 2 = sum a_i where a=(a_1..a_L)
  is the cyclic run vector (gaps between consecutive ones). Lambda = 2^K - 3^L.
  Boehm-Sontacchi weight W(v) = sum_i v_i 2^i 3^{c_i}, c_i = #{j>i: v_j=1}.
  Cycle element x_v = W(v)/Lambda; integer cycle <=> Lambda | W (delta=0) etc.

Modular realization (Ghys 'Knots and dynamics', 2007):
  M(a) = prod_{i=1..L} R^{a_i} L  in PSL(2,Z), R=[[1,1],[0,1]], L=[[1,0],[1,1]].
  #R = K, #L = L. Hyperbolic (positive word), primitive iff necklace primitive.
  Closed geodesic on the modular surface; Lorenz knot in S^3 minus trefoil.
  Rademacher Phi(M) = linking number with the trefoil = #R - #L = K - L.
"""
from fractions import Fraction
from math import log, acosh

R = ((1, 1), (0, 1))
Lm = ((1, 0), (1, 1))

def matmul(A, B):
    return ((A[0][0]*B[0][0]+A[0][1]*B[1][0], A[0][0]*B[0][1]+A[0][1]*B[1][1]),
            (A[1][0]*B[0][0]+A[1][1]*B[1][0], A[1][0]*B[0][1]+A[1][1]*B[1][1]))

def matpow(A, n):
    Rr = ((1, 0), (0, 1))
    for _ in range(n):
        Rr = matmul(Rr, A)
    return Rr

def word_to_runvector(v):
    """cyclic parity word v (tuple of 0/1, at least one 1) -> run vector a
    = cyclic gaps between consecutive ones, normalised to start at first one."""
    K = len(v)
    ones = [i for i in range(K) if v[i] == 1]
    a = []
    for j in range(len(ones)):
        nxt = ones[(j+1) % len(ones)]
        gap = (nxt - ones[j]) % K
        if gap == 0:
            gap = K
        a.append(gap)
    return a  # sum(a)=K, len(a)=L

def runvector_to_matrix(a):
    M = ((1, 0), (0, 1))
    for ai in a:
        Ra = ((1, ai), (0, 1))          # R^{a_i} closed form
        M = matmul(matmul(M, Ra), Lm)
    return M

def word_to_matrix(v):
    return runvector_to_matrix(word_to_runvector(v))

def dedekind_sum(h, k):
    """s(h,k) exact Fraction, O(log k) via Dedekind reciprocity (Euclidean).
       s(h,k) + s(k,h) = -1/4 + (h/k + k/h + 1/(hk))/12,  s depends on h mod k,
       s(1,k) = (k-1)(k-2)/(12k),  s(0,1)=0. Verified against the O(k) def."""
    assert k > 0
    h %= k
    if h == 0:
        return Fraction(0)
    s = Fraction(0)
    sign = 1
    # iterate reciprocity: s(h,k) = -s(k,h) + recip(h,k)
    while True:
        if h == 0:
            break
        if h == 1:
            s += sign * Fraction((k-1)*(k-2), 12*k)
            break
        recip = Fraction(1, 12) * (Fraction(h, k) + Fraction(k, h) + Fraction(1, h*k)) - Fraction(1, 4)
        s += sign * recip
        sign = -sign
        h, k = k % h, h
    return s

def _saw(x):
    fx = x - (x.numerator // x.denominator)  # frac part in [0,1)
    if fx == 0:
        return Fraction(0)
    return fx - Fraction(1, 2)

def rademacher(M):
    """Rademacher function Psi(M) (integer) via Dedekind-sum formula.
    A=(a b;c d) in SL2Z. Returns exact int (Fraction that is integral)."""
    (a, b), (c, d) = M
    if c == 0:
        # A = +-(1 b';0 1); Psi = b/d
        return Fraction(b, d)
    cc = abs(c)
    dd = d % cc
    s = dedekind_sum(dd, cc)
    val = Fraction(a+d, c) - 12*_sign(c)*s - 3*_sign(c*(a+d))
    return val

def _sign(x):
    return (x > 0) - (x < 0)

def bs_weight(v):
    """Boehm-Sontacchi weight W(v) = sum_i v_i 2^i 3^{c_i}."""
    K = len(v)
    # c_i = number of ones strictly after i
    suffix_ones = [0]*(K+1)
    for i in range(K-1, -1, -1):
        suffix_ones[i] = suffix_ones[i+1] + v[i]
    W = 0
    for i in range(K):
        if v[i] == 1:
            c_i = suffix_ones[i+1]
            W += (1 << i) * (3**c_i)
    return W

def lam(K, L):
    return (1 << K) - 3**L

def hyp_length(M):
    (a, b), (c, d) = M
    tr = abs(a + d)
    if tr <= 2:
        return 0.0
    return 2.0 * acosh(tr/2.0)

def analyze_word(v):
    """Return dict of invariants for parity word v (tuple)."""
    K = len(v)
    L = sum(v)
    a = word_to_runvector(v)
    M = runvector_to_matrix(a)
    (m00, m01), (m10, m11) = M
    Lambda = lam(K, L)
    W = bs_weight(v)
    delta = W % Lambda if Lambda != 0 else None
    phi = rademacher(M)
    tr = m00 + m11
    # Dedekind sum of the matrix (c>0 normalisation)
    if m10 != 0:
        ded = dedekind_sum(m11 % abs(m10), abs(m10))
    else:
        ded = Fraction(0)
    return {
        'K': K, 'L': L, 'a': tuple(a), 'Lambda': Lambda, 'W': W, 'delta': delta,
        'Phi': int(phi) if phi.denominator == 1 else float(phi),
        'trace': tr, 'ded_num': ded.numerator, 'ded_den': ded.denominator,
        'ded': float(ded), 'hyp_len': hyp_length(M),
        'M': (m00, m01, m10, m11),
    }

LOG2_3 = log(3)/log(2)
