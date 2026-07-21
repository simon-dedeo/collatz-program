"""Shared helpers for the renormalization-at--1 analysis (renorm_*.py).

State space at level k: [3^k] = {m mod 3^k : m ≡ 2 (mod 3)}, indexed by
i = (m-2)/3.  Certified feasible subeigenvectors cert_k{K}_C.npy are exact
int64 vectors c ≥ 1 satisfying c ≤ F_λ(c) with relative slack ~1e-7 (see
cert_k*_report.json); numerical eigenfunction language below is approximate
up to that margin.

Local coordinates at -1: the depth-ν ball around -1 at level k is
  B_ν = { -1 + u·3^{k-ν} mod 3^k : u mod 3^ν },
i.e. all states agreeing with -1 in the top ... (3-adically: within distance
3^{-(k-ν)}).  All are ≡ 8 (mod 9) when k-ν ≥ 2.
"""
import json, math, os
import numpy as np

ALPHA = math.log(3, 2)
HERE = os.path.dirname(os.path.abspath(__file__))

def load_C(k, mmap=True):
    """Certified feasible subeigenvector as an exact int64 array."""
    return np.load(os.path.join(HERE, f"cert_k{k}_C.npy"),
                   mmap_mode="r" if mmap else None)

def lam_of(k):
    """Certified rational lambda for level k, as float and Fraction."""
    from fractions import Fraction
    rep = json.load(open(os.path.join(HERE, f"cert_k{k}_report.json")))
    fr = Fraction(rep["lambda"])
    return float(fr), fr

def state(k, u, nu):
    """Level-k state -1 + u*3^(k-nu) mod 3^k (u may be any int)."""
    M = 3 ** k
    return (-1 + u * 3 ** (k - nu)) % M

def idx(m):
    """Index of state m (must be ≡ 2 mod 3) in the C array."""
    assert m % 3 == 2, m
    return (m - 2) // 3

def cval(C, k, u, nu):
    """c-value at -1 + u*3^(k-nu), exact int."""
    return int(C[idx(state(k, u, nu))])

def c_at(C, k, m):
    """c-value at arbitrary integer m (reduced mod 3^k), exact int."""
    return int(C[idx(m % 3 ** k)])

def fiber_of(C, k, r):
    """Values on the level-k fiber over level-(k-1) state r: lifts r+j*3^(k-1)."""
    M1 = 3 ** (k - 1)
    return [c_at(C, k, (r % M1) + j * M1) for j in range(3)]

def eig_terms(C, k, m, lam):
    """(c(m), transport term, branch term, weight, min-lift-index) at state m."""
    M = 3 ** k
    m = m % M
    c_m = c_at(C, k, m)
    t = lam ** -2 * c_at(C, k, 4 * m)
    b = m % 9
    if b == 5:
        return c_m, t, 0.0, 0.0, None
    if b == 2:
        r, w = ((4 * m - 2) // 3) % 3 ** (k - 1), lam ** (ALPHA - 2)
    else:
        r, w = ((2 * m - 1) // 3) % 3 ** (k - 1), lam ** (ALPHA - 1)
    lifts = [c_at(C, k, r + j * 3 ** (k - 1)) for j in range(3)]
    jmin = int(np.argmin(lifts))
    return c_m, t, w * min(lifts), w, jmin
