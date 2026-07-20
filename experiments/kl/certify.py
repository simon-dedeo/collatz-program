#!/usr/bin/env python3
"""
certify.py -- exact-rational certification of feasible points for the
Krasikov-Lagarias LP family L^NT_k(lambda)  (KL 2002/2003, arXiv:math/0205002).

WHAT IS CERTIFIED
-----------------
For a given level k >= 2 and a rational lambda = A / 10^7 with 1 < lambda <= 2,
we certify in EXACT integer arithmetic that the linear program L^NT_k(lambda)
of KL (eqs. (2.7)-(2.14)) has a feasible solution.  By KL Theorem 2.2 this
implies  phi^m_k(y) >= Delta_1 * c^m_k * lambda^y  for all m in [3^k], y >= 0,
with Delta_1 = 1/(4 max c^m_k), and hence (KL Theorem 6.1 mechanism)
pi_a(x) >= x^gamma' for every fixed gamma' < gamma = log2(lambda), every
positive a != 0 mod 3, and all x >= x0(a).

THE FEASIBILITY SYSTEM (auxiliaries eliminated at their maximal values,
KL p.5 lines after (2.15); see THEOREM.md section 2)
    for every m in [3^k] = {m mod 3^k : m == 2 mod 3},  with c^m >= 1:
      m == 2 (mod 9):  c^m <= lam^-2 c^{4m} + lam^(a-2) * min_j c^{r2 + j 3^(k-1)}
                       r2 = (4m-2)/3 mod 3^(k-1)
      m == 5 (mod 9):  c^m <= lam^-2 c^{4m}
      m == 8 (mod 9):  c^m <= lam^-2 c^{4m} + lam^(a-1) * min_j c^{r8 + j 3^(k-1)}
                       r8 = (2m-1)/3 mod 3^(k-1)
    (4m reduced mod 3^k;  a = alpha = log2 3.)

HANDLING THE IRRATIONAL EXPONENT alpha = log2(3)
------------------------------------------------
KL do not document an exact-arithmetic device (Thm 6.1 just cites a feasible
solution "found by computer" at lambda = 1.7922310).  We therefore certify a
STRICTLY TIGHTER system: replace the two irrational coefficients by rational
lower bounds W2 <= lam^(alpha-2), W8 <= lam^(alpha-1)  (lam^-2 is exactly
rational).  Since both coefficients multiply nonnegative quantities on the
<=-side, feasibility of the tightened system implies feasibility of the true
L^NT_k(lambda).  W2, W8 are certified by pure integer inequalities:

  * P/Q = 50508/31867 is a continued-fraction convergent of alpha from below;
    2^P < 3^Q  (checked exactly)  ==>  P/Q < alpha.
  * lambda > 1  ==>  lam^(alpha-2) > lam^(P/Q-2) and lam^(alpha-1) > lam^(P/Q-1)
    (t -> lam^t strictly increasing).
  * W2 = B2/10^15 <= lam^(P/Q-2)  <==>  B2^Q * A^(2Q-P) <= 10^(15Q) * 10^(7(2Q-P))
    W8 = B8/10^15 <= lam^(P/Q-1)  <==>  B8^Q * 10^(7(P-Q)) <= A^(P-Q) * 10^(15Q)
    -- finite integer comparisons, verified exactly here.

CERTIFICATE FORMAT (JSON)
-------------------------
  {"k":..., "A":..., "SC_L":10^7, "B2":..., "B8":..., "SC_W":10^15,
   "P":50508, "Q":31867, "SC_C":10^12, "C":[...3^(k-1) integers...]}
meaning lambda = A/SC_L, W2 = B2/SC_W, W8 = B8/SC_W, c^m = C[i]/SC_C where i
indexes the ascending list of residues m == 2 mod 3 in [0, 3^k).

VERIFICATION ('verify' mode) rebuilds the residue system from k with pure
integer arithmetic and checks EVERY constraint exactly:
  (i)    10^7 < A <= 2*10^7                                  (1 < lambda <= 2)
  (ii)   2^P < 3^Q                                           (P/Q < alpha)
  (iii)  B2^Q * A^(2Q-P) <= SC_W^Q * SC_L^(2Q-P)             (W2 <= lam^(P/Q-2))
  (iv)   B8^Q * SC_L^(P-Q) <= A^(P-Q) * SC_W^Q               (W8 <= lam^(P/Q-1))
  (v)    C[i] >= SC_C for all i                              (c >= 1)
  (vi)   for all i:  C[i]*A^2*SC_W <= C[4m]*SC_L^2*SC_W + B*(A^2)*min3(C)
         with B = B2, B8, or absent according to m mod 9     (L1)-(L4)
All of (i)-(vi) together imply L^NT_k(A/SC_L) is feasible (with auxiliaries
c-bar of (2.15) and C^max = max c), i.e. the hypotheses of KL Thm 2.2 hold.

LARGE LEVELS (k >= 15)
----------------------
For k >= 15 the index maps are computed arithmetically (idx(m) = (m-2)/3 for
m == 2 mod 3; no dictionaries) and verification is chunked; the certificate
vector C is stored as an int64 .npy sidecar (cert_k{k}_C.npy, sha256 pinned in
the JSON) instead of inline JSON. The candidate eigenvector may be supplied
from a precomputed file ('genvec' mode, e.g. a GPU run) -- it is only a
candidate: it is refined by power iteration at lambda_cert if needed, rounded
down, and then EVERY constraint is re-checked in exact integer arithmetic
locally, so no correctness burden rests on the GPU computation.

Usage:
  python3 certify.py selftest
  python3 certify.py gen K [--drop D]     # build + exact-verify certificate for level K
  python3 certify.py genvec K VEC.npy LAMHAT [--drop D1,D2,...]
                                          # same, but candidate eigenvector from file
  python3 certify.py verify cert_kK.json  # independent exact re-verification
"""

import json, math, os, sys, time
import numpy as np

ALPHA = math.log2(3.0)
SC_L = 10**7          # lambda grid
SC_C = 10**12         # c grid
SC_W = 10**15         # weight grid
P, Q = 50508, 31867   # convergent of log2(3) from below

HERE = os.path.dirname(os.path.abspath(__file__))


# ----------------------------------------------------------------------
# residue system, straight from the paper (pure integers)
# ----------------------------------------------------------------------
def build_exact(k):
    """Return (ms, i4m, btype, refs) for level k.
    ms    : ascending residues m == 2 mod 3 in [0, 3^k)         (paper's [3^k])
    i4m   : index of 4m mod 3^k                                 ((L1)-(L3) first term)
    btype : m mod 9 in {2,5,8}                                  (branch selector)
    refs  : for btype 2/8 the triple of indices of r + j*3^(k-1), j=0,1,2
            with r = (4m-2)/3 mod 3^(k-1) resp. (2m-1)/3 mod 3^(k-1)  ((2.15) triple)
    """
    M, Mk1 = 3**k, 3**(k-1)
    ms = list(range(2, M, 3))
    idx = {m: i for i, m in enumerate(ms)}
    i4m, btype, refs = [], [], []
    for m in ms:
        i4m.append(idx[(4*m) % M])
        r9 = m % 9
        btype.append(r9)
        if r9 == 2:
            r = ((4*m - 2)//3) % Mk1
            assert r % 3 == 2
            refs.append((idx[r], idx[r+Mk1], idx[r+2*Mk1]))
        elif r9 == 8:
            r = ((2*m - 1)//3) % Mk1
            assert r % 3 == 2
            refs.append((idx[r], idx[r+Mk1], idx[r+2*Mk1]))
        else:
            assert r9 == 5
            refs.append(None)
    return ms, i4m, btype, refs


# ----------------------------------------------------------------------
# float stage: nonlinear Perron (Collatz-Wielandt) iteration
# ----------------------------------------------------------------------
def np_system(k):
    ms, i4m, btype, refs = build_exact(k)
    n = len(ms)
    i4m_a = np.asarray(i4m, dtype=np.int64)
    bt = np.asarray(btype, dtype=np.int64)
    ref_a = np.zeros((n, 3), dtype=np.int64)
    for i, r in enumerate(refs):
        if r is not None:
            ref_a[i] = r
    return n, i4m_a, bt, ref_a


def apply_F(c, lam, n, i4m_a, bt, ref_a, w2=None, w8=None):
    """F_lam(c): RHS of the reduced feasibility system, componentwise."""
    if w2 is None:
        w2 = lam**(ALPHA-2)
    if w8 is None:
        w8 = lam**(ALPHA-1)
    w4 = lam**-2.0
    wvec = np.where(bt == 2, w2, np.where(bt == 8, w8, 0.0))
    m3 = np.minimum(np.minimum(c[ref_a[:, 0]], c[ref_a[:, 1]]), c[ref_a[:, 2]])
    return w4 * c[i4m_a] + wvec * m3


def power_iterate(lam, sysk, c0=None, iters=4000, tol=1e-14):
    """Iterate c <- F(c)/max F(c). Returns (c, cwlo, cwhi): cwlo <= rho <= cwhi."""
    n, i4m_a, bt, ref_a = sysk
    c = np.ones(n) if c0 is None else c0.copy()
    cwlo = cwhi = None
    prev = None
    for t in range(iters):
        f = apply_F(c, lam, *sysk)
        ratio = f / c
        cwlo, cwhi = ratio.min(), ratio.max()
        c = f / f.max()
        if prev is not None and abs(cwhi - cwlo) < tol * cwhi and t > 50:
            break
        prev = cwhi
    return c, cwlo, cwhi


def solve_lambda(k, sysk, tol=1e-10):
    """Secant on log rho(lambda) for the crossing rho = 1 (float estimate)."""
    l0, l1 = 1.70, 1.85
    c = None
    c, lo, hi = power_iterate(l0, sysk, c, iters=3000)
    g0 = math.log(0.5*(lo+hi))
    c, lo, hi = power_iterate(l1, sysk, c, iters=3000)
    g1 = math.log(0.5*(lo+hi))
    for _ in range(60):
        if abs(g1 - g0) < 1e-17:
            break
        l2 = l1 - g1*(l1-l0)/(g1-g0)
        l2 = min(max(l2, 1.05), 2.4)
        if abs(l2 - l1) < tol:
            l1 = l2
            break
        l0, g0 = l1, g1
        l1 = l2
        c, lo, hi = power_iterate(l1, sysk, c, iters=3000)
        g1 = math.log(0.5*(lo+hi))
    return l1, c


# ----------------------------------------------------------------------
# large-k machinery: dict-free arithmetic indexing, chunked exact verify
# ----------------------------------------------------------------------
def big_indices(k, chunk=1 << 24):
    """Same residue system as build_exact(), via arithmetic indexing only:
    for m == 2 (mod 3), index i = (m-2)/3, m = 3i+2. Returns numpy arrays
    (n, i4, mask2, mask8, refbase, step): the min-triple of row i is
    {refbase[i], refbase[i]+step, refbase[i]+2*step}, step = 3^(k-2).
    Built in chunks to bound peak memory at large k."""
    M, Mk1 = 3**k, 3**(k-1)
    n, step = Mk1, Mk1 // 3
    itype = np.int32 if n < 2**31 else np.int64
    i4 = np.empty(n, dtype=itype)
    refbase = np.zeros(n, dtype=itype)
    mask2 = np.empty(n, dtype=bool)
    mask8 = np.empty(n, dtype=bool)
    for lo in range(0, n, chunk):
        hi = min(lo + chunk, n)
        m = 3*np.arange(lo, hi, dtype=np.int64) + 2
        i4[lo:hi] = (((4*m) % M) - 2) // 3
        r9 = m % 9
        k2 = r9 == 2
        k8 = r9 == 8
        mask2[lo:hi] = k2
        mask8[lo:hi] = k8
        rb = np.zeros(hi-lo, dtype=np.int64)
        rb[k2] = ((((4*m[k2] - 2)//3) % Mk1) - 2)//3
        rb[k8] = ((((2*m[k8] - 1)//3) % Mk1) - 2)//3
        refbase[lo:hi] = rb
        del m, r9, k2, k8, rb
    return n, i4, mask2, mask8, refbase, step


def apply_F_big(c, lam, idxs, wvec=None):
    n, i4, mask2, mask8, refbase, step = idxs
    w4 = lam**-2.0
    if wvec is None:
        wvec = np.where(mask2, lam**(ALPHA-2), np.where(mask8, lam**(ALPHA-1), 0.0))
    m3 = np.minimum(np.minimum(c[refbase], c[refbase + step]), c[refbase + 2*step])
    m3 *= wvec
    m3 += w4 * c[i4]
    return m3


def refine_at(c, lam, idxs, gate=2e-8, max_iters=5000, check_every=20, verbose=True):
    """Power-iterate c <- F(c)/max F(c) at fixed lam until min F(c)/c > 1+gate
    (or CW bounds pinch / budget exhausted). Returns (c, cwlo, cwhi, iters)."""
    cwlo = cwhi = None
    t0 = time.time()
    wvec = np.where(idxs[2], lam**(ALPHA-2), np.where(idxs[3], lam**(ALPHA-1), 0.0))
    for t in range(max_iters + 1):
        f = apply_F_big(c, lam, idxs, wvec)
        if t % check_every == 0 or t == max_iters:
            ratio = f / c
            cwlo, cwhi = float(ratio.min()), float(ratio.max())
            del ratio
            if verbose:
                print(f"    refine it={t:5d} cwlo={cwlo:.12f} cwhi={cwhi:.12f}"
                      f" [{time.time()-t0:.0f}s]", flush=True)
            if cwlo > 1.0 + gate:
                c = f / f.max()
                return c, cwlo, cwhi, t
        c = f / f.max()
        del f
    return c, cwlo, cwhi, max_iters


def verify_exact_big(k, A, B2, B8, C, chunk=1 << 21, verbose=True):
    """Chunked exact-integer verification, same checks (i)-(vi) as
    verify_exact() but dict-free (works for any k >= 2; required k >= 15).
    C: numpy int64 array (or list). All comparisons in Python bigints."""
    t0 = time.time()
    fails = []
    if not (SC_L < A <= 2*SC_L):
        fails.append(("(i) lambda range", A))
    if not (2**P < 3**Q):
        fails.append(("(ii) 2^P < 3^Q", (P, Q)))
    if not w2_ok(B2, A):
        fails.append(("(iii) W2 bound", B2))
    if not w8_ok(B8, A):
        fails.append(("(iv) W8 bound", B8))
    C = np.asarray(C, dtype=np.int64)
    M, Mk1 = 3**k, 3**(k-1)
    n, step = Mk1, Mk1 // 3
    if len(C) != n:
        fails.append(("length of C", len(C)))
        return {"ok": False, "fails": fails}
    minC, maxC = int(C.min()), int(C.max())
    if minC < SC_C:
        fails.append(("(v) c >= 1", minC))
    # int64-range guards for the exact-integer gathers below
    assert maxC < 2**62 and 4*M < 2**62
    A2 = A*A
    A2SW = A2 * SC_W
    SL2SW = SC_L*SC_L*SC_W
    B2A2 = B2 * A2
    B8A2 = B8 * A2
    worst = None
    nbad = 0
    for lo in range(0, n, chunk):
        hi = min(lo + chunk, n)
        i = np.arange(lo, hi, dtype=np.int64)
        m = 3*i + 2
        i4 = (((4*m) % M) - 2) // 3
        c4 = C[i4].tolist()
        r9 = (m % 9).tolist()
        # min-triple (value 0 used for branch-5 rows, never read)
        refbase = np.zeros(hi-lo, dtype=np.int64)
        k2 = (m % 9 == 2)
        k8 = (m % 9 == 8)
        refbase[k2] = ((((4*m[k2] - 2)//3) % Mk1) - 2)//3
        refbase[k8] = ((((2*m[k8] - 1)//3) % Mk1) - 2)//3
        m3 = np.minimum(np.minimum(C[refbase], C[refbase + step]),
                        C[refbase + 2*step]).tolist()
        ci = C[lo:hi].tolist()
        mlist = m.tolist()
        del i, m, i4, refbase, k2, k8
        for j in range(hi-lo):
            lhs = ci[j] * A2SW
            rhs = c4[j] * SL2SW
            b = r9[j]
            if b == 2:
                rhs += B2A2 * m3[j]
            elif b == 8:
                rhs += B8A2 * m3[j]
            if lhs > rhs:
                nbad += 1
                if nbad <= 10:
                    fails.append(("(vi) constraint", {"m": mlist[j], "m mod 9": b,
                                                      "lhs": str(lhs), "rhs": str(rhs)}))
            else:
                s = float(rhs - lhs) / float(lhs)
                if worst is None or s < worst[0]:
                    worst = (s, mlist[j])
    if nbad > 10:
        fails.append(("(vi) additional failures", nbad - 10))
    ok = not fails
    res = {"ok": ok, "fails": fails, "n_constraints": n,
           "min_rel_slack": worst[0] if worst else None,
           "argmin_slack_m": worst[1] if worst else None,
           "lambda": f"{A}/{SC_L}", "gamma_float": math.log2(A/SC_L),
           "Cmax_over_SCC": maxC/SC_C, "Delta1": f"{SC_C}/(4*{maxC})",
           "verify_seconds": round(time.time()-t0, 2), "verifier": "big/chunked"}
    if verbose:
        print(f"  exact verification (chunked): {'ALL PASS' if ok else 'FAILED'}"
              f"  ({n} constraints, {res['verify_seconds']}s)")
        if worst:
            print(f"  min relative slack {worst[0]:.3e} at m = {worst[1]} (mod 3^{k})")
        for f_ in fails:
            print("  FAIL:", f_)
    return res


def sha256_file(path):
    import hashlib
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for blk in iter(lambda: fh.read(1 << 24), b""):
            h.update(blk)
    return h.hexdigest()


def gen_from_vec(k, vecpath, lam_hat, drop_units=None, gate=2e-8,
                 max_refine=5000, out=None):
    """Certificate generation from a precomputed candidate eigenvector
    (e.g. GPU run). The vector is refined at lambda_cert if needed; the
    acceptance decision is the local exact-integer verification only."""
    print(f"=== level k = {k}  (n = 3^{k-1} = {3**(k-1)} classes), vec = {vecpath} ===")
    t0 = time.time()
    idxs = big_indices(k)
    n = idxs[0]
    c0 = np.load(vecpath)
    assert c0.shape == (n,), f"eigenvector length {c0.shape} != {n}"
    assert np.all(np.isfinite(c0)) and float(c0.min()) > 0.0, "bad eigenvector"
    print(f"  loaded vector (min {c0.min():.3e}, max {c0.max():.3e}); "
          f"indices built [{time.time()-t0:.0f}s]")
    print(f"  float lambda_hat = {lam_hat!r}  (gamma ~= {math.log2(lam_hat):.9f})")
    if drop_units is None:
        drop_units = [5, 10, 20, 50, 100]
    c_start = c0
    for d in drop_units:
        A = int(round(lam_hat * SC_L)) - d
        lam = A / SC_L
        print(f"  trying lambda_cert = {A}/{SC_L} = {lam}  (drop {d}e-7)")
        c, cwlo, cwhi, its = refine_at(c_start, lam, idxs, gate=gate,
                                       max_iters=max_refine)
        print(f"    CW bounds: {cwlo:.12f} <= rho <= {cwhi:.12f}  ({its} refine iters)")
        if cwlo <= 1.0 + gate:
            print("    insufficient float margin, dropping lambda further")
            c_start = c   # keep refined vector as warm start
            continue
        B2, B8 = certified_weight_bounds(A)
        c = c / c.min()
        assert float(c.max()) * SC_C < 2**53, "c*SC_C exceeds float64 exact-int range"
        C = np.floor(c * SC_C).astype(np.int64)
        del c
        res = verify_exact_big(k, A, B2, B8, C)
        if res["ok"]:
            path = out or os.path.join(HERE, f"cert_k{k}.json")
            cfile = os.path.join(HERE, f"cert_k{k}_C.npy")
            np.save(cfile, C)
            cert = {"k": k, "A": A, "SC_L": SC_L, "B2": B2, "B8": B8, "SC_W": SC_W,
                    "P": P, "Q": Q, "SC_C": SC_C,
                    "C_file": os.path.basename(cfile),
                    "C_sha256": sha256_file(cfile)}
            with open(path, "w") as fh:
                json.dump(cert, fh, indent=1)
            print(f"  certificate written: {path} + {cfile} "
                  f"({os.path.getsize(cfile)/1e6:.0f} MB)")
            res["lambda_float_estimate"] = lam_hat
            res["cert_path"] = path
            res["vec_source"] = vecpath
            res["refine_iters"] = its
            rpt = os.path.join(HERE, f"cert_k{k}_report.json")
            with open(rpt, "w") as fh:
                json.dump(res, fh, indent=1, default=str)
            print(f"  report: {rpt}")
            print(f"  CERTIFIED: L^NT_{k}({A}/{SC_L}) feasible; "
                  f"gamma = log2({A}/{SC_L}) = {math.log2(A/SC_L):.7f}")
            return res
        print("    exact verification failed, dropping lambda further")
        c_start = c0
    print("  NO CERTIFICATE FOUND in candidate range")
    return None


# ----------------------------------------------------------------------
# certified rational weight bounds
# ----------------------------------------------------------------------
def check_pq():
    assert 2**P < 3**Q, "P/Q is not a lower bound for alpha=log2(3)!"


def w2_ok(B2, A):
    # W2 = B2/SC_W <= (A/SC_L)^((P-2Q)/Q)  <=>  B2^Q * A^(2Q-P) <= SC_W^Q * SC_L^(2Q-P)
    return B2**Q * A**(2*Q-P) <= SC_W**Q * SC_L**(2*Q-P)


def w8_ok(B8, A):
    # W8 = B8/SC_W <= (A/SC_L)^((P-Q)/Q)  <=>  B8^Q * SC_L^(P-Q) <= A^(P-Q) * SC_W^Q
    return B8**Q * SC_L**(P-Q) <= A**(P-Q) * SC_W**Q
def certified_weight_bounds(A, verbose=True):
    """Largest (found) integers B2, B8 with W2=B2/SC_W <= lam^(P/Q-2),
    W8=B8/SC_W <= lam^(P/Q-1), lam=A/SC_L; certified by integer comparison."""
    check_pq()
    lam = A / SC_L
    B2 = int(lam**((P - 2*Q)/Q) * SC_W) + 2   # float seed, then exact descent
    while not w2_ok(B2, A):
        B2 -= 1
    B8 = int(lam**((P - Q)/Q) * SC_W) + 2
    while not w8_ok(B8, A):
        B8 -= 1
    if verbose:
        print(f"  weight bounds: W2 = {B2}/{SC_W}  (float lam^(a-2) = {lam**(ALPHA-2):.15f})")
        print(f"                 W8 = {B8}/{SC_W}  (float lam^(a-1) = {lam**(ALPHA-1):.15f})")
    return B2, B8


# ----------------------------------------------------------------------
# exact verification of a certificate
# ----------------------------------------------------------------------
def verify_exact(k, A, B2, B8, C, verbose=True):
    """Check (i)-(vi) of the module docstring in exact integer arithmetic.
    Returns dict of results; raises nothing -- reports failures."""
    t0 = time.time()
    fails = []
    # (i) 1 < lambda <= 2
    if not (SC_L < A <= 2*SC_L):
        fails.append(("(i) lambda range", A))
    # (ii) P/Q < alpha
    if not (2**P < 3**Q):
        fails.append(("(ii) 2^P < 3^Q", (P, Q)))
    # (iii),(iv) weight bounds
    if not w2_ok(B2, A):
        fails.append(("(iii) W2 bound", B2))
    if not w8_ok(B8, A):
        fails.append(("(iv) W8 bound", B8))
    ms, i4m, btype, refs = build_exact(k)
    n = len(ms)
    if len(C) != n:
        fails.append(("length of C", len(C)))
        return {"ok": False, "fails": fails}
    # (v) c >= 1
    minC, maxC = min(C), max(C)
    if minC < SC_C:
        fails.append(("(v) c >= 1", minC))
    # (vi) the LP constraints, scaled integer form (SC_C cancels):
    #   C[i]*A^2*SC_W <= C[i4m]*SC_L^2*SC_W + B*A^2*min3(C)
    A2 = A*A
    A2SW = A2 * SC_W
    SL2SW = SC_L*SC_L*SC_W
    B2A2 = B2 * A2
    B8A2 = B8 * A2
    worst = None   # (relative slack, m)
    nbad = 0
    for i in range(n):
        lhs = C[i] * A2SW
        rhs = C[i4m[i]] * SL2SW
        b = btype[i]
        if b == 2:
            r = refs[i]
            rhs += B2A2 * min(C[r[0]], C[r[1]], C[r[2]])
        elif b == 8:
            r = refs[i]
            rhs += B8A2 * min(C[r[0]], C[r[1]], C[r[2]])
        if lhs > rhs:
            nbad += 1
            if nbad <= 10:
                fails.append(("(vi) constraint", {"m": ms[i], "m mod 9": b,
                                                  "lhs": str(lhs), "rhs": str(rhs)}))
        else:
            s = float(rhs - lhs) / float(lhs)
            if worst is None or s < worst[0]:
                worst = (s, ms[i])
    if nbad > 10:
        fails.append(("(vi) additional failures", nbad - 10))
    ok = not fails
    res = {"ok": ok, "fails": fails, "n_constraints": n,
           "min_rel_slack": worst[0] if worst else None,
           "argmin_slack_m": worst[1] if worst else None,
           "lambda": f"{A}/{SC_L}", "gamma_float": math.log2(A/SC_L),
           "Cmax_over_SCC": maxC/SC_C, "Delta1": f"{SC_C}/(4*{maxC})",
           "verify_seconds": round(time.time()-t0, 2)}
    if verbose:
        print(f"  exact verification: {'ALL PASS' if ok else 'FAILED'}"
              f"  ({n} constraints, {res['verify_seconds']}s)")
        if worst:
            print(f"  min relative slack {worst[0]:.3e} at m = {worst[1]} (mod 3^{k})")
        for f_ in fails:
            print("  FAIL:", f_)
    return res


# ----------------------------------------------------------------------
# certificate generation
# ----------------------------------------------------------------------
def generate(k, drop_units=None, out=None):
    """Build and exactly verify a certificate for level k.
    drop_units: list of integers d; lambda candidate A = floor(lam_hat*SC_L) - d."""
    print(f"=== level k = {k}  (n = 3^{k-1} = {3**(k-1)} classes) ===")
    t0 = time.time()
    sysk = np_system(k)
    print(f"  built system in {time.time()-t0:.1f}s")
    lam_hat, c_warm = solve_lambda(k, sysk)
    print(f"  float lambda_k ~= {lam_hat:.9f}  (gamma ~= {math.log2(lam_hat):.9f})")
    if drop_units is None:
        drop_units = [5, 10, 20, 50, 100]
    for d in drop_units:
        A = int(lam_hat * SC_L) - d
        lam = A / SC_L
        print(f"  trying lambda_cert = {A}/{SC_L} = {lam}  (drop {d}e-7)")
        # converge the Perron vector at lambda_cert; need min F(c)/c > 1 with margin
        c, cwlo, cwhi = power_iterate(lam, sysk, c_warm, iters=20000, tol=1e-15)
        print(f"    CW bounds after iteration: {cwlo:.12f} <= rho <= {cwhi:.12f}")
        if cwlo <= 1.0 + 2e-8:
            print("    insufficient float margin, dropping lambda further")
            continue
        # rational weights
        B2, B8 = certified_weight_bounds(A)
        # round c DOWN on the SC_C grid, normalized to min = 1
        c = c / c.min()
        C = [int(x) for x in np.floor(c * SC_C).astype(np.int64)]
        # exact verification
        res = verify_exact(k, A, B2, B8, C)
        if res["ok"]:
            cert = {"k": k, "A": A, "SC_L": SC_L, "B2": B2, "B8": B8, "SC_W": SC_W,
                    "P": P, "Q": Q, "SC_C": SC_C, "C": C}
            path = out or os.path.join(HERE, f"cert_k{k}.json")
            with open(path, "w") as fh:
                json.dump(cert, fh)
            print(f"  certificate written: {path}  ({os.path.getsize(path)/1e6:.1f} MB)")
            res["lambda_float_estimate"] = lam_hat
            res["cert_path"] = path
            rpt = os.path.join(HERE, f"cert_k{k}_report.json")
            with open(rpt, "w") as fh:
                json.dump(res, fh, indent=1, default=str)
            print(f"  report: {rpt}")
            print(f"  CERTIFIED: L^NT_{k}({A}/{SC_L}) feasible; "
                  f"gamma = log2({A}/{SC_L}) = {math.log2(A/SC_L):.7f}")
            return res
        print("    exact verification failed, dropping lambda further")
    print("  NO CERTIFICATE FOUND in candidate range")
    return None


# ----------------------------------------------------------------------
# self-tests
# ----------------------------------------------------------------------
def selftest():
    # 1. cross-check build_exact against a solver-style numpy reconstruction
    for k in range(2, 8):
        ms, i4m, btype, refs = build_exact(k)
        M = 3**k
        # independent re-derivation with numpy (mirrors kl_perron_solver.build)
        ms2 = np.arange(2, M, 3, dtype=np.int64)
        idx = {m: i for i, m in enumerate(ms2)}
        assert list(ms2) == ms
        assert [idx[(4*m) % M] for m in ms2] == i4m
        for i, m in enumerate(ms2):
            if m % 9 == 2:
                r = ((4*m-2)//3) % (M//3)
                assert refs[i] == tuple(idx[(r + j*(M//3)) % M] for j in range(3))
            elif m % 9 == 8:
                r = ((2*m-1)//3) % (M//3)
                assert refs[i] == tuple(idx[(r + j*(M//3)) % M] for j in range(3))
            else:
                assert refs[i] is None
    print("build_exact matches solver-style construction for k=2..7")

    # 1b. cross-check big_indices (arithmetic, dict-free) against build_exact (dict)
    for k in range(2, 9):
        ms, i4m, btype, refs = build_exact(k)
        n, i4, mask2, mask8, refbase, step = big_indices(k)
        assert n == len(ms)
        assert i4.tolist() == i4m
        assert mask2.tolist() == [b == 2 for b in btype]
        assert mask8.tolist() == [b == 8 for b in btype]
        for i in range(n):
            if btype[i] in (2, 8):
                rb = int(refbase[i])
                assert refs[i] == (rb, rb + step, rb + 2*step)
    print("big_indices (arithmetic) matches build_exact (dict) for k=2..8")

    # 2. k=2 must reproduce the paper's appendix system I_2 exactly:
    #    phi^2 >= phi^8(y-2) + min[phi^2,phi^5,phi^8](y+a-2)
    #    phi^5 >= phi^2(y-2)
    #    phi^8 >= phi^5(y-2) + min[phi^2,phi^5,phi^8](y+a-1)
    ms, i4m, btype, refs = build_exact(2)
    assert ms == [2, 5, 8]
    assert i4m == [2, 0, 1]                      # 4*2=8, 4*5=20=2, 4*8=32=5 (mod 9)
    assert btype == [2, 5, 8]
    assert refs[0] == (0, 1, 2) and refs[1] is None and refs[2] == (0, 1, 2)
    print("k=2 system matches the paper's appendix I_2 (lines 1108-1110)")

    # 3. reproduce the KL Table 2 lambda values (float)
    kl_table = {2: 1.3534010, 3: 1.5275960, 4: 1.6122870, 5: 1.6627590,
                6: 1.6944520, 7: 1.7201900, 8: 1.7449630, 9: 1.7615320}
    for k, ref in kl_table.items():
        sysk = np_system(k)
        lam_hat, _ = solve_lambda(k, sysk)
        assert abs(lam_hat - ref) < 2e-6, (k, lam_hat, ref)
        print(f"  k={k}: lambda={lam_hat:.7f}  KL table {ref:.7f}  diff {lam_hat-ref:+.1e}")
    print("KL Table 2 reproduced (k=2..9) to published precision")

    # 4. weight-bound device sanity at KL's own certified point lambda = 1.7922310
    A = 17922310
    B2, B8 = certified_weight_bounds(A, verbose=False)
    lam = A/SC_L
    assert B2/SC_W <= lam**(ALPHA-2) < (B2+1e6)/SC_W
    assert B8/SC_W <= lam**(ALPHA-1) < (B8+1e6)/SC_W
    assert abs(B2/SC_W - lam**(ALPHA-2)) < 1e-9
    assert abs(B8/SC_W - lam**(ALPHA-1)) < 1e-9
    print(f"weight bounds at KL's lambda=1.7922310: W2={B2}/10^15, W8={B8}/10^15 (certified)")
    print("SELFTEST PASSED")


def verify_file(path):
    with open(path) as fh:
        cert = json.load(fh)
    print(f"verifying {path}: k={cert['k']}, lambda={cert['A']}/{cert['SC_L']}")
    assert cert["SC_L"] == SC_L and cert["SC_C"] == SC_C and cert["SC_W"] == SC_W
    assert cert["P"] == P and cert["Q"] == Q
    if "C_file" in cert:
        cfile = os.path.join(os.path.dirname(os.path.abspath(path)), cert["C_file"])
        digest = sha256_file(cfile)
        assert digest == cert["C_sha256"], f"sha256 mismatch for {cfile}"
        print(f"  C from {cert['C_file']} (sha256 verified: {digest[:16]}...)")
        C = np.load(cfile, allow_pickle=False)
        assert C.dtype == np.int64
        res = verify_exact_big(cert["k"], cert["A"], cert["B2"], cert["B8"], C)
    else:
        res = verify_exact(cert["k"], cert["A"], cert["B2"], cert["B8"], cert["C"])
    print(json.dumps({k_: v for k_, v in res.items() if k_ != "fails"}, indent=1))
    return res["ok"]


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    mode = sys.argv[1]
    if mode == "selftest":
        selftest()
    elif mode == "gen":
        k = int(sys.argv[2])
        drops = None
        if "--drop" in sys.argv:
            drops = [int(x) for x in sys.argv[sys.argv.index("--drop")+1].split(",")]
        r = generate(k, drop_units=drops)
        sys.exit(0 if (r and r["ok"]) else 2)
    elif mode == "genvec":
        k = int(sys.argv[2])
        vecpath = sys.argv[3]
        lam_hat = float(sys.argv[4])
        drops = None
        gate = 2e-8
        if "--drop" in sys.argv:
            drops = [int(x) for x in sys.argv[sys.argv.index("--drop")+1].split(",")]
        if "--gate" in sys.argv:
            gate = float(sys.argv[sys.argv.index("--gate")+1])
        r = gen_from_vec(k, vecpath, lam_hat, drop_units=drops, gate=gate)
        sys.exit(0 if (r and r["ok"]) else 2)
    elif mode == "verify":
        ok = verify_file(sys.argv[2])
        sys.exit(0 if ok else 2)
    else:
        print("unknown mode", mode)
        sys.exit(1)
