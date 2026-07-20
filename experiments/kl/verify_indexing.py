"""Verify the reshape-based fiber indexing against brute force, k=4,5.

Claim: with ms_k = arange(2, 3^k, 3) (index of value m is (m-2)//3, n_k = 3^{k-1}),
the 3 refinements {r, r+3^{k-1}, r+2*3^{k-1}} of the level-(k-1) residue r
(parent index p = (r-2)//3 in ms_{k-1}) sit at level-k indices p + j*3^{k-2}.
Hence c_k.reshape(3, n_{k-1})[j, p] = c_k value at refinement j of parent p.

Depth d: the 3^d level-k refinements {q + t*3^{k-d} : t=0..3^d-1} of the
level-(k-d) residue q (parent index p_q = (q-2)//3 in ms_{k-d}) sit at level-k
indices p_q + t*3^{k-d-1}, i.e. c_k.reshape(3^d, n_{k-d})[:, p_q].
"""
import numpy as np

for k in (4, 5):
    M = 3**k
    ms_k = np.arange(2, M, 3)
    idx = {m: i for i, m in enumerate(ms_k)}
    n_k = len(ms_k)
    assert n_k == 3**(k-1)

    for d in (1, 2, 3):
        Mkd = 3**(k-d)
        ms_par = np.arange(2, Mkd, 3)
        n_par = len(ms_par)
        # brute force: refinements of q are q + t*3^{k-d}, t=0..3^d-1
        brute = np.zeros((3**d, n_par), dtype=np.int64)
        for p, q in enumerate(ms_par):
            for t in range(3**d):
                brute[t, p] = idx[(q + t * Mkd) % M]
        # reshape claim: index = p + t * n_par  (n_par = 3^{k-d-1})
        claim = (np.arange(3**d)[:, None] * n_par) + np.arange(n_par)[None, :]
        assert np.array_equal(brute, claim), f"FAIL k={k} d={d}"
        # equivalent statement: arange(n_k).reshape(3^d, n_par) gives the fibers
        assert np.array_equal(np.arange(n_k).reshape(3**d, n_par), claim)
        print(f"k={k} d={d}: reshape indexing VERIFIED against brute force "
              f"({3**d} x {n_par} fiber table)")

# also verify with an actual eigvector-like array: values at refinements of r
k = 4
M = 3**k
ms_k = np.arange(2, M, 3)
c = np.random.rand(len(ms_k))
r = 14  # level-3 residue, 14 % 3 == 2
p = (r - 2) // 3
fiber_brute = [c[(r + j * 3**(k-1) - 2) // 3] for j in range(3)]
fiber_reshape = c.reshape(3, -1)[:, p]
assert np.allclose(fiber_brute, fiber_reshape)
print("value-level fiber check (k=4, r=14): VERIFIED")
