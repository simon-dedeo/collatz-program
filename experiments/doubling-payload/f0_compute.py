"""The doubling-quine payload value F0(g): exact 2-adic computation.

Setting (HS5/HS20, kernel-checked in DoublingQuineNoGo/DoublingQuineRationalNoGo):
any payload for the legal four-cell return with opcode update g -> 2g satisfies

    A F(g) - D z_g^2 F(2g) = b(z_g),
    A = 3^114,  D = 2^154,  z_m = 2^(23m+54)/3^(17m+40),
    b(z) = (3^57 + 2^77) + 2^77 z + 2^77 z^2,

using z_{2g} = kappa z_g^2, kappa = 3^40/2^54.

New reductions (proved in docs/notes/doubling-payload-value.md):

  U (formal uniqueness).  The homogeneous equation A h(z) = D z^2 h(kappa z^2)
  has only h = 0 among formal power series: coefficient recursion
  h_{2m+2} = (D/A) kappa^m h_m with h_0 = h_1 = 0 kills everything.

  V (value rigidity).  Along a doubling orbit {g0 2^j}, the difference
  Delta(g) of any two ZZ_2-bounded solutions obeys
  |Delta(2g)|_2 = 2^(262+46g) |Delta(g)|_2, which is unbounded unless
  Delta = 0.  Natural-number payloads are ZZ_2-bounded.  Hence ANY
  natural-number payload sequence must equal, value by value, the unique
  2-adically convergent particular solution

    F0(g) = sum_{j>=0} A^{-1} (D/A)^j  (prod_{i<j} z_{2^i g}^2)  b(z_{2^j g}),

  whose terms have exact 2-adic valuation  v2(t_j) = 262 j + 46 g (2^j - 1).

So the entire Section-13 frontier for this return reduces to one question per
doubling orbit: is the explicit 2-adic constant F0(g) a positive integer?
This script computes F0(g) mod 2^N exactly and answers up to height 2^(N/2).
"""
from fractions import Fraction as F

A = 3 ** 114
D = 2 ** 154

def z(m):
    return F(2 ** (23 * m + 54), 3 ** (17 * m + 40))

def b(zz):
    return (3 ** 57 + 2 ** 77) + 2 ** 77 * zz + 2 ** 77 * zz * zz

def v2(n):
    v = 0
    while n % 2 == 0:
        n //= 2; v += 1
    return v

def v2_frac(q):
    return v2(q.numerator) - v2(q.denominator)

def F0_mod(g, N, check_valuations=True):
    """F0(g) mod 2^N via exact rationals; terms beyond v2 > N+64 dropped."""
    M = 1 << N
    total = F(0)
    j = 0
    while True:
        val = 262 * j + 46 * g * (2 ** j - 1)
        if val > N + 64:
            break
        t = F(D ** j, A ** (j + 1))
        for i in range(j):
            t *= z(2 ** i * g) ** 2
        t *= b(z(2 ** j * g))
        if check_valuations:
            assert v2_frac(t) == val, (g, j, v2_frac(t), val)
        total += t
        j += 1
    p, q = total.numerator, total.denominator
    assert q % 2 == 1
    return (p % M) * pow(q % M, -1, M) % M, j

def rational_reconstruct(x, N, margin=8):
    """Find p/q, q odd, |p|,|q| <= 2^(N/2 - margin), p == x*q mod 2^N; or None."""
    M = 1 << N
    bound = 1 << (N // 2 - margin)
    r0, t0, r1, t1 = M, 0, x % M, 1
    while r1 >= bound:
        qq = r0 // r1
        r0, r1 = r1, r0 - qq * r1
        t0, t1 = t1, t0 - qq * t1
    p, q = r1, t1
    if q == 0 or abs(q) > bound:
        return None
    if q < 0:
        p, q = -p, -q
    if q % 2 == 0:
        return None
    if (p - x * q) % M != 0:
        return None
    return p, q

# sanity: reconstruction recovers a planted rational
N0 = 2048
planted = (F(-1234567891234567, 987654321987654321),)
xm = (planted[0].numerator % (1 << N0)) * pow(planted[0].denominator, -1, 1 << N0) % (1 << N0)
rec = rational_reconstruct(xm, N0)
assert rec is not None and F(rec[0], rec[1]) == planted[0]
print("reconstruction self-test: planted rational recovered  OK")
print()

print(" g |    N | terms | top nonzero bit | terminating? | rational p/q with height<=2^(N/2-8)?")
for g in range(1, 7):
    for N in (2048, 4096):
        xm, nterms = F0_mod(g, N)
        top = xm.bit_length() - 1
        terminating = top < N // 2
        rec = rational_reconstruct(xm, N)
        rec_str = "none" if rec is None else f"FOUND {rec}"
        print(f"{g:2d} | {N:4d} | {nterms:5d} | {top:15d} | {str(terminating):12s} | {rec_str}")

print()
print("If 'terminating?' is False at bit ~N, any natural number equal to F0(g)")
print("exceeds 2^(N - N/2); combined with value rigidity (V), any natural-number")
print("payload for the g->2g return at opcode g exceeds that height.")

# consistency across precisions: mod-2^2048 values must agree
for g in range(1, 7):
    a2, _ = F0_mod(g, 2048, check_valuations=False)
    a4, _ = F0_mod(g, 4096, check_valuations=False)
    assert a4 % (1 << 2048) == a2
print("cross-precision consistency (2048 vs 4096 bits): OK")

# the naive Liouville gap, stated with exact constants (for the note):
import math
gap_num = 46.0                      # v2 growth rate coefficient: 46 g 2^j
gap_den = 34 * math.log2(3)         # denominator 3-power growth: 3^(34 g 2^j)
print()
print(f"naive Liouville gap ratio = 46 / (34*log2(3)) = {gap_num/gap_den:.4f} < 1")
print("=> partial-sum approximants alone cannot prove F0(g) irrational;")
print("   a Mahler-style auxiliary construction must improve the exponent by >17%.")
