"""Near-critical word atlas for the accelerated odd map T(x) = (3x+1)/2^v.

The three-word charge lane is uniformly supercritical (every branch expands by
>= 9/8).  This atlas works in the full valuation-word language, where
contracting words exist, and quantifies exactly where the Diophantine
character of log2(3) enters.

Objects.  A valuation word V = (v_1..v_n), width S = sum v_i, satisfies
    2^S T^n(x) = 3^n x + A_V,   A_V = sum_j 3^(n-1-j) 2^(S_j).
Exact-valuation cylinders are single residue classes mod 2^(S+1).
The unique 2-adic point with address V^infinity is
    xi_V = A_V / (2^S - 3^n)   (in ZZ_2; d := |2^S - 3^n| odd).
xi_V < 0 for expanding words (3^n > 2^S), xi_V > 0 for contracting words.

Shadowing bound (same proof as the in-lane repetition bound).  If an odd
integer x follows V^k exactly, then x == xi_V mod 2^(kS), so
    N := (2^S - 3^n) x - A_V   is nonzero* and divisible by 2^(kS), giving

        k <= log2(d*x + A_V) / S.        (*)

(* N = 0 iff x is literally on the rational cycle xi_V; for integer x that is
a genuine Collatz cycle, excluded below 2^71 by verification.)

So the depth to which any integer of height X can track a periodic pattern is
log2(d X)/S + O(1), and the words that allow the DEEPEST shadowing at fixed
width are exactly those minimizing d = |2^S - 3^n|: the continued-fraction
convergents of log2(3).  The "near-critical crack" is indexed by how small d
can be -- the irrationality measure of log2(3).
"""
from fractions import Fraction as F
import math

def v2(n):
    v = 0
    while n % 2 == 0:
        n //= 2; v += 1
    return v

def T_step(x):
    y = 3 * x + 1
    v = v2(y)
    return y >> v, v

# ------------------------------------------------------------- 1. domains
print("== 1. single-step exact-valuation domains ==")
for v in range(1, 9):
    classes = {x % (1 << (v + 1)) for x in range(1, 1 << 14, 2)
               if v2(3 * x + 1) == v}
    assert len(classes) == 1, (v, classes)
print("   {x odd : v2(3x+1)=v} is a single class mod 2^(v+1) for v=1..8  OK")

# ------------------------------------------------- 2. affine data + cylinders
def word_data(V):
    n = len(V); S = sum(V)
    A = 0; Sj = 0
    for j, vj in enumerate(V):
        A += 3 ** (n - 1 - j) * (1 << Sj)
        Sj += vj
    return n, S, A

def follows(x, V):
    for vj in V:
        y = 3 * x + 1
        if v2(y) != vj:
            return False
        x = y >> vj
    return True

def cylinder_min(V):
    """Minimal positive odd x whose exact valuation word starts with V.
    The exact cylinder of (v_1..v_m) is one residue class mod 2^(S_m+1);
    lift one step at a time (2^(v_j) candidates per step, exactly one works)."""
    r, M = 1, 2                       # x odd: class 1 mod 2
    for j, vj in enumerate(V):
        found = [r + ext * M for ext in range(1 << vj)
                 if follows(r + ext * M, V[:j + 1])]
        assert len(found) == 1, (V, j, found)
        M <<= vj
        r = found[0] % M or M
    return r, 2 * M

print("\n== 2. shadowing verification: the -5 cycle word (1,2) ==")
V = (1, 2)
n, S, A = word_data(V)
d = abs((1 << S) - 3 ** n)
xi = F(A, (1 << S) - 3 ** n)
print(f"   word {V}: n={n}, S={S}, A_V={A}, d={d}, xi_V={xi}  (the -5 cycle)")
for k in range(3, 9):
    x = (1 << (3 * k + 1)) - 5        # == -5 mod 2^(3k+1): exact k periods
    assert follows(x, V * k), k
    assert not follows(x, V * (k + 1)), k
    cap = math.log2(d * x + A) / S
    print(f"   x = 2^{3*k+1}-5 = {x:>10d} follows (1,2)^k for exactly k={k} "
          f"periods (bound (*): k <= {cap:.2f})")

print("\n== 3. contracting-word shadowing: the (S,n)=(8,5) convergent ==")
V = (2, 2, 2, 1, 1)
n, S, A = word_data(V)
d = abs((1 << S) - 3 ** n)
print(f"   word {V}: S={S}, n={n}, d=|2^8-3^5|={d}, xi_V = {A}/{d} > 0 "
      f"(a ZZ[1/13] cycle, drift {3**n}/{1<<S} = {3**n/(1<<S):.3f} < 1)")
for k in range(1, 5):
    x, M = cylinder_min(V * k)
    cap = math.log2(d * x + A) / S
    print(f"   k={k}: minimal integer shadow x = {x:>12d}  (bound: k <= {cap:.2f})")

# ------------------------------------------------- 4. convergents of log2(3)
print("\n== 4. the crack index: convergents of log2(3) ==")
def cf_log23(nterms):
    """CF of log_w(u) with exact rational arithmetic."""
    u, w = F(3), F(2)
    terms = []
    for _ in range(nterms):
        a = 0
        while w ** (a + 1) <= u:
            a += 1
        terms.append(a)
        u2 = u / w ** a
        if u2 == 1:
            break
        u, w = w, u2
    return terms

terms = cf_log23(10)
print(f"   CF(log2 3) = {terms}")
convs = []
p0, q0, p1, q1 = 1, 0, terms[0], 1
convs.append((p1, q1))
for a in terms[1:]:
    p0, p1 = p1, a * p1 + p0
    q0, q1 = q1, a * q1 + q0
    convs.append((p1, q1))
print("   (S,n) = convergent (p,q); d = |2^S - 3^n|; depth cap for x <= 2^68:")
for (S, n) in convs[1:]:
    d = abs((1 << S) - 3 ** n)
    cap = (68 + math.log2(d)) / S if d else float('inf')
    kind = "contracting" if (1 << S) > 3 ** n else "expanding  "
    print(f"   (S,n)=({S:3d},{n:3d})  {kind}  log2(d)={math.log2(d):8.2f}  "
          f"d/3^n={d/3**n:9.2e}  shadow cap below 2^68: {cap:6.1f} periods")

# ------------------------------------------------- 5. drift analytics
print("\n== 5. drift analytics of the full language ==")
print("   P(v)=2^-v, E[log2 drift] = log2(3) - 2 = %.4f  (contracting on average)"
      % (math.log2(3) - 2))
p = 2 - math.log2(3)
print(f"   near-critical sub-language {{v=1, v=2}}: zero drift at P(v=1) = {p:.4f}")
print("   in-lane (A/B/C) drift is bounded below by log2(9/8) = %.4f per step:"
      % math.log2(9/8))
print("   the three-word lane cannot express any near-critical address.")
