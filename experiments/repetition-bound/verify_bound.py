"""Exact verification of the cylinder repetition bound for the three-word
zero-carry charge system.

Theorem (address repetition bound, Liouville quality).  Let V be a nonempty
A/B/C word with composed data (A_V, D_V, C_V) = (3^{t_V}, 2^{s_V}, C_V), and
let V' be a prefix of V of dyadic width s'.  If a positive integer H has
branch address beginning V V', then

    N := (A_V - D_V) * H + C_V     satisfies     2^{s_V + s'} | N,

and since 0 < N <= A_V * (H + 7)  (via the kernel-checked BA3 bound
C_V <= 7 (A_V - D_V)),

    (s_V + s') * log 2  <=  t_V * log 3 + log(H + 7).

Because t_V <= s_V with equality only for all-A words, a repetition is
constrained exactly when  s' > s_V (log2(3) - 1) ~ 0.585 s_V: the critical
repetition exponent in the width metric is log2(3).

This script verifies every ingredient exactly on randomized words:
  1. cylinders: address-prefix W <-> one residue class mod 2^{s_W};
  2. the periodic point xi_V = C_V/(D_V - A_V) lies in ZZ_2, sits in V's own
     cylinder at every depth, and is <= 0;
  3. the divisibility 2^{s_V+s'} | N on the whole cylinder;
  4. the inequality and its tightness on the minimal cylinder element.
"""
import random

random.seed(20260728)

BR = {'A': (3, 2, 0), 'B': (9, 8, 3), 'C': (81, 64, 63)}
DOM = {'A': (2, 0), 'B': (8, 5), 'C': (64, 49)}   # modulus, residue
WIDTH = {'A': 1, 'B': 3, 'C': 6}

def v2(x):
    v = 0
    while x % 2 == 0:
        x //= 2; v += 1
    return v

def word_data(word):
    A = D = 1; C = 0
    for b in word:
        a, d, c = BR[b]
        A, C, D = A * a, a * C + c * D, D * d
    return A, D, C

def width(word):
    return sum(WIDTH[b] for b in word)

def takes_branch(H, b):
    m, r = DOM[b]
    return H % m == r

def step(H, b):
    a, d, c = BR[b]
    assert takes_branch(H, b)
    num = a * H + c
    assert num % d == 0
    return num // d

def cylinder_class(word):
    """The unique residue class mod 2^{s_W} whose address starts with W.
    Found by 2-adic lifting; also asserts uniqueness at each level."""
    r, M = 0, 1
    for j, b in enumerate(word):
        m_b = DOM[b][0]
        found = []
        for ext in range(m_b):
            H0 = r + ext * M
            H, ok = H0, True
            for bb in word[:j + 1]:
                if H0 == 0:  # class rep 0: test on 0 + M*m_b instead
                    pass
                if not takes_branch(H, bb):
                    ok = False; break
                H = step(H, bb)
            if ok:
                found.append(H0 % (M * m_b))
        # representative 0 needs care: branch predicates are pure congruences,
        # so membership of the class is well-defined by any representative
        assert len(found) == 1, (word, j, found)
        M *= m_b
        r = found[0]
    return r, M   # class r mod M, M = 2^{s_W}

# ---------------------------------------------------------------- checks 1-2
print("== cylinder structure and periodic point ==")
for trial in range(30):
    word = [random.choice('ABC') for _ in range(random.randint(1, 6))]
    r, M = cylinder_class(word)
    assert M == 2 ** width(word)
    # every element of the class follows the word; neighbors do not
    for rep in (r + M if r == 0 else r, r + 3 * M, r + 17 * M):
        H = rep
        for b in word:
            assert takes_branch(H, b), (word, rep)
            H = step(H, b)
    # xi_V in the class at every depth k
    A, D, C = word_data(word)
    denom = D - A                       # odd, negative for nonempty words
    assert denom % 2 != 0 and denom < 0
    for k in range(1, 4):
        rk, Mk = cylinder_class(word * k)
        xi_mod = (C * pow(denom % Mk, -1, Mk)) % Mk
        assert xi_mod == rk, (word, k)
print("   30 random words: cylinder=single class mod 2^width; xi_V in own cylinder to depth 3  OK")

# ---------------------------------------------------------------- checks 3-4
print("== repetition bound on V V' ==")
rows = []
for trial in range(200):
    V = [random.choice('ABC') for _ in range(random.randint(1, 6))]
    lp = random.randint(1, len(V))
    Vp = V[:lp]                          # fractional repetition, V' prefix of V
    s, sp, t = width(V), width(Vp), sum({'A':1,'B':2,'C':4}[b] for b in V)
    A, D, C = word_data(V)
    r, M = cylinder_class(V + Vp)
    Hmin = r if r > 0 else M
    for H in (Hmin, Hmin + M, Hmin + 5 * M):
        N = (A - D) * H + C
        assert N > 0 and v2(N) >= s + sp, (V, Vp, H, v2(N), s + sp)
        assert 2 ** (s + sp) <= A * (H + 7)
    assert C <= 7 * (A - D)              # BA3, exact
    # tightness: how large must H be vs. the bound's floor?
    floor = (2 ** (s + sp) - C) / (A - D)
    rows.append((s, sp, t, Hmin, floor, Hmin / max(floor, 1e-9)))
print(f"   200 random (V,V') pairs: divisibility 2^(s+s')|N and N<=A(H+7)  OK")
active = [row for row in rows if row[1] > 0.585 * row[0]]
print(f"   constraint-active cases (s' > 0.585 s): {len(active)}/200;",
      "min tightness Hmin/floor = %.2f" % min(row[5] for row in active))

# worked example from the note-check: V = C, square CC
r, M = cylinder_class(list('CC'))
H = r
N = 17 * H + 63
print(f"   exhibit V=C: cylinder of CC = {r} mod {M}; N = 17*{H}+63 = {N} = 2^{v2(N)}*{N >> v2(N)}")

# ------------------------------------------------- quantitative consequence
print("== consequence: forced growth of H under initial squares ==")
print("   For a square VV (s'=s): H >= (4/3)^s * (unit) - 7 when t=s (all-A worst case);")
print("   B/C-heavy words force more.  Examples of the floor (2^{2s}-C)/(A-D):")
for Vstr in ('C', 'CC', 'CCC', 'BBB', 'BCBC', 'AABBCC'):
    V = list(Vstr)
    A, D, C = word_data(V); s = width(V)
    floor = (2 ** (2 * s) - C) // (A - D)
    r, M = cylinder_class(V + V)
    Hmin = r if r > 0 else M
    print(f"   V={Vstr:8s} s={s:3d} t={sum({'A':1,'B':2,'C':4}[b] for b in V):3d}"
          f"  floor={floor:>12d}  minimal cylinder H={Hmin:>14d}")

print()
print("Interpretation: an integer H with an infinite in-lane orbit admits, at")
print("width-position s_n, only repetitions with s' <= 0.585*(s_V + s_n) + log2(H0+7)")
print("(worst case t=s).  Eventual periodicity is the s'->infinity case: this bound")
print("quantitatively implies the audited aperiodicity theorem, and newly excludes")
print("any address whose initial repetition width-exponent exceeds log2(3) i.o.")
