"""Reproduces docs/notes/tropical-geometry.md section 2:
the KL annealed characteristic s(beta) has Archimedean roots beta=1,2 that are
DESTROYED by tropicalization (max of the log2-exponents), whose corners are at
beta=0 and beta=alpha/(alpha-1)=2.7095. Run: python3 tropical_checks.py"""
import math
a = math.log2(3)  # alpha


def s(b):
    return 4 ** (-b) + (1 / 3) * (4 / 3) ** (-b) + (1 / 3) * (2 / 3) ** (-b)


def exps(b):  # log2-exponents of the three monomials of s
    return [-2 * b, -a - (2 - a) * b, (a - 1) * b - a]


if __name__ == "__main__":
    print("Archimedean roots (s=1):", [b for b in (0, 1, 2) if abs(s(b) - 1) < 1e-12])
    print("s(0),s(1),s(2) =", [round(s(b), 6) for b in (0, 1, 2)])
    print("beta=1 term magnitudes:", [round(x, 4) for x in
          (4 ** -1, (1 / 3) * (3 / 4), (1 / 3) * (3 / 2))], "(sum=1, 3-term balance)")
    # tropical curve max(exps)=0 crossings
    xs = [i / 2000 for i in range(-2000, 8000)]
    v = [max(exps(b)) for b in xs]
    cr = [round((xs[i] + xs[i + 1]) / 2, 3) for i in range(len(xs) - 1)
          if v[i] == 0 or v[i] * v[i + 1] < 0]
    print("tropical max(exps)=0 corners:", cr, " (expected ~0 and", round(a / (a - 1), 4), ")")
    print("=> tropical roots != Archimedean roots: lambda=2 is invisible to tropicalization")
