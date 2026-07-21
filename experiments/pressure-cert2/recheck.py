"""recheck.py -- independent from-disk verification of echarge certificates.

Deliberately does NOT import combined.py: transitions, coverage and weights
are re-derived inline from the definitions.  Loads h and results JSON from
disk; verifies every row inequality in exact Fractions and the integer-power
gap R^b < z^a.  Any 'certificate found' is treated as a bug until this passes.
"""
import json
from fractions import Fraction

HERE = '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2'
J, LW, MOD, MODC = 3, 6, 27, 9
P, Q2, Q8 = Fraction(1, 4), Fraction(3, 4), Fraction(3, 2)   # lambda = 2


def windows():
    for d in range(4 ** LW):
        yield tuple((d >> (2 * (LW - 1 - i))) & 3 for i in range(LW))


def widx(D):
    x = 0
    for d in D:
        x = 4 * x + d
    return x


def covered(phase, D):
    S, A, hsum, ph = set(), set(), 0, phase
    for d in D:
        if ph == 2:
            S.add((hsum + d) % 3)
        elif ph == 8:
            A.add(((1 if d >= 2 else 0) + 2 * hsum) % 3)
        hsum = (hsum + d) % 3
        ph = (ph * 4) % 9
    S.add(hsum)                                   # tail
    return len(S) == 3 or len(A) == 3


def trans(q, D):
    out = []
    for e in range(4):
        out.append(((4 * q) % MOD, D[1:] + (e,), P / 4))
    if q % 9 == 2:
        z = ((4 * q - 2) // 3) % MODC
        for i in range(3):
            for e in range(4):
                out.append((z + i * MODC, D[1:] + (e,), Q2 / 12))
    elif q % 9 == 8:
        z = ((2 * q - 1) // 3) % MODC
        E = tuple((2 * D[i]) % 4 + (1 if D[i + 1] >= 2 else 0)
                  for i in range(LW - 1))
        for i in range(3):
            for c in range(2):
                out.append((z + i * MODC, E + ((2 * D[-1]) % 4 + c,), Q8 / 6))
    return out


def main():
    res = json.load(open(f'{HERE}/echarge_results.json'))
    balls = list(range(2, MOD, 3))
    states = [(q, D) for q in balls for D in windows()]
    ix = {s: i for i, s in enumerate(states)}
    unc = [not covered(q % 9, D) for (q, D) in states]

    # ECH1
    h1 = [Fraction(a, b) for a, b in json.load(open(f'{HERE}/ech1_h.json'))]
    R1 = Fraction(res['ECH1']['R_unc'])
    ok1, worst = True, Fraction(0)
    for i, (q, D) in enumerate(states):
        if not unc[i]:
            continue
        num = sum(w * h1[ix[(q2, D2)]] for (q2, D2, w) in trans(q, D)
                  if unc[ix[(q2, D2)]])
        ok1 &= num <= R1 * h1[i]
        worst = max(worst, num / h1[i])
    print(f'ECH1 recheck: rows<=R_unc: {"PASS" if ok1 else "FAIL"}; '
          f'max row ratio {worst} (< 1: {worst < 1})')

    # ECH2
    e2 = res['ECH2']
    if e2.get('feasible'):
        h2 = [Fraction(a, b) for a, b in json.load(open(f'{HERE}/ech2_h.json'))]
        z, R = Fraction(e2['z']), Fraction(e2['R'])
        a, b = e2['a'], e2['b']
        ok2 = True
        for i, (q, D) in enumerate(states):
            num = sum(w * h2[ix[(q2, D2)]] * (z if unc[ix[(q2, D2)]] else 1)
                      for (q2, D2, w) in trans(q, D))
            ok2 &= num <= R * h2[i]
        gap = (R.numerator ** b * z.denominator ** a <
               R.denominator ** b * z.numerator ** a)
        print(f'ECH2 recheck: rows<=R: {"PASS" if ok2 else "FAIL"}; '
              f'gap R^{b}<z^{a}: {"PASS" if gap else "FAIL"}')
    print('h1 positive:', all(x > 0 for x in h1),
          ' min/max h1:', float(min(h1)), float(max(h1)))


if __name__ == '__main__':
    main()
