#!/usr/bin/env python3
"""verify_lemma5_cert.py -- INDEPENDENT verifier for lemma5_exact_cert.json
(format pressure-cert/lemma5-portable-v2).

Deliberately imports NOTHING from the generator modules: plain python
stdlib (json, hashlib, fractions).  Reads the JSON from disk and re-verifies
every row in exact rational/integer arithmetic:

  H0  sha256 of the canonical payload matches the pinned digest.
  S1  states are exactly {q mod 3^J : q = 2 mod 3}; E is exactly the
      backward <4>-orbit {-4^(-t) mod 3^J : t < J}; exc flags match;
      b(e) = 1_{tgt in E}.
  S2  the edge multiset per piece is exactly the automaton from first
      principles (T: q->4q; B2/B8: the three lifted coarse targets, /3
      dilution encoded in the weights).
  S3  weight soundness per piece by pure integer inequalities:
      2^P > 3^Q; Q < P < 2Q; 1 < lam_lo <= lam_hi <= 2;
      w_T >= lam_lo^-2;  (3 w_B2)^Q * a^(2Q-P) >= b^(2Q-P)  (lam_lo = a/b);
      (3 w_B8)^Q * d^(P-Q) >= c^(P-Q)                        (lam_hi = c/d).
  S4  pieces tile [lambda_lo, lambda_hi] contiguously.
  P1  for every (piece, state q): sum_e w_e z^b(e) h(tgt) <= R h(q).
  P2  h > 0 everywhere; z > 1; theta > 0; R z^-theta < 1 by the integer
      comparison R_n^td * z_d^tn < R_d^td * z_n^tn (theta = tn/td).

Exit code 0 iff every check passes.  Usage:
  python3 verify_lemma5_cert.py [path/to/lemma5_exact_cert.json]
"""

import hashlib
import json
import sys
from fractions import Fraction


def frac(s):
    n, d = s.split('/')
    return Fraction(int(n), int(d))


def geq_pow(W: Fraction, lam: Fraction, u: int, v: int) -> bool:
    """Exact check  W >= lam^(u/v),  v > 0, lam > 0, u any sign."""
    a, b = lam.numerator, lam.denominator
    wn, wd = W.numerator, W.denominator
    if u >= 0:
        return wn ** v * b ** u >= wd ** v * a ** u
    return wn ** v * a ** (-u) >= wd ** v * b ** (-u)


def check(cond, label, errors):
    if not cond:
        errors.append(label)
    return cond


def verify_certificate(cert, P, Q, errors):
    name = cert['name']
    J, mod = cert['J'], cert['modulus']
    check(mod == 3 ** J, f'{name}: modulus', errors)
    modc = mod // 3

    # ---- S1: states and exceptional set from first principles
    S_expect = list(range(2, mod, 3))
    states = cert['states']
    check([s['q'] for s in states] == S_expect, f'{name}: state set', errors)
    inv4 = pow(4, -1, mod)
    x, E_expect = (-1) % mod, []
    for _ in range(J):
        E_expect.append(x)
        x = (x * inv4) % mod
    check(sorted(cert['E']) == sorted(E_expect), f'{name}: E orbit', errors)
    Eset = set(cert['E'])
    for s in states:
        check(s['exc'] == (1 if s['q'] in Eset else 0),
              f"{name}: exc flag q={s['q']}", errors)
    h = {s['q']: frac(s['h']) for s in states}
    check(all(v > 0 for v in h.values()), f'{name}: h > 0', errors)

    # ---- S4 + S3: pieces tile the interval; weights sound
    lam_lo, lam_hi = frac(cert['lambda_lo']), frac(cert['lambda_hi'])
    pieces = cert['pieces']
    check(frac(pieces[0]['lam_lo']) == lam_lo, f'{name}: piece tiling lo', errors)
    check(frac(pieces[-1]['lam_hi']) == lam_hi, f'{name}: piece tiling hi', errors)
    for i in range(len(pieces) - 1):
        check(frac(pieces[i]['lam_hi']) == frac(pieces[i + 1]['lam_lo']),
              f'{name}: piece tiling {i}', errors)
    for i, pc in enumerate(pieces):
        a, b = frac(pc['lam_lo']), frac(pc['lam_hi'])
        check(1 < a <= b <= 2, f'{name}: piece {i} lambda range', errors)
        wT, w2, w8 = frac(pc['w_T']), frac(pc['w_B2']), frac(pc['w_B8'])
        check(wT >= a ** -2, f'{name}: piece {i} w_T', errors)
        check(geq_pow(3 * w2, a, P - 2 * Q, Q), f'{name}: piece {i} w_B2', errors)
        check(geq_pow(3 * w8, b, P - Q, Q), f'{name}: piece {i} w_B8', errors)

    # ---- S2: edge multiset per piece from first principles
    def expected_edges():
        out = []
        for q in S_expect:
            out.append((q, (4 * q) % mod, 'T'))
            if q % 9 == 2:
                zt = ((4 * q - 2) // 3) % modc
                out += [(q, zt + i * modc, 'B2') for i in range(3)]
            elif q % 9 == 8:
                zt = ((2 * q - 1) // 3) % modc
                out += [(q, zt + i * modc, 'B8') for i in range(3)]
        return sorted(out)

    exp = expected_edges()
    wkind = [{'T': frac(pc['w_T']), 'B2': frac(pc['w_B2']),
              'B8': frac(pc['w_B8'])} for pc in pieces]
    got = {i: [] for i in range(len(pieces))}
    for e in cert['edges']:
        pi = e['piece']
        check(e['b'] == (1 if e['tgt'] in Eset else 0),
              f"{name}: b(e) {e['src']}->{e['tgt']}", errors)
        check(frac(e['w']) == wkind[pi][e['kind']],
              f"{name}: edge w vs piece table {e}", errors)
        got[pi].append((e['src'], e['tgt'], e['kind']))
    for pi in range(len(pieces)):
        check(sorted(got[pi]) == exp, f'{name}: edge multiset piece {pi}', errors)

    # ---- P1: row inequalities, exact
    z, theta, R = frac(cert['z']), frac(cert['theta']), frac(cert['R'])
    rows = 0
    for pi in range(len(pieces)):
        lhs = {q: Fraction(0) for q in S_expect}
        for e in cert['edges']:
            if e['piece'] != pi:
                continue
            w = frac(e['w'])
            lhs[e['src']] += w * (z if e['b'] else 1) * h[e['tgt']]
        for q in S_expect:
            check(lhs[q] <= R * h[q], f'{name}: row piece={pi} q={q}', errors)
            rows += 1

    # ---- P2: gap inequality, integer form
    check(z > 1 and theta > 0, f'{name}: z,theta ranges', errors)
    tn, td = theta.numerator, theta.denominator
    check(R.numerator ** td * z.denominator ** tn
          < R.denominator ** td * z.numerator ** tn,
          f'{name}: R z^-theta < 1', errors)
    return rows, len(cert['edges'])


def main(path):
    with open(path) as f:
        doc = json.load(f)
    errors = []
    check(doc.get('format') == 'pressure-cert/lemma5-portable-v2',
          'format tag', errors)

    # H0: payload hash
    sha = doc.pop('sha256_payload', None)
    canon = json.dumps(doc, sort_keys=True, separators=(',', ':'))
    check(hashlib.sha256(canon.encode()).hexdigest() == sha,
          'sha256 payload', errors)

    # alpha upper bound: P/Q > log2(3), 1 < P/Q < 2
    P, Q = doc['alpha_upper']['P'], doc['alpha_upper']['Q']
    check(2 ** P > 3 ** Q, 'alpha: 2^P > 3^Q', errors)
    check(Q < P < 2 * Q, 'alpha: Q < P < 2Q', errors)

    total_rows = total_edges = 0
    for cert in doc['certificates']:
        rows, edges = verify_certificate(cert, P, Q, errors)
        total_rows += rows
        total_edges += edges
        print(f"  cert '{cert['name']}': J={cert['J']} pieces="
              f"{len(cert['pieces'])} states={len(cert['states'])} "
              f"edges={edges} row-inequalities={rows} -> "
              f"{'OK so far' if not errors else 'ERRORS'}")

    if errors:
        print(f'FAIL: {len(errors)} failed checks; first 10:')
        for e in errors[:10]:
            print('  -', e)
        return 1
    print(f'PASS: all checks (sha256, alpha bound, {total_edges} edges, '
          f'{total_rows} row inequalities, gap inequalities) verified exactly.')
    return 0


if __name__ == '__main__':
    p = sys.argv[1] if len(sys.argv) > 1 else \
        '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert/lemma5_exact_cert.json'
    sys.exit(main(p))
