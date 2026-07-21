#!/usr/bin/env python3
"""pressure_cert.py -- orchestrator for the Lemma 3 + Lemma 5 certificate search.

Writes:
  lemma3_blocks.csv    per (L, phase, K): coverage + Birkhoff data (exact-arith
                       domination over policies, top-digit u-cells, lambda-interval)
  lemma3_census.csv    coverage-count distribution per (L, phase)
  lemma5_theta.csv     per (J, z): exactly-verified (h, R), theta_req = lnR/lnz,
                       for lambda-interval [lam18,2] and for lambda=2
  lemma5_scaling.csv   per J: pi(E_J), theta*(J), rho_offE, first-return sum
  lemma5_exact_cert.json  one fully exact certificate instance (2.9)+(2.10)
  validation.csv       V1-V4 results
Run:  python3 pressure_cert.py [--full]
"""

import csv
import json
import sys
from fractions import Fraction

import automaton as am
import exact_weights as ew
import lemma3 as l3
import lemma5 as l5

HERE = '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert'
TWO = Fraction(2)
LAM18 = ew.LAM18


def write_csv(name, rows, fields=None):
    if not rows:
        return
    fields = fields or list(rows[0].keys())
    with open(f'{HERE}/{name}', 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction='ignore')
        w.writeheader()
        for r in rows:
            w.writerow({k: (str(v) if isinstance(v, Fraction) else v)
                        for k, v in r.items()})
    print('wrote', name, f'({len(rows)} rows)')


def run_lemma3(full=False):
    census = []
    for L in (3, 6, 9):
        for phase in (2, 5, 8):
            for cover, cnt in sorted(l3.coverage_census(phase, L).items()):
                census.append({'L': L, 'phase': phase, 'cells_covering': cover,
                               'count': cnt, 'fraction': cnt / 4 ** L})
    write_csv('lemma3_census.csv', census)
    rows = []
    for L in ((3, 6, 9) if full else (6, 9)):
        for K in (2, 4):
            rows += l3.scan_phase(L, LAM18, TWO, K)
    write_csv('lemma3_blocks.csv', rows)
    return rows


def run_lemma5():
    theta_rows = []
    for J in (2, 3, 4, 5, 6):
        E = am.exceptional_set(J)
        for tag, lo, hi, pieces in (('uniform[lam18,2]', LAM18, TWO, 8),
                                    ('lam=2', TWO, TWO, 1)):
            rows, best = l5.theta_star(J, E, lo, hi, pieces=pieces)
            for r in rows:
                theta_rows.append({'J': J, 'range': tag, 'z': r['z'],
                                   'R_exact': r['R'], 'R_float': r['R_float'],
                                   'theta_req': r['theta_req'],
                                   'best': r is best})
    write_csv('lemma5_theta.csv', theta_rows)
    return theta_rows


def run_scaling():
    """Float scaling diagnostics J=3..10, sparse edge-list matvecs."""
    import numpy as np
    from math import log
    rows = []
    for J in range(3, 11):
        E = set(am.exceptional_set(J))
        S = am.states(J)
        ix = {q: i for i, q in enumerate(S)}
        n = len(S)
        ed = am.edges(J)
        src = np.array([ix[s] for (s, d, k) in ed])
        dst = np.array([ix[d] for (s, d, k) in ed])
        kind = np.array([0 if k == 'T' else (1 if k == 'B2' else 2)
                         for (s, d, k) in ed])
        inE = np.array([1.0 if d in E else 0.0 for (s, d, k) in ed])

        def rad_vec(lam, z=1.0, transpose=False, mask=None, it=20000):
            a = log(3, 2)
            wt = np.where(kind == 0, lam ** -2,
                          np.where(kind == 1, lam ** (a - 2) / 3,
                                   lam ** (a - 1) / 3))
            wt = wt * np.where(inE > 0, z, 1.0)
            s_, d_ = (dst, src) if transpose else (src, dst)
            if mask is not None:
                keep = mask[src] & mask[dst]
                s_, d_, wt = s_[keep], d_[keep], wt[keep]
            v = np.ones(n)
            r = 1.0
            for _ in range(it):
                v2 = np.zeros(n)
                np.add.at(v2, s_, wt * v[d_])
                r2 = v2.max()
                if r2 == 0:
                    return 0.0, v
                v2 /= r2
                if np.abs(v2 - v).max() < 1e-13:
                    return r2, v2
                v, r = v2, r2
            return r, v

        rho, v = rad_vec(2.0)
        _, u = rad_vec(2.0, transpose=True)
        w = u * v
        w /= w.sum()
        piE = float(sum(w[i] for i, q in enumerate(S) if q in E))
        zs = (1.02, 1.05, 1.1, 1.25, 1.5, 2.0, 4.0)
        ths2 = [log(rad_vec(2.0, z)[0]) / log(z) for z in zs]
        ths18 = [log(rad_vec(float(LAM18), z)[0]) / log(z) for z in zs]
        mask = np.array([q not in E for q in S])
        rOff = rad_vec(2.0, mask=mask)[0]
        ret, rho_cc = (l5.first_return_sum(J, l5.weights_at(TWO), E)
                       if J <= 8 else (None, None))
        rows.append({'J': J, 'E_size': len(E), 'pi_E_lam2': piE,
                     'theta_star_lam2': min(ths2),
                     'theta_star_uniform_lam18': min(ths18),
                     'rho_offE_lam2': float(rOff),
                     'first_return_sum_lam2': ret})
    write_csv('lemma5_scaling.csv', rows)
    return rows


PREDICATE = [
    "PORTABLE CERTIFICATE. Claim per certificate, all arithmetic exact rational:",
    "(P1) for every piece and every state q:",
    "       sum over edges e with piece(e)=piece, src(e)=q of",
    "         w_e * z^b(e) * h(tgt(e))  <=  R * h(q),",
    "(P2) R * z^(-theta) < 1,  z > 1,  theta > 0,  h(q) > 0 for all q.",
    "Soundness side conditions (checked by the verifier from first principles):",
    "(S1) states = all residues q mod 3^J with q = 2 mod 3;",
    "     E = {-4^(-t) mod 3^J : 0 <= t < J} (backward <4>-orbit balls);",
    "     b(e) = 1 if tgt(e) in E else 0.",
    "(S2) edges per piece are EXACTLY: T: q -> 4q mod 3^J; and for q = 2 mod 9",
    "     the three B2 edges q -> ((4q-2)/3 mod 3^(J-1)) + i*3^(J-1), i=0,1,2;",
    "     for q = 8 mod 9 the three B8 edges with (2q-1)/3.  (Per-fiber-mass",
    "     normalization: branch weights carry the /3 dilution.)",
    "(S3) weight soundness on the piece [lam_lo, lam_hi] (1 < lam_lo <= lam_hi <= 2):",
    "     w_T >= lam_lo^(-2) >= lambda^(-2);",
    "     3*w_B2 >= lam_lo^(P/Q - 2) > lambda^(alpha-2)   (alpha < P/Q, lam > 1,",
    "       and lambda^(alpha-2) decreasing in lambda since alpha < 2);",
    "     3*w_B8 >= lam_hi^(P/Q - 1) > lambda^(alpha-1)   (increasing, alpha > 1);",
    "     P/Q > alpha = log2(3) certified by the integer inequality 2^P > 3^Q;",
    "     P/Q < 2 and P/Q > 1 certified by P < 2Q, P > Q.",
    "(S4) pieces tile [lambda_lo, lambda_hi] contiguously.",
    "Consequence (sol-pressure.md (2.9)-(2.11)): for every c <= F_lambda(c),",
    "lambda in [lambda_lo, lambda_hi], every minimizing policy, the ball-mass",
    "flow M satisfies M <= W M edgewise-dominated by (w_e); Markov then gives",
    "nu_k{N_E >= theta*n} <= C*(R*z^(-theta))^n per n automaton moves.",
]

STATE_ENCODING = (
    "state q = integer residue mod 3^J, q = 2 mod 3 (the 3-adic ball"
    " B(q,3^-J) in Y = 2+3Z_3); 'exc' = 1 iff q in E; h = 'num/den'"
    " positive rational; edges keyed (piece,src,tgt,kind) with kind in"
    " {T,B2,B8}; w = 'num/den' certified upper bound valid on the piece.")


def _frac(s: Fraction) -> str:
    return f'{s.numerator}/{s.denominator}'


def _build_portable(name, J, z, theta, lam_lo, lam_hi, npieces):
    E = am.exceptional_set(J)
    Eset = set(E)
    S = am.states(J)
    # pieces with certified endpoint weight bounds (the ones actually used)
    pieces, subw = [], []
    for i in range(npieces):
        a = lam_lo + (lam_hi - lam_lo) * i / npieces
        b = lam_lo + (lam_hi - lam_lo) * (i + 1) / npieces
        enc = ew.weight_enclosures(a, b)
        pieces.append({'lam_lo': _frac(a), 'lam_hi': _frac(b),
                       'w_T': _frac(enc['p_hi']),
                       'w_B2': _frac(enc['q2_hi'] / 3),
                       'w_B8': _frac(enc['q8_hi'] / 3)})
        subw.append({'p': enc['p_hi'], 'q2': enc['q2_hi'],
                     'q8': enc['q8_hi']})
    h, R, _ = l5.certify_h(J, subw, E, z)
    assert l5.exact_gap_check(R, z, theta), (name, 'gap check failed')
    ix = {q: i for i, q in enumerate(S)}
    edges = []
    for pi, pc in enumerate(pieces):
        wk = {'T': pc['w_T'], 'B2': pc['w_B2'], 'B8': pc['w_B8']}
        for (src, tgt, kind) in am.edges(J):
            edges.append({'piece': pi, 'src': src, 'tgt': tgt, 'kind': kind,
                          'b': 1 if tgt in Eset else 0, 'w': wk[kind]})
    return {'name': name, 'J': J, 'modulus': 3 ** J,
            'lambda_lo': _frac(lam_lo), 'lambda_hi': _frac(lam_hi),
            'z': _frac(z), 'theta': _frac(theta), 'R': _frac(R),
            'R_float': float(R), 'E': E,
            'states': [{'q': q, 'exc': 1 if q in Eset else 0,
                        'h': _frac(h[ix[q]])} for q in S],
            'pieces': pieces, 'edges': edges}


def run_exact_instance():
    """Portable, self-contained (2.9)+(2.10) certificates (format v2):
    lambda=2 (J=6, z=5/4, theta=1/8) and uniform [lam18,2] (J=6, z=3/2,
    theta=1/4, 8 pieces).  Independently re-checkable from the JSON alone
    by verify_lemma5_cert.py."""
    import hashlib
    payload = {
        'format': 'pressure-cert/lemma5-portable-v2',
        'predicate': PREDICATE,
        'state_encoding': STATE_ENCODING,
        'alpha_upper': {'P': 24727, 'Q': 15601,
                        'certifies': 'P/Q > log2(3) via 2^P > 3^Q'},
        'certificates': [
            _build_portable('lam2', 6, Fraction(5, 4), Fraction(1, 8),
                            TWO, TWO, 1),
            _build_portable('uniform_lam18_2', 6, Fraction(3, 2),
                            Fraction(1, 4), LAM18, TWO, 8),
        ],
    }
    canon = json.dumps(payload, sort_keys=True, separators=(',', ':'))
    payload['sha256_payload'] = hashlib.sha256(canon.encode()).hexdigest()
    with open(f'{HERE}/lemma5_exact_cert.json', 'w') as f:
        json.dump(payload, f, indent=1)
    print('wrote lemma5_exact_cert.json;',
          'certs:', [c['name'] for c in payload['certificates']],
          'edges:', [len(c['edges']) for c in payload['certificates']],
          'sha256:', payload['sha256_payload'][:16], '...')
    return payload


def run_validation(deep=False):
    import validate as va
    rows = []
    for k in (7, 8):
        rows.append({'check': f'V1_index_arithmetic_k{k}',
                     'result': 'PASS' if va.v1_index_arithmetic(k, False)
                     else 'FAIL'})
    for k in (15, 16):
        for J in (2, 3):
            s, m, sl = va.v2_ball_domination(k, J, False)
            rows.append({'check': f'V2_ball_domination_k{k}_J{J}',
                         'result': 'PASS' if (s and m) else 'FAIL',
                         'min_rel_slack': sl})
    for k, K in va.v4_cone_K((15, 16), False).items():
        rows.append({'check': f'V4_cone_K_k{k}', 'result': f'{K:.4f}'})
    ks = (15, 16, 17, 18, 19) if deep else (15, 16)
    for r in va.v3_empirical_E_mass(ks=ks, verbose=False):
        rows.append({'check': f"V3_nuE_k{r['k']}_J{r['J']}",
                     'result': f"{r['nu_E']:.6f}"})
    write_csv('validation.csv', rows,
              fields=['check', 'result', 'min_rel_slack'])
    return rows


if __name__ == '__main__':
    full = '--full' in sys.argv
    steps = [a for a in sys.argv[1:] if not a.startswith('--')] or \
            ['lemma3', 'lemma5', 'scaling', 'exact', 'validation']
    if 'lemma3' in steps:
        print('== Lemma 3 ==', flush=True)
        run_lemma3(full)
    if 'lemma5' in steps:
        print('== Lemma 5 ==', flush=True)
        run_lemma5()
    if 'scaling' in steps:
        print('== scaling ==', flush=True)
        run_scaling()
    if 'exact' in steps:
        print('== exact instance ==', flush=True)
        run_exact_instance()
    if 'validation' in steps:
        print('== validation ==', flush=True)
        run_validation(deep=full)
