"""portable_cert.py -- emit the self-contained combined-localization
certificate per CLEAN_LEAN/GPU_CERTIFICATE_SPEC.md."""
import csv
import hashlib
import json
from fractions import Fraction

HERE = '/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2'


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def main():
    res = json.load(open(f'{HERE}/echarge_results.json'))
    tau_rows = list(csv.DictReader(open(f'{HERE}/blocks_tau.csv')))
    lam2K2 = {r['phase']: r for r in tau_rows
              if r['tag'] == 'lam2' and r['K'] == '2'}
    cert = {
        'name': 'combined-localization-certificate',
        'version': '2026-07-20.1',
        'checker': 'recheck.py (independent code path, exact Fractions)',
        'state_semantics': {
            'low_window': 'ball q mod 3^3, q==2 mod 3 (9 states)',
            'top_window': 'first 6 base-4 digits of u=m/3^k (4096 windows); '
                          'DEPTH-MEMORY register, not static residue '
                          '(<4>-orbit of -1 fills Q_J, so residue-E is vacuous)',
            'states': 36864, 'edges': 368640, 'min_level': 'k >= 11',
            'exceptional_charge_rule': 'b(e)=1 iff TARGET window uncovered: '
                'S = {tail+B2 shift adds}, A = {B8 affine adds}; covered iff '
                '|S|=3 or |A|=3; -1 spine (all-3 digits) is uncovered forever',
            'cone_cell': 'HYPOTHESIS (not proved): all admissible input '
                'profiles in C_K, K=2 (empirical max 1.87 at k=15,16); '
                'D-interval [3/(2K+1),1] dominates every minimizing policy '
                'within C_K; K-degradation table in blocks_tau.csv',
        },
        'weights_lambda2_exact': {'p': '1/4', 'q2': '3/4', 'q8': '3/2',
                                  'proof': '2^alpha=3 exactly; alpha sandwich '
                                  '50508/31867 < alpha < 24727/15601 by integer '
                                  'power comparison (exact_weights.py)'},
        'transitions': {
            'T': 'q->4q mod 27; window shifts left, new digit e (4 edges, p/4)',
            'B2': 'q==2(9): R2(q)+i*9; window shifts left (12 edges, q2/12)',
            'B8': 'q==8(9): R8(q)+i*9; window x2-map e_i=2d_i mod4+[d_{i+1}>=2],'
                  ' last-digit carry c (6 edges, q8/6)',
            'model': 'ANNEALED U-SPLIT (hypothesis U): new-digit mass share '
                     'sigma; Haar sigma=1/4 used; measured on certified '
                     'k=15,16 vectors: sigma_max=0.419/0.343, mass-weighted '
                     '0.2514/0.2505; borrow (-1 cylinder) edges are '
                     'k-boundary terms of Haar measure O(3^-k 4^Lw), verified '
                     'exhaustively at k=9,10 (validate2.py T1)',
        },
        'localization': {
            'good_block_contraction': {
                'phase2': {'covered': 840, 'of': 4096,
                           'X_max': lam2K2['2']['X_max'],
                           'tau_upper': lam2K2['2']['tau_upper'],
                           'tau_float': float(lam2K2['2']['tau_float'])},
                'phase5': {'covered': 672, 'of': 4096,
                           'X_max': lam2K2['5']['X_max'],
                           'tau_upper': lam2K2['5']['tau_upper'],
                           'tau_float': float(lam2K2['5']['tau_float'])},
                'phase8': {'covered': 0, 'of': 4096,
                           'note': 'L_w=6 never covers phase 8; covered '
                                   'fraction 0.377 at L=9 (needs L_w>=9)'},
            },
            'bad_block_amplification': 'C=1 projectively: every block matrix '
                'has no zero rows (verified for all 12288 (phase,window)) => '
                'Hilbert-metric nonexpansive; envelope row bound C_row <= '
                '5/3 + eps at lambda=2, K=2 (blocks_tau.csv)',
            'charge_density': 'osc > t forces all but O_t(1) visited states '
                'to be uncovered (each covered visit contracts d_H by tau); '
                'sufficient rational density theta = a/b = 60/64 = 15/16',
            'model_caveat': 'single-profile envelope: block terms treat '
                'sibling/transport inputs as one profile; the honest '
                'multi-input (product-cone) contraction is NOT certified '
                'here -- this is the remaining Lemma-3 model gap',
        },
        'tilted_pressure': {
            'restricted_gap_ECH1': {
                'statement': 'sum over unc->unc edges w_e h(q\') <= R_unc h(q)',
                'R_unc': res['ECH1']['R_unc'],
                'R_unc_float': res['ECH1']['R_unc_float'],
                'h_sidecar': 'ech1_h.json', 'h_sha256': sha(f'{HERE}/ech1_h.json'),
            },
            'tilted_ECH2': {
                'statement': 'sum_e w_e z^{b(e)} h(q\') <= R h(q), all 36864 rows',
                'z': res['ECH2']['z'], 'R': res['ECH2']['R'],
                'R_float': res['ECH2']['R_float'],
                'a': res['ECH2']['a'], 'b': res['ECH2']['b'],
                'gap': 'R^64 < z^60, exact integer comparison, PASS',
                'h_sidecar': 'ech2_h.json', 'h_sha256': sha(f'{HERE}/ech2_h.json'),
            },
            'pi_unc_annealed': res['pi_unc_float'],
            'nu_unc_measured_k15_k16': [0.900389, 0.900791],
        },
        'verdict': {
            'off_exceptional_contraction': 'YES on covered states (tau<1 '
                'exact) for phases 2,5; phase 8 empty at L_w=6',
            'aligned_leak': 'face cone (option a): 2x2 face contracts '
                '(tau_face <= 0.539/0.539/0.963 by phase, clean-face half); '
                'pinned-scale multiplier interval [0.600,1.667] CONTAINS 1: '
                'marginal mode, cannot close alone. Charge treatment '
                '(option b): CLOSES in-model: R_unc = 52435/57248 < 1 and '
                'R^64 < z^60 with theta=15/16 < 1 available from '
                'localization.',
            'unconditional': False,
            'remaining_hypotheses': [
                'U(sigma): u-digit mass split; worst-case measured 0.343-0.419 '
                '(need <= 0.273 for pointwise closure R_unc*4sigma<1 at (3,6); '
                'mass-weighted 0.2505 closes with margin 0.918)',
                'C_K product-cone invariance (K=2), incl. sibling cross-fiber '
                'independence -- single-profile envelope not yet dominated',
                'uniform lambda in [lam18,2] version (only lambda=2 emitted '
                'here; tau uniform data present in blocks_tau.csv)'],
        },
        'sidecar_hashes': {f: sha(f'{HERE}/{f}') for f in
                           ('blocks_tau.csv', 'dfa_counts.csv', 'facecone.csv',
                            'echarge_results.json')},
    }
    out = f'{HERE}/cert_combined_J3Lw6.json'
    json.dump(cert, open(out, 'w'), indent=1)
    print('wrote', out)


if __name__ == '__main__':
    main()
