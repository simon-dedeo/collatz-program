"""m4_data.py -- exact diagnostics from certified feasible subeigenvectors k=15,16.

Question: does normalized fiber oscillation PERSIST on balls that avoid the
exceptional set E_3 (zero charge), or does it decay?  If off-E balls carry
Theta(1) normalized oscillation, oscillation persists without charge =>
zero-charge oscillation is real => (CL) impossible (falsification), confirmed on
data (not on an envelope).

We also validate the between-sibling mass spread (sol-contraction L5 osc source)
and the per-ball mean oscillation, split by E_3 membership.  Exact int64 sums.
Reuses the fiber layout: index i in [0,3^(k-1)); state m=2+3i; the fiber of a
level-(k-1) state r is {i_r, i_r+3^(k-2), i_r+2*3^(k-2)} (three lifts); ball of
r is (2+3*i_r) mod 27 ... we group level-(k-1) states by ball mod 27.
"""
import json, csv, os
import numpy as np
import automaton as am

KL = '/Users/simon/Desktop/COLLATZ/experiments/kl'
MOD = 27
E = set(am.exceptional_set(3))     # {5,20,26}


def fiber_osc_by_ball(k):
    """Return per-ball (mod 27) stats of level-(k-1) fibers.
    C array: index i<->m=2+3i.  Lift stride = 3^(k-2): fiber of level-(k-1)
    state s (s in [0,3^(k-2))) is C[s], C[s+stride], C[s+2*stride]."""
    C = np.load(f'{KL}/cert_k{k}_C.npy')
    stride = 3 ** (k - 2)
    a = C[:stride].astype(np.int64)
    b = C[stride:2 * stride].astype(np.int64)
    c = C[2 * stride:3 * stride].astype(np.int64)
    mx = np.maximum(np.maximum(a, b), c)
    mn = np.minimum(np.minimum(a, b), c)
    mean = (a + b + c) / 3.0
    rng = (mx - mn).astype(np.float64)
    osc = np.where(mean > 0, rng / mean, 0.0)
    # ball of level-(k-1) state s: m = 2+3s, ball = m mod 27
    s_idx = np.arange(stride, dtype=np.int64)
    ball = (2 + 3 * s_idx) % MOD
    stats = {}
    for q in am.states(3):
        sel = ball == q
        n = int(sel.sum())
        stats[q] = {
            'ball': q, 'in_E': int(q in E), 'n_fibers': n,
            'mean_osc': float(osc[sel].mean()),
            'mass': float(mean[sel].sum() * 3),          # total fiber mass
            'frac_osc_gt_0.2': float((osc[sel] > 0.2).mean()),
        }
    return stats


if __name__ == '__main__':
    outdir = os.path.dirname(os.path.abspath(__file__))
    allrows = []
    summary = []
    for k in (15, 16):
        st = fiber_osc_by_ball(k)
        for q in am.states(3):
            r = dict(st[q]); r['k'] = k; allrows.append(r)
        # aggregate: mean osc over E balls vs C balls (mass-weighted)
        def agg(inE):
            tot_mass = sum(st[q]['mass'] for q in am.states(3) if st[q]['in_E'] == inE)
            wosc = sum(st[q]['mean_osc'] * st[q]['mass'] for q in am.states(3) if st[q]['in_E'] == inE)
            return wosc / tot_mass if tot_mass else 0.0, tot_mass
        oscE, mE = agg(1)
        oscC, mC = agg(0)
        summary.append({'k': k, 'massweighted_osc_E': round(oscE, 5),
                        'massweighted_osc_C': round(oscC, 5),
                        'mass_frac_C': round(mC / (mC + mE), 5)})
        print(f"k={k}: mass-weighted mean osc  E_3={oscE:.4f}  C(zero-charge)={oscC:.4f}"
              f"  ;  mass fraction in C = {mC/(mC+mE):.4f}")
    with open(os.path.join(outdir, 'csv', 'm4_ball_osc.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=['k', 'ball', 'in_E', 'n_fibers', 'mean_osc',
                                          'mass', 'frac_osc_gt_0.2'])
        w.writeheader()
        for r in allrows:
            w.writerow({kk: r[kk] for kk in w.fieldnames})
    with open(os.path.join(outdir, 'csv', 'm4_summary.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(summary[0].keys())); w.writeheader(); w.writerows(summary)
    print("Per-ball detail -> csv/m4_ball_osc.csv")
