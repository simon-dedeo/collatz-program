"""m6_witness.py -- emit the portable FALSIFICATION witness JSON.
No certificate was found; instead an explicit zero-charge oscillation-carrying
cycle with normalized-oscillation eigenvalue exactly 1 (marginal).  Format
'pressure-cert2/falsification-v1'.  Self-contained; re-checkable by m5_recheck.
"""
import json, os, hashlib
from fractions import Fraction as F

WIT = {
    "format": "pressure-cert2/falsification-v1",
    "target": "Charged spine-face Lyapunov lemma (CL) at (J=3, L_w=6)",
    "verdict": "FALSIFIED",
    "reason": ("The oscillation-carrying (aligned top-window) face is exactly "
               "MARGINAL and is not forced to incur E_3 charge; a zero-charge "
               "cycle carries nonzero spine-face oscillation with normalized "
               "eigenvalue exactly 1. Hence no rho<1/R6 can satisfy (CL)+(SG)."),
    "charge_def": "e(gamma)=#{low-window edge targets in E_3}, E_3={5,20,26} mod 27",
    "aligned_block": {
        "phases": [2, 8, 5, 2, 8, 5],
        "events": ["B2@0", "B8@1", "B2@3", "B8@4", "tail p^6"],
        "aligned_perms": {"transport": "j->j", "B2": "j->j", "B8": "j->2j (swap 1,2)"},
        "marginal_eigenvector": [2, -1, -1],
        "lam=2": {"p": "1/4", "q2": "3/4", "q8": "3/2",
                  "perron_mean": "4681/4096", "eig_osc": "4681/4096",
                  "normalized_osc_eigenvalue": "1"},
        "note": ("(2,-1,-1) is fixed by every aligned perm (identity fixes all; "
                 "swap fixes (2,-1,-1)); so it is an eigenvector with the SAME "
                 "eigenvalue as the mean (1,1,1), for EVERY lambda and every "
                 "symmetric policy D0=D1=D2. Normalized osc multiplier == 1 exactly.")
    },
    "zero_charge_cycle": {
        "complement_C": [2, 8, 11, 14, 17, 23],
        "E_3": [5, 20, 26],
        "C_strongly_connected_avoiding_E3": True,
        "trivial_selfloop": "B2 at ball 2 -> {2,11,20}: target 2 in C (e=0)",
        "osc_carrying_edge": ("B8 at ball 8 -> siblings {5,14,23}; drop E-sibling "
                              "5, keep 14,23 in C: carries between-sibling swap "
                              "oscillation with zero charge"),
    },
    "coupling_gap": ("Top-window (aligned/oscillation) and low-window (E_3 charge) "
                     "are independent coordinates of r; the aligned class is "
                     "reachable at every ball state; the <4>-orbit of -1 fills "
                     "Q_J. No supplied theorem forces aligned-class time to visit "
                     "E_3. (Confirmed by gpt-5.6-sol, independently verified.)"),
    "gap_estimate_to_lambda_inf": {
        "cycle_growth_rate": 1.0,
        "meaning": ("MARGINAL (exactly 1): zero Lyapunov gap => (CL) architecture "
                    "does NOT close at (3,6). Does NOT imply lambda_inf<2; "
                    "consistent with renormalization-at-minus-one's transversal "
                    "spectrum {0,1} and 'no autonomous transversal decay'."),
    },
    "data_corroboration": {
        "source": "experiments/kl/cert_k15_C.npy, cert_k16_C.npy (exact int64)",
        "mass_weighted_mean_osc_k15": {"E_3": 0.0773, "C_zero_charge": 0.0698},
        "mass_weighted_mean_osc_k16": {"E_3": 0.0702, "C_zero_charge": 0.0635},
        "mass_fraction_in_C_k15": 0.5230,
        "reading": ("Oscillation on zero-charge balls ~ oscillation on E_3 "
                    "(ratio ~0.9); ~52% of eigenvector mass sits off E_3 and "
                    "carries comparable oscillation. Charge does not localize "
                    "oscillation at J=3."),
    },
    "envelope_check": {
        "module": "m3_augmented.py",
        "rho_mass_full_lam2": 1.0, "matches_s(2)": True,
        "rho_mass_C_lam2": 0.639285,
        "normalized_osc_growth_C_lam2": 1.029,
        "note": ("Upper-bound (M,R) envelope: mass part validated (=s(lambda)); "
                 "normalized oscillation growth stays >=1 even on zero-charge C, "
                 "corroborating non-decay (envelope is an upper bound; the exact "
                 "marginal value is 1 from the eigenvector identity above)."),
    },
    "validation": {
        "V1_index_arithmetic_k7_k8": "PASS (sol-contraction Lemma 1)",
        "V2_ball_domination_k15_k16": "PASS (exact int; automaton mass = Lemma 5)",
        "independent_recheck": "m5_recheck.py (stdlib, plain Fractions) -> CONFIRMED",
    },
}

if __name__ == '__main__':
    outdir = os.path.dirname(os.path.abspath(__file__))
    payload = json.dumps(WIT, indent=1, sort_keys=True)
    sha = hashlib.sha256(payload.encode()).hexdigest()
    WIT["sha256_payload"] = sha
    path = os.path.join(outdir, 'falsification_witness.json')
    with open(path, 'w') as f:
        json.dump(WIT, f, indent=1)
    print("wrote", path, "sha256", sha[:16])
