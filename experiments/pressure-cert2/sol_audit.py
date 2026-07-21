"""One authorized external audit call (OpenAI responses API, gpt-5.6-sol)."""
import json
import ssl
import urllib.request

try:
    import certifi
    _CTX = ssl.create_default_context(cafile=certifi.where())
except ImportError:
    _CTX = ssl.create_default_context()

KEY = open('/Users/simon/Desktop/DANIEL/API_KEY').read().strip()

BRIEF = """Audit request (Collatz KL pressure program, combined automaton).
Setup: states = (ball q mod 27) x (first 6 base-4 digits D of u=m/3^k).
Exceptional = window-uncovered: block support classes S (tail+B2 shift adds),
A (B8 affine adds); covered iff |S|=3 or |A|=3 (verified vs matrices).
Depth-memory, not residue (the <4>-orbit of -1 fills Q_J). Annealed u-split
mass model at lambda=2 (p,q2,q8 = 1/4,3/4,3/2 exact): T edges p/4 x4,
B2 q2/12 x12, B8 q8/6 x6 (x2 digit map with carry); columns sum to 1 exactly.
Results (all exact rationals, independently rechecked from disk):
(1) tau<1 on covered states: phase2 X_max cross-ratio -> tau <= 0.9992675
(840/4096 covered), phase5 tau <= 0.9943329 (672/4096), phase8 0 covered at
L_w=6; all 12288 block matrices have no zero rows => projectively
nonexpansive (bad-block C=1 in Hilbert metric).
(2) Restricted gap: R_unc = 52435/57248 = 0.9159 < 1 on the uncovered-only
subautomaton. (3) Tilted: z=21/20, exact R=1.0454, theta=15/16, R^64<z^60.
(4) Face cone on aligned {0,3}-digit windows: half have |A|=1: 2x2 face
tau_face <= 0.539 (phases 2,5) / 0.963 (phase 8); pinned-scale multiplier
interval [0.600, 1.667] contains 1 (marginal, matches renormalization
eigenvalue-1 chain mode). (5) Localization: covered visit contracts d_H by
tau; osc>t forces all-but-O_t(1) uncovered visits, so theta=15/16 charge
density available; with R^b<z^a the Lean-side Chernoff chain closes IN-MODEL.
Declared hypotheses: (H1) U(sigma) u-split: M(q,De)<=sigma M(q,D); measured
on certified k=15,16 eigenvectors sigma_max=0.419/0.343 (decreasing),
mass-weighted 0.2505; worst-case closure at (3,6) needs sigma<=0.273 (fails
now), at (3,9) needs ~0.36-0.42 (passes measured). (H2) product-cone C_K
(K=2) incl. sibling cross-fiber independence: single-profile envelope only.
Questions: (a) any soundness hole in the charge rule or the C=1
nonexpansiveness claim (no zero rows suffices for Hilbert-metric
nonexpansion of the induced projective map)? (b) is the localization step
(covered visit => factor tau on d_H; disjoint 6-windows; all-but-O(1)
charges) correctly stated for a path mixing T/B2/B8 moves, where windows
transform by shift/shift/x2? (c) sharpest known way to discharge H1 (u-split)
-- can it be replaced by a two-sided window (natural extension) automaton
without losing column normalization? Answer tersely, numbered."""


def main():
    req = {'model': 'gpt-5.6-sol', 'input': BRIEF,
           'reasoning': {'effort': 'high'}}
    r = urllib.request.Request(
        'https://api.openai.com/v1/responses',
        data=json.dumps(req).encode(),
        headers={'Authorization': f'Bearer {KEY}',
                 'Content-Type': 'application/json'})
    with urllib.request.urlopen(r, timeout=900, context=_CTX) as resp:
        out = json.load(resp)
    txt = ''
    for item in out.get('output', []):
        for c in item.get('content', []) or []:
            if c.get('type') == 'output_text':
                txt += c['text']
    open('/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2/sol_audit_answer.md',
         'w').write(txt)
    print(txt[:400])
    print(f'...[{len(txt)} chars] wrote sol_audit_answer.md')


if __name__ == '__main__':
    main()
