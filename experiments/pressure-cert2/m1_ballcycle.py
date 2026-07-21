"""m1_ballcycle.py -- LOW-window (ball) structure at J=3 and the zero-charge
question on the ball factor alone.

The pressure charge e counts path-visits to E_J (Lemma 5's tilt: b(e)=1 iff the
edge TARGET ball in E_J).  A zero-charge cycle must be a closed walk in the
ball automaton (edges T, B2, B8) that never enters E_J.  Here we enumerate the
ball automaton at J=3, its edges, E_3, and decide whether the complement C
carries any cycle (SCC analysis) -- and the per-block (L_w=6) transport charge.
Pure integer arithmetic; reuses automaton.py.
"""
from fractions import Fraction
import csv, os
import automaton as am

J = 3
MOD = 3 ** J          # 27
Lw = 6


def ball_edges():
    """All edges (src,dst,kind); kind in T,B2,B8. Reuses am.edges but we also
    tag the mod-9 phase of src."""
    E = am.edges(J)
    return E


def scc(nodes, adj):
    """Tarjan SCC. adj: dict node->set(node). Returns list of components."""
    idx = {}; low = {}; onstk = {}; stk = []; out = []; c = [0]
    import sys
    sys.setrecursionlimit(10000)
    def strong(v):
        idx[v] = low[v] = c[0]; c[0] += 1; stk.append(v); onstk[v] = True
        for w in adj.get(v, ()):  # noqa
            if w not in idx:
                strong(w); low[v] = min(low[v], low[w])
            elif onstk.get(w):
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = stk.pop(); onstk[w] = False; comp.append(w)
                if w == v:
                    break
            out.append(comp)
    for v in nodes:
        if v not in idx:
            strong(v)
    return out


def analyse():
    S = am.states(J)
    E = set(am.exceptional_set(J))          # {5,20,26}
    C = [q for q in S if q not in E]
    edges = ball_edges()
    # full adjacency (all edges)
    adj_full = {q: set() for q in S}
    for (s, d, k) in edges:
        adj_full[s].add(d)
    # adjacency restricted to complement C (edges within C only)
    adj_C = {q: set() for q in C}
    for (s, d, k) in edges:
        if s in C and d in C:
            adj_C[s].add(d)
    comps_full = scc(S, adj_full)
    comps_C = scc(C, adj_C)
    # a "cycle" exists in C iff some SCC has >1 node OR a self-loop
    self_loops_C = [q for q in C if q in adj_C[q]]
    nontriv_C = [comp for comp in comps_C if len(comp) > 1]
    # per-block transport charge along the L_w=6 transport orbit from each q:
    # intermediate transport targets 4^t q, t=1..6, count those in E
    block_rows = []
    for q in S:
        vis = []
        x = q
        chg = 0
        for t in range(1, Lw + 1):
            x = (4 * x) % MOD
            vis.append(x)
            if x in E:
                chg += 1
        block_rows.append((q, q % 9, chg, tuple(vis), (4 ** Lw) % MOD))
    return {
        'S': S, 'E': sorted(E), 'C': C, 'edges': edges,
        'comps_full': comps_full, 'comps_C': comps_C,
        'self_loops_C': self_loops_C, 'nontriv_C': nontriv_C,
        'block_rows': block_rows,
    }


if __name__ == '__main__':
    r = analyse()
    outdir = os.path.dirname(os.path.abspath(__file__))
    # edges csv
    with open(os.path.join(outdir, 'csv', 'm1_ball_edges.csv'), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['src', 'src_mod9', 'dst', 'kind', 'dst_in_E'])
        for (s, d, k) in r['edges']:
            w.writerow([s, s % 9, d, k, int(d in set(r['E']))])
    # block charge csv
    with open(os.path.join(outdir, 'csv', 'm1_block_charge.csv'), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['q', 'phase', 'block_charge_e', 'transport_targets', 'block_ball_map_mult'])
        for (q, ph, chg, vis, mult) in r['block_rows']:
            w.writerow([q, ph, chg, '|'.join(map(str, vis)), mult])
    # verdict summary
    print('J=3 states:', r['S'])
    print('E_3 =', r['E'], ' complement C =', r['C'])
    print('SCCs of full ball graph:', r['comps_full'])
    print('SCCs within complement C:', r['comps_C'])
    print('self-loops in C:', r['self_loops_C'])
    print('nontrivial SCCs in C:', r['nontriv_C'])
    zc = bool(r['self_loops_C'] or r['nontriv_C'])
    print('ZERO-CHARGE ball cycle exists (avoiding E_3):', zc)
    mn = min(chg for (_, _, chg, _, _) in r['block_rows'])
    mx = max(chg for (_, _, chg, _, _) in r['block_rows'])
    print(f'per-block (L_w=6) transport charge: min={mn} max={mx} over start balls')
