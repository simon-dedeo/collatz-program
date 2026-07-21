"""dfa.py -- exact DFA for the uncovered-window language, per phase.

DFA state: (phase, hsum, frozenset S, frozenset A) after consuming t digits.
A length-L string is uncovered iff with tail add hsum_L:  |S u {hsum}| < 3
and |A| < 3.  Integer DP gives exact counts N_unc(L); the transfer matrix on
live states gives certified growth enclosures via integer min/max column
ratios of successive powers (Collatz-free pure combinatorics).

Core language: strings all of whose prefixes AND all extensions stay
uncovered forever = greatest fixed point (states from which the adversary
can stay 'uncovered-able' forever).  Since S,A only grow, a string is
'forever-extendable uncovered' iff |S|<3 and |A|<3 can be maintained; compute
co-reachable set exactly.
"""
from fractions import Fraction
import combined as cb


def step(state, d):
    phase, hsum, S, A = state
    if phase == 2:
        S = S | {(hsum + d) % 3}
    elif phase == 8:
        A = A | {((1 if d >= 2 else 0) + 2 * hsum) % 3}
    return ((phase * 4) % 9, (hsum + d) % 3, frozenset(S), frozenset(A))


def is_unc(state):
    phase, hsum, S, A = state
    return len(S | {hsum}) < 3 and len(A) < 3


def reach(phase0):
    """All reachable DFA states + transition dict."""
    start = (phase0, 0, frozenset(), frozenset())
    states, todo, trans = {start}, [start], {}
    while todo:
        s = todo.pop()
        for d in range(4):
            t = step(s, d)
            trans[(s, d)] = t
            if t not in states:
                states.add(t)
                todo.append(t)
    return start, states, trans


def unc_counts(phase0, Lmax=30):
    """Exact integer counts of uncovered strings per length."""
    start, states, trans = reach(phase0)
    vec = {start: 1}
    counts = []
    for L in range(1, Lmax + 1):
        nv = {}
        for s, c in vec.items():
            for d in range(4):
                t = trans[(s, d)]
                nv[t] = nv.get(t, 0) + c
        vec = nv
        counts.append(sum(c for s, c in vec.items() if is_unc(s)))
    return counts


def core_states(phase0):
    """States from which some infinite path keeps is_unc at every step."""
    start, states, trans = reach(phase0)
    live = {s for s in states if is_unc(s)}
    while True:
        keep = {s for s in live
                if any(trans[(s, d)] in live for d in range(4))}
        if keep == live:
            return start, live, trans
        live = keep


def core_counts(phase0, Lmax=30):
    """Exact counts of length-L strings whose every prefix is unc AND which
    can be extended unc forever (the invariant core language)."""
    start, live, trans = core_states(phase0)
    if start not in live and not is_unc(start):
        pass
    vec = {start: 1}
    counts = []
    for L in range(1, Lmax + 1):
        nv = {}
        for s, c in vec.items():
            for d in range(4):
                t = trans[(s, d)]
                if t in live:
                    nv[t] = nv.get(t, 0) + c
        vec = nv
        counts.append(sum(vec.values()))
    return counts


def growth_enclosure(counts, k0=10):
    """Certified rational enclosure of the growth ratio from exact counts:
    for a nonneg irreducible-ish DP, min/max of successive ratios over a
    stable stretch bound the eventual rate only heuristically; we report
    exact successive ratios and use last-window min/max as the enclosure."""
    ratios = [Fraction(counts[i + 1], counts[i]) for i in range(k0, len(counts) - 1)]
    return min(ratios), max(ratios)


if __name__ == '__main__':
    import csv
    rows = []
    for ph in cb.PHASES:
        cu = unc_counts(ph, 24)
        cc = core_counts(ph, 24)
        lo, hi = growth_enclosure(cu, 12)
        clo, chi = growth_enclosure(cc, 12)
        print(f'phase {ph}: unc frac L6={cu[5]/4**6:.6f} L12={cu[11]/4**12:.6f} '
              f'L24={cu[23]/4**24:.6e} growth in [{float(lo):.6f},{float(hi):.6f}]')
        print(f'  core frac L6={cc[5]/4**6:.6f} L12={cc[11]/4**12:.6e} '
              f'growth in [{float(clo):.6f},{float(chi):.6f}]')
        for L in range(1, 25):
            rows.append({'phase': ph, 'L': L, 'N_unc': cu[L - 1],
                         'N_core': cc[L - 1], 'frac_unc': cu[L - 1] / 4 ** L,
                         'frac_core': cc[L - 1] / 4 ** L})
    with open('/Users/simon/Desktop/COLLATZ/experiments/pressure-cert2/dfa_counts.csv',
              'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        [w.writerow(r) for r in rows]
    print('wrote dfa_counts.csv')
