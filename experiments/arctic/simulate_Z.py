#!/usr/bin/env python3
"""
Deterministic simulator for the EXACT (blank-free) Zantema Z on states h 1^k B.
Confirms the macro-steps
    h 1^{2n}   B ->* h 1^{n}    B    (even)
    h 1^{2n+1} B ->* h 1^{3n+2} B    (odd)
and reports per-rule application counts.  Rules applied leftmost-innermost by a fixed
strategy that mirrors the Turing-machine sweep (deterministic on reachable states).
"""
RULES = [
    ("R1", ['h','1','1'], ['1','h']),
    ("R2", ['1','1','h'], ['1','1','s']),
    ("R3", ['1','s'],     ['s','1']),
    ("R4", ['s'],         ['h']),
    ("R5", ['h','1'],     ['t','1','1']),
    ("R6", ['1','t'],     ['t','1','1','1']),
    ("R7", ['t'],         ['h']),
]
def find(w, pat):
    for i in range(len(w)-len(pat)+1):
        if w[i:i+len(pat)] == pat:
            return i
    return -1

def step(w):
    """One deterministic macro-Collatz step on w = ['h']+['1']*k+['B'] -> h1^{C(k)}B.
       Returns (new_word, counts_dict). Uses the priority order that realizes the sweep."""
    counts = {name:0 for (name,_,_) in RULES}
    # priority: move head right (R1) until it can't; then decide even (R2) or odd (R5);
    # then sweep back (R3/R6); then turn around (R4/R7). One full macro step.
    while True:
        # try R1 (h11->1h): sweep h right
        i = find(w, ['h','1','1'])
        if i != -1:
            w = w[:i] + ['1','h'] + w[i+3:]; counts["R1"] += 1; continue
        # now h is followed by at most one 1.  Even: '...11h' pattern? R2 (11h->11s)
        i = find(w, ['1','1','h'])
        if i != -1:
            w = w[:i] + ['1','1','s'] + w[i+3:]; counts["R2"] += 1
            # sweep s left: R3 (1s->s1) until s at far left, then R4 (s->h)
            while True:
                j = find(w, ['1','s'])
                if j != -1:
                    w = w[:j] + ['s','1'] + w[j+2:]; counts["R3"] += 1; continue
                break
            j = find(w, ['s'])
            w = w[:j] + ['h'] + w[j+1:]; counts["R4"] += 1
            return w, counts
        # Odd: h followed by exactly one 1 then B  -> R5 (h1->t11)
        i = find(w, ['h','1'])
        if i != -1:
            w = w[:i] + ['t','1','1'] + w[i+2:]; counts["R5"] += 1
            # sweep t left: R6 (1t->t111), then R7 (t->h)
            while True:
                j = find(w, ['1','t'])
                if j != -1:
                    w = w[:j] + ['t','1','1','1'] + w[j+2:]; counts["R6"] += 1; continue
                break
            j = find(w, ['t'])
            w = w[:j] + ['h'] + w[j+1:]; counts["R7"] += 1
            return w, counts
        # h alone (k==0): h B -> ... R5 needs h1; nothing applies; halt.
        return w, counts

def count_ones(w):
    return sum(1 for c in w if c == '1')

def macro(k):
    w = ['h'] + ['1']*k + ['B']
    w2, counts = step(w)
    return count_ones(w2), counts

def collatz(k):
    return k//2 if k % 2 == 0 else (3*k+1)//2

if __name__ == '__main__':
    import sys
    print("verifying single macro-step matches C(k)=k/2 (even) or (3k+1)/2 (odd):")
    ok = True
    for k in range(0, 40):
        out, counts = macro(k)
        exp = collatz(k) if k >= 1 else 0
        tag = "OK" if out == exp else "MISMATCH"
        if out != exp: ok = False
        if k < 12 or out != exp:
            print(f"  k={k:3d} -> {out:3d}  expected C={exp:3d}  {tag}  counts={counts}")
    print("ALL MACRO STEPS OK" if ok else "FAILURE")

    # multi-step derivation 8n+1 ->* 9n+2 (odd,even,odd) rule totals
    print("\nfull derivation h1^{8n+1}B ->* h1^{9n+2}B, per-rule totals:")
    print("n," + ",".join(name for (name,_,_) in RULES) + ",final,expect")
    for n in range(0, 8):
        k = 8*n+1
        tot = {name:0 for (name,_,_) in RULES}
        steps = 0
        while k not in (1,) and steps < 10:
            # do macro steps until we reach 9n+2 (three steps: odd->even->odd)
            w = ['h'] + ['1']*k + ['B']
            w2, c = step(w)
            for kk in c: tot[kk]+=c[kk]
            k = count_ones(w2); steps += 1
            if steps == 3: break
        print(f"{n}," + ",".join(str(tot[name]) for (name,_,_) in RULES) + f",{k},{9*n+2}")

    # even-only chain 2^m ->* 1 (rule R4 count = m), odd-chain 2^m-1 ->* 3^m-1 (R7 count=m)
    print("\neven chain h1^{2^m}B ->* h1B : R4 uses per macro (should be 1 each even step)")
    for m in range(1,6):
        k = 2**m; r4=0; r7=0; seq=[k]
        while k > 1:
            w=['h']+['1']*k+['B']; w2,c=step(w); r4+=c['R4']; r7+=c['R7']; k=count_ones(w2); seq.append(k)
        print(f"  m={m} seq={seq} R4={r4} R7={r7}")
