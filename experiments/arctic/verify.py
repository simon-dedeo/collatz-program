#!/usr/bin/env python3
"""Independent (no-z3) verification of arctic models AND rewrite-derivation rule counts."""
import glob, re, os
NINF = float('-inf')

# ---------- pure-python max-plus ----------
def mmul(A,B):
    n,m,p=len(A),len(B),len(B[0])
    return [[max((A[i][k]+B[k][j]) for k in range(m)) for j in range(p)] for i in range(n)]
def mvec(A,v):
    return [max(A[i][k]+v[k] for k in range(len(v))) for i in range(len(A))]
def vmax(u,w): return [max(u[i],w[i]) for i in range(len(u))]
def waffine(word,Ms,vs):
    M=[row[:] for row in Ms[word[0]]]; v=vs[word[0]][:]
    for a in word[1:]:
        v=vmax(mvec(M,vs[a]),v); M=mmul(M,Ms[a])
    return M,v
def ge(a,b): return a>=b  # -inf handled by float
def gt(a,b): return (a>b) or (a==NINF and b==NINF)  # arctic |>

RULES=[("R1",['h','1','1'],['1','h']),("R2",['1','1','h','B'],['1','1','s','B']),
       ("R3",['1','s'],['s','1']),("R4",['B','s'],['B','h']),
       ("R5",['h','1','B'],['t','1','1','B']),("R6",['1','t'],['t','1','1','1']),
       ("R7",['B','t'],['B','h'])]

def parse_found(path):
    Ms,vs={},{}
    for line in open(path):
        m=re.match(r'\s*M_(\w+)\s*=\s*(\[\[.*\]\])',line)
        if m:
            a=m.group(1); mat=eval(m.group(2))
            Ms[a]=[[(NINF if x<=-999999 else x) for x in row] for row in mat]
        m=re.match(r'\s*v_(\w+)\s*=\s*(\[.*\])',line)
        if m:
            a=m.group(1); vv=eval(m.group(2))
            vs[a]=[(NINF if x<=-999999 else x) for x in vv]
    return Ms,vs

def check_model(path):
    Ms,vs=parse_found(path)
    target=re.search(r'_(R\d)\.txt$',path)
    target=target.group(1) if target else '?'
    d=len(Ms['1'])
    report=[]
    ok_strict=None
    for (name,L,R) in RULES:
        ML,vL=waffine(L,Ms,vs); MR,vR=waffine(R,Ms,vs)
        weak=all(ge(ML[i][j],MR[i][j]) for i in range(d) for j in range(d)) and all(ge(vL[i],vR[i]) for i in range(d))
        strict=all(gt(ML[i][j],MR[i][j]) for i in range(d) for j in range(d)) and all(gt(vL[i],vR[i]) for i in range(d))
        report.append((name,weak,strict))
        if name==target: ok_strict=strict
    # well-def: (M)_00>=0 OR v_0>=0
    welldef=all((Ms[a][0][0]>=0) or (vs[a][0]>=0) for a in Ms)
    allweak=all(w for(_,w,_) in report)
    return target,d,allweak,ok_strict,welldef,report


def check_dp_scope_counterexample():
    """Verify why both dependency-pair rules must be required weak.

    This scalar AZ interpretation makes every Z rule weak and I_s strict, but
    leaves I_t unoriented.  Thus "all Z weak + one I strict" is not the theorem.
    """
    Ms = {
        '1': [[1]], 'B': [[NINF]], 'M': [[0]],
        'h': [[-1]], 's': [[0]], 't': [[NINF]],
    }
    vs = {
        '1': [2], 'B': [0], 'M': [NINF],
        'h': [0], 's': [1], 't': [0],
    }

    def orientation(left, right):
        ml, vl = waffine(left, Ms, vs)
        mr, vr = waffine(right, Ms, vs)
        weak = ge(ml[0][0], mr[0][0]) and ge(vl[0], vr[0])
        strict = gt(ml[0][0], mr[0][0]) and gt(vl[0], vr[0])
        return weak, strict

    assert all(orientation(left, right)[0] for _, left, right in RULES)
    i_s = orientation(['M', 's'], ['M', 'h'])
    i_t = orientation(['M', 't'], ['M', 'h'])
    assert i_s == (True, True)
    assert i_t == (False, False)
    assert all((Ms[a][0][0] >= 0) or (vs[a][0] >= 0) for a in Ms)
    return i_s, i_t

# ---------- rewrite simulator: confirm rule usage counts ----------
def apply_once(s):
    """One leftmost-ish rewrite; returns (new_string, rule_name) or None. Deterministic-ish
       following the intended Turing simulation (search each rule left to right)."""
    # order matters for a faithful simulation of the machine; we search all, prefer the
    # unique applicable machine step. Represent string as list of chars over {1,B,h,s,t}.
    for (name,L,R) in RULES:
        Ls,Rs=''.join(L),''.join(R)
        i=s.find(Ls)
        if i>=0:
            return s[:i]+Rs+s[i+len(Ls):], name
    return None

def simulate(n, maxsteps=10**7):
    """Run Z from B h 1^n B; count rule uses; return (final,counts,steps)."""
    from collections import Counter
    s='B'+'h'+'1'*n+'B'
    cnt=Counter(); steps=0
    while steps<maxsteps:
        r=apply_once(s)
        if r is None: break
        s,name=r; cnt[name]+=1; steps+=1
    return s,cnt,steps


def replace_once(s, lhs, rhs):
    """Apply one specified rewrite, asserting that its occurrence is unique."""
    pos = s.find(lhs)
    assert pos >= 0, (s, lhs)
    assert s.find(lhs, pos + 1) < 0, (s, lhs)
    return s[:pos] + rhs + s[pos + len(lhs):]


def marked_odd_macro(r):
    """Check M h 1^(2r+1) B ->* M h 1^(3r+2) B and return counts."""
    from collections import Counter
    s = 'M' + 'h' + '1' * (2 * r + 1) + 'B'
    cnt = Counter()
    for _ in range(r):
        s = replace_once(s, 'h11', '1h'); cnt['R1'] += 1
    s = replace_once(s, 'h1B', 't11B'); cnt['R5'] += 1
    for _ in range(r):
        s = replace_once(s, '1t', 't111'); cnt['R6'] += 1
    s = replace_once(s, 'Mt', 'Mh'); cnt['I_t'] += 1
    assert s == 'M' + 'h' + '1' * (3 * r + 2) + 'B'
    return cnt


def marked_even_macro(r):
    """Check M h 1^(2r) B ->* M h 1^r B for r>=2 and return counts."""
    from collections import Counter
    assert r >= 2
    s = 'M' + 'h' + '1' * (2 * r) + 'B'
    cnt = Counter()
    for _ in range(r):
        s = replace_once(s, 'h11', '1h'); cnt['R1'] += 1
    s = replace_once(s, '11hB', '11sB'); cnt['R2'] += 1
    for _ in range(r):
        s = replace_once(s, '1s', 's1'); cnt['R3'] += 1
    s = replace_once(s, 'Ms', 'Mh'); cnt['I_s'] += 1
    assert s == 'M' + 'h' + '1' * r + 'B'
    return cnt


def unmarked_odd_macro(r):
    """Check B h 1^(2r+1) B ->* B h 1^(3r+2) B."""
    from collections import Counter
    s = 'B' + 'h' + '1' * (2 * r + 1) + 'B'
    cnt = Counter()
    for _ in range(r):
        s = replace_once(s, 'h11', '1h'); cnt['R1'] += 1
    s = replace_once(s, 'h1B', 't11B'); cnt['R5'] += 1
    for _ in range(r):
        s = replace_once(s, '1t', 't111'); cnt['R6'] += 1
    s = replace_once(s, 'Bt', 'Bh'); cnt['R7'] += 1
    assert s == 'B' + 'h' + '1' * (3 * r + 2) + 'B'
    return cnt


def unmarked_even_macro(r):
    """Check B h 1^(2r) B ->* B h 1^r B for r>=2."""
    from collections import Counter
    assert r >= 2
    s = 'B' + 'h' + '1' * (2 * r) + 'B'
    cnt = Counter()
    for _ in range(r):
        s = replace_once(s, 'h11', '1h'); cnt['R1'] += 1
    s = replace_once(s, '11hB', '11sB'); cnt['R2'] += 1
    for _ in range(r):
        s = replace_once(s, '1s', 's1'); cnt['R3'] += 1
    s = replace_once(s, 'Bs', 'Bh'); cnt['R4'] += 1
    assert s == 'B' + 'h' + '1' * r + 'B'
    return cnt


def verify_strict_macro_family(max_n=12):
    """Verify 8N+1 -> 12N+2 -> 6N+1 -> 9N+2 and exact counts."""
    from collections import Counter
    for n in range(1, max_n + 1):
        cnt = Counter()
        cnt.update(marked_odd_macro(4 * n))
        cnt.update(marked_even_macro(6 * n + 1))
        cnt.update(marked_odd_macro(3 * n))
        expected = Counter({
            'R1': 13 * n + 1,
            'R2': 1,
            'R3': 6 * n + 1,
            'R5': 2,
            'R6': 7 * n,
            'I_s': 1,
            'I_t': 2,
        })
        assert cnt == expected, (n, cnt, expected)
        ordinary = Counter()
        ordinary.update(unmarked_odd_macro(4 * n))
        ordinary.update(unmarked_even_macro(6 * n + 1))
        ordinary.update(unmarked_odd_macro(3 * n))
        expected_ordinary = Counter({
            'R1': 13 * n + 1,
            'R2': 1,
            'R3': 6 * n + 1,
            'R4': 1,
            'R5': 2,
            'R6': 7 * n,
            'R7': 2,
        })
        assert ordinary == expected_ordinary, (n, ordinary, expected_ordinary)
    return max_n

if __name__=='__main__':
    print("=== MODEL VERIFICATION (independent of z3) ===")
    here = os.path.dirname(os.path.abspath(__file__))
    expected = [f'FOUND_AZ_d1_K2_R{r}.txt' for r in (1, 2, 3, 5, 6)]
    paths = sorted(glob.glob(os.path.join(here, 'FOUND_AZ_d1_*.txt')))
    assert [os.path.basename(p) for p in paths] == expected
    for p in paths:
        tgt,d,allweak,strict,welldef,rep=check_model(p)
        valid = allweak and strict and welldef
        assert valid, (p, rep)
        print(f"{os.path.basename(p)}: dim={d} all_weak={allweak} target_strict={strict} welldef={welldef}  VALID={valid}")
    i_s, i_t = check_dp_scope_counterexample()
    print(f"DP scope counterexample: all Z weak, I_s={i_s}, I_t={i_t}  VALID=True")
    print("\n=== DERIVATION RULE COUNTS (B h 1^n B ->* ...) ===")
    for n in [1,2,3,4,5,7,8,9,16,17]:
        fin,cnt,steps=simulate(n)
        print(f"n={n:3d} steps={steps:5d} final={fin[:40]} counts={dict(sorted(cnt.items()))}")
    checked = verify_strict_macro_family()
    print(f"\nPASS: marked and unmarked odd-even-odd macro samples for N=1..{checked}")
