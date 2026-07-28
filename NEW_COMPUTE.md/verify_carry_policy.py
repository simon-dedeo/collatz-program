#!/usr/bin/env python3
"""Independently rebuild and score a carry_policy_cegis finite corpus."""
import collections, pathlib, re, sys

Word=collections.namedtuple("Word","S O r b")
State=collections.namedtuple("State","target odd_count")
ROOT=State(0,0)

MASK = (1 << 64) - 1
CONST1 = 0x9E3779B97F4A7C15
CONST2 = 0xD1B54A32D192ED03

def xr(x):
    x ^= (x << 13) & MASK; x ^= x >> 7; x ^= (x << 17) & MASK
    return x & MASK

def v2cap(x):
    return 127 if x == 0 else min(127, (x & -x).bit_length() - 1)

def features(state):
    H = (state.target + 1) // 3
    assert 3 * H == state.target + 1
    z, c = H, 0
    while z % 3 == 0: z //= 3; c += 1
    D = state.odd_count - c
    f = [D, c, z.bit_length(), v2cap(z-1), v2cap(z+1), v2cap(H), D*D, c*c, D*c] + [0]*16
    f[9 + z % 16] = 1
    return f

def make_word(bits):
    S=len(bits); O=bits.count('1'); constant=0
    for length,bit in enumerate(bits):
        if bit=='1': constant=3*constant+(1<<length)
    modulus=1<<S; r=(-constant*pow(3**O,-1,modulus))%modulus
    numerator=3**O*r+constant; assert numerator%modulus==0
    return Word(S,O,r,numerator//modulus)

def extend(state,word):
    modulus=1<<word.S; power=3**state.odd_count
    q=((word.r-state.target)*pow(power,-1,modulus))%modulus
    boundary=state.target+power*q; difference=boundary-word.r
    assert difference>=0 and difference%modulus==0
    return State(word.b+3**word.O*(difference//modulus),state.odd_count+word.O),q

def choose(qs, x):
    x = xr(x); r = x
    if r % 10 < 7: return min(range(len(qs)), key=lambda j: (qs[j], j)), x
    x = xr(x); return x % len(qs), x

def selected_source_words(bound):
    found={}
    for source in range(1,bound+1):
        state=source; bits=[]; odds=0; complete=False
        while True:
            if state==2: break
            if state==1:
                if 3**(odds+1)>2**(len(bits)+1):
                    bits.append('1'); complete=True
                break
            odd=state&1; bits.append('1' if odd else '0'); odds+=odd
            state=(3*state+1)//2 if odd else state//2
            if 3**odds>2**len(bits): complete=True; break
            assert len(bits)<62
        if complete:
            row=make_word(''.join(bits))
            found.setdefault((row.S,row.r),row)
    return sorted(found.values(),key=lambda row:row.r)

def corpus(words, walks, steps, seed):
    rows=[]
    for w in range(walks):
        x=(seed ^ (((w+1)*CONST1)&MASK))&MASK
        if not x: x=1
        state=ROOT
        pairs=[extend(state,word) for word in words]
        pick,x=choose([q for _,q in pairs],x); state=pairs[pick][0]
        for _ in range(steps):
            pf=features(state); pairs=[extend(state,word) for word in words]
            rows.append([(q,[a-b for a,b in zip(pf,features(child))]) for child,q in pairs])
            pick,x=choose([q for _,q in pairs],x); state=pairs[pick][0]
    return rows

def corpus_records(words, walks, steps, seed):
    """Rebuild the corpus while retaining the exact parent state metadata."""
    records=[]
    for w in range(walks):
        x=(seed ^ (((w+1)*CONST1)&MASK))&MASK
        if not x: x=1
        state=ROOT
        pairs=[extend(state,word) for word in words]
        pick,x=choose([q for _,q in pairs],x); state=pairs[pick][0]
        for depth in range(steps):
            pf=features(state); pairs=[extend(state,word) for word in words]
            row=[(q,[a-b for a,b in zip(pf,features(child))]) for child,q in pairs]
            H=(state.target+1)//3; z,c=H,0
            while z%3==0: z//=3; c+=1
            records.append((w,depth,state.odd_count-c,c,z,row))
            pick,x=choose([q for _,q in pairs],x); state=pairs[pick][0]
    return records

def score(coeff, rows):
    feasible=scale=0
    for row in rows:
        needs=[]
        for q,delta in row:
            d=sum(a*b for a,b in zip(coeff,delta))
            if (q==0 and d>=0) or (q>0 and d>0): needs.append(0 if q==0 else (q+d-1)//d)
        if needs: feasible+=1; scale=max(scale,min(needs))
    return feasible,scale

def diagnose(coeff, records):
    """Print exact rows on which no word has nonnegative Bellman margin."""
    misses=[]
    for w,depth,D,c,z,row in records:
        choices=[]
        for index,(q,delta) in enumerate(row):
            drop=sum(a*b for a,b in zip(coeff,delta))
            choices.append((drop-q,index,q,drop))
        margin,index,q,drop=max(choices)
        if margin<0:
            misses.append((w,depth,D,c,z,index,q,drop,margin))
    print("walk\tdepth\tD\tc\tz\tword_index\tq\tpotential_drop\tmargin")
    for miss in misses:
        print("\t".join(map(str,miss)))
    print("diagnostic_misses",len(misses))

def main(path, diagnostic=False):
    lines=path.read_text().splitlines(); head=dict(re.findall(r"(\w+)=([^\s]+)",lines[0])); best=dict(x.split("=",1) for x in next(x for x in reversed(lines) if x.startswith("BEST\t")).split("\t")[1:])
    bound,walks,steps,seed=map(int,(head["word_bound"],head["walks"],head["steps"],head["seed"])); coeff=list(map(int,best["coeff"].split(',')))
    words=selected_source_words(bound); assert len(words)==int(head["words"])
    train=score(coeff,corpus(words,walks,steps,seed)); held=score(coeff,corpus(words,walks,steps,seed^CONST2))
    assert train==(int(best["train_feasible"]),int(best["train_max_scale"])),(train,best)
    assert held==(int(best["held_feasible"]),int(best["held_max_scale"])),(held,best)
    print("verified carry-policy corpus:",train,held,"rows",walks*steps)
    if diagnostic:
        diagnose(coeff,corpus_records(words,walks,steps,seed^CONST2))

if __name__=="__main__":
    if len(sys.argv) not in (2,3) or (len(sys.argv)==3 and sys.argv[2]!="--diagnose"):
        raise SystemExit("usage: verify_carry_policy.py OUTPUT.tsv [--diagnose]")
    main(pathlib.Path(sys.argv[1]),len(sys.argv)==3)
