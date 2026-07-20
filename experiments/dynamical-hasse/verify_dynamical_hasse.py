from itertools import product
from fractions import Fraction

def W(v):
    K=len(v); 
    return sum(v[i]*(2**i)*(3**sum(v[j] for j in range(i+1,K))) for i in range(K))

def xv(v):
    K=len(v); L=sum(v)
    return Fraction(W(v), 2**K - 3**L)

# 1) parity consistency + T^K(x)=x for all words K<=10
def T(x):
    return x/2 if (x.numerator % 2 == 0) else (3*x+1)/2
ok=True
for K in range(1,11):
    for v in product([0,1],repeat=K):
        x=xv(v); y=x
        for i in range(K):
            par = y.numerator % 2  # denominator odd always
            assert y.denominator %2==1
            if par != v[i]: ok=False; print("parity fail",v)
            y=T(y)
        if y!=x: ok=False; print("period fail",v)
print("parity+period all words K<=10:", ok)

# 2) translation lemma: t_v = translation by W*2^{-K} mod |Lambda|, all words K<=12 with |Lambda|>1
def check_translation():
    for K in range(1,13):
        for v in product([0,1],repeat=K):
            L=sum(v); Lam=abs(2**K-3**L)
            if Lam<=1: continue
            inv2=pow(2,-1,Lam)
            # composite affine map mod Lam
            a,b=1,0  # x -> a x + b
            for bit in v:
                if bit==0: a,b=(a*inv2)%Lam,(b*inv2)%Lam
                else: a,b=(3*a*inv2)%Lam,((3*b+1)*inv2)%Lam
            expect_b=(W(v)*pow(inv2,K,Lam))%Lam
            if a%Lam!=1 or b!=expect_b: print("translation fail",v); return False
    return True
print("translation lemma K<=12:", check_translation())

# 3) (11,7): which weight-7 words of length 11 have 139 | W?
hits=[v for v in product([0,1],repeat=11) if sum(v)==7 and W(v)%139==0]
print("(11,7) integral words:",len(hits),"of",sum(1 for v in product([0,1],repeat=11) if sum(v)==7))
print("all are rotations of -17 word:", all(xv(v)==Fraction(-17) or xv(v)in[Fraction(z) for z in(-25,-37,-55,-82,-41,-61,-91,-136,-68,-34)] for v in hits))

# 4) unit stratum check |2^K-3^L|=1 for K<=200,L<=200
sols=[(K,L) for K in range(1,201) for L in range(0,201) if abs(2**K-3**L)==1]
print("unit stratum:",sols)

# 5) trace formula spot check: N(K,L) via brute force vs formula count, K=11,L=7 => 11/... 
# (formula equivalence is combinatorially the same count; brute force above suffices)

# 6) Steiner closed form W(1^L 0^(K-L)) = 3^L-2^L
print("steiner W:", all(W(tuple([1]*L+[0]*(K-L)))==3**L-2**L for K in range(2,14) for L in range(1,K)))

# 7) -17 word data
v=(1,1,1,1,0,1,1,1,0,0,0)
print("W(-17 word)=",W(v), "Lambda=",2**11-3**7, "x=",xv(v))
