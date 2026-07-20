#!/usr/bin/env python3
"""Exact symbolic verification (sympy, exact rationals) for docs/notes/carries-spectrum.md.

Checks, all in exact arithmetic (no floats):
  1. m in {3,5,7,9,15}, b=2:
       charpoly(K_m) == (x-1) * prod_O (x^{|O|} - 2^{-|O|})   as polynomials over Q.
  2. m in {3,5,9,15}: exact identity K^L = Pi + 2^{-L}(I - Pi), L = ord_m(2).
  3. m in {3,5,7,9}: extended affine chain K~ on {0,...,m}:
       charpoly(K~) == (x - 1/2) * charpoly(K_m), and eigenvalue 1/2 semisimple
       (checked exactly: rank(K~ - I/2) == (m+1) - algebraic multiplicity).
  4. Orbit-sum lemma T_O = sum_{x in O} w^{-2^{-1}x} / (1 - w^{-x}) == 0 (w = exp(2 pi i/m)),
     verified exactly with cyclotomic arithmetic for every orbit, m in {3,5,7,9,15}.
"""
import sympy as sp
from sympy import Rational, eye, ones, zeros, symbols, expand

x = symbols('x')


def build_K(m, b=2):
    K = zeros(m, m)
    for c in range(m):
        for d in range(b):
            K[c, (b * 0 + m * d + c) // b] += Rational(1, b)
    return K


def build_K_ext(m):
    Ke = zeros(m + 1, m + 1)
    for c in range(m + 1):
        for bbit in (0, 1):
            Ke[c, (m * bbit + c) // 2] += Rational(1, 2)
    return Ke


def orbits(m, b=2):
    seen, orbs = set(), []
    for s in range(1, m):
        if s in seen:
            continue
        orb, y = [], s
        while y not in seen:
            seen.add(y)
            orb.append(y)
            y = (b * y) % m
        orbs.append(orb)
    return orbs


def predicted_poly(m, b=2):
    p = (x - 1)
    for O in orbits(m, b):
        rho = len(O)
        p *= (x ** rho - Rational(1, b ** rho))
    return expand(p)


def ord_mod(b, m):
    o, y = 1, b % m
    while y != 1:
        y = (y * b) % m
        o += 1
    return o


print("1. Exact characteristic polynomial identity, b = 2")
for m in [3, 5, 7, 9, 15]:
    K = build_K(m)
    cp = K.charpoly(x).as_expr()          # exact, over Q
    pred = predicted_poly(m)
    ok = expand(cp - pred) == 0
    print(f"   m={m:>2}: charpoly(K) == (x-1)*prod_O(x^|O| - 2^-|O|)  ->  {ok}")
    assert ok

print("\n2. Exact power identity K^L = Pi + 2^{-L}(I - Pi)")
for m in [3, 5, 9, 15]:
    K = build_K(m)
    L = ord_mod(2, m)
    Pi = ones(m, m) / m
    ok = (K ** L - (Pi + Rational(1, 2 ** L) * (eye(m) - Pi))) == zeros(m, m)
    print(f"   m={m:>2}, L={L:>2}:  ->  {ok}")
    assert ok

print("\n3. Affine (constant-addend) extended chain on {0,...,m}")
for m in [3, 5, 7, 9]:
    K = build_K(m)
    Ke = build_K_ext(m)
    cpK = K.charpoly(x).as_expr()
    cpKe = Ke.charpoly(x).as_expr()
    ok_poly = expand(cpKe - expand((x - Rational(1, 2)) * cpK)) == 0
    # algebraic multiplicity of 1/2 in K~ = 1 + (number of <2>-orbits mod m)  (one 1/2 per orbit)
    alg = 1 + len(orbits(m))
    rank = (Ke - Rational(1, 2) * eye(m + 1)).rank()   # exact rank over Q
    ok_ss = (rank == (m + 1) - alg)
    print(f"   m={m:>2}: charpoly(K~) == (x-1/2)*charpoly(K) -> {ok_poly};"
          f"  eig 1/2 semisimple (rank {rank} = {m+1}-{alg}) -> {ok_ss}")
    assert ok_poly and ok_ss

print("\n4. Orbit-sum lemma  T_O = sum_{x in O} w^{-x/2} / (1 - w^{-x}) == 0  (exact cyclotomic)")
# Exact arithmetic in Q(zeta_m): put the sum over the common denominator
# prod_{x in O}(1 - z^x)  (z = w^{-1}, a primitive m-th root of unity, so nonzero
# denominators), and check the numerator is divisible by the cyclotomic
# polynomial Phi_m(z).  T_O = 0  <=>  numerator == 0 mod Phi_m.
z = symbols('z')
for m in [3, 5, 7, 9, 15]:
    inv2 = pow(2, -1, m)
    Phi = sp.cyclotomic_poly(m, z)
    for O in orbits(m):
        num = sp.Integer(0)
        for xx in O:
            term = z ** ((inv2 * xx) % m)
            for yy in O:
                if yy != xx:
                    term *= (1 - z ** yy)
            num += term
        rem = sp.rem(sp.expand(num), Phi, z)
        ok = sp.expand(rem) == 0
        print(f"   m={m:>2}, orbit of {O[0]} (size {len(O)}): numerator == 0 mod Phi_m  ->  {ok}")
        assert ok

print("\nAll exact checks passed.")
