#!/usr/bin/env python3
"""Finite exact checks supporting the unsigned-solenoid leading-pole argument.

The general proof is in ``docs/notes/solenoid-zeta.md``.  This checker uses
only Python integers and ``Fraction``.  It verifies the binomial identities,
the prime-to-6 correction, a direct word enumeration at small levels, and the
coefficient identity

    zeta(u) = (1 - 4u)^(-2) exp(-sum(e_k u^k/k)).

It also checks the integer inequalities behind the candidate exponential gap
``rho_T,rho_U < 4``.  Turning these finite identities and constant inequalities
into a universal tail bound and holomorphic continuation is part of the
handwritten argument, not something this script proves.
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction


def prime_to_six_part(n: int) -> int:
    n = abs(n)
    if n == 0:
        raise ValueError("the K=0 identity map has infinitely many fixed points")
    while n % 2 == 0:
        n //= 2
    while n % 3 == 0:
        n //= 3
    return n


def threshold_index(k: int) -> int:
    """Largest L with 3^L < 2^k, found without floating logarithms."""
    two_k = 2**k
    r = 0
    while 3 ** (r + 1) < two_k:
        r += 1
    assert 3**r < two_k < 3 ** (r + 1)
    return r


def level_data(k: int) -> dict[str, int]:
    if k < 1:
        raise ValueError("K must be positive")

    two_k = 2**k
    four_k = 4**k
    r = threshold_index(k)

    signed = 0
    raw = 0
    corrected = 0
    for ell in range(k + 1):
        multiplicity = math.comb(k, ell)
        difference = two_k - 3**ell
        signed += multiplicity * difference
        raw += multiplicity * abs(difference)
        corrected += multiplicity * prime_to_six_part(difference)
        if ell >= 1:
            assert math.gcd(abs(difference), 6) == 1

    tail_t = two_k * sum(math.comb(k, ell) for ell in range(r + 1, k + 1))
    tail_u = sum(math.comb(k, ell) * 3**ell for ell in range(r + 1))
    all_even_raw = two_k - 1
    all_even_corrected = prime_to_six_part(all_even_raw)
    correction_d = all_even_raw - all_even_corrected
    error_e = 2 * four_k - corrected

    assert signed == 0
    assert raw == 2 * sum(
        math.comb(k, ell) * (two_k - 3**ell) for ell in range(r + 1)
    )
    assert raw == 2 * four_k - 2 * (tail_t + tail_u)
    assert corrected == raw - correction_d
    assert error_e == 2 * (tail_t + tail_u) + correction_d
    assert error_e > 0

    return {
        "raw": raw,
        "corrected": corrected,
        "T": tail_t,
        "U": tail_u,
        "D": correction_d,
        "e": error_e,
    }


def brute_word_coefficient(k: int) -> int:
    total = 0
    for word in range(1 << k):
        ell = word.bit_count()
        total += prime_to_six_part(2**k - 3**ell)
    return total


def exp_from_log_derivative(weights: list[int]) -> list[Fraction]:
    """Coefficients of exp(sum weights[k] u^k/k), with weights[0] unused."""
    out = [Fraction(1)]
    for n in range(1, len(weights)):
        numerator = sum(weights[k] * out[n - k] for k in range(1, n + 1))
        out.append(numerator / n)
    return out


def verify(max_k: int, brute_k: int) -> None:
    if max_k < 1:
        raise ValueError("max_k must be positive")
    brute_k = min(brute_k, max_k)

    # 3/5 < log_3(2) < 2/3, checked after clearing powers.
    assert 3**3 < 2**5
    assert 2**3 < 3**2

    # rho_T = 5(2/3)^(3/5) < 4; compare fifth powers.
    assert 5**5 * 2**3 < 4**5 * 3**3
    # rho_U = 3(3/2)^(2/3) < 4; compare third powers.
    assert 3**3 * 3**2 < 4**3 * 2**2

    levels = [None] + [level_data(k) for k in range(1, max_k + 1)]
    for k in range(1, brute_k + 1):
        assert brute_word_coefficient(k) == levels[k]["corrected"]

    a = [0] + [levels[k]["corrected"] for k in range(1, max_k + 1)]
    e = [0] + [levels[k]["e"] for k in range(1, max_k + 1)]
    zeta = exp_from_log_derivative(a)
    residual = exp_from_log_derivative([0] + [-e[k] for k in range(1, max_k + 1)])

    # (1-4u)^2 zeta(u) = exp(-sum e_k u^k/k), coefficient by coefficient.
    for n in range(max_k + 1):
        factored = zeta[n]
        if n >= 1:
            factored -= 8 * zeta[n - 1]
        if n >= 2:
            factored += 16 * zeta[n - 2]
        assert factored == residual[n]

    print("PASS: exact signed/absolute/corrected identities for K=1..", max_k)
    print("PASS: direct word enumeration for K=1..", brute_k)
    print("PASS: zeta leading-pole factorization through degree", max_k)
    print("PASS: exact powered inequalities certify rho_T,rho_U < 4")
    for k in sorted({1, 2, 5, 10, max_k}):
        if k <= max_k:
            ratio = levels[k]["corrected"] / 4**k
            print(f"K={k:3d}  a_K/4^K={ratio:.12f}  e_K={levels[k]['e']}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=80)
    parser.add_argument("--brute-k", type=int, default=16)
    args = parser.parse_args()
    verify(args.max_k, args.brute_k)


if __name__ == "__main__":
    main()
