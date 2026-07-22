#!/usr/bin/env python3
"""Exact perfect-power closure equation for the autonomous charge bouncer.

At a charge-bouncer defect boundary write

    y + 1 = D^m u,                 D=2^23,
    C^m u = 1 + B^h q,             C=3^17, B=2^154,
    y' + 1 = D^m' u' = 1 + A^h q, A=3^114.

The fixed register forces ``F | u`` for

    F=(A-B)/5.

The first genuinely self-similar payload ansatz is therefore

    u=F*r^23,  u'=F*r'^23.

The exponent 23 is selected by the hardware: it turns one power of two in
``r'`` into exactly one next defect cell in ``y'+1``.  Eliminating q gives the
necessary reproduction equation

    A^h C^m r^23 - B^h D^m' r'^23 = (A^h-B^h)/F.   (PQ)

For the shortest recharge h=1, (PQ) becomes a finite family of 23 generalized
Fermat equations.  Absorbing complete 23rd powers leaves

    3^e X^23 - 2^16 Y^23 = 5,
    e=(114+17m) mod 23.

Exact finite-field tests at p=47,139,461 eliminate 22 of the 23 exponent
classes.  Only e=15, equivalently m=5 mod 23, survives.  This is a direct
closure obstruction, not a seed search.  It does not settle the surviving
Thue equation or construct an infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from unit_charge_bouncer import A, B, C, D, F


SCHEMA = "collatz-unit-charge-power-quine-v1"


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 1
    return True


def power_residues(prime: int) -> set[int]:
    if not is_prime(prime):
        raise ValueError("finite-field obstruction expects a prime")
    return {pow(value, 23, prime) for value in range(prime)}


def surviving_exponents(prime: int, candidates: set[int]) -> set[int]:
    """Return e for which 3^e X^23-2^16 Y^23=5 is soluble mod p."""
    residues = power_residues(prime)
    right = {pow(2, 16, prime) * value % prime for value in residues}
    survivors: set[int] = set()
    for exponent in candidates:
        coefficient = pow(3, exponent, prime)
        if any(
            (coefficient * value - 5) % prime in right
            for value in residues
        ):
            survivors.add(exponent)
    return survivors


def exact_factorization_of_F() -> dict[int, int]:
    factors = {
        173: 1,
        168803: 1,
        1707499: 1,
        33826633: 1,
        73768171: 1,
        317905672921: 1,
        12463506446779: 1,
    }
    product = 1
    for prime, exponent in factors.items():
        if not is_prime(prime):
            raise AssertionError("recorded F factor is not prime")
        product *= pow(prime, exponent)
    if product != F:
        raise AssertionError("recorded prime factorization of F changed")
    return factors


def check_power_quine_identity(
    h: int, m: int, next_m: int, r: int, next_r: int
) -> dict[str, int | bool]:
    """Check algebraic equivalence after eliminating the collision quotient.

    This routine deliberately accepts only tuples satisfying (PQ).  It is a
    verifier for a proposed closure candidate, not a generator.
    """
    if min(h, m, next_m, r, next_r) < 1:
        raise ValueError("power-quine parameters must be positive")
    left = pow(A, h) * pow(C, m) * pow(r, 23)
    left -= pow(B, h) * pow(D, next_m) * pow(next_r, 23)
    numerator = pow(A, h) - pow(B, h)
    if numerator % F:
        raise AssertionError("fixed-register divisor F was lost")
    right = numerator // F
    return {
        "h": h,
        "m": m,
        "next_m": next_m,
        "r": r,
        "next_r": next_r,
        "left": left,
        "right": right,
        "power_quine_equation_holds": left == right,
    }


def build_record() -> dict[str, object]:
    if A - B != 5 * F:
        raise AssertionError("charge fixed-form divisor identity failed")
    if (A, B, C, D) != (
        pow(3, 114),
        pow(2, 154),
        pow(3, 17),
        pow(2, 23),
    ):
        raise AssertionError("charge-bouncer radix constants changed")

    factors = exact_factorization_of_F()
    alive = set(range(23))
    rows: list[dict[str, object]] = []
    expected = {
        47: {4, 6, 15},
        139: {6, 15},
        461: {15},
    }
    for prime in (47, 139, 461):
        before = sorted(alive)
        alive = surviving_exponents(prime, alive)
        if alive != expected[prime]:
            raise AssertionError(f"finite-field survivors changed at p={prime}")
        rows.append(
            {
                "prime": prime,
                "prime_is_one_mod_23": prime % 23 == 1,
                "power_residue_count_including_zero": len(
                    power_residues(prime)
                ),
                "candidate_exponents_before": before,
                "candidate_exponents_after": sorted(alive),
            }
        )

    if alive != {15}:
        raise AssertionError("short-recharge sieve did not leave one class")
    matching_m = {
        m for m in range(23) if (114 + 17 * m) % 23 in alive
    }
    if matching_m != {5}:
        raise AssertionError("surviving exponent did not decode to m=5 mod 23")

    # This is only a negative sanity example: r=r'=1 and m=m'=1 does not
    # solve PQ.  A positive tuple would have to pass check_power_quine_identity
    # and then the still-separate exact valuation/register conditions.
    sanity = check_power_quine_identity(1, 1, 1, 1, 1)
    if sanity["power_quine_equation_holds"]:
        raise AssertionError("negative sanity tuple unexpectedly closed")

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact derivation data for the invariant u=F*r^23 charge-bouncer "
            "closure ansatz; exact finite-field elimination of 22 of 23 "
            "short-recharge exponent classes; the surviving generalized "
            "Fermat equation is not settled and no orbit is claimed"
        ),
        "constants": {
            "A": A,
            "B": B,
            "C": C,
            "D": D,
            "F": F,
            "F_prime_factorization": {
                str(prime): exponent for prime, exponent in factors.items()
            },
        },
        "bouncer_radix_equations": [
            "C^m*u=1+B^h*q",
            "D^m_next*u_next=1+A^h*q",
        ],
        "invariant_payload_ansatz": "u=F*r^23, u_next=F*r_next^23",
        "why_exponent_23": (
            "D=2^23, so multiplying v2(r_next) by 23 writes exactly the "
            "next defect-cell count while preserving the fixed factor F"
        ),
        "necessary_reproduction_equation": (
            "A^h*C^m*r^23-B^h*D^m_next*r_next^23=(A^h-B^h)/F"
        ),
        "shortest_recharge_h_one": {
            "equation_before_absorbing_powers": (
                "3^(114+17m)*r^23-2^(154+23m_next)*r_next^23=5"
            ),
            "reduced_equations": "3^e*X^23-2^16*Y^23=5",
            "e_definition": "e=(114+17m) mod 23",
            "finite_field_sieve": rows,
            "surviving_e_mod_23": 15,
            "surviving_m_mod_23": 5,
            "surviving_equation": "3^15*X^23-2^16*Y^23=5",
            "status": (
                "open in this exact artifact; a separate PARI diagnostic is "
                "not verification evidence"
            ),
        },
        "negative_sanity_tuple": sanity,
        "checks": {
            "fixed_divisor_A_minus_B_equals_5F": True,
            "F_factorization_reconstructed": True,
            "power_quine_elimination_identity": True,
            "finite_field_residue_sets_enumerated_exactly": True,
            "twenty_two_exponent_classes_excluded": True,
            "one_exponent_class_remains": True,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_bouncer.py"),
        Path(__file__).with_name("unit_charge_discharge.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def canonical_json(payload: dict[str, object]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def verify_certificate(path: Path) -> None:
    stored = json.loads(path.read_text())
    expected = json.loads(canonical_json(build_record()))
    if stored != expected:
        raise AssertionError("power-quine artifact does not reconstruct exactly")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        build_record()
        print("unit charge power-quine selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record()))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge power-quine artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # pragma: no cover - CLI failure path
        print(f"ERROR: {exc}", file=sys.stderr)
        raise
