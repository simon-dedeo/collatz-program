#!/usr/bin/env python3
"""Exact resonance data for the next perfect-power charge-bouncer lane.

For a recharge of length ``h``, the perfect-23rd-power necessary equation is

    3^(114h+17m) r^23 - 2^(154h+23m') r'^23
      = (A^h-B^h)/F.

At ``h=23`` both recharge coefficients are complete 23rd powers.  Moreover,

    A^23 = 3^4 C^154,       B^23 = D^154.

Thus the exponent determinant leaves only a four-trit residual when 23
recharge cells are exchanged against 154 defect cells.  This worker checks
that identity and the fact that the three finite-field sieves which nearly
closed ``h=1`` leave every exponent class at ``h=23``.  It does not construct
a corrected payload or an infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

from unit_charge_bouncer import A, B, C, D, F


SCHEMA = "collatz-unit-charge-power-resonance-v1"
RECHARGE = 23
PRIMES = (47, 139, 461)


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
        raise ValueError("resonance sieve expects a prime")
    return {pow(value, 23, prime) for value in range(prime)}


def reduced_rhs(h: int) -> int:
    numerator = pow(A, h) - pow(B, h)
    if numerator % F:
        raise AssertionError("fixed divisor did not divide recharge forcing")
    return numerator // F


def surviving_exponents(h: int, prime: int) -> set[int]:
    """Solve the reduced h-recharge equation modulo ``prime`` for each e."""
    residues = power_residues(prime)
    rhs = reduced_rhs(h) % prime
    binary_exponent = (154 * h) % 23
    binary_terms = {
        pow(2, binary_exponent, prime) * value % prime for value in residues
    }
    return {
        exponent
        for exponent in range(23)
        if any(
            (pow(3, exponent, prime) * value - rhs) % prime in binary_terms
            for value in residues
        )
    }


def source_sha256() -> str:
    sources = [Path(__file__), Path(__file__).with_name("unit_charge_bouncer.py")]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_record() -> dict[str, object]:
    if pow(A, 23) != pow(3, 4) * pow(C, 154):
        raise AssertionError("ternary determinant-four resonance failed")
    if pow(B, 23) != pow(D, 154):
        raise AssertionError("binary rank-one resonance failed")

    phi23 = (pow(A, 23) - pow(B, 23)) // (A - B)
    rhs = reduced_rhs(RECHARGE)
    if rhs != 5 * phi23:
        raise AssertionError("23-cell forcing lost its cyclotomic form")
    if gcd(F, phi23) != 1:
        raise AssertionError("unexpected fixed-divisor/cyclotomic overlap")

    rows: list[dict[str, object]] = []
    all_exponents = set(range(23))
    for prime in PRIMES:
        survivors = surviving_exponents(RECHARGE, prime)
        if survivors != all_exponents:
            raise AssertionError(f"h=23 resonance was locally cut at p={prime}")
        rows.append(
            {
                "prime": prime,
                "prime_is_one_mod_23": prime % 23 == 1,
                "power_residue_count_including_zero": len(power_residues(prime)),
                "surviving_exponents": sorted(survivors),
            }
        )

    opcode_to_exponent = {
        m: (114 * RECHARGE + 17 * m) % 23 for m in range(23)
    }
    if set(opcode_to_exponent.values()) != all_exponents:
        raise AssertionError("opcode residue did not parameterize all exponents")

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact h=23 determinant-four resonance and complete local "
            "survival at p=47,139,461; no corrected payload, transition, "
            "or infinite orbit is claimed"
        ),
        "recharge_h": RECHARGE,
        "constants": {"A": A, "B": B, "C": C, "D": D, "F": F},
        "resonance_identities": ["A^23=3^4*C^154", "B^23=D^154"],
        "reduced_equation": (
            "3^e*X^23-2^f*Y^23=(A^h-B^h)/F, "
            "e=(114h+17m) mod 23, f=154h mod 23"
        ),
        "h23_binary_exponent_mod_23": (154 * RECHARGE) % 23,
        "h23_rhs_digits": len(str(rhs)),
        "h23_rhs_cyclotomic_identity": "(A^23-B^23)/F=5*Phi_23(A,B)",
        "gcd_F_Phi23": gcd(F, phi23),
        "opcode_residue_to_exponent": {
            str(m): exponent for m, exponent in opcode_to_exponent.items()
        },
        "finite_field_sieve": rows,
        "checks": {
            "ternary_resonance_exact": True,
            "binary_resonance_exact": True,
            "cyclotomic_forcing_exact": True,
            "fixed_divisor_coprime_to_Phi23": True,
            "all_23_exponent_classes_survive_all_three_primes": True,
        },
    }


def canonical_json(payload: dict[str, object]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def verify_certificate(path: Path) -> None:
    stored = json.loads(path.read_text())
    expected = json.loads(canonical_json(build_record()))
    if stored != expected:
        raise AssertionError("power-resonance artifact does not reconstruct")


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
        print("unit charge power resonance selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record()))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge power resonance artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
