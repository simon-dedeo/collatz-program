#!/usr/bin/env python3
"""Exact canonical public-cofactor language for the charge bouncer.

Every accepted public bouncer state has a unique form

    y = D^m*w - 1,

where ``m>0`` and ``w`` is positive and odd.  The fixed register further
requires

    M | D^m*w-1,       F | D^m*w.

Since ``gcd(F*D,M)=1`` and ``M`` is odd, the legal cofactors at opcode ``m``
are one ordinary affine family

    w = w_m + S*t,     S=2*F*M,     t>=0.

For consecutive opcodes ``m,h,m'``, eliminating the odd collision quotient
gives the exact public recurrence

    B^h*D^m'*w' = A^h*C^m*w - (A^h-B^h).

After substituting the canonical cofactor bases this becomes

    2^(154h+23m')*t' = 3^(114h+17m)*t + kappa.

Thus every branch reads one low binary cylinder and writes an affine ternary
tail:

    t=rho+2^P*u  ->  t'=sigma+3^Q*u.

Unlike quadratic-form coordinates, ``(m,t)`` is uniquely recoverable from the
public integer.  This worker reconstructs the bases and branch constants and
replays a bounded complete family through the arithmetic ``bouncer_step``
surrogate.  The artifact is an exact arithmetic interface audit, not a
literal Collatz-word compiler, infinite orbit, or counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from unit_charge_bouncer import (
    A,
    B,
    C,
    D,
    F,
    bouncer_step,
    constants,
    reverse_bouncer_step,
)


SCHEMA = "collatz-unit-charge-public-cofactor-v2"
REGISTER_MODULUS = int(constants()["M"])
COFACTOR_STRIDE = 2 * F * REGISTER_MODULUS
REGISTER_ODD_PART = C - D


def canonical_cofactor_base(m: int) -> int:
    """Least positive odd cofactor satisfying the fixed public register."""
    if m < 1:
        raise ValueError("defect opcode must be positive")
    multiplier = F * pow(D, m)
    inverse = pow(multiplier % REGISTER_MODULUS, -1, REGISTER_MODULUS)
    if inverse % 2 == 0:
        inverse += REGISTER_MODULUS
    base = F * inverse
    if not 0 < base < COFACTOR_STRIDE:
        raise AssertionError("canonical cofactor base left its period")
    if base % 2 != 1 or base % F:
        raise AssertionError("canonical cofactor base lost parity/register")
    if (pow(D, m) * base - 1) % REGISTER_MODULUS:
        raise AssertionError("canonical cofactor base missed public register")
    return base


def cofactor_tail(m: int, w: int) -> int:
    """Decode the unique nonnegative affine tail of a legal positive cofactor."""
    if w <= 0 or w % 2 != 1:
        raise ValueError("public cofactor must be positive and odd")
    if w % F or (pow(D, m) * w - 1) % REGISTER_MODULUS:
        raise ValueError("public cofactor missed the fixed register")
    difference = w - canonical_cofactor_base(m)
    if difference < 0 or difference % COFACTOR_STRIDE:
        raise AssertionError("legal cofactor did not have a canonical tail")
    return difference // COFACTOR_STRIDE


def public_state(m: int, tail: int) -> tuple[int, int]:
    """Return ``(y,w)`` from its uniquely decoded public coordinates."""
    if m < 1 or tail < 0:
        raise ValueError("public state coordinates are out of range")
    w = canonical_cofactor_base(m) + COFACTOR_STRIDE * tail
    y = pow(D, m) * w - 1
    if y <= 0 or y % 2 != 1:
        raise AssertionError("public cofactor produced a malformed state")
    if y % REGISTER_MODULUS or (y + 1) % F:
        raise AssertionError("public cofactor produced a state off register")
    return y, w


def branch(m: int, h: int, next_m: int) -> dict[str, int | str | bool]:
    """Construct the exact canonical tail transducer for one opcode triple."""
    if min(m, h, next_m) < 1:
        raise ValueError("all public-cofactor opcodes must be positive")
    input_base = canonical_cofactor_base(m)
    output_base = canonical_cofactor_base(next_m)
    ternary_coefficient = pow(A, h) * pow(C, m)
    binary_coefficient = pow(B, h) * pow(D, next_m)
    correction = pow(A, h) - pow(B, h)
    kappa_numerator = (
        ternary_coefficient * input_base
        - correction
        - binary_coefficient * output_base
    )
    if kappa_numerator % COFACTOR_STRIDE:
        raise AssertionError("canonical branch correction was not integral")
    kappa = kappa_numerator // COFACTOR_STRIDE
    source_residue = (
        -kappa * pow(ternary_coefficient, -1, binary_coefficient)
    ) % binary_coefficient
    target_base = (
        ternary_coefficient * source_residue + kappa
    ) // binary_coefficient
    if target_base < 0:
        raise AssertionError("canonical branch target tail became negative")

    p = 154 * h + 23 * next_m
    q = 114 * h + 17 * m
    if binary_coefficient != pow(2, p):
        raise AssertionError("binary branch exponent changed")
    if ternary_coefficient != pow(3, q):
        raise AssertionError("ternary branch exponent changed")
    return {
        "m": m,
        "h": h,
        "next_m": next_m,
        "P": p,
        "Q": q,
        "input_cofactor_base": input_base,
        "output_cofactor_base": output_base,
        "cofactor_stride": COFACTOR_STRIDE,
        "kappa": kappa,
        "source_tail_residue": source_residue,
        "target_tail_base": target_base,
        "tail_map": "t=rho+2^P*u -> t'=sigma+3^Q*u",
        "canonical_coordinates_are_public": True,
    }


def replay_branch_member(
    branch_row: dict[str, int | str | bool], surviving_tail: int
) -> dict[str, int | bool]:
    if surviving_tail < 0:
        raise ValueError("surviving tail must be nonnegative")
    m = int(branch_row["m"])
    h = int(branch_row["h"])
    next_m = int(branch_row["next_m"])
    p = int(branch_row["P"])
    q_exponent = int(branch_row["Q"])
    source_tail = int(branch_row["source_tail_residue"]) + pow(
        2, p
    ) * surviving_tail
    target_tail = int(branch_row["target_tail_base"]) + pow(
        3, q_exponent
    ) * surviving_tail
    y, w = public_state(m, source_tail)
    output_y, output_w = public_state(next_m, target_tail)

    if (
        pow(A, h) * (pow(C, m) * w - 1)
        != pow(B, h) * (pow(D, next_m) * output_w - 1)
    ):
        raise AssertionError("public-cofactor recurrence failed")
    collision_quotient = (pow(C, m) * w - 1) // pow(B, h)
    if collision_quotient <= 0 or collision_quotient % 2 != 1:
        raise AssertionError("public recurrence did not produce an odd quotient")
    if pow(A, h) * collision_quotient != output_y:
        raise AssertionError("public recurrence output identity failed")
    if collision_quotient % REGISTER_ODD_PART:
        raise AssertionError("collision quotient lost the canonical ternary rail")
    next_ternary_rail = collision_quotient // REGISTER_ODD_PART
    if (
        pow(C, m) * w
        != 1 + pow(B, h) * REGISTER_ODD_PART * next_ternary_rail
    ):
        raise AssertionError("S-unit ladder collision square failed")
    if (
        pow(D, next_m) * output_w
        != 1 + pow(A, h) * REGISTER_ODD_PART * next_ternary_rail
    ):
        raise AssertionError("S-unit ladder next-state square failed")

    arithmetic = bouncer_step(y)
    if (
        arithmetic.output_y != output_y
        or arithmetic.input_defect_cells != m + 1
        or arithmetic.background_cells != h - 1
        or arithmetic.output_defect_cells != next_m + 1
    ):
        raise AssertionError("canonical public recurrence missed bouncer arithmetic")
    reverse = reverse_bouncer_step(output_y)
    if reverse.input_y != y:
        raise AssertionError("canonical public recurrence lost reverse readback")
    if cofactor_tail(m, w) != source_tail:
        raise AssertionError("input public coordinates did not decode uniquely")
    if cofactor_tail(next_m, output_w) != target_tail:
        raise AssertionError("output public coordinates did not decode uniquely")
    return {
        "surviving_tail": surviving_tail,
        "source_tail": source_tail,
        "target_tail": target_tail,
        "input_y": y,
        "output_y": output_y,
        "input_w": w,
        "output_w": output_w,
        "collision_quotient": collision_quotient,
        "next_ternary_rail": next_ternary_rail,
        "S_unit_ladder_square": True,
        "public_recurrence_exact": True,
        "arithmetic_bouncer_replay": True,
        "reverse_readback": True,
        "canonical_decode": True,
    }


def dyadic_cylinders_intersect(
    first_residue: int, first_bits: int, second_residue: int, second_bits: int
) -> bool:
    """Whether two ordinary residue cylinders modulo powers of two meet."""
    common_bits = min(first_bits, second_bits)
    modulus = pow(2, common_bits)
    return (first_residue - second_residue) % modulus == 0


def build_record(bound: int = 3, members: int = 2) -> dict[str, object]:
    if bound < 1 or members < 1:
        raise ValueError("audit bounds must be positive")
    if REGISTER_MODULUS != pow(3, 33) * (C - D):
        raise AssertionError("public register modulus changed")
    if COFACTOR_STRIDE % 2 or COFACTOR_STRIDE != 2 * F * REGISTER_MODULUS:
        raise AssertionError("canonical cofactor stride changed")

    base_rows: list[dict[str, int | bool]] = []
    for m in range(1, bound + 2):
        base = canonical_cofactor_base(m)
        base_rows.append(
            {
                "m": m,
                "w_m": base,
                "w_m_odd": base % 2 == 1,
                "F_divides_w_m": base % F == 0,
                "M_divides_Dm_w_m_minus_one": (
                    (pow(D, m) * base - 1) % REGISTER_MODULUS == 0
                ),
            }
        )

    branch_rows: list[dict[str, object]] = []
    for m in range(1, bound + 1):
        for h in range(1, bound + 1):
            for next_m in range(1, bound + 1):
                row = branch(m, h, next_m)
                row["members"] = [
                    replay_branch_member(row, tail) for tail in range(members)
                ]
                branch_rows.append(row)

    prefix_rows: list[dict[str, int | bool]] = []
    for m in range(1, bound + 1):
        same_source = [row for row in branch_rows if int(row["m"]) == m]
        collisions = 0
        for first_index, first in enumerate(same_source):
            for second in same_source[first_index + 1 :]:
                if dyadic_cylinders_intersect(
                    int(first["source_tail_residue"]),
                    int(first["P"]),
                    int(second["source_tail_residue"]),
                    int(second["P"]),
                ):
                    collisions += 1
        if collisions:
            raise AssertionError("bounded public instruction cylinders overlapped")
        prefix_rows.append(
            {
                "m": m,
                "branches_compared": len(same_source),
                "pairs_compared": len(same_source) * (len(same_source) - 1) // 2,
                "intersections": collisions,
                "prefix_free_within_bound": True,
            }
        )

    partial_kraft = sum(
        (Fraction(1, pow(2, 154 * h + 23 * next_m))
         for h in range(1, bound + 1)
         for next_m in range(1, bound + 1)),
        start=Fraction(0, 1),
    )
    infinite_kraft = Fraction(
        1, (pow(2, 154) - 1) * (pow(2, 23) - 1)
    )
    if not 0 < partial_kraft < infinite_kraft:
        raise AssertionError("public instruction Kraft mass changed")

    same_defect_capacity = [
        {
            "m": m,
            "h": h,
            "Q": 114 * h + 17 * m,
            "P": 154 * h + 23 * m,
            "ternary_coefficient_exceeds_binary_address": (
                pow(3, 114 * h + 17 * m) > pow(2, 154 * h + 23 * m)
            ),
        }
        for m in range(1, bound + 1)
        for h in range(1, bound + 1)
    ]
    if not all(row["ternary_coefficient_exceeds_binary_address"] for row in same_defect_capacity):
        raise AssertionError("same-defect public tail lost its exact scale surplus")

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact canonical public-cofactor bases and affine tail branch "
            "formulas; bounded complete arithmetic bouncer and reverse replay; "
            "no literal Collatz-word compiler, invariant language, infinite "
            "orbit, or counterexample"
        ),
        "constants": {
            "A": A,
            "B": B,
            "C": C,
            "D": D,
            "F": F,
            "M": REGISTER_MODULUS,
            "S": COFACTOR_STRIDE,
            "R": REGISTER_ODD_PART,
        },
        "public_state": "y=D^m*(w_m+S*t)-1",
        "public_step": "A^h*(C^m*w-1)=B^h*(D^m_next*w_next-1)",
        "tail_step": "2^P*t_next=3^Q*t+kappa",
        "bounds": {
            "opcode_bound": bound,
            "members_per_branch": members,
            "branches": len(branch_rows),
            "arithmetic_replays": len(branch_rows) * members,
        },
        "canonical_bases": base_rows,
        "branches": branch_rows,
        "instruction_code": {
            "minimum_source_bits": 177,
            "bounded_prefix_checks": prefix_rows,
            "partial_kraft_mass": {
                "numerator": partial_kraft.numerator,
                "denominator": partial_kraft.denominator,
            },
            "all_positive_opcodes_kraft_mass": {
                "formula": "1/((2^154-1)*(2^23-1))",
                "numerator": infinite_kraft.numerator,
                "denominator": infinite_kraft.denominator,
            },
            "scope": (
                "pairwise prefix-freeness is checked only within the audit "
                "bound; the infinite Kraft sum is an exact geometric-series identity"
            ),
        },
        "same_defect_capacity": same_defect_capacity,
        "checks": {
            "canonical_public_coordinates": True,
            "branch_kappa_integral": True,
            "affine_binary_to_ternary_tail_map": True,
            "bounded_instruction_cylinders_prefix_free": True,
            "arithmetic_bouncer_replay": True,
            "reverse_readback": True,
            "S_unit_ladder_squares": True,
            "counterexample_not_claimed": True,
        },
    }


def source_sha256() -> str:
    sources = [Path(__file__), Path(__file__).with_name("unit_charge_bouncer.py")]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def canonical_json(payload: dict[str, object]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def verify_certificate(path: Path) -> None:
    stored = json.loads(path.read_text())
    bounds = stored["bounds"]
    expected = json.loads(
        canonical_json(
            build_record(
                int(bounds["opcode_bound"]), int(bounds["members_per_branch"])
            )
        )
    )
    if stored != expected:
        raise AssertionError("public-cofactor artifact does not reconstruct")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--bound", type=int, default=3)
    build.add_argument("--members", type=int, default=2)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        build_record()
        print("unit charge public cofactor selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record(args.bound, args.members)))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge public cofactor artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
