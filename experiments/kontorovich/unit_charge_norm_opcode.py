#!/usr/bin/env python3
"""Exact discriminant and opcode sieve for quadratic bouncer types.

For a positive binary norm

    N_d(x,u) = x^2 + d*u^2,       d = 7 (mod 8),

the mod-eight obstruction to a bouncer endpoint disappears.  The remaining
public register has odd part

    R = C-D = 5*19*1271069.

This creates a less obvious local constraint.  If a register prime ``p`` is
inert, i.e. ``-d`` is a nonsquare modulo p, then ``p | N_d(x,u)`` forces both
coordinates to vanish modulo p and hence ``p^2 | N_d(x,u)``.  If both the
input state and collision quotient are norms, the accepted collision equation
then gives

    C^m = D^m (mod p^2).

Every prime p dividing C-D exactly once has C/D=1+p*a (mod p^2), a nonzero,
so this is equivalent to ``p | m``.  Thus the tempting d=7 type pays the
hidden opcode tax ``95 | m`` at every typed transition.

The smallest squarefree d=7 (mod 8) avoiding an inert prime in R is d=31.
It has a further exact hardware match:

    R = 7706^2 + 31*1407^2.

Consequently every collision quotient q=R*r inherits an N_31 representation
from r, and every output A^h*q does too.  Dividing the accepted collision by R
gives the smaller payload recurrence

    2^(23m+154h) r' - 3^(17m+114g) r
      = (C^m-D^m)/(C-D),

when the input is the previous output ``A^g*R*r``.  This is a discriminant
selection and recurrence reduction, not an integral transition or orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path

from breakoff_delay_gate import v2
from unit_charge_bouncer import (
    A,
    B,
    C,
    D,
    bouncer_step,
    packet_to_y,
    replay_transition,
    transition_family,
)


SCHEMA = "collatz-unit-charge-norm-opcode-v2"
REGISTER_ODD_PART = C - D
REGISTER_PRIMES = (5, 19, 1271069)
SELECTED_D = 31
REGISTER_NORM_COORDINATES = (7706, 1407)
FIRST_TYPED_CANDIDATE = {
    "m": 1,
    "h": 1,
    "next_m": 1,
    "k": 3180293,
    "input_residual_coordinates": (
        -28658127184646064172542759367153679581704294829838548980354034456639546032643609,
        1078575712960634712747037457253951321204403377829171643523788548752107122821810,
    ),
    "quotient_residual_coordinates": (
        25293912740823340049271985250618220733473654296842351017066815767,
        17038148618045669233572156837187768759649201299206881708917247590,
    ),
}


def norm(d: int, x: int, u: int) -> int:
    return x * x + d * u * u


def norm_multiply(
    d: int, first: tuple[int, int], second: tuple[int, int]
) -> tuple[int, int]:
    """Multiply coordinates in Z[sqrt(-d)]."""
    x, u = first
    t, v = second
    result = (x * t - d * u * v, x * v + u * t)
    if norm(d, *result) != norm(d, x, u) * norm(d, t, v):
        raise AssertionError("quadratic norm multiplication failed")
    return result


def vp(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero is not used")
    exponent = 0
    value = abs(value)
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def is_squarefree(value: int) -> bool:
    if value < 1:
        return False
    divisor = 2
    while divisor * divisor <= value:
        if value % (divisor * divisor) == 0:
            return False
        divisor += 1
    return True


def legendre(value: int, prime: int) -> int:
    if value % prime == 0:
        return 0
    residue = pow(value % prime, (prime - 1) // 2, prime)
    return -1 if residue == prime - 1 else residue


def register_prime_row(d: int, prime: int) -> dict[str, int | str | bool]:
    if REGISTER_ODD_PART % prime:
        raise ValueError("prime is not in the register odd part")
    if vp(REGISTER_ODD_PART, prime) != 1:
        raise AssertionError("opcode sieve expects a simple register prime")
    modulus = prime * prime
    ratio = C * pow(D, -1, modulus) % modulus
    if (ratio - 1) % prime:
        raise AssertionError("C/D stopped being one modulo the register prime")
    tangent = ((ratio - 1) // prime) % prime
    if tangent == 0:
        raise AssertionError("register ratio lost its first-order term")
    character = legendre(-d, prime)
    return {
        "prime": prime,
        "v_p_C_minus_D": vp(REGISTER_ODD_PART, prime),
        "legendre_minus_d": character,
        "splitting": {1: "split", 0: "ramified", -1: "inert"}[character],
        "C_over_D_mod_p2": ratio,
        "first_order_tangent": tangent,
        "ratio_to_p_is_one_mod_p2": pow(ratio, prime, modulus) == 1,
        "inert_type_forces_opcode_divisibility": character == -1,
        "forced_opcode_divisor": prime if character == -1 else 1,
    }


def normalized_family(m: int, h: int, next_m: int) -> dict[str, int | bool]:
    """Normalize one accepted affine family by 3^34*(C-D) and C-D.

    The tail is ``n=n0+3*k``.  It forces one extra factor of three beyond the
    public register's 3^33, removing the inert-prime parity obstruction for
    d=31.  If both displayed residual linear forms are N_31 values, the
    corresponding family member is a literal typed accepted transition.
    """
    if min(m, h, next_m) < 1:
        raise ValueError("opcodes must be positive")
    family = transition_family(m + 1, h - 1, next_m + 1)
    packet0, output_packet0 = family.member(0)
    packet1, output_packet1 = family.member(1)
    y0 = packet_to_y(packet0)
    y_step = packet_to_y(packet1) - y0
    output0 = packet_to_y(output_packet0)
    output_step = packet_to_y(output_packet1) - output0
    if output0 % pow(A, h) or output_step % pow(A, h):
        raise AssertionError("accepted output lost its recharge square")
    q0 = output0 // pow(A, h)
    q_step = output_step // pow(A, h)

    input_register_factor = pow(3, 33) * REGISTER_ODD_PART
    if y0 % input_register_factor or y_step % input_register_factor:
        raise AssertionError("input affine family lost the public register")
    if q0 % REGISTER_ODD_PART or q_step % REGISTER_ODD_PART:
        raise AssertionError("quotient affine family lost C-D")
    input_base = y0 // input_register_factor
    input_step = y_step // input_register_factor
    quotient_base = q0 // REGISTER_ODD_PART
    quotient_step = q_step // REGISTER_ODD_PART
    if input_step % 3 == 0:
        raise AssertionError("tail no longer controls the next ternary digit")
    tail_residue = (-input_base * pow(input_step, -1, 3)) % 3
    residual_input_base = (input_base + input_step * tail_residue) // 3
    residual_input_step = input_step
    residual_quotient_base = quotient_base + quotient_step * tail_residue
    residual_quotient_step = 3 * quotient_step

    replay_rows: list[dict[str, int | bool]] = []
    for k in (0, 1, 7):
        tail = tail_residue + 3 * k
        packet, output_packet = family.member(tail)
        y = packet_to_y(packet)
        output = packet_to_y(output_packet)
        quotient = output // pow(A, h)
        residual_input = residual_input_base + residual_input_step * k
        residual_quotient = (
            residual_quotient_base + residual_quotient_step * k
        )
        if y != pow(3, 34) * REGISTER_ODD_PART * residual_input:
            raise AssertionError("normalized input linear form failed")
        if quotient != REGISTER_ODD_PART * residual_quotient:
            raise AssertionError("normalized quotient linear form failed")
        step = bouncer_step(y)
        if (
            step.output_y != output
            or step.input_defect_cells != m + 1
            or step.background_cells != h - 1
            or step.output_defect_cells != next_m + 1
        ):
            raise AssertionError("normalized family missed literal bouncer replay")
        replay_rows.append(
            {
                "k": k,
                "tail": tail,
                "input_identity": True,
                "quotient_identity": True,
                "literal_bouncer_replay": True,
            }
        )

    return {
        "m": m,
        "h": h,
        "next_m": next_m,
        "tail_formula": "tail=tail_residue_mod_3+3*k",
        "tail_residue_mod_3": tail_residue,
        "input_identity": "y=3^34*(C-D)*(input_base+input_step*k)",
        "input_base": residual_input_base,
        "input_step": residual_input_step,
        "quotient_identity": "q=(C-D)*(quotient_base+quotient_step*k)",
        "quotient_base": residual_quotient_base,
        "quotient_step": residual_quotient_step,
        "input_linear_form_primitive": gcd(
            residual_input_base, residual_input_step
        )
        == 1,
        "quotient_linear_form_primitive": gcd(
            residual_quotient_base, residual_quotient_step
        )
        == 1,
        "replay_rows": replay_rows,
    }


def geometric_debris(m: int) -> int:
    if m < 1:
        raise ValueError("opcode must be positive")
    numerator = pow(C, m) - pow(D, m)
    if numerator % REGISTER_ODD_PART:
        raise AssertionError("geometric debris lost C-D")
    direct = sum(pow(C, m - 1 - j) * pow(D, j) for j in range(m))
    if numerator // REGISTER_ODD_PART != direct:
        raise AssertionError("geometric debris identity failed")
    return direct


def multiply_upper_triangular(
    left: tuple[int, int, int], right: tuple[int, int, int]
) -> tuple[int, int, int]:
    """Multiply [[a,b],[0,d]] triples, with ``left`` acting last."""
    a_left, b_left, d_left = left
    a_right, b_right, d_right = right
    return (
        a_left * a_right,
        a_left * b_right + b_left * d_right,
        d_left * d_right,
    )


def defect_matrix(m: int) -> tuple[int, int, int]:
    """The recharge-free affine defect matrix J_m."""
    return (pow(C, m), geometric_debris(m), pow(D, m))


def normalized_step_matrix(m: int, g: int, h: int) -> tuple[int, int, int]:
    """Matrix for 2^P*r_next = 3^Q*r + H_m."""
    if min(m, g, h) < 1:
        raise ValueError("normalized bouncer opcodes must be positive")
    return (
        pow(C, m) * pow(A, g),
        geometric_debris(m),
        pow(D, m) * pow(B, h),
    )


def defect_semigroup_row(m: int, n: int) -> dict[str, int | bool]:
    """Check J_n J_m=J_(m+n) and the shared signed fixed coordinate."""
    if min(m, n) < 1:
        raise ValueError("defect lengths must be positive")
    product = multiply_upper_triangular(defect_matrix(n), defect_matrix(m))
    target = defect_matrix(m + n)
    if product != target:
        raise AssertionError("defect matrices stopped forming an additive semigroup")
    # R*f_m(r)+1=(C/D)^m*(R*r+1), checked without division.
    for residual in (-17, 0, 1, 23):
        numerator = pow(C, m) * residual + geometric_debris(m)
        if (
            REGISTER_ODD_PART * numerator + pow(D, m)
            != pow(C, m) * (REGISTER_ODD_PART * residual + 1)
        ):
            raise AssertionError("shared fixed-coordinate conjugacy failed")
    return {
        "m": m,
        "n": n,
        "J_n_times_J_m_equals_J_m_plus_n": True,
        "H_addition_law": (
            geometric_debris(m + n)
            == pow(C, n) * geometric_debris(m)
            + pow(D, m) * geometric_debris(n)
        ),
        "common_signed_fixed_point": "r=-1/(C-D)",
        "conjugating_coordinate": "z=(C-D)*r+1",
    }


def opcode_chain_row(
    initial_g: int, opcodes: tuple[tuple[int, int], ...]
) -> dict[str, object]:
    """Check the exact upper-triangular composition formula CP4."""
    if initial_g < 1 or not opcodes:
        raise ValueError("chain needs a positive initial recharge and one opcode")
    matrices: list[tuple[int, int, int]] = []
    p_values: list[int] = []
    q_values: list[int] = []
    debris_values: list[int] = []
    g = initial_g
    total = (1, 0, 1)
    for m, h in opcodes:
        matrix = normalized_step_matrix(m, g, h)
        matrices.append(matrix)
        p_values.append(23 * m + 154 * h)
        q_values.append(17 * m + 114 * g)
        debris_values.append(geometric_debris(m))
        total = multiply_upper_triangular(matrix, total)
        g = h

    explicit_debris = 0
    for index, debris in enumerate(debris_values):
        earlier_twos = pow(2, sum(p_values[:index]))
        later_threes = pow(3, sum(q_values[index + 1 :]))
        explicit_debris += debris * earlier_twos * later_threes
    expected = (
        pow(3, sum(q_values)),
        explicit_debris,
        pow(2, sum(p_values)),
    )
    if total != expected:
        raise AssertionError("opcode-chain composition formula failed")
    return {
        "initial_g": initial_g,
        "opcodes_m_h": [list(opcode) for opcode in opcodes],
        "P_values": p_values,
        "Q_values": q_values,
        "total_P": sum(p_values),
        "total_Q": sum(q_values),
        "composed_debris": explicit_debris,
        "matrix_product_matches_CP4": True,
    }


def verify_first_typed_candidate() -> dict[str, object]:
    """Replay the first represented affine-family member and its next failure."""
    d = SELECTED_D
    m = int(FIRST_TYPED_CANDIDATE["m"])
    h = int(FIRST_TYPED_CANDIDATE["h"])
    next_m = int(FIRST_TYPED_CANDIDATE["next_m"])
    k = int(FIRST_TYPED_CANDIDATE["k"])
    input_residual_coordinates = tuple(
        int(value) for value in FIRST_TYPED_CANDIDATE["input_residual_coordinates"]
    )
    quotient_residual_coordinates = tuple(
        int(value)
        for value in FIRST_TYPED_CANDIDATE["quotient_residual_coordinates"]
    )
    normalized = normalized_family(m, h, next_m)
    tail = int(normalized["tail_residue_mod_3"]) + 3 * k
    residual_input = int(normalized["input_base"]) + int(
        normalized["input_step"]
    ) * k
    residual_quotient = int(normalized["quotient_base"]) + int(
        normalized["quotient_step"]
    ) * k
    if norm(d, *input_residual_coordinates) != residual_input:
        raise AssertionError("candidate input residual is not the recorded norm")
    if norm(d, *quotient_residual_coordinates) != residual_quotient:
        raise AssertionError("candidate quotient residual is not the recorded norm")

    family = transition_family(m + 1, h - 1, next_m + 1)
    packet, output_packet = family.member(tail)
    input_y = packet_to_y(packet)
    output_y = packet_to_y(output_packet)
    if output_y % pow(A, h):
        raise AssertionError("candidate output lost its recharge factor")
    quotient = output_y // pow(A, h)

    input_coordinates = norm_multiply(
        d, REGISTER_NORM_COORDINATES, input_residual_coordinates
    )
    input_coordinates = (
        pow(3, 17) * input_coordinates[0],
        pow(3, 17) * input_coordinates[1],
    )
    quotient_coordinates = norm_multiply(
        d, REGISTER_NORM_COORDINATES, quotient_residual_coordinates
    )
    output_coordinates = (
        pow(3, 57 * h) * quotient_coordinates[0],
        pow(3, 57 * h) * quotient_coordinates[1],
    )
    if norm(d, *input_coordinates) != input_y:
        raise AssertionError("candidate public input is not N_31")
    if norm(d, *quotient_coordinates) != quotient:
        raise AssertionError("candidate collision quotient is not N_31")
    if norm(d, *output_coordinates) != output_y:
        raise AssertionError("candidate output did not regenerate N_31")

    step = bouncer_step(input_y)
    if (
        step.output_y != output_y
        or step.input_defect_cells != m + 1
        or step.background_cells != h - 1
        or step.output_defect_cells != next_m + 1
    ):
        raise AssertionError("candidate missed literal bouncer semantics")
    macro_replay = replay_transition(family, tail)

    # The type regenerates, but its first output does not expose a whole next
    # recharge block.  Record the exact failure rather than calling it a chain.
    next_collision = pow(C, next_m) * (output_y + 1) - pow(D, next_m)
    next_collision_valuation = v2(next_collision)
    next_recharge_difference = next_collision_valuation - 23 * next_m
    if next_recharge_difference % 154 == 0:
        raise AssertionError("recorded one-step candidate unexpectedly continued")

    return {
        "d": d,
        "m": m,
        "h": h,
        "next_m": next_m,
        "normalized_family_k": k,
        "family_tail": tail,
        "input_residual": residual_input,
        "input_residual_coordinates": list(input_residual_coordinates),
        "quotient_residual": residual_quotient,
        "quotient_residual_coordinates": list(quotient_residual_coordinates),
        "input_y": input_y,
        "input_y_decimal_digits": len(str(input_y)),
        "input_coordinates": list(input_coordinates),
        "collision_quotient": quotient,
        "quotient_coordinates": list(quotient_coordinates),
        "output_y": output_y,
        "output_y_decimal_digits": len(str(output_y)),
        "output_coordinates": list(output_coordinates),
        "strict_public_state_growth": output_y > input_y,
        "literal_bouncer_step": True,
        "underlying_macro_replay": macro_replay,
        "next_collision_valuation": next_collision_valuation,
        "next_recharge_difference": next_recharge_difference,
        "next_recharge_remainder_mod_154": next_recharge_difference % 154,
        "next_step_accepted": False,
    }


def build_record() -> dict[str, object]:
    if REGISTER_ODD_PART != 5 * 19 * 1271069:
        raise AssertionError("register factorization changed")
    if norm(SELECTED_D, *REGISTER_NORM_COORDINATES) != REGISTER_ODD_PART:
        raise AssertionError("selected discriminant lost its register norm")

    candidates: list[dict[str, object]] = []
    for d in range(7, SELECTED_D + 1, 8):
        if not is_squarefree(d):
            continue
        prime_rows = [register_prime_row(d, prime) for prime in REGISTER_PRIMES]
        forced_divisor = 1
        for row in prime_rows:
            forced_divisor *= int(row["forced_opcode_divisor"])
        candidates.append(
            {
                "d": d,
                "d_mod_8": d % 8,
                "squarefree": True,
                "register_prime_rows": prime_rows,
                "forced_opcode_divisor": forced_divisor,
                "has_no_inert_register_prime": forced_divisor == 1,
            }
        )
    if [row["d"] for row in candidates] != [7, 15, 23, 31]:
        raise AssertionError("small discriminant list changed")
    if candidates[0]["forced_opcode_divisor"] != 95:
        raise AssertionError("d=7 opcode tax changed")
    if not candidates[-1]["has_no_inert_register_prime"]:
        raise AssertionError("d=31 stopped clearing the register-prime sieve")
    if any(row["has_no_inert_register_prime"] for row in candidates[:-1]):
        raise AssertionError("d=31 is no longer the first untaxed candidate")

    families = [
        normalized_family(1, 1, 1),
        normalized_family(2, 1, 1),
        normalized_family(2, 2, 2),
    ]
    if not all(
        row["input_linear_form_primitive"]
        and row["quotient_linear_form_primitive"]
        for row in families
    ):
        raise AssertionError("normalized residual family acquired a fixed divisor")

    debris_rows = [
        {"m": m, "H_m": geometric_debris(m), "H_m_bits": geometric_debris(m).bit_length()}
        for m in (1, 2, 3, 19, 95)
    ]
    semigroup_rows = [
        defect_semigroup_row(m, n)
        for m, n in ((1, 1), (1, 2), (2, 3), (19, 23))
    ]
    chain_rows = [
        opcode_chain_row(1, ((1, 1),)),
        opcode_chain_row(1, ((1, 1), (1, 1))),
        opcode_chain_row(2, ((1, 3), (2, 1), (4, 2))),
    ]
    typed_candidate = verify_first_typed_candidate()

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact inert-register-prime opcode sieve for quadratic norm "
            "types; minimal squarefree d=7 mod 8 without that local tax; "
            "exact representation of C-D by N_31; and normalized accepted "
            "affine transition families; one literal outward N_31-typed "
            "accepted transition with exact next-step failure; exact "
            "recharge-free defect semigroup and general finite opcode-chain "
            "composition law; no self-synchronizing infinite recurrence or "
            "counterexample"
        ),
        "constants": {
            "A": A,
            "B": B,
            "C": C,
            "D": D,
            "C_minus_D": REGISTER_ODD_PART,
            "register_primes": list(REGISTER_PRIMES),
        },
        "opcode_sieve": {
            "principle": (
                "if -d is nonsquare mod p and p divides an N_d value, then "
                "p^2 divides it; the collision modulo p^2 forces p|m"
            ),
            "small_squarefree_candidates": candidates,
            "d_7_forces_m_multiple_of": 95,
            "first_candidate_without_inert_register_prime": SELECTED_D,
        },
        "selected_type": {
            "d": SELECTED_D,
            "class_number_diagnostic_not_used_as_proof": 3,
            "register_norm_identity": (
                "C-D=7706^2+31*1407^2"
            ),
            "register_norm_coordinates": list(REGISTER_NORM_COORDINATES),
        },
        "normalized_accepted_families": families,
        "first_literal_typed_transition": typed_candidate,
        "payload_recurrence": {
            "state_form": "y=A^g*(C-D)*r",
            "quotient_form": "q=(C-D)*r_next",
            "equation": (
                "2^(23m+154h)*r_next-3^(17m+114g)*r=H_m"
            ),
            "H_m": "(C^m-D^m)/(C-D)",
            "geometric_debris_rows": debris_rows,
            "defect_semigroup_identity": "J_n*J_m=J_(m+n)",
            "defect_semigroup_rows": semigroup_rows,
            "finite_opcode_chain_identity": (
                "2^(sum P_t)*r_N=3^(sum Q_t)*r_0+K_W"
            ),
            "finite_opcode_chain_rows": chain_rows,
        },
        "checks": {
            "d_7_opcode_tax_exact": True,
            "d_31_minimal_in_tested_complete_range": True,
            "C_minus_D_is_N31": True,
            "normalized_families_literal_replay": True,
            "one_literal_typed_transition_replayed": True,
            "defect_semigroup_exact": True,
            "finite_opcode_chain_formula_exact": True,
            "two_step_chain_not_claimed": True,
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
    expected = json.loads(canonical_json(build_record()))
    if stored != expected:
        raise AssertionError("norm-opcode artifact does not reconstruct")


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
        print("unit charge norm opcode selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record()))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge norm opcode artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
