#!/usr/bin/env python3
"""Exact quadratic-norm reproduction interface for the charge bouncer.

The public 23rd-power type is rigid enough to lead to Thue equations.  A
two-coordinate homogeneous type is much less rigid.  For

    N_d(x,u) = x^2 + d*u^2

both bouncer recharge multipliers are squares:

    A^h = (3^(57h))^2,       B^h = (2^(77h))^2.

Consequently a collision quotient ``q=N_d(t,v)`` automatically gives an
output of the same type, ``A^h*q=N_d(3^(57h)t,3^(57h)v)``.  The collision
side scales in the same way by ``B^h``.  This is a literal two-rail data type,
not a metaphor.

The naive choice d=1 is universally impossible: every accepted bouncer state
and every collision quotient is 7 modulo 8, whereas a sum of two squares is
never 3 modulo 4.  The smallest local correction is d=7.  This audit uses a
more hardware-matched discriminant

    d_hw = 13*(3^17-2^23) = 5*13*19*1271069 = 7 (mod 8).

It ramifies every non-ternary prime forced by the public register.  Exact CRT
witnesses show that the norm type separately contains inputs with any audited
defect opcode and collision quotients whose scaled outputs have any audited
next opcode.  An exact PARI-discovered rational point also shows that the
rank-four collision quadric for m=h=1 has no rational obstruction.

The endpoint witnesses are deliberately *not paired*.  The remaining problem
is the integral coupling equation

    C^m*(N_d(x,u)+1) = D^m*(1+B^h*N_d(t,v)).

Thus this worker certifies a locally legal and automatically reproducing type,
not an ordinary transition, infinite orbit, or counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

from breakoff_delay_gate import v2
from unit_charge_bouncer import A, B, C, D, F, constants, defect_phase
from unit_charge_power_quine import exact_factorization_of_F, is_prime


SCHEMA = "collatz-unit-charge-quadratic-norm-v1"
REGISTER_ODD_PART = C - D
HARDWARE_D = 13 * REGISTER_ODD_PART
HARDWARE_D_FACTORS = (5, 13, 19, 1271069)


def norm(d: int, x: int, u: int) -> int:
    if d < 1:
        raise ValueError("norm coefficient must be positive")
    return x * x + d * u * u


def crt_pair(a: int, modulus_a: int, b: int, modulus_b: int) -> int:
    if gcd(modulus_a, modulus_b) != 1:
        raise ValueError("CRT moduli must be coprime")
    return (
        a
        + modulus_a
        * (((b - a) * pow(modulus_a, -1, modulus_b)) % modulus_b)
    ) % (modulus_a * modulus_b)


def crt_many(congruences: list[tuple[int, int]]) -> int:
    value, modulus = congruences[0]
    value %= modulus
    for target, next_modulus in congruences[1:]:
        value = crt_pair(value, modulus, target % next_modulus, next_modulus)
        modulus *= next_modulus
    return value


def legendre(value: int, prime: int) -> int:
    residue = pow(value % prime, (prime - 1) // 2, prime)
    return -1 if residue == prime - 1 else residue


def tonelli_shanks(value: int, prime: int) -> int | None:
    """A deterministic square root modulo an odd prime, when one exists."""
    value %= prime
    if value == 0:
        return 0
    if legendre(value, prime) != 1:
        return None
    if prime % 4 == 3:
        return pow(value, (prime + 1) // 4, prime)

    odd = prime - 1
    exponent = 0
    while odd % 2 == 0:
        exponent += 1
        odd //= 2
    nonresidue = 2
    while legendre(nonresidue, prime) != -1:
        nonresidue += 1
    c = pow(nonresidue, odd, prime)
    root = pow(value, (odd + 1) // 2, prime)
    residue = pow(value, odd, prime)
    level = exponent
    while residue != 1:
        i = 1
        square = residue * residue % prime
        while square != 1:
            square = square * square % prime
            i += 1
            if i >= level:
                raise AssertionError("Tonelli-Shanks failed to descend")
        correction = pow(c, 1 << (level - i - 1), prime)
        root = root * correction % prime
        c = correction * correction % prime
        residue = residue * c % prime
        level = i
    if root * root % prime != value:
        raise AssertionError("modular square-root check failed")
    return root


def norm_representation_mod_prime(d: int, target: int, prime: int) -> tuple[int, int]:
    """Find x,u with x^2+d*u^2=target (mod prime)."""
    if prime == 2 or not is_prime(prime) or d % prime == 0:
        raise ValueError("expected an odd nondegenerate prime modulus")
    for u in range(256):
        root = tonelli_shanks(target - d * u * u, prime)
        if root is not None:
            if norm(d, root, u) % prime != target % prime:
                raise AssertionError("finite-field norm solver failed")
            return root, u
    raise AssertionError("unexpectedly long finite-field norm search")


def norm_representation_mod_F(d: int, target: int) -> tuple[int, int]:
    x_congruences: list[tuple[int, int]] = []
    u_congruences: list[tuple[int, int]] = []
    for prime in exact_factorization_of_F():
        x, u = norm_representation_mod_prime(d, target, prime)
        x_congruences.append((x, prime))
        u_congruences.append((u, prime))
    x = crt_many(x_congruences)
    u = crt_many(u_congruences)
    if norm(d, x, u) % F != target % F:
        raise AssertionError("CRT norm representation modulo F failed")
    return x, u


def odd_square_roots_mod_power_of_two(target: int, bits: int) -> list[int]:
    if bits < 3 or target % 8 != 1:
        raise ValueError("odd 2-adic squares require target=1 mod 8")
    roots = [root for root in range(8) if root * root % 8 == target % 8]
    modulus = 8
    while modulus < (1 << bits):
        next_modulus = 2 * modulus
        roots = sorted(
            {
                candidate
                for root in roots
                for candidate in (root, root + modulus)
                if candidate * candidate % next_modulus == target % next_modulus
            }
        )
        modulus = next_modulus
    if len(roots) != 4:
        raise AssertionError("odd 2-adic unit should have four square roots")
    return roots


def exact_two_adic_norm_root(d: int, scale: int, exponent: int) -> int:
    """Return u with v2(scale*d*u^2+1)=exponent."""
    if exponent < 3 or d % 8 != 7 or scale % 8 != 1:
        raise ValueError("hardware norm root expects d=7 and scale=1 mod 8")
    low_modulus = 1 << exponent
    target = (-pow(scale * d, -1, low_modulus)) % low_modulus
    for root in odd_square_roots_mod_power_of_two(target, exponent):
        if v2(scale * d * root * root + 1) == exponent:
            return root
    raise AssertionError("failed to select an exact 2-adic norm root")


def typed_input(d: int, m: int) -> dict[str, int | bool]:
    """Construct an independently legal N_d input with defect opcode m."""
    if m < 1:
        raise ValueError("defect opcode must be positive")
    exponent = 23 * m
    modulus_two = 1 << (exponent + 1)
    u_two = exact_two_adic_norm_root(d, 1, exponent)
    x_f, u_f = norm_representation_mod_F(d, -1)
    register_modulus = constants()["M"]
    x = crt_many([(0, modulus_two), (0, register_modulus), (x_f, F)])
    u = crt_many([(u_two, modulus_two), (0, register_modulus), (u_f, F)])
    y = norm(d, x, u)
    if y % register_modulus or (y + 1) % F:
        raise AssertionError("typed input missed the public register")
    if v2(y + 1) != exponent or defect_phase(y) != m:
        raise AssertionError("typed input missed its exact defect opcode")
    return {
        "m": m,
        "x": x,
        "u": u,
        "y": y,
        "y_decimal_digits": len(str(y)),
        "y_mod_8": y % 8,
        "y_mod_M": y % register_modulus,
        "y_plus_one_mod_F": (y + 1) % F,
        "exact_v2_y_plus_one": v2(y + 1),
        "defect_phase_replay": defect_phase(y),
        "norm_identity": y == norm(d, x, u),
    }


def typed_output_quotient(d: int, h: int, next_m: int) -> dict[str, int | bool]:
    """Construct q=N_d(t,v) for which A^h*q is an independently legal output."""
    if min(h, next_m) < 1:
        raise ValueError("recharge and next opcode must be positive")
    exponent = 23 * next_m
    scale = pow(A, h)
    modulus_two = 1 << (exponent + 1)
    v_two = exact_two_adic_norm_root(d, scale, exponent)
    target_f = -pow(scale, -1, F)
    t_f, v_f = norm_representation_mod_F(d, target_f)

    # q=2 mod 3 is forced by 1+B^h*q=0 mod C.  Since d_hw=1 mod 3,
    # t=v=1 supplies it.  Setting both coordinates to zero modulo C-D
    # supplies the non-ternary part of the output register.
    if d % 3 != 1:
        raise AssertionError("chosen hardware discriminant changed mod 3")
    t = crt_many(
        [(0, modulus_two), (0, REGISTER_ODD_PART), (1, 3), (t_f, F)]
    )
    v = crt_many(
        [(v_two, modulus_two), (0, REGISTER_ODD_PART), (1, 3), (v_f, F)]
    )
    q = norm(d, t, v)
    output = scale * q
    if q % 3 != 2 or q % REGISTER_ODD_PART:
        raise AssertionError("typed quotient missed collision/output residues")
    if output % constants()["M"] or (output + 1) % F:
        raise AssertionError("typed quotient missed the public output register")
    if v2(output + 1) != exponent or defect_phase(output) != next_m:
        raise AssertionError("typed quotient missed the next defect opcode")
    return {
        "h": h,
        "next_m": next_m,
        "t": t,
        "v": v,
        "q": q,
        "q_decimal_digits": len(str(q)),
        "q_mod_8": q % 8,
        "q_mod_3": q % 3,
        "q_mod_C_minus_D": q % REGISTER_ODD_PART,
        "output": output,
        "output_decimal_digits": len(str(output)),
        "output_mod_M": output % constants()["M"],
        "output_plus_one_mod_F": (output + 1) % F,
        "exact_v2_output_plus_one": v2(output + 1),
        "defect_phase_replay": defect_phase(output),
        "quotient_norm_identity": q == norm(d, t, v),
        "output_norm_identity": output
        == norm(d, pow(3, 57 * h) * t, pow(3, 57 * h) * v),
    }


def quadratic_collision_value(
    d: int, m: int, h: int, x: int, u: int, t: int, v: int, w: int
) -> int:
    """Homogenized rank-five collision quadric; w=1 is the affine equation."""
    return (
        pow(C, m) * x * x
        + d * pow(C, m) * u * u
        - pow(D, m) * pow(B, h) * t * t
        - d * pow(D, m) * pow(B, h) * v * v
        + (pow(C, m) - pow(D, m)) * w * w
    )


def build_record() -> dict[str, object]:
    register_modulus = constants()["M"]
    if A != pow(3, 114) or B != pow(2, 154):
        raise AssertionError("recharge constants changed")
    if A != pow(pow(3, 57), 2) or B != pow(pow(2, 77), 2):
        raise AssertionError("recharge multipliers stopped being squares")
    if REGISTER_ODD_PART != 5 * 19 * 1271069:
        raise AssertionError("public register odd part factorization changed")
    if any(not is_prime(prime) for prime in HARDWARE_D_FACTORS):
        raise AssertionError("hardware discriminant factors changed")
    product = 1
    for prime in HARDWARE_D_FACTORS:
        product *= prime
    if product != HARDWARE_D or HARDWARE_D % 8 != 7:
        raise AssertionError("hardware discriminant reconstruction failed")
    if gcd(HARDWARE_D, F) != 1 or gcd(register_modulus, F) != 1:
        raise AssertionError("CRT register moduli stopped being coprime")

    reproduction_rows: list[dict[str, int | bool]] = []
    for h, t, v in ((1, 1, 2), (2, 17, 23), (23, 123, 456)):
        q = norm(HARDWARE_D, t, v)
        collision_t = pow(2, 77 * h) * t
        collision_v = pow(2, 77 * h) * v
        output_t = pow(3, 57 * h) * t
        output_v = pow(3, 57 * h) * v
        reproduction_rows.append(
            {
                "h": h,
                "t": t,
                "v": v,
                "q": q,
                "B^h_q_is_same_norm": pow(B, h) * q
                == norm(HARDWARE_D, collision_t, collision_v),
                "A^h_q_is_same_norm": pow(A, h) * q
                == norm(HARDWARE_D, output_t, output_v),
            }
        )
    if not all(
        row["B^h_q_is_same_norm"] and row["A^h_q_is_same_norm"]
        for row in reproduction_rows
    ):
        raise AssertionError("quadratic norm type did not reproduce")

    # Universal modular obstruction for d=1.  Accepted inputs have
    # 2^23 | y+1.  Accepted outputs have the same property and A^h=1 mod 8,
    # so their odd collision quotients are also 7 mod 8.
    square_residues_mod_8 = sorted({value * value % 8 for value in range(8)})
    sum_two_square_residues_mod_8 = sorted(
        {(x + u) % 8 for x in square_residues_mod_8 for u in square_residues_mod_8}
    )
    if 7 in sum_two_square_residues_mod_8 or 3 in sum_two_square_residues_mod_8:
        raise AssertionError("sum-of-two-squares residue obstruction failed")
    if A % 8 != 1:
        raise AssertionError("odd recharge square stopped being 1 mod 8")

    input_rows = [typed_input(HARDWARE_D, m) for m in (1, 2, 5)]
    output_rows = [
        typed_output_quotient(HARDWARE_D, h, next_m)
        for h, next_m in ((1, 1), (2, 3), (23, 5))
    ]

    # PARI/GP qfsolve supplied this homogeneous rational point for d_hw,
    # m=h=1.  Exact integer replay below is the certificate.  Its final
    # coordinate is nonzero, so division by w gives a rational point on the
    # affine collision quadric.  It is not an integral transition.
    rational_point = (
        17952930487330537910943645854158815232,
        -9087309927151032065233891666952192,
        3946624527521511,
        215429899185,
        36116729962692172969805786968649367552,
    )
    rational_point_value = quadratic_collision_value(
        HARDWARE_D, 1, 1, *rational_point
    )
    if rational_point[-1] == 0 or rational_point_value != 0:
        raise AssertionError("recorded rational collision point failed")

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact automatic closure of a quadratic norm data type under "
            "recharge scaling; universal mod-8 failure of d=1; exact separate "
            "input/output endpoint inhabitants for a hardware-matched d; and "
            "one exact rational collision-quadric point; no paired integral "
            "transition, infinite orbit, or counterexample"
        ),
        "constants": {
            "A": A,
            "B": B,
            "C": C,
            "D": D,
            "F": F,
            "M": register_modulus,
            "register_odd_part_C_minus_D": REGISTER_ODD_PART,
            "hardware_d": HARDWARE_D,
            "hardware_d_factorization": list(HARDWARE_D_FACTORS),
            "hardware_d_mod_8": HARDWARE_D % 8,
        },
        "type": "N_d(x,u)=x^2+d*u^2",
        "automatic_reproduction": {
            "reason": "A^h=(3^(57h))^2 and B^h=(2^(77h))^2",
            "rows": reproduction_rows,
        },
        "sum_two_squares_failure": {
            "square_residues_mod_8": square_residues_mod_8,
            "sum_two_square_residues_mod_8": sum_two_square_residues_mod_8,
            "accepted_input_residue_mod_8": 7,
            "accepted_collision_quotient_residue_mod_8": 7,
            "universal_obstruction": True,
        },
        "hardware_matched_type": {
            "why_d": (
                "d=7 mod 8 admits the compulsory endpoint residue; d contains "
                "every non-ternary prime in C-D, so those public-register "
                "primes are ramified rather than inert"
            ),
            "independently_legal_inputs": input_rows,
            "independently_legal_output_quotients": output_rows,
        },
        "collision_quadric": {
            "affine_equation": (
                "C^m*(x^2+d*u^2+1)=D^m*(1+B^h*(t^2+d*v^2))"
            ),
            "homogenized_diagonal": (
                "[C^m,d*C^m,-D^m*B^h,-d*D^m*B^h,C^m-D^m]"
            ),
            "rational_point_d_hw_m_1_h_1": list(rational_point),
            "exact_quadric_value": rational_point_value,
            "last_coordinate_nonzero": True,
            "integral_congruence_coupling_open": True,
        },
        "checks": {
            "quadratic_type_reproduces_under_every_audited_recharge": True,
            "sum_two_squares_universally_impossible": True,
            "hardware_type_has_independently_legal_endpoints": True,
            "core_collision_quadric_has_a_rational_point": True,
            "ordinary_transition_not_claimed": True,
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
        raise AssertionError("quadratic-norm artifact does not reconstruct")


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
        print("unit charge quadratic norm selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record()))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge quadratic norm artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
