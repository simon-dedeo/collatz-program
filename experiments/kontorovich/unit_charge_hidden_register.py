#!/usr/bin/env python3
"""Exact hidden-``F`` register behind public-state 23rd-power closure.

For the charge bouncer write

    A=3^114, B=2^154, C=3^17, D=2^23, F=(A-B)/5.

In a public-state power transition put ``y=s^23``, ``h=23*ell``, and
``q=t^23``.  With ``z=B^ell*t`` and exact valuation quotients

    s+1 = D^m F w,          z+1 = C^m F v,

the transition equation is equivalent to

    w Q(s) = v Q(z),        Q(x)=(x^23+1)/(x+1).

Since ``Q(-1+u)=23-253u+1771u^2-...`` and ``gcd(23,F)=1``, every input
``w`` has a unique collision lift ``v`` modulo every power of ``F``.  The
first two digits are

    v = w + 11 F (C^m-D^m) (w mod F)^2             (mod F^2).

If the next defect opcode is ``m'``, the next hidden quotient ``w'`` obeys

    D^m' w' = C^m v + 5 S_ell t,
    S_ell=(A^ell-B^ell)/(A-B).

At first precision this is the affine instruction

    w' = D^(-m') (C^m w - 5 ell B^(-1))            (mod F).

Thus recharge length is a fully writable, nonlocal opcode modulo ``F``.  This
worker implements exact digit lifting, verifies the first two closed formulas,
and constructs every requested first-digit write in a fixed audit set.  It
also constructs visible-register inputs with arbitrary nonzero hidden residue,
showing that the visible register alone does not force a second factor of F.

This is a necessary-state transducer over the F-adics, not an ordinary Collatz
orbit.  It does not prove that a chosen recharge opcode has the required 2-adic
collision valuation, that the F-adic lift is a positive integer, or that an
infinite program exists.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import comb, gcd
from pathlib import Path

from breakoff_delay_gate import v2
from unit_charge_bouncer import A, B, C, D, F, constants


SCHEMA = "collatz-unit-charge-hidden-register-v1"


def plus_cofactor(x: int) -> int:
    """Return the exact alternating cofactor Q(x)."""
    if x == -1:
        return 23
    numerator = pow(x, 23) + 1
    if numerator % (x + 1):
        raise AssertionError("23rd-power cofactor stopped being integral")
    return numerator // (x + 1)


def taylor_coefficients() -> list[int]:
    """Coefficients of Q(-1+u), from u^0 through u^22."""
    return [(-1 if j % 2 else 1) * comb(23, j + 1) for j in range(23)]


def q_at_minus_one(u: int) -> int:
    return sum(c * pow(u, j) for j, c in enumerate(taylor_coefficients()))


def collision_balance(w: int, v: int, m: int) -> int:
    if min(w, v, m) < 1:
        raise ValueError("hidden-register parameters must be positive")
    s = -1 + F * pow(D, m) * w
    z = -1 + F * pow(C, m) * v
    return w * plus_cofactor(s) - v * plus_cofactor(z)


def collision_lift(w: int, m: int, precision: int) -> int:
    """Unique v modulo F^precision satisfying the cofactor balance."""
    if min(w, m, precision) < 1:
        raise ValueError("lift parameters must be positive")
    v = w % F
    inverse_23 = pow(23, -1, F)
    for level in range(1, precision):
        modulus = pow(F, level)
        balance = collision_balance(w, v, m)
        if balance % modulus:
            raise AssertionError("collision lift lost its previous digit")
        digit = ((balance // modulus) * inverse_23) % F
        v += digit * modulus
        if collision_balance(w, v, m) % pow(F, level + 1):
            raise AssertionError("collision digit failed to Hensel-lift")
    return v % pow(F, precision)


def geometric_quotient_mod(ell: int, modulus: int) -> int:
    """Compute S_ell=(A^ell-B^ell)/(A-B) modulo modulus quickly."""
    if ell < 1 or modulus < 1:
        raise ValueError("geometric quotient parameters must be positive")
    extended = (A - B) * modulus
    numerator = (pow(A, ell, extended) - pow(B, ell, extended)) % extended
    if numerator % (A - B):
        raise AssertionError("modular geometric quotient was not integral")
    return (numerator // (A - B)) % modulus


def hidden_step(
    w: int, m: int, ell: int, next_m: int, precision: int
) -> int:
    """Apply the necessary F-adic hidden-register instruction."""
    if min(w, m, ell, next_m, precision) < 1:
        raise ValueError("hidden-step parameters must be positive")
    modulus = pow(F, precision)
    v = collision_lift(w, m, precision)
    z = (-1 + F * pow(C, m) * v) % modulus
    t = z * pow(pow(B, ell, modulus), -1, modulus) % modulus
    sell = geometric_quotient_mod(ell, modulus)
    rhs = pow(C, m) * v + 5 * sell * t
    return rhs * pow(pow(D, next_m), -1, modulus) % modulus


def first_digit_formula(w: int, m: int, ell: int, next_m: int) -> int:
    inverse_b = pow(B, -1, F)
    return (
        pow(pow(D, next_m), -1, F)
        * (pow(C, m) * w - 5 * ell * inverse_b)
    ) % F


def opcode_for_target(r: int, target: int, m: int, next_m: int) -> int:
    """Least positive ell modulo F which writes target from r."""
    if min(m, next_m) < 1:
        raise ValueError("opcodes must be positive")
    residue = (
        B
        * pow(5, -1, F)
        * (pow(C, m) * r - pow(D, next_m) * target)
    ) % F
    return F if residue == 0 else residue


def second_precision_formula(
    w: int, m: int, ell: int, next_m: int
) -> int:
    modulus = F * F
    r = w % F
    inverse_b = pow(B, -1, modulus)
    correction = (
        11 * pow(C, m) * (pow(C, m) - pow(D, m)) * r * r
        + 5 * ell * inverse_b * pow(C, m) * r
        - 25 * comb(ell, 2) * inverse_b * inverse_b
    )
    numerator = pow(C, m) * w - 5 * ell * inverse_b + F * correction
    return numerator * pow(pow(D, next_m), -1, modulus) % modulus


def crt_pair(a: int, modulus_a: int, b: int, modulus_b: int) -> int:
    if gcd(modulus_a, modulus_b) != 1:
        raise ValueError("CRT moduli must be coprime")
    return (
        a
        + modulus_a
        * (((b - a) * pow(modulus_a, -1, modulus_b)) % modulus_b)
    ) % (modulus_a * modulus_b)


def visible_input_with_hidden_residue(m: int, residue: int) -> tuple[int, int]:
    """Construct s and w showing that F^2 is not visibly forced."""
    if m < 1 or not 0 < residue < F:
        raise ValueError("use a positive nonzero hidden residue")
    register_modulus = constants()["M"]
    target_mod_m = pow(pow(D, m) * F, -1, register_modulus)
    w = crt_pair(residue, F, target_mod_m, register_modulus)
    if w == 0:
        w += F * register_modulus
    if w % 2 == 0:
        w += F * register_modulus
    s = -1 + pow(D, m) * F * w
    if s % register_modulus or (s + 1) % F:
        raise AssertionError("constructed root missed the visible register")
    if (s + 1) % (F * F) == 0:
        raise AssertionError("visible register unexpectedly forced F^2")
    if v2(s + 1) != 23 * m:
        raise AssertionError("constructed root missed the exact input opcode")
    return s, w


def build_record() -> dict[str, object]:
    register_modulus = constants()["M"]
    if A - B != 5 * F:
        raise AssertionError("fixed divisor identity changed")
    unit_gcds = {
        "gcd_5_F": gcd(5, F),
        "gcd_23_F": gcd(23, F),
        "gcd_A_F": gcd(A, F),
        "gcd_B_F": gcd(B, F),
        "gcd_C_F": gcd(C, F),
        "gcd_D_F": gcd(D, F),
        "gcd_M_F": gcd(register_modulus, F),
    }
    if any(value != 1 for value in unit_gcds.values()):
        raise AssertionError("hidden-register coefficient lost invertibility")

    coefficients = taylor_coefficients()
    if coefficients[:3] != [23, -253, 1771]:
        raise AssertionError("cofactor Taylor expansion changed")
    for u in (1, 2, 5, F, F * 17):
        if q_at_minus_one(u) != plus_cofactor(-1 + u):
            raise AssertionError("cofactor Taylor identity failed")

    lift_rows: list[dict[str, int | bool]] = []
    for m in (1, 2, 9, 23):
        for w in (1, F + 3, 2 * F + 11):
            lifted = collision_lift(w, m, 3)
            predicted_two = (
                w
                + 11
                * F
                * (pow(C, m) - pow(D, m))
                * pow(w % F, 2)
            ) % (F * F)
            lift_rows.append(
                {
                    "m": m,
                    "w": w,
                    "v_mod_F3": lifted,
                    "balance_divisible_by_F3": collision_balance(
                        w, lifted, m
                    )
                    % pow(F, 3)
                    == 0,
                    "first_nonlinear_carry_matches": lifted % (F * F)
                    == predicted_two,
                }
            )
    if not all(
        row["balance_divisible_by_F3"]
        and row["first_nonlinear_carry_matches"]
        for row in lift_rows
    ):
        raise AssertionError("hidden collision lift audit failed")

    write_rows: list[dict[str, int | bool]] = []
    for r, target, m, next_m in (
        (1, 0, 1, 1),
        (1, 1, 1, 1),
        (17, 23, 2, 3),
        (F - 1, 42, 9, 5),
        (123456789, F - 7, 23, 11),
    ):
        ell = opcode_for_target(r, target, m, next_m)
        result = hidden_step(r, m, ell, next_m, 1)
        write_rows.append(
            {
                "input_residue": r,
                "target_residue": target,
                "m": m,
                "next_m": next_m,
                "least_positive_ell_mod_F": ell,
                "ell_decimal_digits": len(str(ell)),
                "first_digit_formula_matches": first_digit_formula(
                    r, m, ell, next_m
                )
                == target % F,
                "exact_F_adic_step_writes_target": result == target % F,
            }
        )
    if not all(
        row["first_digit_formula_matches"]
        and row["exact_F_adic_step_writes_target"]
        for row in write_rows
    ):
        raise AssertionError("fully writable opcode audit failed")

    second_rows: list[dict[str, int | bool]] = []
    for w, m, ell, next_m in (
        (1, 1, 1, 1),
        (F + 7, 2, 3, 5),
        (2 * F + 11, 9, 23, 9),
        (3 * F + 101, 23, 146, 17),
    ):
        exact = hidden_step(w, m, ell, next_m, 2)
        closed = second_precision_formula(w, m, ell, next_m)
        second_rows.append(
            {
                "w": w,
                "m": m,
                "ell": ell,
                "next_m": next_m,
                "output_mod_F2": exact,
                "quadratic_second_digit_formula_matches": exact == closed,
            }
        )
    if not all(
        row["quadratic_second_digit_formula_matches"] for row in second_rows
    ):
        raise AssertionError("second hidden digit formula failed")

    freedom_rows: list[dict[str, int | bool]] = []
    for m, residue in ((1, 1), (2, 17), (9, F - 1), (23, 123456789)):
        s, w = visible_input_with_hidden_residue(m, residue)
        freedom_rows.append(
            {
                "m": m,
                "requested_w_mod_F": residue,
                "constructed_w_mod_F": w % F,
                "s_decimal_digits": len(str(s)),
                "s_mod_M": s % register_modulus,
                "s_plus_one_mod_F": (s + 1) % F,
                "s_plus_one_not_divisible_by_F2": (s + 1) % (F * F) != 0,
                "exact_v2_s_plus_one": v2(s + 1),
            }
        )
    if not all(
        row["requested_w_mod_F"] == row["constructed_w_mod_F"]
        and row["s_mod_M"] == 0
        and row["s_plus_one_mod_F"] == 0
        and row["s_plus_one_not_divisible_by_F2"]
        and row["exact_v2_s_plus_one"] == 23 * row["m"]
        for row in freedom_rows
    ):
        raise AssertionError("visible hidden-residue freedom audit failed")

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact F-adic necessary-state transducer, arbitrary first-digit "
            "opcode writes, quadratic second digit, and visible-register "
            "non-forcing of F^2; no ordinary transition or infinite orbit"
        ),
        "constants": {
            "A": A,
            "B": B,
            "C": C,
            "D": D,
            "F": F,
            "M": register_modulus,
            "F_bits": F.bit_length(),
            "F_decimal_digits": len(str(F)),
        },
        "unit_gcds": unit_gcds,
        "plus_cofactor_taylor_coefficients": coefficients,
        "collision_lift": {
            "balance": "w*Q(-1+F*D^m*w)=v*Q(-1+F*C^m*v)",
            "unique_digit_reason": "derivative in v is -23 mod F",
            "first_nonlinear_carry": (
                "v=w+11*F*(C^m-D^m)*(w mod F)^2 mod F^2"
            ),
            "rows": lift_rows,
        },
        "first_digit_instruction": {
            "formula": (
                "w'=D^(-m')*(C^m*w-5*ell*B^(-1)) mod F"
            ),
            "opcode_synthesis": (
                "ell=B*5^(-1)*(C^m*r-D^m'*target) mod F"
            ),
            "rows": write_rows,
            "all_residues_writable_because": "5, B, and D are units mod F",
        },
        "second_digit_instruction": {
            "description": (
                "explicit quadratic formula in w mod F, ell, m, and m'"
            ),
            "rows": second_rows,
        },
        "visible_register_F2_nonforcing": {
            "construction": (
                "CRT chooses odd w with prescribed nonzero w mod F and "
                "D^m*F*w=1 mod M; s=-1+D^m*F*w"
            ),
            "rows": freedom_rows,
        },
        "checks": {
            "cofactor_taylor_identity_exact": True,
            "unique_collision_digits_checked_through_F3": True,
            "first_hidden_digit_fully_writable": True,
            "quadratic_second_digit_formula_exact_mod_F2": True,
            "visible_register_does_not_force_second_F": True,
            "ordinary_integer_transition_not_claimed": True,
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
        raise AssertionError("hidden-register artifact does not reconstruct")


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
        print("unit charge hidden register selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record()))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge hidden register artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
