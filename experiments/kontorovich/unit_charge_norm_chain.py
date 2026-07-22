#!/usr/bin/env python3
"""Exact two-step quadratic-form type family for the charge bouncer.

The discriminant -124 has reduced forms

    Q0(x,u)=x^2+31*u^2,
    Q1(x,u)=5*x^2+4*x*u+7*u^2,
    Q2(x,u)=5*x^2-4*x*u+7*u^2.

Q1 and Q2 represent the same unoriented integer set (replace x by -x), so
the public arithmetic type has two observable classes: principal Q0 and
nonprincipal Q1.  Every form is homogeneous of degree two and is therefore
preserved by bouncer recharge.  Moreover the forced register factor

    R=C-D=7706^2+31*1407^2

is principal.  Multiplication by 7706+1407*sqrt(-31) gives an explicit integer
linear map preserving each form class while multiplying its value by R.

This worker compiles two consecutive accepted bouncer blocks into three
normalized affine residuals.  If all three residuals are represented by Q0 or
Q1, they certify a literal two-step typed chain; the first output inherits the
class of the first quotient and the second output inherits the second.

The ``emit-gp`` command emits a targeted sufficient search in which the three
residuals are prime.  GP proves primality and asks the two reduced forms for
coordinates.  A search hit still has to pass this worker's exact macro replay.
"""

from __future__ import annotations

import argparse
import hashlib
from math import gcd
from pathlib import Path

from breakoff_superether import link_macros
from unit_charge_bouncer import (
    A,
    C,
    D,
    bouncer_step,
    compose,
    packet_to_y,
)
from unit_charge_morphic import opcode_blocks
from unit_charge_quadratic_norm import (
    crt_many,
    norm_representation_mod_F,
    odd_square_roots_mod_power_of_two,
)


SCHEMA = "collatz-unit-charge-norm-chain-v1"
DISCRIMINANT_D = 31
REGISTER_ODD_PART = C - D
REGISTER_ELEMENT = (7706, 1407)
FORMS = {
    0: (1, 0, 31),
    1: (5, 4, 7),
}


def form_value(form_class: int, x: int, u: int) -> int:
    a, b, c = FORMS[form_class]
    return a * x * x + b * x * u + c * u * u


def register_action(form_class: int, x: int, u: int) -> tuple[int, int]:
    """Multiply a form coordinate by 7706+1407*sqrt(-31)."""
    a, b, c = FORMS[form_class]
    p, q = REGISTER_ELEMENT
    if b % 2:
        raise AssertionError("discriminant -124 form should have even b")
    result = (
        (p - q * (b // 2)) * x - q * c * u,
        q * a * x + (p + q * (b // 2)) * u,
    )
    if form_value(form_class, *result) != REGISTER_ODD_PART * form_value(
        form_class, x, u
    ):
        raise AssertionError("principal register action failed")
    return result


def apply_macro(macro, packet: int) -> int:
    difference = packet - macro.input_packet_base
    stride = 1 << macro.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("packet missed compiled block source")
    tail = difference // stride
    return macro.output_packet_base + macro.output_packet_stride * tail


def two_block_family(
    first: tuple[int, int], second: tuple[int, int], final_m: int
) -> dict[str, object]:
    """Compile two accepted blocks and expose three residual linear forms."""
    if min(*first, *second, final_m) < 1:
        raise ValueError("opcodes must be positive")
    bound = max(*first, *second, final_m)
    blocks, branches = opcode_blocks(bound)
    block0 = blocks[first]
    block1 = blocks[second]
    executed = compose(block0, block1)
    following = branches[final_m + 1]
    source_tail, _ = link_macros(executed, following)
    packet_base = executed.input_packet_base + (
        1 << executed.input_packet_stride_exponent
    ) * source_tail
    packet_stride = 1 << (
        executed.input_packet_stride_exponent
        + following.input_packet_stride_exponent
    )

    state_rows: list[tuple[int, int, int]] = []
    for tail in (0, 1):
        packet0 = packet_base + packet_stride * tail
        packet1 = apply_macro(block0, packet0)
        packet2 = apply_macro(block1, packet1)
        y0, y1, y2 = (packet_to_y(packet) for packet in (packet0, packet1, packet2))
        if y1 % pow(A, first[1]) or y2 % pow(A, second[1]):
            raise AssertionError("compiled chain lost a recharge factor")
        state_rows.append((y0, y1 // pow(A, first[1]), y2 // pow(A, second[1])))

    input_factor = pow(3, 33) * REGISTER_ODD_PART
    bases = state_rows[0]
    steps = tuple(state_rows[1][index] - bases[index] for index in range(3))
    if bases[0] % input_factor or steps[0] % input_factor:
        raise AssertionError("chain input lost the public register")
    if any(value % REGISTER_ODD_PART for value in bases[1:] + steps[1:]):
        raise AssertionError("chain quotient lost the public register")
    raw_input_base = bases[0] // input_factor
    raw_input_step = steps[0] // input_factor
    if raw_input_step % 3 == 0:
        raise AssertionError("chain tail stopped selecting the extra ternary digit")
    tail_residue = (-raw_input_base * pow(raw_input_step, -1, 3)) % 3
    forms = [
        ((raw_input_base + raw_input_step * tail_residue) // 3, raw_input_step)
    ]
    for base, step in zip(bases[1:], steps[1:]):
        base //= REGISTER_ODD_PART
        step //= REGISTER_ODD_PART
        forms.append((base + step * tail_residue, 3 * step))

    replay_rows: list[dict[str, int | bool]] = []
    for k in (0, 1, 7):
        tail = tail_residue + 3 * k
        packet0 = packet_base + packet_stride * tail
        packet1 = apply_macro(block0, packet0)
        packet2 = apply_macro(block1, packet1)
        y0, y1, y2 = (packet_to_y(packet) for packet in (packet0, packet1, packet2))
        q0 = y1 // pow(A, first[1])
        q1 = y2 // pow(A, second[1])
        residuals = [base + step * k for base, step in forms]
        if y0 != pow(3, 34) * REGISTER_ODD_PART * residuals[0]:
            raise AssertionError("chain input normalization failed")
        if q0 != REGISTER_ODD_PART * residuals[1]:
            raise AssertionError("first quotient normalization failed")
        if q1 != REGISTER_ODD_PART * residuals[2]:
            raise AssertionError("second quotient normalization failed")
        step0 = bouncer_step(y0)
        step1 = bouncer_step(y1)
        if step0.output_y != y1 or step1.output_y != y2:
            raise AssertionError("two-block family missed literal bouncer replay")
        replay_rows.append(
            {
                "k": k,
                "tail": tail,
                "first_step_replayed": True,
                "second_step_replayed": True,
            }
        )

    return {
        "first_opcode": list(first),
        "second_opcode": list(second),
        "final_m": final_m,
        "tail_residue_mod_3": tail_residue,
        "linear_forms": [
            {
                "role": role,
                "base": base,
                "step": step,
                "primitive": gcd(base, step) == 1,
            }
            for role, (base, step) in zip(
                ("input_residual", "first_quotient_residual", "second_quotient_residual"),
                forms,
            )
        ],
        "replay_rows": replay_rows,
    }


def emit_gp(start: int, stop: int) -> str:
    if start < 0 or stop < start:
        raise ValueError("invalid search interval")
    family = two_block_family((1, 1), (1, 1), 1)
    lines = [
        "f0=Qfb(1,0,31);",
        "f1=Qfb(5,4,7);",
        (
            "rep(n)={my(r=qfbsolve(f0,n,2));"
            "if(#r,return([0,r[1],r[2]]));"
            "r=qfbsolve(f1,n,2);if(#r,return([1,r[1],r[2]]));return([])};"
        ),
    ]
    for index, row in enumerate(family["linear_forms"]):
        lines.append(f"b{index}={row['base']};s{index}={row['step']};")
    lines.append("hits=0;")
    lines.append(
        f"for(k={start},{stop},n0=b0+s0*k;"
        "if(ispseudoprime(n0),n1=b1+s1*k;"
        "if(ispseudoprime(n1),n2=b2+s2*k;"
        "if(ispseudoprime(n2)&&isprime(n0)&&isprime(n1)&&isprime(n2),"
        "r0=rep(n0);r1=rep(n1);r2=rep(n2);"
        "if(#r0&&#r1&&#r2,hits++;"
        'print("HIT ",k," ",r0[1]," ",r0[2]," ",r0[3]," ",'
        'r1[1]," ",r1[2]," ",r1[3]," ",r2[1]," ",r2[2]," ",r2[3]))))));'
    )
    lines.append(f'print("DONE {start} {stop} hits=",hits);')
    return "\n".join(lines) + "\n"


def sqrt_mod_odd_prime_power(value: int, prime: int, exponent: int) -> int | None:
    """Lift one nonzero modular square root digit by digit."""
    modulus = pow(prime, exponent)
    value %= modulus
    roots = [root for root in range(prime) if root * root % prime == value % prime]
    if not roots:
        return None
    root = roots[0]
    power = prime
    for _ in range(1, exponent):
        for digit in range(prime):
            candidate = root + digit * power
            if (candidate * candidate - value) % (power * prime) == 0:
                root = candidate
                break
        else:
            raise AssertionError("odd-prime square root failed to lift")
        power *= prime
    if root * root % modulus != value:
        raise AssertionError("odd-prime-power square root check failed")
    return root


def middle_principal_parameterization() -> dict[str, int | bool]:
    """Force the middle residual to be Q0 along a quadratic k(z)."""
    family = two_block_family((1, 1), (1, 1), 1)
    middle = family["linear_forms"][1]
    base = int(middle["base"])
    step = int(middle["step"])
    remaining = step
    exponent_two = 0
    exponent_three = 0
    while remaining % 2 == 0:
        exponent_two += 1
        remaining //= 2
    while remaining % 3 == 0:
        exponent_three += 1
        remaining //= 3
    from unit_charge_bouncer import F

    if remaining != F:
        raise AssertionError("middle slope factorization changed")

    modulus_two = 1 << exponent_two
    u_two = 2
    square_target_two = (base - DISCRIMINANT_D * u_two * u_two) % modulus_two
    x_two = odd_square_roots_mod_power_of_two(
        square_target_two, exponent_two
    )[0]
    modulus_three = pow(3, exponent_three)
    u_three = 1
    x_three = sqrt_mod_odd_prime_power(
        base - DISCRIMINANT_D * u_three * u_three, 3, exponent_three
    )
    if x_three is None:
        raise AssertionError("middle residual lost its 3-adic norm root")
    x_f, u_f = norm_representation_mod_F(DISCRIMINANT_D, base)
    x = crt_many(
        [(x_two, modulus_two), (x_three, modulus_three), (x_f, F)]
    )
    u = crt_many(
        [(u_two, modulus_two), (u_three, modulus_three), (u_f, F)]
    )
    value = form_value(0, x, u)
    if (value - base) % step:
        raise AssertionError("middle residual norm missed its affine line")
    k0 = (value - base) // step
    if k0 < 0:
        raise AssertionError("middle residual parameterization is not positive")
    # Replacing x by x+step*z gives
    # k(z)=k0+2*x*z+step*z^2 and keeps L1(k(z))=Q0(x+step*z,u).
    for z in (0, 1, 7):
        k = k0 + 2 * x * z + step * z * z
        if base + step * k != form_value(0, x + step * z, u):
            raise AssertionError("quadratic middle parameterization failed")
    return {
        "middle_base": base,
        "middle_step": step,
        "middle_step_v2": exponent_two,
        "middle_step_v3": exponent_three,
        "middle_step_remaining_factor_is_F": True,
        "x0": x,
        "u0": u,
        "k0": k0,
        "k_formula": "k(z)=k0+2*x0*z+middle_step*z^2",
        "coordinate_formula": "(x(z),u(z))=(x0+middle_step*z,u0)",
    }


def emit_quadratic_gp(start: int, stop: int) -> str:
    """Emit a search with the middle residual identically principal."""
    if start < 0 or stop < start:
        raise ValueError("invalid search interval")
    family = two_block_family((1, 1), (1, 1), 1)
    parameter = middle_principal_parameterization()
    first = family["linear_forms"][0]
    third = family["linear_forms"][2]
    lines = [
        "f0=Qfb(1,0,31);",
        "f1=Qfb(5,4,7);",
        (
            "rep(n)={my(r=qfbsolve(f0,n,2));"
            "if(#r,return([0,r[1],r[2]]));"
            "r=qfbsolve(f1,n,2);if(#r,return([1,r[1],r[2]]));return([])};"
        ),
        f"x0={parameter['x0']};",
        f"u0={parameter['u0']};",
        f"k0={parameter['k0']};",
        f"sm={parameter['middle_step']};",
        f"b0={first['base']};s0={first['step']};",
        f"b2={third['base']};s2={third['step']};",
        "hits=0;",
        (
            f"for(z={start},{stop},k=k0+2*x0*z+sm*z^2;"
            "n0=b0+s0*k;if(ispseudoprime(n0),n2=b2+s2*k;"
            "if(ispseudoprime(n2)&&isprime(n0)&&isprime(n2),"
            "r0=rep(n0);r2=rep(n2);if(#r0&&#r2,hits++;"
            'print("HIT ",z," ",r0[1]," ",r0[2]," ",r0[3]," ",'
            'r2[1]," ",r2[2]," ",r2[3])))));'
        ),
        f'print("DONEQ {start} {stop} hits=",hits);',
    ]
    return "\n".join(lines) + "\n"


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_bouncer.py"),
        Path(__file__).with_name("unit_charge_morphic.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    emit = subparsers.add_parser("emit-gp")
    emit.add_argument("--start", type=int, required=True)
    emit.add_argument("--stop", type=int, required=True)
    emit_quadratic = subparsers.add_parser("emit-quadratic-gp")
    emit_quadratic.add_argument("--start", type=int, required=True)
    emit_quadratic.add_argument("--stop", type=int, required=True)
    args = parser.parse_args()
    if args.command == "selftest":
        family = two_block_family((1, 1), (1, 1), 1)
        if not all(row["primitive"] for row in family["linear_forms"]):
            raise AssertionError("chain residual forms acquired a fixed divisor")
        for form_class in FORMS:
            register_action(form_class, 17, 23)
        middle_principal_parameterization()
        print("unit charge norm chain selftest: PASS")
    elif args.command == "emit-gp":
        print(emit_gp(args.start, args.stop), end="")
    elif args.command == "emit-quadratic-gp":
        print(emit_quadratic_gp(args.start, args.stop), end="")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
