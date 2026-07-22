#!/usr/bin/env python3
"""Exact partial-theta obstruction for linear unit-radix schedules.

At one fixed hierarchy level write

    p(n)=a*n+b+e,  q(n)=c*n+d,
    2^(p(n+1)) h_(t+1) = 3^(q(n)) h_t + s.

For the unary schedule ``n_t=n0+t``, finite backward unrolling identifies the
unique 2-adic initial core with a Tschakaloff/partial-theta value.  This worker
checks the finite identity against exact linked unit branches at all six
compiled hierarchy levels and audits the elementary hypotheses of the
Vaananen--Wallisser (1989) irrationality theorem.  The external theorem is
cited, not reproved here.  The result closes only linear ``n -> n+1`` unit
schedules, not nonlinear packet feedback or Collatz.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_renormalization import construct_hierarchy
from breakoff_superether import AffineMacro, RegisterISA, link_macros
from breakoff_unit_slice import UnitBranch, unit_branch, unit_isa


SCHEMA = "collatz-unit-linear-theta-v1"


def as_macro(branch: UnitBranch) -> AffineMacro:
    return AffineMacro(
        cells=branch.cells,
        input_packet_base=branch.input_packet_base,
        input_packet_stride_exponent=branch.input_packet_stride_exponent,
        output_packet_base=branch.output_packet_base,
        output_packet_stride=branch.output_packet_stride,
    )


def append_macro(current: AffineMacro, following: AffineMacro) -> AffineMacro:
    source_tail, target_tail = link_macros(current, following)
    return AffineMacro(
        cells=current.cells + following.cells,
        input_packet_base=(
            current.input_packet_base
            + (1 << current.input_packet_stride_exponent) * source_tail
        ),
        input_packet_stride_exponent=(
            current.input_packet_stride_exponent
            + following.input_packet_stride_exponent
        ),
        output_packet_base=(
            following.output_packet_base
            + following.output_packet_stride * target_tail
        ),
        output_packet_stride=(
            current.output_packet_stride * following.output_packet_stride
        ),
    )


def compile_linear_schedule(
    parent: RegisterISA, start_cells: int, transitions: int
) -> tuple[AffineMacro, list[UnitBranch]]:
    if start_cells < 1 or transitions < 1:
        raise ValueError("linear schedule bounds must be positive")
    branches = [
        unit_branch(parent, start_cells + offset)
        for offset in range(transitions + 1)
    ]
    compiled = as_macro(branches[0])
    for branch in branches[1:]:
        compiled = append_macro(compiled, as_macro(branch))
    return compiled, branches


def replay_linear_schedule(
    parent: RegisterISA, start_cells: int, transitions: int
) -> tuple[list[int], list[int]]:
    compiled, branches = compile_linear_schedule(
        parent, start_cells, transitions
    )
    unit = unit_isa(parent)
    packet = compiled.input_packet_base
    odd_cores: list[int] = []
    packet_states = [packet]
    for index, branch in enumerate(branches):
        difference = packet - branch.input_packet_base
        stride = 1 << branch.input_packet_stride_exponent
        if difference < 0 or difference % stride:
            raise AssertionError("compiled linear schedule missed a branch")
        tail = difference // stride
        source, target = branch.member(tail)
        if source != packet:
            raise AssertionError("linear schedule source packet changed")
        source_register = unit.register_offset + unit.register_stride * source
        public_exponent = unit.binary_cell * branch.cells + unit.binary_offset
        if v2(source_register) != public_exponent:
            raise AssertionError("linear schedule public valuation failed")
        core = source_register >> public_exponent
        if math.gcd(core, 6) != 1:
            raise AssertionError("linear schedule core is not coprime to six")
        odd_cores.append(core)
        if index < transitions:
            target_register = unit.register_offset + unit.register_stride * target
            q = unit.ternary_cell * branch.cells + unit.ternary_offset
            if (
                pow(3, q) * core + unit.collision_sign
                != (1 << unit.division_exponent) * target_register
            ):
                raise AssertionError("linear schedule unit recurrence failed")
            packet = target
            packet_states.append(packet)
    return odd_cores, packet_states


def theta_exponents(
    parent: RegisterISA, start_cells: int, term_index: int
) -> tuple[int, int]:
    if start_cells < 1 or term_index < 0:
        raise ValueError("theta indices must be nonnegative")
    unit = unit_isa(parent)
    j = term_index
    p0 = unit.binary_offset + unit.division_exponent
    q0 = unit.ternary_cell * start_cells + unit.ternary_offset
    two_exponent = (
        j * (unit.binary_cell * (start_cells + 1) + p0)
        + unit.binary_cell * j * (j - 1) // 2
    )
    three_exponent = (
        (j + 1) * q0 + unit.ternary_cell * j * (j + 1) // 2
    )
    return two_exponent, three_exponent


def terminal_exponents(
    parent: RegisterISA, start_cells: int, transitions: int
) -> tuple[int, int]:
    if transitions < 1:
        raise ValueError("at least one transition is required")
    unit = unit_isa(parent)
    p0 = unit.binary_offset + unit.division_exponent
    two_exponent = sum(
        unit.binary_cell * (start_cells + index) + p0
        for index in range(1, transitions + 1)
    )
    three_exponent = sum(
        unit.ternary_cell * (start_cells + index) + unit.ternary_offset
        for index in range(transitions)
    )
    return two_exponent, three_exponent


def verify_finite_identity(
    parent: RegisterISA, start_cells: int, transitions: int
) -> dict[str, object]:
    unit = unit_isa(parent)
    cores, packets = replay_linear_schedule(parent, start_cells, transitions)
    partial = Fraction(0)
    terms = []
    for index in range(transitions):
        two_exponent, three_exponent = theta_exponents(
            parent, start_cells, index
        )
        term = Fraction(1 << two_exponent, pow(3, three_exponent))
        partial -= unit.collision_sign * term
        terms.append((two_exponent, three_exponent))
    terminal_two, terminal_three = terminal_exponents(
        parent, start_cells, transitions
    )
    terminal = Fraction(
        (1 << terminal_two) * cores[-1], pow(3, terminal_three)
    )
    if Fraction(cores[0]) != partial + terminal:
        raise AssertionError("finite unit partial-theta identity failed")

    modulus = 1 << terminal_two
    partial_residue = (
        partial.numerator * pow(partial.denominator, -1, modulus)
    ) % modulus
    if cores[0] % modulus != partial_residue:
        raise AssertionError("unit partial-theta 2-adic residue failed")
    return {
        "level": parent.level,
        "collision_sign": unit.collision_sign,
        "start_cells": start_cells,
        "transitions": transitions,
        "linked_branches": transitions + 1,
        "compiled_input_packet_bits": packets[0].bit_length(),
        "compiled_terminal_packet_bits": packets[-1].bit_length(),
        "terminal_two_adic_precision_bits": terminal_two,
        "terminal_triadic_denominator_exponent": terminal_three,
        "first_term_exponents": list(terms[0]),
        "last_term_exponents": list(terms[-1]),
        "finite_rational_identity_checked": True,
        "two_adic_residue_checked": True,
    }


def theorem_parameters(parent: RegisterISA) -> dict[str, object]:
    unit = unit_isa(parent)
    a = unit.binary_cell
    c = unit.ternary_cell
    if not pow(3, c) > (1 << a) > 1:
        raise AssertionError("partial-theta base is not in the theorem range")
    if 3 * a < 4 * c:
        raise AssertionError("a/c lost the uniform 4/3 lower bound")
    if not (1 << 8) > pow(3, 5):
        raise AssertionError("log(2)/log(3) separator failed")
    if not 45 < 64:
        raise AssertionError("1/6 versus golden-ratio separator failed")
    p_offset = unit.binary_offset + unit.division_exponent
    coefficient_checks = 0
    for start_cells in range(1, 5):
        for index in range(64):
            # F(2^a/3^c,z) and f_(3^c/2^a)(alpha) have the same
            # numerator/denominator exponents when alpha=(3^c/2^a)z.
            f_two = (
                a * index * (index + 1) // 2
                + (a * start_cells + p_offset) * index
            )
            F_two = (
                a * index * (index - 1) // 2
                + (a * (start_cells + 1) + p_offset) * index
            )
            f_three = (
                c * index * (index + 1) // 2
                + (c * start_cells + unit.ternary_offset) * index
            )
            F_three = (
                c * index * (index - 1) // 2
                + (c * (start_cells + 1) + unit.ternary_offset) * index
            )
            if (f_two, f_three) != (F_two, F_three):
                raise AssertionError("partial-theta function conversion failed")
            coefficient_checks += 1
    return {
        "level": parent.level,
        "q": f"3^{c}/2^{a}",
        "q_numerator": str(pow(3, c)),
        "q_denominator": str(1 << a),
        "prime": 2,
        "alpha_for_start_n0": (
            f"2^({a}*n0+{p_offset})/"
            f"3^({c}*n0+{unit.ternary_offset})"
        ),
        "candidate_for_start_n0": (
            f"-{unit.collision_sign}/"
            f"3^({c}*n0+{unit.ternary_offset}) * f_q(alpha)"
        ),
        "exact_size_chain": (
            "2^8>3^5 gives log(2)/log(3)>5/8; "
            "3a>=4c gives a*log(2)/(c*log(3))>5/6; "
            "45<64 gives 1/6<(3-sqrt(5))/2"
        ),
        "external_conclusion": (
            "Vaananen--Wallisser (1989) makes 1 and f_q(alpha) "
            "Q-linearly independent in Q_2"
        ),
        "elementary_hypotheses": {
            "q_reduced": True,
            "q_numerator_absolute_greater_than_one": True,
            "alpha_nonzero_rational_for_every_n0_at_least_1": True,
            "distinct_alpha_ratio_conditions": "vacuous_for_ell_1",
            "two_adic_convergence": f"abs_2(q)=2^{a}>1",
            "function_conversion_coefficients_checked": coefficient_checks,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate(
    start_cells: int = 1, transitions: int = 8
) -> dict[str, object]:
    hierarchy, _ = construct_hierarchy(6)
    finite = [
        verify_finite_identity(parent, start_cells, transitions)
        for parent in hierarchy
    ]
    parameters = [theorem_parameters(parent) for parent in hierarchy]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact finite partial-theta identities for one n->n+1 schedule "
            "at each of six compiled unit levels, plus an exact application-"
            "hypothesis audit of Vaananen--Wallisser (1989); the external "
            "irrationality theorem is cited, not reproved"
        ),
        "external_source": {
            "authors": "K. Vaananen and R. Wallisser",
            "title": (
                "Zu einem Satz von Skolem ueber lineare Unabhaengigkeit "
                "von Werten gewisser Thetareihen"
            ),
            "journal": "Manuscripta Mathematica 65 (1989), 199-212",
            "digitized_full_text": (
                "https://gdz.sub.uni-goettingen.de/download/pdf/"
                "PPN365956996_0065/LOG_0016.pdf"
            ),
            "theorem_parameters": {"ell": 1, "sigma": 0, "p": 2},
        },
        "linear_schedule": "n_t=n0+t for arbitrary n0>=1",
        "candidate_formula": (
            "h0=-s/3^(q(n0)) * F(2^a/3^c, "
            "2^(p(n0+1))/3^(q(n0+1)))"
        ),
        "function_conversion": (
            "F(2^a/3^c,z)=f_(3^c/2^a)((3^c/2^a)z)"
        ),
        "ordinary_program_conclusion": (
            "the cited theorem makes every linear-schedule candidate "
            "irrational in Q_2, hence no candidate is an ordinary integer"
        ),
        "bounds": {
            "compiled_levels": 6,
            "finite_regression_start_cells": start_cells,
            "finite_regression_transitions": transitions,
        },
        "finite_checks": finite,
        "theorem_application": parameters,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit-theta artifact schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["finite_regression_start_cells"]),
        int(bounds["finite_regression_transitions"]),
    )
    if data != expected:
        raise ValueError("unit linear-theta artifact failed reconstruction")


def selftest() -> None:
    hierarchy, _ = construct_hierarchy(6)
    for parent in hierarchy:
        theorem_parameters(parent)
        for start in range(1, 4):
            verify_finite_identity(parent, start, 3)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--start-cells", type=int, default=1)
    build.add_argument("--transitions", type=int, default=8)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit linear-theta selftest: PASS")
    elif args.command == "build":
        data = build_certificate(args.start_cells, args.transitions)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit linear-theta artifact: PASS")


if __name__ == "__main__":
    main()
