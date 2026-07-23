#!/usr/bin/env python3
"""Partial-theta obstruction for arithmetic-growth ether schedules.

For an accepted autonomous ether step, write the invariant public register as

    Y_t = 2^(8*n_t-5) * h_t,   h_t odd.

The public counter law is exactly

    2^(8*n_(t+1)+15) * h_(t+1)
      = 3^(6*n_t+11) * h_t + 51.

Prescribe an arithmetic valuation counter ``n_t=n0+k*t``, with ``n0,k>=1``.
Finite backward unrolling gives the unique 2-adic initial candidate

    h0 = -51/3^(6*n0+11)
         * F(2^(8*k)/3^(6*k),
             2^(8*(n0+k)+15)/3^(6*(n0+k)+11)).

Coefficientwise this is a nonzero rational multiple of the paper-normalized
Vaananen--Wallisser theta value with

    q = 3^(6*k)/2^(8*k),
    alpha = 2^(8*n0+15)/3^(6*n0+11).

The same 1989 full-source theorem already used elsewhere in this repository
makes that value irrational in Q_2.  Hence, accepting the cited theorem, no
arithmetic-growth branch schedule is realized by an ordinary integer.  This
worker checks the finite ether recurrence, exact partial-theta identity,
coefficient conversion, and every elementary theorem hypothesis.  It cites
the external irrationality theorem; it does not reprove it and does not prove
Collatz.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence

from breakoff_delay_gate import v2
from breakoff_ether_counter import (
    branch,
    counter_next,
    packet_to_register,
)
from breakoff_ether_dynamics import PrefixCylinder, branch_input_packet


SCHEMA = "collatz-breakoff-ether-linear-theta-v1"
BINARY_CELL = 8
BINARY_OFFSET = 15
TERNARY_CELL = 6
TERNARY_OFFSET = 11
COLLISION_CONSTANT = 51


def schedule(start_branch: int, branch_step: int, transitions: int) -> list[int]:
    if min(start_branch, branch_step, transitions) < 1:
        raise ValueError("linear schedule parameters must be positive")
    return [start_branch + branch_step * index for index in range(transitions + 1)]


def compile_schedule(branches: Sequence[int]) -> PrefixCylinder:
    if len(branches) < 2:
        raise ValueError("schedule must contain a transition")
    prefix = PrefixCylinder.start(branches[0])
    for following in branches[1:]:
        prefix = prefix.extend(following)
    return prefix


def replay_schedule(
    start_branch: int, branch_step: int, transitions: int
) -> tuple[list[int], list[int], PrefixCylinder]:
    branches = schedule(start_branch, branch_step, transitions)
    prefix = compile_schedule(branches)
    first = branch(branches[0])
    packet = branch_input_packet(first, prefix.initial_address)
    register = packet_to_register(packet)
    odd_parts: list[int] = []
    registers = [register]
    for index, expected_branch in enumerate(branches):
        exponent = v2(register)
        if exponent != 8 * expected_branch - 5:
            raise AssertionError("linear schedule selected the wrong ether branch")
        odd = register >> exponent
        if odd % 2 != 1:
            raise AssertionError("ether branch payload is not odd")
        odd_parts.append(odd)
        if index == transitions:
            break
        following = counter_next(register)
        if following is None:
            raise AssertionError("compiled linear schedule halted early")
        next_branch = branches[index + 1]
        if (
            (1 << (8 * next_branch + 15)) * (following >> (8 * next_branch - 5))
            != (3 ** (6 * expected_branch + 11)) * odd + COLLISION_CONSTANT
        ):
            raise AssertionError("ether odd-part recurrence failed")
        register = following
        registers.append(register)
    return odd_parts, registers, prefix


def theta_exponents(
    start_branch: int, branch_step: int, term_index: int
) -> tuple[int, int]:
    if min(start_branch, branch_step) < 1 or term_index < 0:
        raise ValueError("invalid theta exponent query")
    j = term_index
    two_exponent = (
        j * (BINARY_CELL * start_branch + BINARY_OFFSET)
        + BINARY_CELL * branch_step * j * (j + 1) // 2
    )
    three_exponent = (
        (j + 1) * (TERNARY_CELL * start_branch + TERNARY_OFFSET)
        + TERNARY_CELL * branch_step * j * (j + 1) // 2
    )
    return two_exponent, three_exponent


def terminal_exponents(
    start_branch: int, branch_step: int, transitions: int
) -> tuple[int, int]:
    if min(start_branch, branch_step, transitions) < 1:
        raise ValueError("invalid terminal exponent query")
    two_exponent = sum(
        BINARY_CELL * (start_branch + branch_step * index) + BINARY_OFFSET
        for index in range(1, transitions + 1)
    )
    three_exponent = sum(
        TERNARY_CELL * (start_branch + branch_step * index) + TERNARY_OFFSET
        for index in range(transitions)
    )
    return two_exponent, three_exponent


def finite_identity(
    start_branch: int, branch_step: int, transitions: int
) -> dict[str, Any]:
    odd_parts, registers, prefix = replay_schedule(
        start_branch, branch_step, transitions
    )
    partial = Fraction(0)
    terms: list[tuple[int, int]] = []
    for index in range(transitions):
        two_exponent, three_exponent = theta_exponents(
            start_branch, branch_step, index
        )
        partial -= COLLISION_CONSTANT * Fraction(
            1 << two_exponent, 3 ** three_exponent
        )
        terms.append((two_exponent, three_exponent))
    terminal_two, terminal_three = terminal_exponents(
        start_branch, branch_step, transitions
    )
    terminal = Fraction(
        (1 << terminal_two) * odd_parts[-1], 3 ** terminal_three
    )
    if Fraction(odd_parts[0]) != partial + terminal:
        raise AssertionError("finite ether partial-theta identity failed")

    modulus = 1 << terminal_two
    partial_residue = (
        partial.numerator * pow(partial.denominator, -1, modulus)
    ) % modulus
    if odd_parts[0] % modulus != partial_residue:
        raise AssertionError("ether partial-theta 2-adic residue failed")
    return {
        "start_branch": start_branch,
        "branch_step": branch_step,
        "transitions": transitions,
        "linked_branches": transitions + 1,
        "compiled_initial_tail_bits": prefix.initial_address.bit_length(),
        "compiled_precision_bits": prefix.initial_bits,
        "initial_register_bits": registers[0].bit_length(),
        "terminal_register_bits": registers[-1].bit_length(),
        "terminal_two_adic_precision_bits": terminal_two,
        "terminal_triadic_denominator_exponent": terminal_three,
        "first_term_exponents": list(terms[0]),
        "last_term_exponents": list(terms[-1]),
        "finite_rational_identity_checked": True,
        "two_adic_residue_checked": True,
    }


def theorem_application_audit() -> dict[str, Any]:
    if not 3 ** TERNARY_CELL > 2 ** BINARY_CELL > 1:
        raise AssertionError("theta base is outside the theorem range")
    if 3 * BINARY_CELL < 4 * TERNARY_CELL:
        raise AssertionError("binary/ternary exponent ratio lost the 4/3 bound")
    if not 2**8 > 3**5 or not 45 < 64:
        raise AssertionError("exact logarithmic separator audit failed")

    coefficient_checks = 0
    for branch_step in range(1, 9):
        for start_branch in range(1, 9):
            for index in range(64):
                # F(Q,z), Q=2^(8k)/3^(6k), has Q^(j(j-1)/2)z^j.
                f_two = (
                    BINARY_CELL * branch_step * index * (index + 1) // 2
                    + (BINARY_CELL * start_branch + BINARY_OFFSET) * index
                )
                F_two = (
                    BINARY_CELL * branch_step * index * (index - 1) // 2
                    + (
                        BINARY_CELL * (start_branch + branch_step)
                        + BINARY_OFFSET
                    )
                    * index
                )
                f_three = (
                    TERNARY_CELL * branch_step * index * (index + 1) // 2
                    + (TERNARY_CELL * start_branch + TERNARY_OFFSET) * index
                )
                F_three = (
                    TERNARY_CELL * branch_step * index * (index - 1) // 2
                    + (
                        TERNARY_CELL * (start_branch + branch_step)
                        + TERNARY_OFFSET
                    )
                    * index
                )
                if (f_two, f_three) != (F_two, F_three):
                    raise AssertionError("ether theta function conversion failed")
                coefficient_checks += 1
    return {
        "schedule": "n_t=n0+k*t for arbitrary n0>=1 and k>=1",
        "paper_parameter_q": "3^(6*k)/2^(8*k)",
        "paper_argument_alpha": "2^(8*n0+15)/3^(6*n0+11)",
        "candidate": (
            "-51/3^(6*n0+11) * "
            "f_(3^(6*k)/2^(8*k))(2^(8*n0+15)/3^(6*n0+11))"
        ),
        "external_source": {
            "authors": "K. Vaananen and R. Wallisser",
            "title": (
                "Zu einem Satz von Skolem ueber lineare Unabhaengigkeit "
                "von Werten gewisser Thetareihen"
            ),
            "journal": "Manuscripta Mathematica 65 (1989), 199-212",
            "theorem_parameters": {"ell": 1, "sigma": 0, "p": 2},
        },
        "elementary_hypotheses": {
            "q_reduced_for_every_k": True,
            "q_numerator_greater_than_one": True,
            "alpha_nonzero_rational": True,
            "distinct_argument_conditions": "vacuous_for_ell_1",
            "two_adic_convergence": "abs_2(q)=2^(8*k)>1",
            "exact_size_chain": (
                "2^8>3^5 gives log(2)/log(3)>5/8; "
                "3*8=4*6 gives 8log(2)/(6log(3))>5/6; "
                "45<64 gives 1/6<(3-sqrt(5))/2"
            ),
            "function_conversion_coefficients_checked": coefficient_checks,
        },
        "conditional_conclusion": (
            "accepting the cited theorem, every arithmetic-growth candidate "
            "is irrational in Q_2 and hence not an ordinary integer"
        ),
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("breakoff_ether_dynamics.py"),
        Path(__file__).with_name("breakoff_ether_counter.py"),
        Path(__file__).with_name("breakoff_ether_glider.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def build_audit(max_start: int, max_step: int, transitions: int) -> dict[str, Any]:
    if min(max_start, max_step, transitions) < 1:
        raise ValueError("audit bounds must be positive")
    finite = [
        finite_identity(start, step, transitions)
        for start in range(1, max_start + 1)
        for step in range(1, max_step + 1)
    ]
    return {
        "odd_payload_recurrence": (
            "2^(8*n_(t+1)+15)*h_(t+1)=3^(6*n_t+11)*h_t+51"
        ),
        "bounds": {
            "finite_start_branch": [1, max_start],
            "finite_branch_step": [1, max_step],
            "finite_transitions": transitions,
        },
        "finite_schedule_checks": finite,
        "finite_schedules_checked": len(finite),
        "theorem_application": theorem_application_audit(),
        "claim_scope": (
            "exact finite ether replays and partial-theta identities in the "
            "stated box; exact coefficient/hypothesis audit for all n0,k>=1; "
            "the published irrationality theorem is cited, not reproved"
        ),
        "closure_status": {
            "counterexample": None,
            "closed_conditionally_on_external_theorem": (
                "every arithmetic valuation counter n_t=n0+k*t, k>=1"
            ),
            "remaining": (
                "nonlinear or payload-dependent unbounded counters and "
                "bounded aperiodic branch schedules"
            ),
        },
    }


def build_artifact(max_start: int, max_step: int, transitions: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_sha256": source_sha256(),
        "audit": build_audit(max_start, max_step, transitions),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema", "generated_at_utc", "verifier_sha256", "audit", "artifact_sha256"
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["verifier_sha256"] != source_sha256():
        raise ValueError("verifier hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    bounds = data["audit"]["bounds"]
    actual = build_audit(
        int(bounds["finite_start_branch"][1]),
        int(bounds["finite_branch_step"][1]),
        int(bounds["finite_transitions"]),
    )
    if data["audit"] != actual:
        raise AssertionError("artifact differs from exact recomputation")
    return {
        "artifact_sha256": advertised,
        "verifier_sha256": data["verifier_sha256"],
        "finite_schedules_checked": actual["finite_schedules_checked"],
        "conditional_closed_family": "n_t=n0+k*t for all n0,k>=1",
        "external_theorem_reproved": False,
        "counterexample": None,
    }


def selftest() -> None:
    record = finite_identity(1, 1, 4)
    if record["linked_branches"] != 5:
        raise AssertionError("linear ether replay changed")
    audit = theorem_application_audit()
    if audit["elementary_hypotheses"]["function_conversion_coefficients_checked"] != 4096:
        raise AssertionError("theta coefficient audit changed")


def parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-start", type=int, default=4)
    build.add_argument("--max-step", type=int, default=4)
    build.add_argument("--transitions", type=int, default=8)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("breakoff ether linear-theta selftest: PASS")
        return 0
    if args.command == "build":
        selftest()
        args.output.write_text(
            json.dumps(
                build_artifact(args.max_start, args.max_step, args.transitions),
                indent=2,
                sort_keys=True,
            )
            + "\n"
        )
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
