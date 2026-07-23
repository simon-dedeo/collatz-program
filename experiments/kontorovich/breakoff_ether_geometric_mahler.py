#!/usr/bin/env python3
"""Mahler obstruction for geometrically growing ether branch schedules.

After one successful autonomous ether step, write the public odd part as
``3*u_t``.  In positive branch coordinates its exact recurrence is

    2^(8*n_(t+1)+15) * u_(t+1)
      = 3^(6*n_t+11) * u_t + 17.                         (EC17)

Prescribe the genuinely aperiodic, unbounded schedule

    n_t = n0 * d^t,    n0 >= 1, d >= 2.

Put

    a = 2^15/3^11,
    z = 2^(8*n0*d)/3^(6*n0*d),
    e_j = (d^j-1)/(d-1),
    G_(d,a)(z) = sum_(j>=0) a^j z^e_j.

Finite backward unrolling gives the unique 2-adic initial candidate

    u0 = -17/3^(6*n0+11) * G_(d,a)(z),

and the lacunary series satisfies the exact Mahler equation

    G_(d,a)(z) = 1 + a*z*G_(d,a)(z^d).

Wang's p-adic Mahler-value theorem applies with theorem parameters
``p=2, rho=d, n0=1, M0=d``: its numerical condition is simply ``d<d^2``.
The remaining function-transcendence premise follows by scalar descent from
Q to C_2 and the classical Hadamard gap theorem: over C the nonconstant
exponents obey ``e_(j+1)=1+d*e_j`` and the series has radius one.

This worker checks literal finite EC17 replays, the backward rational and
2-adic identities, bounded instances of the closed exponent formula and
functional equation, and bounded exact regressions for the elementary
external-theorem hypotheses.  The all-parameter identities are recorded as a
research derivation awaiting Lean.  It cites the external theorems rather than
reproving them.  Its proposed conditional conclusion excludes this geometric
schedule family; it constructs no infinite orbit and does not disprove
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
from breakoff_ether_counter import branch, counter_next, packet_to_register
from breakoff_ether_dynamics import PrefixCylinder, branch_input_packet


SCHEMA = "collatz-breakoff-ether-geometric-mahler-v1"
BINARY_CELL = 8
BINARY_OFFSET = 15
TERNARY_CELL = 6
TERNARY_OFFSET = 11
CORE_CONSTANT = 17


def geometric_levels(
    start_branch: int, multiplier: int, transitions: int
) -> list[int]:
    if start_branch < 1 or multiplier < 2 or transitions < 1:
        raise ValueError("invalid geometric schedule")
    return [start_branch * multiplier**index for index in range(transitions + 1)]


def compile_branches(branches: Sequence[int]) -> PrefixCylinder:
    if len(branches) < 2:
        raise ValueError("schedule must contain a transition")
    prefix = PrefixCylinder.start(branches[0])
    for following in branches[1:]:
        prefix = prefix.extend(following)
    return prefix


def replay_core_schedule(
    start_branch: int, multiplier: int, transitions: int
) -> tuple[list[int], list[int], PrefixCylinder]:
    """Compile one predecessor, then replay literal EC17 public states."""

    levels = geometric_levels(start_branch, multiplier, transitions)
    compiled_levels = [1, *levels]
    prefix = compile_branches(compiled_levels)
    first = branch(compiled_levels[0])
    packet = branch_input_packet(first, prefix.initial_address)
    register = packet_to_register(packet)
    cores: list[int] = []
    registers: list[int] = []
    for index, expected_branch in enumerate(compiled_levels):
        exponent = v2(register)
        if exponent != BINARY_CELL * expected_branch - 5:
            raise AssertionError("compiled schedule selected the wrong branch")
        odd_part = register >> exponent
        if odd_part % 2 != 1:
            raise AssertionError("public odd part is not odd")
        if index > 0:
            if odd_part % 3 or odd_part % 9 == 0:
                raise AssertionError("forced ternary core is not exact")
            cores.append(odd_part // 3)
            registers.append(register)
        if index + 1 == len(compiled_levels):
            break
        following = counter_next(register)
        if following is None:
            raise AssertionError("compiled geometric schedule halted early")
        register = following

    for index in range(transitions):
        source = levels[index]
        target = levels[index + 1]
        if (
            (1 << (BINARY_CELL * target + BINARY_OFFSET)) * cores[index + 1]
            != 3 ** (TERNARY_CELL * source + TERNARY_OFFSET) * cores[index]
            + CORE_CONSTANT
        ):
            raise AssertionError("constant-seventeen core recurrence failed")
        if cores[index + 1] % 3 != 1:
            raise AssertionError("core lost its forced residue modulo three")
    return cores, registers, prefix


def geometric_exponent(multiplier: int, index: int) -> int:
    if multiplier < 2 or index < 0:
        raise ValueError("invalid geometric exponent")
    return (multiplier**index - 1) // (multiplier - 1)


def term_exponents(
    start_branch: int, multiplier: int, term_index: int
) -> tuple[int, int]:
    if start_branch < 1 or multiplier < 2 or term_index < 0:
        raise ValueError("invalid term exponent query")
    j = term_index
    e_j = geometric_exponent(multiplier, j)
    e_next = geometric_exponent(multiplier, j + 1)
    two = BINARY_CELL * start_branch * multiplier * e_j + BINARY_OFFSET * j
    three = TERNARY_CELL * start_branch * e_next + TERNARY_OFFSET * (j + 1)
    return two, three


def terminal_exponents(
    start_branch: int, multiplier: int, transitions: int
) -> tuple[int, int]:
    if start_branch < 1 or multiplier < 2 or transitions < 1:
        raise ValueError("invalid terminal exponent query")
    e_n = geometric_exponent(multiplier, transitions)
    two = (
        BINARY_CELL * start_branch * multiplier * e_n
        + BINARY_OFFSET * transitions
    )
    three = (
        TERNARY_CELL * start_branch * e_n
        + TERNARY_OFFSET * transitions
    )
    return two, three


def finite_identity(
    start_branch: int, multiplier: int, transitions: int
) -> dict[str, Any]:
    levels = geometric_levels(start_branch, multiplier, transitions)
    cores, registers, prefix = replay_core_schedule(
        start_branch, multiplier, transitions
    )
    partial = Fraction(0)
    closed_form_checks = 0
    terms: list[tuple[int, int]] = []
    for index in range(transitions):
        two, three = term_exponents(start_branch, multiplier, index)
        direct_two = sum(
            BINARY_CELL * levels[k] + BINARY_OFFSET
            for k in range(1, index + 1)
        )
        direct_three = sum(
            TERNARY_CELL * levels[k] + TERNARY_OFFSET
            for k in range(index + 1)
        )
        if (two, three) != (direct_two, direct_three):
            raise AssertionError("closed geometric term exponents failed")
        partial -= CORE_CONSTANT * Fraction(1 << two, 3**three)
        terms.append((two, three))
        closed_form_checks += 1

    terminal_two, terminal_three = terminal_exponents(
        start_branch, multiplier, transitions
    )
    direct_terminal_two = sum(
        BINARY_CELL * levels[k] + BINARY_OFFSET
        for k in range(1, transitions + 1)
    )
    direct_terminal_three = sum(
        TERNARY_CELL * levels[k] + TERNARY_OFFSET
        for k in range(transitions)
    )
    if (terminal_two, terminal_three) != (
        direct_terminal_two,
        direct_terminal_three,
    ):
        raise AssertionError("closed geometric terminal exponents failed")

    terminal = Fraction(
        (1 << terminal_two) * cores[-1], 3**terminal_three
    )
    if Fraction(cores[0]) != partial + terminal:
        raise AssertionError("finite EC17 backward identity failed")

    modulus = 1 << terminal_two
    partial_residue = (
        partial.numerator * pow(partial.denominator, -1, modulus)
    ) % modulus
    if cores[0] % modulus != partial_residue:
        raise AssertionError("finite EC17 2-adic identity failed")

    return {
        "start_branch": start_branch,
        "multiplier": multiplier,
        "transitions": transitions,
        "levels": levels,
        "compiled_predecessor_branch": 1,
        "compiled_initial_tail_bits": prefix.initial_address.bit_length(),
        "compiled_precision_bits": prefix.initial_bits,
        "initial_core_bits": cores[0].bit_length(),
        "terminal_core_bits": cores[-1].bit_length(),
        "initial_register_bits": registers[0].bit_length(),
        "terminal_register_bits": registers[-1].bit_length(),
        "terminal_two_adic_precision_bits": terminal_two,
        "first_term_exponents": list(terms[0]),
        "last_term_exponents": list(terms[-1]),
        "closed_exponent_checks": closed_form_checks + 1,
        "finite_rational_identity_checked": True,
        "two_adic_residue_checked": True,
        "literal_public_core_replay_checked": True,
    }


def mahler_coefficient_audit() -> dict[str, Any]:
    checks = 0
    for multiplier in range(2, 9):
        for start_branch in range(1, 9):
            for index in range(64):
                e_j = geometric_exponent(multiplier, index)
                e_next = geometric_exponent(multiplier, index + 1)
                if e_next != 1 + multiplier * e_j:
                    raise AssertionError("Mahler exponent recursion failed")
                actual_two, actual_three = term_exponents(
                    start_branch, multiplier, index
                )
                candidate_two = (
                    BINARY_OFFSET * index
                    + BINARY_CELL * start_branch * multiplier * e_j
                )
                candidate_three = (
                    TERNARY_OFFSET * index
                    + TERNARY_CELL * start_branch * multiplier * e_j
                    + TERNARY_CELL * start_branch
                    + TERNARY_OFFSET
                )
                if (actual_two, actual_three) != (
                    candidate_two,
                    candidate_three,
                ):
                    raise AssertionError("Mahler candidate coefficient failed")
                checks += 1
    return {
        "family": "n_t=n0*d^t for arbitrary n0>=1 and integer d>=2",
        "series": "G_(d,a)(z)=sum_(j>=0) a^j*z^((d^j-1)/(d-1))",
        "coefficient": "a=2^15/3^11",
        "argument": "z=2^(8*n0*d)/3^(6*n0*d)",
        "functional_equation": "G_(d,a)(z)=1+a*z*G_(d,a)(z^d)",
        "candidate": "u0=-17/3^(6*n0+11)*G_(d,a)(z)",
        "coefficient_checks": checks,
    }


def theorem_application_audit() -> dict[str, Any]:
    if not 2**BINARY_OFFSET < 3**TERNARY_OFFSET:
        raise AssertionError("complex coefficient does not have size below one")
    if not 3**TERNARY_CELL > 2**BINARY_CELL > 1:
        raise AssertionError("ether scale assumptions changed")
    for multiplier in range(2, 257):
        if not multiplier < multiplier**2:
            raise AssertionError("Wang numerical condition failed")
        for index in range(1, 65):
            e_j = geometric_exponent(multiplier, index)
            e_next = geometric_exponent(multiplier, index + 1)
            if not e_next > multiplier * e_j:
                raise AssertionError("Hadamard gap condition failed")

    return {
        "wang_theorem": {
            "author": "Tian Qin Wang",
            "title": (
                "p-adic Transcendence and p-adic Transcendence Measures "
                "for the Values of Mahler Type Functions"
            ),
            "journal": "Acta Mathematica Sinica 22 (2006), 187-194",
            "doi": "10.1007/s10114-005-0534-4",
            "theorem": 1,
            "parameters": {
                "p_adic_prime": 2,
                "rho": "d",
                "functional_degree_n0": 1,
                "M0": "max(d,1)=d",
                "Q0": "a*z",
                "Q1": "1-u",
                "elimination_polynomial_g": "a*z",
            },
            "elementary_hypotheses": {
                "coefficient_field": "Q",
                "functional_equation": "a*z*G(z^d)+1-G(z)=0",
                "size_condition": "M0*n0^2=d<d^2=rho^2 for every d>=2",
                "argument_nonzero": True,
                "argument_two_adic_size": "abs_2(z)=2^(-8*n0*d)<1",
                "convergence": (
                    "for abs_2(z)<1, abs_2(a^j*z^e_j) tends to zero"
                ),
                "nonvanishing_iterates": "g(z^(d^k))=a*z^(d^k)!=0",
            },
        },
        "function_transcendence": {
            "external_source": (
                "Hadamard gap theorem, as stated for example in "
                "J.-C. Puchta, On Fabry's gap theorem, Arch. Math. "
                "(Brno) 38 (2002), 307-309"
            ),
            "exact_hypotheses": {
                "complex_coefficient_size": "0<2^15/3^11<1",
                "complex_radius": (
                    "one, since abs(a)^(j/e_j) tends to one"
                ),
                "gap_identity": "e_(j+1)=1+d*e_j>d*e_j for j>=1",
                "natural_boundary": "the complex unit circle",
                "descent": (
                    "a polynomial relation over C_2(z) for a Q-coefficient "
                    "series descends coefficientwise to Q(z)"
                ),
                "conclusion": "G is transcendental over C_2(z)",
            },
        },
        "conditional_conclusion": (
            "accepting Wang Theorem 1 and the classical Hadamard gap theorem, "
            "the forced EC17 candidate is transcendental in Q_2 and cannot "
            "be an ordinary integer; the universal EC17-to-value bridge is "
            "a research derivation awaiting Lean"
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


def build_audit(
    max_start: int, max_multiplier: int, transitions: int
) -> dict[str, Any]:
    if max_start < 1 or max_multiplier < 2 or transitions < 1:
        raise ValueError("audit bounds are invalid")
    finite = [
        finite_identity(start, multiplier, transitions)
        for start in range(1, max_start + 1)
        for multiplier in range(2, max_multiplier + 1)
    ]
    return {
        "core_recurrence": (
            "2^(8*n_(t+1)+15)*u_(t+1)=3^(6*n_t+11)*u_t+17"
        ),
        "bounds": {
            "finite_start_branch": [1, max_start],
            "finite_multiplier": [2, max_multiplier],
            "finite_transitions": transitions,
        },
        "finite_schedule_checks": finite,
        "finite_schedules_checked": len(finite),
        "mahler_reduction": mahler_coefficient_audit(),
        "theorem_application": theorem_application_audit(),
        "claim_scope": (
            "exact finite public replays, EC17 backward identities, and "
            "Mahler coefficient identities in the stated boxes; bounded exact "
            "regressions for the elementary theorem hypotheses; the universal "
            "algebra is a research derivation awaiting Lean, and the two "
            "published external theorems are cited, not reproved"
        ),
        "closure_status": {
            "counterexample": None,
            "proposed_conditional_closure_awaiting_lean": (
                "every geometric branch counter n_t=n0*d^t, n0>=1,d>=2"
            ),
            "remaining": (
                "more general nonlinear or payload-dependent aperiodic "
                "schedules, including non-geometric period-three escapes"
            ),
        },
    }


def build_artifact(
    max_start: int, max_multiplier: int, transitions: int
) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_sha256": source_sha256(),
        "audit": build_audit(max_start, max_multiplier, transitions),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema",
        "generated_at_utc",
        "verifier_sha256",
        "audit",
        "artifact_sha256",
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
        int(bounds["finite_multiplier"][1]),
        int(bounds["finite_transitions"]),
    )
    if data["audit"] != actual:
        raise AssertionError("artifact differs from exact recomputation")
    return {
        "artifact_sha256": advertised,
        "verifier_sha256": data["verifier_sha256"],
        "finite_schedules_checked": actual["finite_schedules_checked"],
        "proposed_conditional_family": "n_t=n0*d^t for all n0>=1,d>=2",
        "external_theorems_reproved": False,
        "counterexample": None,
    }


def selftest() -> None:
    record = finite_identity(1, 2, 4)
    if record["levels"] != [1, 2, 4, 8, 16]:
        raise AssertionError("geometric ether replay changed")
    audit = mahler_coefficient_audit()
    if audit["coefficient_checks"] != 3584:
        raise AssertionError("Mahler coefficient audit changed")
    theorem_application_audit()


def parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-start", type=int, default=3)
    build.add_argument("--max-multiplier", type=int, default=4)
    build.add_argument("--transitions", type=int, default=6)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("breakoff ether geometric-Mahler selftest: PASS")
        return 0
    if args.command == "build":
        selftest()
        args.output.write_text(
            json.dumps(
                build_artifact(
                    args.max_start, args.max_multiplier, args.transitions
                ),
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
