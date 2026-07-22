#!/usr/bin/env python3
"""Exact returning unit macro and its autonomous reproduction equation.

The level-two sign-negative unit ISA has transition law

    n -> m:  3^q(n) h - 1 = 2^p(m) h',
    p(n)=23*n+54,  q(n)=17*n+40.

The previously advertised three-collision synthesized-marker route was not a
legal linked path: after targeting state 1 it used q(g) as though the source
state were g.  This worker uses the legal four-transition return

    1 -> 1 -> g -> g -> 1.

It checks the literal transitions on bounded public rows, derives the exact
composition for every positive g, and exposes the actual quine obligation

    3^R(g) F(g) - C(g) = 2^S(g) F(f(g)).

An infinite positive odd solution, with the four intermediate divisions exact
at every generation, would be one autonomous ordinary orbit.  No such F is
supplied here.  The worker also checks the exact coefficient obstruction to a
finite Laurent-polynomial successor ansatz.  A short pole-propagation argument
upgrades that obstruction to rational functions, but that upgrade remains a
research derivation until separately formalized.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


SCHEMA = "collatz-unit-return-quine-v1"


def p(cells: int) -> int:
    if cells < 1:
        raise ValueError("unit opcode must be positive")
    return 23 * cells + 54


def q(cells: int) -> int:
    if cells < 1:
        raise ValueError("unit opcode must be positive")
    return 17 * cells + 40


def v2(value: int) -> int:
    if value == 0:
        raise ValueError("v2(0) is undefined")
    value = abs(value)
    return (value & -value).bit_length() - 1


@dataclass(frozen=True)
class ReturnRow:
    internal_opcode_g: int
    internal_binary_exponent_P: int
    internal_ternary_exponent_Q: int
    composition_three_exponent_R: int
    composition_two_exponent_S: int
    composition_constant_C: int
    canonical_source: int
    canonical_output: int
    intermediate_bit_lengths: tuple[int, int, int, int, int]
    source_stride_two_exponent: int
    output_stride_three_exponent: int
    coefficient_expanding: bool


def composition_constant(P: int, Q: int) -> int:
    """Constant for the legal route 1 -> 1 -> g -> g -> 1."""
    return (
        pow(3, 2 * Q + 57)
        + pow(2, 77) * pow(3, 2 * Q)
        + pow(2, 77 + P) * pow(3, Q)
        + pow(2, 77 + 2 * P)
    )


def replay_return(g: int, source: int) -> tuple[int, int, int, int, int]:
    """Replay the four exact source/target-compatible unit transitions."""
    P = p(g)
    Q = q(g)
    states = [source]
    for source_q, target_p in ((57, 77), (57, P), (Q, P), (Q, 77)):
        numerator = pow(3, source_q) * states[-1] - 1
        if v2(numerator) != target_p:
            raise AssertionError(
                f"illegal unit transition: expected v2={target_p}, "
                f"found {v2(numerator)}"
            )
        target = numerator >> target_p
        if target <= 0 or target % 2 != 1:
            raise AssertionError("unit transition did not produce a positive odd core")
        states.append(target)
    return tuple(states)  # type: ignore[return-value]


def build_row(g: int) -> ReturnRow:
    P = p(g)
    Q = q(g)
    R = 114 + 2 * Q
    S = 154 + 2 * P
    C = composition_constant(P, Q)

    # Select the unique source modulo 2^(S+1) whose composed output is odd.
    # This one congruence forces the complete finite valuation word; the
    # literal replay below independently checks every intermediate valuation.
    modulus = 1 << (S + 1)
    source = ((C + (1 << S)) * pow(pow(3, R), -1, modulus)) % modulus
    if source == 0:
        source = modulus
    states = replay_return(g, source)
    output = states[-1]
    if pow(3, R) * source - C != (1 << S) * output:
        raise AssertionError("four-transition composition identity failed")

    # Every lift source+2^(S+1)t follows the same word and changes the output
    # by 2*3^R*t.  Thus the branch coefficient ratio is 3^R/2^S.
    lifted = replay_return(g, source + (1 << (S + 1)))[-1]
    if lifted - output != 2 * pow(3, R):
        raise AssertionError("return-family affine stride failed")
    expanding = pow(3, R) > pow(2, S)
    if not expanding:
        raise AssertionError("public returning branch unexpectedly lost growth")

    X = pow(2, P)
    Y = pow(3, Q)
    if C != (
        (pow(3, 57) + pow(2, 77)) * Y * Y
        + pow(2, 77) * X * Y
        + pow(2, 77) * X * X
    ):
        raise AssertionError("mixed-base composition constant changed")

    return ReturnRow(
        internal_opcode_g=g,
        internal_binary_exponent_P=P,
        internal_ternary_exponent_Q=Q,
        composition_three_exponent_R=R,
        composition_two_exponent_S=S,
        composition_constant_C=C,
        canonical_source=source,
        canonical_output=output,
        intermediate_bit_lengths=tuple(value.bit_length() for value in states),
        source_stride_two_exponent=S + 1,
        output_stride_three_exponent=R,
        coefficient_expanding=expanding,
    )


def check_successor_quine_algebra(rows: int) -> dict[str, object]:
    """Check the exact normalized equation for g -> g+1."""
    if rows < 2:
        raise ValueError("successor audit needs at least two rows")
    c_numerator = pow(2, 23)
    c_denominator = pow(3, 17)
    if not 0 < c_numerator < c_denominator:
        raise AssertionError("successor mixed-base scale is not a contraction")

    for g in range(1, rows):
        X = pow(2, p(g))
        Y = pow(3, q(g))
        next_X = pow(2, p(g + 1))
        next_Y = pow(3, q(g + 1))
        if next_X * Y * c_denominator != next_Y * X * c_numerator:
            raise AssertionError("z_(g+1)=(2^23/3^17)z_g failed")

    # Exact conditions used by the Laurent-polynomial degree proof.  If a
    # Laurent polynomial had a negative least exponent, A*f contributes that
    # exponent while z^2*f(cz) cannot.  Hence it is a polynomial.  Positive
    # degree then creates an unmatched top exponent d+2; degree zero cannot
    # supply the nonzero linear forcing coefficient.
    A = pow(3, 114)
    D = pow(2, 154)
    b0 = pow(3, 57) + pow(2, 77)
    b1 = pow(2, 77)
    b2 = pow(2, 77)
    if not all(value > 0 for value in (A, D, b0, b1, b2)):
        raise AssertionError("normalized quine coefficients lost positivity")

    return {
        "opcode_schedule": "g -> g+1",
        "z_definition": "z_g=2^(23*g+54)/3^(17*g+40)",
        "z_update": "z_(g+1)=(2^23/3^17)*z_g",
        "c_numerator": c_numerator,
        "c_denominator": c_denominator,
        "normalized_equation": (
            "3^114*f(z)-[(3^57+2^77)+2^77*z+2^77*z^2]="
            "2^154*z^2*f((2^23/3^17)*z)"
        ),
        "laurent_polynomial_obstruction": {
            "scope": "all finite Laurent polynomials over Q",
            "negative_minimum_exponent_impossible": True,
            "positive_degree_top_exponent_shift": 2,
            "degree_zero_killed_by_nonzero_linear_forcing": b1,
            "checked_exactly": True,
        },
        "rational_function_upgrade": {
            "status": "research derivation sent for independent formalization",
            "idea": (
                "a nonzero finite pole alpha forces c*alpha, c^2*alpha, ... "
                "to be poles; c is not a root of unity.  A pole at zero "
                "cannot cancel the two-degree shift.  Hence a rational "
                "solution would be Laurent polynomial."
            ),
        },
    }


def build_certificate(rows: int = 16) -> dict[str, object]:
    if rows < 2:
        raise ValueError("return-quine certificate needs at least two rows")
    public_rows = [build_row(g) for g in range(1, rows + 1)]
    encoded_rows = [asdict(row) for row in public_rows]
    rows_sha256 = hashlib.sha256(
        json.dumps(encoded_rows, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact legal four-transition returning families for public opcodes "
            f"g=1..{rows}, the symbolic all-g composition and quine equation, "
            "and an exact all-degree Laurent-polynomial obstruction for the "
            "successor ansatz; no infinite orbit or counterexample is claimed"
        ),
        "unit_transition": "n->m: 3^q(n)*h-1=2^p(m)*h'",
        "p_of_n": "23*n+54",
        "q_of_n": "17*n+40",
        "legal_return_route": "1->1->g->g->1",
        "all_g_composition": {
            "R_g": "114+2*(17*g+40)",
            "S_g": "154+2*(23*g+54)",
            "C_g": (
                "3^(2*Q_g+57)+2^77*3^(2*Q_g)+"
                "2^(77+P_g)*3^Q_g+2^(77+2*P_g)"
            ),
            "macro": "3^R_g*h-C_g=2^S_g*h'",
            "family": (
                "h=a_g+2^(S_g+1)*v -> "
                "h'=b_g+2*3^R_g*v"
            ),
        },
        "autonomous_reproduction_gate": {
            "equation": "3^R_g*F(g)-C_g=2^S_g*F(f(g))",
            "required_semantics": (
                "F(g) and all four intermediate cores are positive odd, "
                "and the same finite rule F,f supplies every generation"
            ),
            "fresh_crt_per_generation_is_not_closure": True,
        },
        "successor_quine": check_successor_quine_algebra(rows),
        "doubling_hint": {
            "opcode_schedule": "g -> 2*g",
            "z_update": "z_(2g)=(3^40/2^54)*z_g^2",
            "interpretation": (
                "a genuine base-squaring Mahler equation; it is a more "
                "faithful self-similar target than another finite bank"
            ),
        },
        "audited_row_count": rows,
        "audited_rows_sha256": rows_sha256,
        "first_audited_row": encoded_rows[0],
        "last_audited_row": encoded_rows[-1],
        "checks": {
            "four_literal_exact_transitions_per_row": True,
            "source_and_target_state_labels_match": True,
            "composition_identity": True,
            "return_family_stride": True,
            "mixed_base_constant_identity": True,
            "strict_coefficient_growth_on_public_rows": True,
            "successor_z_update": True,
            "all_degree_laurent_polynomial_obstruction": True,
        },
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def canonical_json(payload: dict[str, object]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def verify_certificate(path: Path) -> None:
    stored = json.loads(path.read_text())
    rows = int(stored["audited_row_count"])
    expected = json.loads(canonical_json(build_certificate(rows)))
    if stored != expected:
        raise AssertionError("return-quine artifact does not reconstruct exactly")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--rows", type=int, default=16)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        build_certificate()
        print("unit return-quine selftest: PASS")
    elif args.command == "build":
        payload = build_certificate(args.rows)
        args.output.write_text(canonical_json(payload))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit return-quine verification: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # pragma: no cover - CLI failure path
        print(f"ERROR: {exc}", file=sys.stderr)
        raise
