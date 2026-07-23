#!/usr/bin/env python3
"""Exact theta decomposition for periodic-increment ether counters.

After one successful autonomous ether step, the public odd part has exactly
one factor of three.  In positive branch coordinates write it as ``3*u_t``.
The literal public recurrence then has the constant-seventeen form

    2^(8*n_(t+1)+15) * u_(t+1)
      = 3^(6*n_t+11) * u_t + 17.                         (EC17)

Suppose the branch increments repeat with period ``L``:

    n_(t+1) - n_t = d_(t mod L),    K=sum(d_r)>0.

The levels may move down inside a cycle, but every realized level must remain
positive.  Splitting the backward EC17 series at term ``j=L*q+r`` gives

    T_(L*q+r) = T_r * Q^choose(q,2) * R_r^q,
    Q           = 2^(8*K*L) / 3^(6*K*L),
    R_(r+1)/R_r = 2^(8*K) / 3^(6*K).

Thus the unique 2-adic candidate is a rational linear combination of ``L``
paper-normalized Vaananen--Wallisser theta values.  Their arguments are
pairwise separated modulo powers of the common paper parameter because
``0 < |r-s| < L`` cannot equal a nonzero multiple of ``L``.

For the ether exponent ratio, the 1989 sufficient size hypothesis passes at
``L=2`` but already fails at ``L=3``.  Consequently period three, rather than
period four as in the older phase-glider system, is the first escape from
that particular theorem.  The external linear-independence theorem is cited,
not reproved.  Until the generic split is kernel-checked, this worker claims
only its exact bounded replays and coefficient audits.
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


SCHEMA = "collatz-breakoff-ether-periodic-theta-v1"
BINARY_CELL = 8
BINARY_OFFSET = 15
TERNARY_CELL = 6
TERNARY_OFFSET = 11
CORE_CONSTANT = 17


def periodic_levels(
    start_branch: int, increments: Sequence[int], transitions: int
) -> list[int]:
    if start_branch < 1 or transitions < 1 or not increments:
        raise ValueError("invalid periodic schedule")
    if sum(increments) < 1:
        raise ValueError("periodic increment word must have positive cycle sum")
    levels = [start_branch]
    for index in range(transitions):
        following = levels[-1] + increments[index % len(increments)]
        if following < 1:
            raise ValueError("periodic schedule left the positive branches")
        levels.append(following)
    return levels


def compile_branches(branches: Sequence[int]) -> PrefixCylinder:
    if len(branches) < 2:
        raise ValueError("schedule must contain a transition")
    prefix = PrefixCylinder.start(branches[0])
    for following in branches[1:]:
        prefix = prefix.extend(following)
    return prefix


def replay_core_schedule(
    start_branch: int, increments: Sequence[int], transitions: int
) -> tuple[list[int], list[int], PrefixCylinder]:
    """Compile one arbitrary predecessor, then replay literal EC17 states."""

    levels = periodic_levels(start_branch, increments, transitions)
    compiled_levels = [1, *levels]
    prefix = compile_branches(compiled_levels)
    first = branch(compiled_levels[0])
    packet = branch_input_packet(first, prefix.initial_address)
    register = packet_to_register(packet)
    core_values: list[int] = []
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
            core_values.append(odd_part // 3)
            registers.append(register)
        if index + 1 == len(compiled_levels):
            break
        following = counter_next(register)
        if following is None:
            raise AssertionError("compiled periodic schedule halted early")
        register = following

    for index in range(transitions):
        source = levels[index]
        target = levels[index + 1]
        if (
            (1 << (BINARY_CELL * target + BINARY_OFFSET))
            * core_values[index + 1]
            != 3 ** (TERNARY_CELL * source + TERNARY_OFFSET)
            * core_values[index]
            + CORE_CONSTANT
        ):
            raise AssertionError("constant-seventeen core recurrence failed")
        if core_values[index + 1] % 3 != 1:
            raise AssertionError("core lost its forced residue modulo three")
    return core_values, registers, prefix


def term_exponents(levels: Sequence[int], term_index: int) -> tuple[int, int]:
    if term_index < 0 or term_index >= len(levels):
        raise ValueError("theta term index is outside the supplied levels")
    two = sum(
        BINARY_CELL * levels[index] + BINARY_OFFSET
        for index in range(1, term_index + 1)
    )
    three = sum(
        TERNARY_CELL * levels[index] + TERNARY_OFFSET
        for index in range(term_index + 1)
    )
    return two, three


def terminal_exponents(levels: Sequence[int]) -> tuple[int, int]:
    transitions = len(levels) - 1
    if transitions < 1:
        raise ValueError("terminal exponent needs one transition")
    two = sum(
        BINARY_CELL * levels[index] + BINARY_OFFSET
        for index in range(1, transitions + 1)
    )
    three = sum(
        TERNARY_CELL * levels[index] + TERNARY_OFFSET
        for index in range(transitions)
    )
    return two, three


def finite_identity(
    start_branch: int, increments: Sequence[int], transitions: int
) -> dict[str, Any]:
    levels = periodic_levels(start_branch, increments, transitions)
    cores, registers, prefix = replay_core_schedule(
        start_branch, increments, transitions
    )
    partial = Fraction(0)
    for index in range(transitions):
        two, three = term_exponents(levels, index)
        partial -= CORE_CONSTANT * Fraction(1 << two, 3**three)
    terminal_two, terminal_three = terminal_exponents(levels)
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
        "increment_word": list(increments),
        "period": len(increments),
        "cycle_gain": sum(increments),
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
        "finite_rational_identity_checked": True,
        "two_adic_residue_checked": True,
        "literal_public_core_replay_checked": True,
    }


def residue_decomposition_audit(
    start_branch: int, increments: Sequence[int], cycles: int
) -> dict[str, Any]:
    period = len(increments)
    cycle_gain = sum(increments)
    if period < 1 or cycle_gain < 1 or cycles < 2:
        raise ValueError("invalid residue decomposition audit")
    max_term = period * cycles + period
    levels = periodic_levels(start_branch, increments, max_term)
    q_two = BINARY_CELL * cycle_gain * period
    q_three = TERNARY_CELL * cycle_gain * period
    rho_two = BINARY_CELL * cycle_gain
    rho_three = TERNARY_CELL * cycle_gain
    residues: list[dict[str, Any]] = []
    coefficient_checks = 0
    for residue in range(period):
        prefix_two, prefix_three = term_exponents(levels, residue)
        ratio_two = sum(
            BINARY_CELL * levels[index] + BINARY_OFFSET
            for index in range(residue + 1, residue + period + 1)
        )
        ratio_three = sum(
            TERNARY_CELL * levels[index] + TERNARY_OFFSET
            for index in range(residue + 1, residue + period + 1)
        )
        if residue:
            first = residues[0]
            if ratio_two != first["ratio_two_exponent"] + rho_two * residue:
                raise AssertionError("binary residue ratio shift failed")
            if ratio_three != first["ratio_three_exponent"] + rho_three * residue:
                raise AssertionError("ternary residue ratio shift failed")
        for cycle in range(cycles):
            actual_two, actual_three = term_exponents(
                levels, period * cycle + residue
            )
            expected_two = (
                prefix_two
                + ratio_two * cycle
                + q_two * cycle * (cycle - 1) // 2
            )
            expected_three = (
                prefix_three
                + ratio_three * cycle
                + q_three * cycle * (cycle - 1) // 2
            )
            if (actual_two, actual_three) != (expected_two, expected_three):
                raise AssertionError("periodic theta residue split failed")

            # F(Q,R_r)=f_(1/Q)(R_r/Q), coefficient by coefficient.
            paper_two = (
                q_two * cycle * (cycle + 1) // 2
                + (ratio_two - q_two) * cycle
            )
            paper_three = (
                q_three * cycle * (cycle + 1) // 2
                + (ratio_three - q_three) * cycle
            )
            f_two = q_two * cycle * (cycle - 1) // 2 + ratio_two * cycle
            f_three = (
                q_three * cycle * (cycle - 1) // 2 + ratio_three * cycle
            )
            if (paper_two, paper_three) != (f_two, f_three):
                raise AssertionError("paper theta conversion failed")
            coefficient_checks += 1
        residues.append(
            {
                "residue": residue,
                "prefix_two_exponent": prefix_two,
                "prefix_three_exponent": prefix_three,
                "ratio_two_exponent": ratio_two,
                "ratio_three_exponent": ratio_three,
                "paper_argument_two_exponent": ratio_two - q_two,
                "paper_argument_three_exponent": ratio_three - q_three,
            }
        )

    separation_checks = 0
    for left in range(period):
        for right in range(period):
            if left == right:
                continue
            difference = left - right
            for power in range(-8, 9):
                # alpha_l/alpha_r=rho^(l-r), while paper q^z=rho^(-L*z).
                if difference == -period * power:
                    raise AssertionError("theta arguments were not separated")
                separation_checks += 1
    return {
        "start_branch": start_branch,
        "increment_word": list(increments),
        "period": period,
        "cycle_gain": cycle_gain,
        "paper_parameter": (
            f"3^({q_three})/2^({q_two})"
        ),
        "theta_inverse_two_exponent": q_two,
        "theta_inverse_three_exponent": q_three,
        "one_residue_ratio_two_exponent": rho_two,
        "one_residue_ratio_three_exponent": rho_three,
        "residues": residues,
        "coefficient_checks": coefficient_checks,
        "bounded_separation_checks": separation_checks,
        "symbolic_separation_identity": "r-s=-period*z",
    }


def theorem_boundary_audit() -> dict[str, Any]:
    # gamma=1-(4/3)*log(2)/log(3).
    if not 3**TERNARY_CELL > 2**BINARY_CELL > 1:
        raise AssertionError("paper theta base is outside the theorem range")
    if not 2**8 > 3**5:
        raise AssertionError("gamma<1/6 logarithmic separator failed")
    if not 13**2 > 9 * 17:
        raise AssertionError("1/6<Gamma(2,0) radical separator failed")

    # 2^128<3^81 gives gamma>5/32.  Also 97/16<sqrt(37) gives
    # Gamma(3,0)<5/32.
    if not 2**128 < 3**81:
        raise AssertionError("5/32<gamma logarithmic separator failed")
    if not 97**2 < 37 * 16**2:
        raise AssertionError("Gamma(3,0)<5/32 radical separator failed")
    return {
        "external_source": {
            "authors": "K. Vaananen and R. Wallisser",
            "title": (
                "Zu einem Satz von Skolem ueber lineare Unabhaengigkeit "
                "von Werten gewisser Thetareihen"
            ),
            "journal": "Manuscripta Mathematica 65 (1989), 199-212",
            "theorem_parameters": {
                "ell": "period",
                "sigma": 0,
                "p": 2,
            },
        },
        "size_parameter": "gamma=1-8*log(2)/(6*log(3))",
        "threshold": (
            "Gamma(L,0)=(2*L+1-sqrt(1+4*L^2))/(2*L)"
        ),
        "period_two": {
            "exact_chain": (
                "2^8>3^5 gives gamma<1/6; 13^2>9*17 gives "
                "1/6<Gamma(2,0)"
            ),
            "criterion": "passes",
        },
        "period_three": {
            "exact_chain": (
                "2^128<3^81 gives gamma>5/32; "
                "97^2<37*16^2 gives Gamma(3,0)<5/32"
            ),
            "criterion": "fails",
        },
        "conditional_scope_pending_lean": (
            "the displayed generic residue algebra would let the cited "
            "theorem close every positive-mean period-two increment word; "
            "the universal bridge is requested from the companion Lean worker"
        ),
        "first_theorem_escape": (
            "period three; failure of this sufficient estimate is not an orbit"
        ),
    }


def sample_words() -> list[tuple[int, tuple[int, ...]]]:
    return [
        (3, (1, 2)),
        (3, (2, 1)),
        (3, (2, -1)),
        (3, (-1, 2)),
        (4, (3, -2)),
        (4, (-2, 3)),
        (4, (1, 1, 2)),
        (4, (1, 2, 1)),
        (4, (2, 1, 1)),
        (4, (2, -1, 1)),
        (4, (-1, 2, 1)),
        (4, (1, -1, 2)),
        (4, (3, -1, -1)),
        (4, (-1, 3, -1)),
        (4, (-1, -1, 3)),
    ]


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


def build_audit(transitions: int, theta_cycles: int) -> dict[str, Any]:
    if transitions < 3 or theta_cycles < 2:
        raise ValueError("audit bounds are too small")
    samples = sample_words()
    finite = [
        finite_identity(start, word, transitions)
        for start, word in samples
    ]
    decompositions = [
        residue_decomposition_audit(start, word, theta_cycles)
        for start, word in samples
    ]
    return {
        "core_recurrence": (
            "2^(8*n_(t+1)+15)*u_(t+1)="
            "3^(6*n_t+11)*u_t+17"
        ),
        "periodic_increment_law": (
            "n_(t+1)-n_t=d_(t mod L), K=sum(d)>0"
        ),
        "bounds": {
            "finite_transitions": transitions,
            "theta_cycles_per_residue": theta_cycles,
            "sample_words": len(samples),
        },
        "finite_schedule_checks": finite,
        "residue_decomposition_checks": decompositions,
        "theorem_boundary": theorem_boundary_audit(),
        "claim_scope": (
            "exact literal public EC17 replays, finite rational and 2-adic "
            "identities, and periodic residue coefficient checks for the "
            "listed words and bounds; exact elementary period-two/three "
            "size separators; the external theorem and universal generic "
            "residue bridge are not proved by this artifact"
        ),
        "closure_status": {
            "counterexample": None,
            "bounded_samples": "all exact checks passed",
            "universal_period_two": "pending companion Lean bridge",
            "period_three": (
                "first failure of the cited sufficient theorem; not a witness"
            ),
        },
    }


def build_artifact(transitions: int, theta_cycles: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_sha256": source_sha256(),
        "audit": build_audit(transitions, theta_cycles),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema", "generated_at_utc", "verifier_sha256", "audit",
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
        int(bounds["finite_transitions"]),
        int(bounds["theta_cycles_per_residue"]),
    )
    if data["audit"] != actual:
        raise AssertionError("artifact differs from exact recomputation")
    checks = sum(
        item["coefficient_checks"]
        for item in actual["residue_decomposition_checks"]
    )
    return {
        "artifact_sha256": advertised,
        "verifier_sha256": data["verifier_sha256"],
        "finite_schedules_checked": len(actual["finite_schedule_checks"]),
        "theta_coefficients_checked": checks,
        "period_two_external_criterion": "passes",
        "period_three_external_criterion": "fails",
        "universal_period_two_lean_bridge": "pending",
        "counterexample": None,
    }


def selftest() -> None:
    record = finite_identity(3, (2, -1), 4)
    if record["levels"] != [3, 5, 4, 6, 5]:
        raise AssertionError("periodic core replay changed")
    decomposition = residue_decomposition_audit(3, (1, 2), 5)
    if decomposition["coefficient_checks"] != 10:
        raise AssertionError("periodic theta decomposition changed")
    theorem_boundary_audit()


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--transitions", type=int, default=9)
    build.add_argument("--theta-cycles", type=int, default=16)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("breakoff ether periodic-theta selftest: PASS")
    elif args.command == "build":
        artifact = build_artifact(args.transitions, args.theta_cycles)
        args.output.write_text(render(artifact))
        print(f"wrote {args.output}")
    else:
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
