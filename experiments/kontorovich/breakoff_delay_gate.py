#!/usr/bin/env python3
"""Exact checker for regenerative delay/collision gates in the break-off map.

The autonomous break-off transition is

    B(k) = (3^(v2(k)+2) * oddpart(k) + 1) / 8.

A clean delay-line state has the form ``k=9*2^(3*q)*c-1``.  Each opcode-zero
step consumes exactly three powers of two and multiplies ``c`` by nine.  After
``q`` such steps the collision state is ``3^(2*q+2)*c-1``.  This module
constructs the unique residue class of ``c`` which gives collision opcode
``j`` and emits a fresh clean delay of length ``q_next``.

Every check is exact integer arithmetic.  A finite gate, or a finite chain of
gates, is not an infinite Collatz orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from router_breakoff import literal_step, v2


SCHEMA = "collatz-breakoff-delay-gate-v1"


def breakoff_next(k: int) -> int:
    """Apply one legal break-off step and require its exact router replay."""
    step = literal_step(k)
    if step is None:
        raise AssertionError("illegal break-off state")
    return step.next_k


@dataclass(frozen=True)
class DelayGate:
    delay: int
    collision_opcode: int
    next_delay: int
    coefficient_residue: int
    coefficient_modulus: int
    collision_odd_base: int
    collision_odd_stride: int
    output_coefficient_base: int
    output_coefficient_stride: int

    def member(self, tail: int) -> tuple[int, int, int, int, int]:
        if tail < 0:
            raise ValueError("tail must be nonnegative")
        c = self.coefficient_residue + self.coefficient_modulus * tail
        u = self.collision_odd_base + self.collision_odd_stride * tail
        c_next = (
            self.output_coefficient_base
            + self.output_coefficient_stride * tail
        )
        start = 9 * pow(2, 3 * self.delay) * c - 1
        collision = pow(3, 2 * self.delay + 2) * c - 1
        endpoint = 9 * pow(2, 3 * self.next_delay) * c_next - 1
        return c, u, c_next, start, collision, endpoint


def gate(delay: int, collision_opcode: int, next_delay: int) -> DelayGate:
    """Construct one universal affine delay-to-delay splash family."""
    if delay < 1 or collision_opcode < 0 or next_delay < 1:
        raise ValueError("delays must be positive and opcode nonnegative")
    q = delay
    j = collision_opcode
    q_next = next_delay
    emitted_exponent = 3 * (q_next + 1)
    total_exponent = j + emitted_exponent
    ternary_exponent = j + 2 * q + 2
    modulus = pow(2, total_exponent + 1)

    # Enforce exact valuation total_exponent in
    #   3^(j+2q+2)c + 2^j - 3^j.
    target = (
        pow(3, j)
        - pow(2, j)
        + pow(2, total_exponent)
    ) % modulus
    residue = (
        target * pow(pow(3, ternary_exponent), -1, modulus)
    ) % modulus
    if residue == 0:
        residue = modulus

    collision_numerator = pow(3, 2 * q + 2) * residue - 1
    if v2(collision_numerator) != j:
        raise AssertionError("constructor missed the collision opcode")
    odd_base = collision_numerator >> j
    output_numerator = pow(3, j) * odd_base + 1
    if v2(output_numerator) != emitted_exponent:
        raise AssertionError("constructor missed the regenerated delay")
    output_base = output_numerator >> emitted_exponent

    result = DelayGate(
        delay=q,
        collision_opcode=j,
        next_delay=q_next,
        coefficient_residue=residue,
        coefficient_modulus=modulus,
        collision_odd_base=odd_base,
        collision_odd_stride=(
            pow(2, emitted_exponent + 1) * pow(3, 2 * q + 2)
        ),
        output_coefficient_base=output_base,
        output_coefficient_stride=2 * pow(3, ternary_exponent),
    )
    check_gate_member(result, 0)
    check_gate_member(result, 1)
    return result


def check_gate_member(candidate: DelayGate, tail: int) -> None:
    q = candidate.delay
    j = candidate.collision_opcode
    q_next = candidate.next_delay
    c, u, c_next, start, collision, endpoint = candidate.member(tail)
    if min(c, u, c_next, start, collision, endpoint) <= 0:
        raise AssertionError("delay gate is not positive")
    if collision != pow(2, j) * u or v2(collision) != j:
        raise AssertionError("collision factorization failed")
    if v2(pow(3, j) * u + 1) != 3 * (q_next + 1):
        raise AssertionError("output gap is not exact")
    if (
        pow(2, j + 3 * q_next + 3) * c_next
        != pow(3, j + 2 * q + 2) * c + pow(2, j) - pow(3, j)
    ):
        raise AssertionError("eliminated splash balance failed")

    state = start
    for tick in range(q):
        if v2(state) != 0:
            raise AssertionError("delay cell did not emit opcode zero")
        expected = 9 * pow(2, 3 * (q - tick - 1)) * pow(9, tick + 1) * c - 1
        state = breakoff_next(state)
        if state != expected:
            raise AssertionError("three-bit delay identity failed")
    if state != collision:
        raise AssertionError("delay line missed its collision state")
    if v2(state) != j:
        raise AssertionError("collision emitted the wrong opcode")
    state = breakoff_next(state)
    if state != endpoint:
        raise AssertionError("collision missed the regenerated gap")
    if endpoint != 9 * pow(2, 3 * q_next) * c_next - 1:
        raise AssertionError("endpoint is not a clean delay state")


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(
    max_delay: int,
    max_opcode: int,
    max_next_delay: int,
    replay_tails: int,
) -> dict[str, object]:
    if min(max_delay, max_next_delay, replay_tails) < 1 or max_opcode < 0:
        raise ValueError("invalid audit bounds")
    gates: list[DelayGate] = []
    replays = 0
    for q in range(1, max_delay + 1):
        for j in range(max_opcode + 1):
            for q_next in range(1, max_next_delay + 1):
                candidate = gate(q, j, q_next)
                gates.append(candidate)
                for tail in range(replay_tails):
                    check_gate_member(candidate, tail)
                    replays += 1
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "symbolic affine constructor for every listed (q,j,q_next); "
            "literal exact router/Collatz replay for tails in the stated "
            "bound; no infinite ordinary orbit claim"
        ),
        "bounds": {
            "delay": [1, max_delay],
            "collision_opcode": [0, max_opcode],
            "next_delay": [1, max_next_delay],
            "tails_per_gate": replay_tails,
        },
        "universal_formula": {
            "input": "k=9*2^(3q)*c-1",
            "delay_tick": "9*2^(3q)*c-1 -> 9*2^(3(q-1))*(9c)-1",
            "collision": "3^(2q+2)*c-1=2^j*u, u odd",
            "renewal": "3^j*u+1=2^(3(q_next+1))*c_next, c_next odd",
            "balance": (
                "2^(j+3q_next+3)*c_next="
                "3^(j+2q+2)*c+2^j-3^j"
            ),
            "coefficient_modulus": "2^(j+3q_next+4)",
        },
        "gate_count": len(gates),
        "literal_macro_replays": replays,
        "gates": [asdict(candidate) for candidate in gates],
    }


def selftest() -> None:
    certificate = build_certificate(3, 6, 3, 3)
    if certificate["gate_count"] != 3 * 7 * 3:
        raise AssertionError("selftest gate count changed")
    example = gate(1, 2, 1)
    c, u, c_next, start, collision, endpoint = example.member(0)
    if (c, u, c_next, start, collision, endpoint) != (
        13,
        263,
        37,
        935,
        1052,
        2663,
    ):
        raise AssertionError("small regenerative example changed")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    describe = subparsers.add_parser("describe")
    describe.add_argument("delay", type=int)
    describe.add_argument("collision_opcode", type=int)
    describe.add_argument("next_delay", type=int)
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-delay", type=int, default=8)
    build.add_argument("--max-opcode", type=int, default=16)
    build.add_argument("--max-next-delay", type=int, default=8)
    build.add_argument("--replay-tails", type=int, default=8)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff_delay_gate selftest: PASS")
    elif args.command == "describe":
        print(json.dumps(asdict(gate(
            args.delay, args.collision_opcode, args.next_delay
        )), indent=2))
    elif args.command == "build":
        certificate = build_certificate(
            args.max_delay,
            args.max_opcode,
            args.max_next_delay,
            args.replay_tails,
        )
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["delay"][1]),
            int(bounds["collision_opcode"][1]),
            int(bounds["next_delay"][1]),
            int(bounds["tails_per_gate"]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff delay-gate artifact: PASS")


if __name__ == "__main__":
    main()
