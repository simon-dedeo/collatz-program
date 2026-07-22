#!/usr/bin/env python3
"""Exact symbolic checker for the autonomous router break-off counter.

Write ``k=2^j*u`` with ``u`` odd.  On the invariant class ``k=8 (mod 9)``,
one universal outward router step is equivalent to

    8*k' = 3^(j+2)*u + 1.

For each opcode ``j`` the legal ``u`` form one residue class modulo 72, and
the output is an affine ternary write.  This checker exposes that complete
branch grammar and translates literal members back to exact Collatz splash
states.  It does not assert that any ordinary orbit survives forever.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from complete_splash_isa import decode_payload, verify_member


SCHEMA = "collatz-router-breakoff-v1"


def v2(value: int) -> int:
    if value <= 0:
        raise ValueError("v2 expects a positive integer")
    return (value & -value).bit_length() - 1


def v3(value: int) -> int:
    if value <= 0:
        raise ValueError("v3 expects a positive integer")
    exponent = 0
    while value % 3 == 0:
        value //= 3
        exponent += 1
    return exponent


@dataclass(frozen=True)
class BreakoffBranch:
    opcode: int
    odd_payload_residue: int
    odd_payload_modulus: int
    input_base: int
    input_stride: int
    output_base: int
    output_stride: int

    def member(self, tail: int) -> tuple[int, int, int]:
        if tail < 0:
            raise ValueError("tail must be nonnegative")
        u = self.odd_payload_residue + self.odd_payload_modulus * tail
        k = self.input_base + self.input_stride * tail
        next_k = self.output_base + self.output_stride * tail
        return u, k, next_k


def branch(opcode: int) -> BreakoffBranch:
    """Construct the complete affine branch with ``v2(k)=opcode``."""
    if opcode < 0:
        raise ValueError("opcode must be nonnegative")
    target_mod_eight = 7 if opcode % 2 == 0 else 5
    target_mod_nine = (
        8 * pow(pow(2, opcode, 9), -1, 9)
    ) % 9
    residue = next(
        u
        for u in range(1, 72, 2)
        if u % 8 == target_mod_eight and u % 9 == target_mod_nine
    )
    output_numerator = pow(3, opcode + 2) * residue + 1
    if output_numerator % 8:
        raise AssertionError("CRT branch did not make an integral output")
    result = BreakoffBranch(
        opcode=opcode,
        odd_payload_residue=residue,
        odd_payload_modulus=72,
        input_base=pow(2, opcode) * residue,
        input_stride=pow(2, opcode) * 72,
        output_base=output_numerator // 8,
        output_stride=pow(3, opcode + 4),
    )
    check_branch(result)
    return result


def check_branch(candidate: BreakoffBranch) -> None:
    j = candidate.opcode
    if candidate.odd_payload_modulus != 72:
        raise AssertionError("unexpected branch modulus")
    for tail in (0, 1):
        u, k, next_k = candidate.member(tail)
        if u <= 0 or u % 2 == 0:
            raise AssertionError("branch payload is not positive odd")
        if k != pow(2, j) * u or v2(k) != j or k % 9 != 8:
            raise AssertionError("branch input factorization failed")
        if 8 * next_k != pow(3, j + 2) * u + 1:
            raise AssertionError("break-off equation failed")
        if next_k % 9 != 8 or next_k <= k:
            raise AssertionError("branch lost renewal or growth")


@dataclass(frozen=True)
class LiteralStep:
    k: int
    opcode: int
    odd_payload: int
    next_k: int
    rail_length: int
    payload: int
    next_rail_length: int
    next_payload: int
    collatz_start: int
    collatz_endpoint: int
    valuation_word: list[int]


def literal_step(k: int) -> LiteralStep | None:
    """Decode one legal break-off step and replay its Collatz router."""
    if k <= 0 or k % 9 != 8:
        raise ValueError("expected a positive k congruent to 8 modulo 9")
    j = v2(k)
    u = k >> j
    numerator = pow(3, j + 2) * u + 1
    if numerator % 8:
        return None
    next_k = numerator // 8
    if next_k % 9 != 8 or next_k <= k:
        raise AssertionError("literal step lost invariant growth")

    y = 8 * k - 1
    exponent_three = v3(y)
    if exponent_three < 2:
        raise AssertionError("mod-nine invariant lost two factors of three")
    r = exponent_three - 2
    h = y // pow(3, exponent_three)
    p = 3 * h
    p_next = 3 * u
    if 8 * next_k - 1 != pow(3, j + 2) * u:
        raise AssertionError("next sparse coordinates failed")
    if (
        pow(2, j + 3) * p_next
        != pow(3, r + 2) * p + 3
    ):
        raise AssertionError("router payload recurrence failed")

    decoded = decode_payload(r, p)
    if decoded is None:
        raise AssertionError("legal break-off step decoded as halt")
    gate, family_index = decoded
    if (
        gate.branch != "odd_catcher"
        or gate.clean_ticks != 0
        or gate.to_plus_extra != 1
        or gate.output_gap != j + 1
    ):
        raise AssertionError("canonical decoder chose the wrong router")
    start, endpoint = verify_member(gate, family_index)
    expected_start = -1 + pow(2, r + 1) * p
    expected_endpoint = -1 + pow(2, j + 1) * p_next
    if start != expected_start or endpoint != expected_endpoint:
        raise AssertionError("Collatz sparse endpoints disagree")
    if endpoint <= start:
        raise AssertionError("universal router stopped growing")
    return LiteralStep(
        k=k,
        opcode=j,
        odd_payload=u,
        next_k=next_k,
        rail_length=r,
        payload=p,
        next_rail_length=j,
        next_payload=p_next,
        collatz_start=start,
        collatz_endpoint=endpoint,
        valuation_word=[1] * r + [2, 1],
    )


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(max_opcode: int, replay_tails: int) -> dict[str, object]:
    if max_opcode < 0 or replay_tails < 1:
        raise ValueError("invalid audit bounds")
    branches = [branch(j) for j in range(max_opcode + 1)]
    literal_replays = 0
    for candidate in branches:
        for tail in range(replay_tails):
            _, k, next_k = candidate.member(tail)
            step = literal_step(k)
            if step is None or step.next_k != next_k:
                raise AssertionError("affine member failed literal replay")
            literal_replays += 1
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "complete symbolic branch formula for each listed opcode; "
            "literal exact Collatz replay only for tails in the stated bound; "
            "no infinite ordinary orbit claim"
        ),
        "bounds": {
            "opcodes": [0, max_opcode],
            "tails_per_opcode": replay_tails,
        },
        "universal_formula": {
            "input": "k=2^j*u, u odd, k=8 mod 9",
            "transition": "8*k'=3^(j+2)*u+1",
            "legal_u_mod_8": "7 if j even; 5 if j odd",
            "output": "k'=8 mod 9 and k'>k",
            "affine_tail": "u=u_j+72*t; k'=b_j+3^(j+4)*t",
        },
        "literal_replays": literal_replays,
        "branches": [asdict(candidate) for candidate in branches],
    }


def selftest() -> None:
    certificate = build_certificate(32, 32)
    if certificate["literal_replays"] != 33 * 32:
        raise AssertionError("selftest replay count changed")
    for k in range(8, 1 << 16, 9):
        step = literal_step(k)
        candidate = branch(v2(k))
        u = k >> v2(k)
        legal = (
            (u - candidate.odd_payload_residue)
            % candidate.odd_payload_modulus
            == 0
        )
        if (step is not None) != legal:
            raise AssertionError("bounded converse disagrees with branch")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    describe = subparsers.add_parser("describe")
    describe.add_argument("k", type=int)
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-opcode", type=int, default=64)
    build.add_argument("--replay-tails", type=int, default=64)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("router_breakoff selftest: PASS")
    elif args.command == "describe":
        step = literal_step(args.k)
        print(json.dumps(None if step is None else asdict(step), indent=2))
    elif args.command == "build":
        certificate = build_certificate(args.max_opcode, args.replay_tails)
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["opcodes"][1]), int(bounds["tails_per_opcode"])
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("router_breakoff artifact: PASS")


if __name__ == "__main__":
    main()
