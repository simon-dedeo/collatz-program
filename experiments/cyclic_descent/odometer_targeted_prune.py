#!/usr/bin/env python3
"""Exact front-end prunes for the autonomous base-17 counter target.

The target branch schedule is

    m_n = j + 8*17^v17(n+1),             1 <= j <= 8.

Its counter logic is not a search variable.  The carry-height word is the
fixed point of the substitution ``h -> 0^16 (h+1)``.  This module exposes
cheap necessary tests which should run before difference-map optimization or
literal Collatz replay:

* exact odometer/substitution agreement;
* exact dyadic/triadic block-cost identities;
* the defective-Jordan 17-block recurrence;
* bounded ordinary-root exclusion by canonical dyadic residues; and
* direct rejection of an explicitly proposed ordinary root.

Passing any finite test is not evidence of an infinite orbit.  Failing one is
an exact rejection within its stated scope.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "collatz-autonomous-17-adic-targeted-prune-v1"
Z0 = 494_251_421
W0 = 83_499_104
RESONANCE = 473


def v17(value: int) -> int:
    if value <= 0:
        raise ValueError("v17 expects a positive integer")
    result = 0
    while value % 17 == 0:
        value //= 17
        result += 1
    return result


def carry_height(index: int) -> int:
    """Carry height at zero-based odometer time ``index``."""

    if index < 0:
        raise ValueError("index must be nonnegative")
    return v17(index + 1)


def branch(j: int, index: int) -> int:
    if not 1 <= j <= 8:
        raise ValueError("rail j must lie in 1..8")
    return j + 8 * 17 ** carry_height(index)


def substitute_heights(word: Iterable[int]) -> list[int]:
    result: list[int] = []
    for height in word:
        if height < 0:
            raise ValueError("carry heights must be nonnegative")
        result.extend([0] * 16)
        result.append(height + 1)
    return result


def substitution_word(depth: int) -> list[int]:
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    word = [0]
    for _ in range(depth):
        word = substitute_heights(word)
    return word


@dataclass(frozen=True)
class BlockSignature:
    depth: int
    epochs: int
    place_sum: int
    branch_sum: int
    dyadic_cost: int
    triadic_cost: int


def block_signature(j: int, depth: int) -> BlockSignature:
    """Closed signature for the first ``17^depth`` target branches."""

    if not 1 <= j <= 8:
        raise ValueError("rail j must lie in 1..8")
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    epochs = 17**depth
    weighted = 1 if depth == 0 else 17 ** (depth - 1) * (17 + 16 * depth)
    total_branch = j * epochs + 8 * weighted
    dyadic = 8 * total_branch + 15 * epochs
    triadic = 6 * total_branch + 11 * epochs
    return BlockSignature(depth, epochs, weighted, total_branch, dyadic, triadic)


def signature_rejections(j: int, row: BlockSignature) -> list[str]:
    """Return exact reasons why a proposed block signature is impossible."""

    expected = block_signature(j, row.depth)
    failures: list[str] = []
    for field in ("epochs", "place_sum", "branch_sum", "dyadic_cost", "triadic_cost"):
        if getattr(row, field) != getattr(expected, field):
            failures.append(f"{field}_mismatch")
    if 3 * row.dyadic_cost != 4 * row.triadic_cost + row.epochs:
        failures.append("three_S_ne_four_O_plus_epochs")
    decoded = row.dyadic_cost - row.triadic_cost - 4 * row.epochs
    if decoded < 0 or decoded % 2:
        failures.append("aggregate_branch_not_integral")
    elif decoded // 2 != row.branch_sum:
        failures.append("aggregate_branch_mismatch")
    return failures


def jordan_rejections(previous: BlockSignature, current: BlockSignature) -> list[str]:
    """Check one exact 17-block renormalization step."""

    failures: list[str] = []
    if current.depth != previous.depth + 1:
        failures.append("nonconsecutive_depth")
    if current.epochs != 17 * previous.epochs:
        failures.append("epoch_not_times_17")
    if current.place_sum != 17 * previous.place_sum + 16 * previous.epochs:
        failures.append("place_sum_jordan_failure")
    if current.dyadic_cost != 17 * previous.dyadic_cost + 1024 * previous.epochs:
        failures.append("dyadic_jordan_failure")
    if current.triadic_cost != 17 * previous.triadic_cost + 768 * previous.epochs:
        failures.append("triadic_jordan_failure")
    return failures


def branch_delta(m: int) -> int:
    if m <= 0:
        raise ValueError("branch must be positive")
    raw = 3 ** (6 * m) * W0 - 2 ** (8 * m - 5) * Z0
    if raw <= 0 or raw % RESONANCE:
        raise AssertionError("public branch defect identity failed")
    return raw // RESONANCE


@dataclass(frozen=True)
class ResetData:
    dyadic_cost: int = 0
    triadic_cost: int = 0
    defect: int = 0


def append_reset(data: ResetData, target: int) -> ResetData:
    """Compose ``2^S q'=3^O q+D`` with one public reset."""

    binary = 8 * target + 15
    ternary = 6 * target + 11
    delta = branch_delta(target)
    return ResetData(
        data.dyadic_cost + binary,
        data.triadic_cost + ternary,
        3**ternary * data.defect + 2**data.dyadic_cost * delta,
    )


def canonical_residue(data: ResetData) -> int:
    modulus = 1 << data.dyadic_cost
    return (-data.defect * pow(3**data.triadic_cost, -1, modulus)) % modulus


@dataclass(frozen=True)
class RootCapResult:
    rail: int
    bit_cap: int
    rejected: bool
    decisive_depth: int | None
    targets_checked: int
    residue_bit_length: int
    written_bits: int


def prune_root_cap(j: int, bit_cap: int, maximum_steps: int) -> RootCapResult:
    """Reject every initial payload below ``2^bit_cap`` if possible."""

    if bit_cap <= 0 or maximum_steps <= 0:
        raise ValueError("bit cap and maximum steps must be positive")
    data = ResetData()
    residue = 0
    for index in range(maximum_steps):
        data = append_reset(data, branch(j, index))
        residue = canonical_residue(data)
        if residue >= 1 << bit_cap:
            return RootCapResult(j, bit_cap, True, index + 1, index + 1,
                                 residue.bit_length(), data.dyadic_cost)
    return RootCapResult(j, bit_cap, False, None, maximum_steps,
                         residue.bit_length(), data.dyadic_cost)


@dataclass(frozen=True)
class ExplicitRootResult:
    accepted_steps: int
    first_failed_target: int | None
    final_payload: str


def prune_explicit_root(q0: int, j: int, maximum_steps: int) -> ExplicitRootResult:
    """Literally replay a proposed public payload until divisibility fails."""

    if q0 < 0 or maximum_steps <= 0:
        raise ValueError("root must be nonnegative and steps positive")
    q = q0
    for index in range(maximum_steps):
        target = branch(j, index)
        numerator = 3 ** (6 * target + 11) * q + branch_delta(target)
        denominator = 1 << (8 * target + 15)
        if numerator % denominator:
            return ExplicitRootResult(index, target, str(q))
        q = numerator // denominator
    return ExplicitRootResult(maximum_steps, None, str(q))


def build_audit(maximum_depth: int, root_caps: list[int], root_steps: int) -> dict[str, Any]:
    if maximum_depth < 1:
        raise ValueError("maximum depth must be at least one")
    substitution_checks = []
    for depth in range(min(maximum_depth, 4) + 1):
        word = substitution_word(depth)
        direct = [carry_height(index) for index in range(17**depth)]
        if word != direct:
            raise AssertionError("base-17 substitution stopped matching v17")
        substitution_checks.append({"depth": depth, "symbols": len(word)})

    rails: list[dict[str, Any]] = []
    mutation_rejections = 0
    for j in range(1, 9):
        rows = [block_signature(j, depth) for depth in range(maximum_depth + 1)]
        for row in rows:
            if signature_rejections(j, row):
                raise AssertionError("true ruler signature rejected")
            for field in ("epochs", "place_sum", "branch_sum", "dyadic_cost", "triadic_cost"):
                changed = asdict(row)
                changed[field] += 1
                if not signature_rejections(j, BlockSignature(**changed)):
                    raise AssertionError(f"mutated {field} escaped signature prune")
                mutation_rejections += 1
        for left, right in zip(rows, rows[1:]):
            if jordan_rejections(left, right):
                raise AssertionError("true Jordan block rejected")
        rails.append({
            "j": j,
            "signatures": [asdict(row) for row in rows],
            "root_caps": [asdict(prune_root_cap(j, cap, root_steps)) for cap in root_caps],
        })

    return {
        "schema": SCHEMA,
        "audit": {
            "counter_language": "sigma(h)=0^16,(h+1)",
            "branch_language": "m(h)=j+8*17^h; m(h+1)=17*m(h)-16*j",
            "epoch_signature": "S=8*sum(m)+15*N; O=6*sum(m)+11*N; 3*S=4*O+N",
            "jordan_prune": "N'=17*N; A'=17*A+16*N; S'=17*S+1024*N; O'=17*O+768*N",
            "ordinary_prune": (
                "for an asserted root q0<2^B, reject as soon as the monotone "
                "canonical prefix residue is at least 2^B"
            ),
            "substitution_checks": substitution_checks,
            "mutation_rejections": mutation_rejections,
            "rails": rails,
            "counterexample": None,
            "scope": (
                "necessary exact front-end filters only; a surviving bounded "
                "root cap or exact block signature is not an infinite orbit"
            ),
        },
    }


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def write_artifact(path: Path, maximum_depth: int, root_caps: list[int], root_steps: int) -> None:
    artifact = build_audit(maximum_depth, root_caps, root_steps)
    artifact["worker_sha256"] = source_sha256()
    artifact["artifact_sha256"] = hashlib.sha256(canonical_json(artifact["audit"])).hexdigest()
    path.write_bytes(json.dumps(artifact, indent=2, sort_keys=True).encode() + b"\n")


def verify_artifact(path: Path) -> None:
    artifact = json.loads(path.read_text())
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unsupported targeted-prune schema")
    rails = artifact["audit"]["rails"]
    maximum_depth = len(rails[0]["signatures"]) - 1
    root_caps = [row["bit_cap"] for row in rails[0]["root_caps"]]
    root_steps = max(row["targets_checked"] for rail in rails for row in rail["root_caps"])
    rebuilt = build_audit(maximum_depth, root_caps, root_steps)
    if rebuilt["audit"] != artifact["audit"]:
        raise AssertionError("targeted-prune artifact reconstruction failed")
    if artifact.get("worker_sha256") != source_sha256():
        raise AssertionError("targeted-prune worker hash mismatch")
    expected_hash = hashlib.sha256(canonical_json(artifact["audit"])).hexdigest()
    if artifact.get("artifact_sha256") != expected_hash:
        raise AssertionError("targeted-prune artifact hash mismatch")


def parse_caps(value: str) -> list[int]:
    caps = [int(part) for part in value.split(",") if part]
    if not caps or any(cap <= 0 for cap in caps):
        raise argparse.ArgumentTypeError("caps must be comma-separated positive integers")
    return caps


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-depth", type=int, default=5)
    build.add_argument("--root-caps", type=parse_caps, default=parse_caps("64,128,256"))
    build.add_argument("--root-steps", type=int, default=12)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    root = subparsers.add_parser("root")
    root.add_argument("q0", type=int)
    root.add_argument("--rail", type=int, default=1)
    root.add_argument("--steps", type=int, default=64)
    args = parser.parse_args()
    if args.command == "build":
        write_artifact(args.output, args.maximum_depth, args.root_caps, args.root_steps)
        print(json.dumps({"output": str(args.output), "status": "built"}, sort_keys=True))
    elif args.command == "verify":
        verify_artifact(args.artifact)
        print("autonomous 17-adic targeted-prune verification: PASS")
    else:
        print(json.dumps(asdict(prune_explicit_root(args.q0, args.rail, args.steps)), sort_keys=True))


if __name__ == "__main__":
    main()
