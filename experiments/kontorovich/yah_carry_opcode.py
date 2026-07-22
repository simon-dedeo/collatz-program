#!/usr/bin/env python3
"""Exact carry-defect and run-opcode audit for the YAH Collatz SRS.

The mixed-base auxiliary rules have an almost-symmetry which complements
binary and ternary digits.  The terminal rules break that symmetry by a
positive carry.  This worker isolates the carry exactly and checks several
formula-generated run-length instructions one literal rewrite at a time.

It is not an orbit search.  The finite regressions support a symbolic design
principle: a counterexample compiler must regenerate the token consumed by
the outward max-trit counter instruction.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah


SCHEMA = "yah_carry_opcode_audit_v1"
DIGIT_AFFINE = {
    "a": (2, 0),
    "b": (2, 1),
    "e": (3, 0),
    "f": (3, 1),
    "g": (3, 2),
}
COMPLEMENT = {"a": "b", "b": "a", "e": "g", "f": "f", "g": "e"}


def affine_pair(word: str) -> tuple[int, int]:
    """Return ``(s,t)`` for the digit-word action ``x |-> s*x+t``."""

    slope = 1
    intercept = 0
    for symbol in word:
        if symbol not in DIGIT_AFFINE:
            raise ValueError(f"non-digit in affine word: {word!r}")
        base, digit = DIGIT_AFFINE[symbol]
        slope *= base
        intercept = base * intercept + digit
    return slope, intercept


def compose_pair(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    """Pair for reading the word represented by ``left`` then ``right``."""

    left_slope, left_intercept = left
    right_slope, right_intercept = right
    return (
        right_slope * left_slope,
        right_slope * left_intercept + right_intercept,
    )


def is_saturated(word: str) -> bool:
    """Every digit is maximal in its own base."""

    return all(symbol in "bg" for symbol in word)


def complement_word(word: str) -> str:
    return "".join(COMPLEMENT[symbol] for symbol in word)


def auxiliary_complement_audit() -> dict[str, Any]:
    """Check that digit complement permutes the six A-rules exactly."""

    auxiliary = {
        (rule.lhs, rule.rhs): rule.name
        for rule in yah.RULES
        if rule.family == "A"
    }
    permutation: dict[str, str] = {}
    for rule in yah.RULES:
        if rule.family != "A":
            continue
        mapped = (complement_word(rule.lhs), complement_word(rule.rhs))
        if mapped not in auxiliary:
            raise AssertionError(f"digit complement breaks {rule.name}")
        permutation[rule.name] = auxiliary[mapped]
    if len(permutation) != 6 or any(
        permutation[permutation[name]] != name for name in permutation
    ):
        raise AssertionError("auxiliary complement is not an involution")
    return {
        "digit_map": COMPLEMENT,
        "rule_permutation": dict(sorted(permutation.items())),
        "verdict": "digit complement is an involutive automorphism of subsystem A",
    }


def replay_expected(
    start: str, steps: list[dict[str, Any]], expected: str
) -> dict[str, Any]:
    endpoint, states = yah.replay_trace(start, steps)
    if endpoint != expected:
        raise AssertionError(f"trace ends at {endpoint!r}, expected {expected!r}")
    return {
        "start": start,
        "endpoint": endpoint,
        "step_count": len(steps),
        "maximum_word_length": max(map(len, states)),
        "trace_sha256": yah.sha256_bytes(yah.canonical_json(states)),
    }


def zero_run_pass_trace(n: int) -> tuple[str, list[dict[str, Any]], str]:
    """``bin0 tri0^n . ->+ tri0^n .``."""

    if n < 0:
        raise ValueError("run length must be nonnegative")
    start = "a" + "e" * n + "d"
    steps = [{"rule": "A_f0", "position": i} for i in range(n)]
    steps.append({"rule": "DT_f", "position": n})
    return start, steps, "e" * n + "d"


def max_run_increment_trace(n: int) -> tuple[str, list[dict[str, Any]], str]:
    """``bin1 tri2^n . ->+ tri2^(n+1) .``."""

    if n < 0:
        raise ValueError("run length must be nonnegative")
    start = "b" + "g" * n + "d"
    steps = [{"rule": "A_t2", "position": i} for i in range(n)]
    steps.append({"rule": "DT_t", "position": n})
    return start, steps, "g" * (n + 1) + "d"


def left_transfer_trace(
    zero_count: int, max_count: int
) -> tuple[str, list[dict[str, Any]], str]:
    """Transfer one left zero into a right max-trit counter.

    In paper symbols this is

        / 0^k 2^n . ->+ / 1^(k-1) 2^(n+1) .

    for ``k>=1``.  Exactly one dynamic rule occurs.
    """

    if zero_count < 1 or max_count < 0:
        raise ValueError("need zero_count>=1 and max_count>=0")
    start = "c" + "e" * zero_count + "g" * max_count + "d"
    steps: list[dict[str, Any]] = [{"rule": "B_0", "position": 0}]
    steps.extend(
        {"rule": "A_t0", "position": i}
        for i in range(1, zero_count)
    )
    steps.extend(
        {"rule": "A_t2", "position": i}
        for i in range(zero_count, zero_count + max_count)
    )
    steps.append(
        {"rule": "DT_t", "position": zero_count + max_count}
    )
    endpoint = (
        "c" + "f" * (zero_count - 1) + "g" * (max_count + 1) + "d"
    )
    return start, steps, endpoint


def deterministic_one_dynamic(word: str) -> tuple[str, list[dict[str, Any]]]:
    """Push the rightmost available binary digit to ``.`` and fire once."""

    steps: list[dict[str, Any]] = []
    for _ in range(100_000):
        successors = list(yah.rewrite_successors(word))
        dynamic = [
            item
            for item in successors
            if yah.RULE_BY_NAME[item[0]].family == "DT"
        ]
        if dynamic:
            rule_name, position, endpoint = dynamic[-1]
            steps.append({"rule": rule_name, "position": position})
            return endpoint, steps
        auxiliary = [
            item
            for item in successors
            if yah.RULE_BY_NAME[item[0]].family == "A"
        ]
        if auxiliary:
            rule_name, position, word = max(auxiliary, key=lambda item: item[1])
            steps.append({"rule": rule_name, "position": position})
            continue
        boundary = [
            item
            for item in successors
            if yah.RULE_BY_NAME[item[0]].family == "B"
        ]
        if boundary:
            rule_name, position, word = boundary[0]
            steps.append({"rule": rule_name, "position": position})
            continue
        raise ValueError("word halted before a dynamic step")
    raise RuntimeError("dynamic normalization exceeded its safety bound")


def tri1_max_halving_trace(n: int) -> tuple[str, list[dict[str, Any]], str]:
    """Two dynamic steps turn ``/ 1 2^n .`` into alternating ``02`` pairs."""

    if n < 0:
        raise ValueError("run length must be nonnegative")
    start = "c" + "f" + "g" * n + "d"
    middle, first = deterministic_one_dynamic(start)
    endpoint, second = deterministic_one_dynamic(middle)
    expected = "c" + "eg" * ((n + 1) // 2) + "d"
    if endpoint != expected:
        raise AssertionError(
            f"two-dynamic identity failed at n={n}: {endpoint!r}"
        )
    return start, first + second, expected


def affine_defect_audit(max_length: int) -> dict[str, Any]:
    if max_length < 0:
        raise ValueError("maximum length must be nonnegative")
    by_length: dict[str, dict[str, int]] = {}
    words_checked = 0
    for length in range(max_length + 1):
        count = 0
        saturated_count = 0
        minimum_defect: int | None = None
        maximum_defect = 0
        for symbols in itertools.product(yah.DIGIT_ALPHABET, repeat=length):
            word = "".join(symbols)
            slope, intercept = affine_pair(word)
            defect = slope - intercept
            if defect < 1:
                raise AssertionError("mixed-radix digit intercept reached its slope")
            saturated = is_saturated(word)
            if (defect == 1) != saturated:
                raise AssertionError("defect-one words are not exactly saturated")

            # The complemented image of ``bin0 . -> .`` would require
            # ``bin1 V`` to have the same affine pair as ``V bin0``.
            left = compose_pair(DIGIT_AFFINE["b"], (slope, intercept))
            right = compose_pair((slope, intercept), DIGIT_AFFINE["a"])
            if left[0] != right[0] or left[1] - right[1] != defect:
                raise AssertionError("complement boundary defect identity failed")

            count += 1
            saturated_count += int(saturated)
            minimum_defect = defect if minimum_defect is None else min(
                minimum_defect, defect
            )
            maximum_defect = max(maximum_defect, defect)
        words_checked += count
        by_length[str(length)] = {
            "words": count,
            "saturated_defect_one_words": saturated_count,
            "minimum_defect": minimum_defect if minimum_defect is not None else 0,
            "maximum_defect": maximum_defect,
        }
    return {
        "max_digit_word_length": max_length,
        "words_checked": words_checked,
        "by_length": by_length,
        "identity": (
            "pair(bin1 ++ V).intercept - pair(V ++ bin0).intercept "
            "= slope(V)-intercept(V) >= 1"
        ),
        "symbolic_scope": (
            "the displayed identity is algebraic for every finite digit word; "
            "the artifact exhausts only the stated length bound"
        ),
    }


def run_macro_audit(max_run: int, max_transfer: int) -> dict[str, Any]:
    if max_run < 0 or max_transfer < 1:
        raise ValueError("invalid run bounds")

    zero_samples: dict[str, Any] = {}
    max_samples: dict[str, Any] = {}
    alternating_samples: dict[str, Any] = {}
    for n in range(max_run + 1):
        start, steps, endpoint = zero_run_pass_trace(n)
        meta = replay_expected(start, steps, endpoint)
        if n in {0, 1, max_run}:
            zero_samples[str(n)] = meta

        start, steps, endpoint = max_run_increment_trace(n)
        meta = replay_expected(start, steps, endpoint)
        if n in {0, 1, max_run}:
            max_samples[str(n)] = meta

        start, steps, endpoint = tri1_max_halving_trace(n)
        meta = replay_expected(start, steps, endpoint)
        if n in {0, 1, 2, max_run}:
            alternating_samples[str(n)] = meta

    transfer_cases = 0
    transfer_steps = 0
    transfer_outward_cases = 0
    transfer_samples: dict[str, Any] = {}
    for zero_count in range(1, max_transfer + 1):
        for max_count in range(max_transfer + 1):
            start, steps, endpoint = left_transfer_trace(zero_count, max_count)
            meta = replay_expected(start, steps, endpoint)
            start_value = yah.canonical_value(start)
            endpoint_value = yah.canonical_value(endpoint)
            expected_start = (
                3 ** (zero_count + max_count) + 3**max_count - 1
            )
            expected_endpoint = (
                3 ** (max_count + 1) * (3**zero_count + 1) // 2 - 1
            )
            if start_value != expected_start or endpoint_value != expected_endpoint:
                raise AssertionError("left-transfer value formula failed")
            if 2 * endpoint_value != 3 * start_value + 1:
                raise AssertionError("left transfer is not one shortcut odd step")
            if endpoint_value <= start_value:
                raise AssertionError("left transfer lost outwardness")
            if sum(
                yah.RULE_BY_NAME[step["rule"]].family == "DT" for step in steps
            ) != 1:
                raise AssertionError("left transfer must contain one dynamic step")
            transfer_cases += 1
            transfer_steps += len(steps)
            transfer_outward_cases += 1
            if (zero_count, max_count) in {
                (1, 0),
                (1, max_transfer),
                (max_transfer, max_transfer),
            }:
                meta["canonical_start_value"] = start_value
                meta["canonical_endpoint_value"] = endpoint_value
                transfer_samples[f"{zero_count},{max_count}"] = meta

    return {
        "max_single_run": max_run,
        "max_transfer_coordinate": max_transfer,
        "zero_run_pass_cases": max_run + 1,
        "max_run_increment_cases": max_run + 1,
        "tri1_max_halving_cases": max_run + 1,
        "left_transfer_cases": transfer_cases,
        "left_transfer_outward_cases": transfer_outward_cases,
        "left_transfer_total_replayed_steps": transfer_steps,
        "samples": {
            "zero_run_pass": zero_samples,
            "max_run_increment": max_samples,
            "tri1_max_halving": alternating_samples,
            "left_transfer": transfer_samples,
        },
        "formulae": [
            "bin0 tri0^n . ->+ tri0^n .",
            "bin1 tri2^n . ->+ tri2^(n+1) .",
            "/ tri0^k tri2^n . ->+ / tri1^(k-1) tri2^(n+1) .",
            "/ tri1 tri2^n . ->+ / (tri0 tri2)^ceil(n/2) .",
        ],
        "scope": (
            "every listed bounded instance is literally replayed; the all-n,k "
            "formulae are research-side induction schemas pending Lean replay"
        ),
    }


def worker_sha256() -> str:
    return yah.sha256_bytes(Path(__file__).read_bytes())


def dependency_sha256() -> str:
    return yah.sha256_bytes(Path(yah.__file__).read_bytes())


def build_artifact(max_affine_length: int, max_run: int, max_transfer: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "yah_worker_sha256": dependency_sha256(),
        "upstream": {
            "paper": yah.PAPER_URL,
            "authors_repository_commit": yah.UPSTREAM_COMMIT,
        },
        "rule_table_sha256": yah.sha256_bytes(yah.canonical_json(yah.rule_table())),
        "complement": COMPLEMENT,
        "auxiliary_complement": auxiliary_complement_audit(),
        "affine_boundary_defect": affine_defect_audit(max_affine_length),
        "run_macro_replay": run_macro_audit(max_run, max_transfer),
        "closure_status": {
            "candidate": None,
            "missing_instruction": (
                "the max-trit counter increments only by consuming a binary-one "
                "or a left tri0 token; no rule here regenerates that token"
            ),
        },
    }
    payload = dict(data)
    data["artifact_sha256"] = yah.sha256_bytes(yah.canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema",
        "generated_at_utc",
        "worker_sha256",
        "yah_worker_sha256",
        "upstream",
        "rule_table_sha256",
        "complement",
        "auxiliary_complement",
        "affine_boundary_defect",
        "run_macro_replay",
        "closure_status",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["yah_worker_sha256"] != dependency_sha256():
        raise ValueError("YAH dependency hash mismatch")
    if data["rule_table_sha256"] != yah.sha256_bytes(
        yah.canonical_json(yah.rule_table())
    ):
        raise ValueError("rule table hash mismatch")
    if data["auxiliary_complement"] != auxiliary_complement_audit():
        raise ValueError("auxiliary complement replay mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != yah.sha256_bytes(yah.canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")

    affine_bound = data["affine_boundary_defect"]["max_digit_word_length"]
    if data["affine_boundary_defect"] != affine_defect_audit(affine_bound):
        raise ValueError("affine defect replay mismatch")
    run_data = data["run_macro_replay"]
    rebuilt = run_macro_audit(
        run_data["max_single_run"], run_data["max_transfer_coordinate"]
    )
    if run_data != rebuilt:
        raise ValueError("run macro replay mismatch")
    if data["closure_status"]["candidate"] is not None:
        raise ValueError("unexpected advertised closure candidate")
    return {
        "artifact_sha256": data["artifact_sha256"],
        "worker_sha256": data["worker_sha256"],
        "affine_words": data["affine_boundary_defect"]["words_checked"],
        "run_cases": (
            3 * (run_data["max_single_run"] + 1)
            + run_data["left_transfer_cases"]
        ),
        "candidate": None,
    }


def selftest() -> None:
    if complement_word(complement_word(yah.DIGIT_ALPHABET)) != yah.DIGIT_ALPHABET:
        raise AssertionError("digit complement is not an involution")
    if affine_pair("") != (1, 0) or affine_pair("bgg") != (18, 17):
        raise AssertionError("affine evaluator regression failed")
    for n in range(8):
        for builder in (zero_run_pass_trace, max_run_increment_trace):
            start, steps, endpoint = builder(n)
            replay_expected(start, steps, endpoint)
        start, steps, endpoint = tri1_max_halving_trace(n)
        replay_expected(start, steps, endpoint)
    for k in range(1, 6):
        for n in range(6):
            start, steps, endpoint = left_transfer_trace(k, n)
            replay_expected(start, steps, endpoint)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-affine-length", type=int, default=8)
    build.add_argument("--max-run", type=int, default=128)
    build.add_argument("--max-transfer", type=int, default=32)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "selftest":
        selftest()
        print("selftest: ok")
        return 0
    if args.command == "build":
        selftest()
        artifact = build_artifact(
            args.max_affine_length, args.max_run, args.max_transfer
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
