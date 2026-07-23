#!/usr/bin/env python3
"""Exact rational reconstruction probe for period-three EC17 residues.

For every positive period-three schedule in the configured finite box, this
worker computes the canonical future-forced core residue at cycle boundary
``q = 0`` modulo ``2^2048`` and ``2^4096``.  Each residue is computed both by
backward substitution and by the independent direct-series formula.

At each precision it then asks whether the residue is represented by a
reduced signed rational ``a / b`` with

    |a| <= 2^512,  0 < b <= 2^512,  b odd.

The strict gate ``2*A*B < 2^P`` makes such a bounded reconstruction unique.
A schedule is recorded as a rational candidate only when the same reduced
pair is reconstructed at both precisions.  Even such a repeated finite pair
would remain a lead rather than a theorem about the infinite 2-adic series.
In particular, this worker never reports a Collatz counterexample without a
separate proof that a positive denominator-one candidate satisfies the
entire infinite EC17 recurrence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from math import gcd
from pathlib import Path
from typing import Any, Iterable, Sequence

from breakoff_ether_period3_normalized_margin import words_in_box
from breakoff_ether_period3_sieve import (
    backward_residue,
    direct_series_residue,
    stays_positive,
)


SCHEMA = "collatz-breakoff-ether-period3-rational-reconstruction-v1"
INCREMENT_ABS_BOUND = 1
MAX_START_BRANCH = 8
CYCLE_BOUNDARY = 0
PRECISIONS = (2048, 4096)
NUMERATOR_BOUND_BITS = 512
DENOMINATOR_BOUND_BITS = 512
NUMERATOR_BOUND = 1 << NUMERATOR_BOUND_BITS
DENOMINATOR_BOUND = 1 << DENOMINATOR_BOUND_BITS


@dataclass(frozen=True)
class ReconstructionRow:
    precision_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    residue_bits: int
    residue_sha256: str
    backward_equals_direct: bool
    uniqueness_gate_passed: bool
    reconstructed_numerator: int | None
    reconstructed_denominator: int | None


@dataclass(frozen=True)
class ScheduleResult:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    rows: tuple[ReconstructionRow, ...]
    repeated_pair_at_both_precisions: bool
    repeated_numerator: int | None
    repeated_denominator: int | None
    repeated_pair_is_positive_integer: bool


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def rational_reconstruct(
    residue: int,
    precision_bits: int,
    numerator_bound: int,
    denominator_bound: int,
) -> tuple[int, int] | None:
    """Return the unique bounded reduced rational represented modulo ``2^P``.

    The extended Euclidean loop is the standard rational-reconstruction
    algorithm.  The strict ``2*A*B < modulus`` hypothesis guarantees that two
    distinct rationals in the stated box cannot represent the same residue.
    """

    if min(precision_bits, numerator_bound, denominator_bound) < 1:
        raise ValueError("rational-reconstruction bounds must be positive")
    modulus = 1 << precision_bits
    if not 0 <= residue < modulus:
        raise ValueError("residue escaped its canonical range")
    if not 2 * numerator_bound * denominator_bound < modulus:
        raise ValueError("rational-reconstruction uniqueness gate failed")
    if residue == 0:
        return (0, 1)

    old_remainder, remainder = modulus, residue
    old_coefficient, coefficient = 0, 1
    while remainder > numerator_bound:
        quotient = old_remainder // remainder
        old_remainder, remainder = (
            remainder,
            old_remainder - quotient * remainder,
        )
        old_coefficient, coefficient = (
            coefficient,
            old_coefficient - quotient * coefficient,
        )

    numerator = remainder
    denominator = coefficient
    if denominator < 0:
        numerator = -numerator
        denominator = -denominator
    if not (
        abs(numerator) <= numerator_bound
        and 0 < denominator <= denominator_bound
        and denominator % 2 == 1
        and gcd(abs(numerator), denominator) == 1
        and (denominator * residue - numerator) % modulus == 0
    ):
        return None
    return numerator, denominator


def audit_precision(
    start_branch: int,
    word: Sequence[int],
    precision_bits: int,
) -> ReconstructionRow:
    if precision_bits not in PRECISIONS:
        raise ValueError("unexpected rational-reconstruction precision")
    residue, transitions, accumulated = backward_residue(
        start_branch, word, precision_bits
    )
    direct = direct_series_residue(start_branch, word, precision_bits)
    if residue != direct:
        raise AssertionError("backward and direct future residues disagree")
    pair = rational_reconstruct(
        residue,
        precision_bits,
        NUMERATOR_BOUND,
        DENOMINATOR_BOUND,
    )
    return ReconstructionRow(
        precision_bits=precision_bits,
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        residue_bits=residue.bit_length(),
        residue_sha256=digest_natural(residue),
        backward_equals_direct=True,
        uniqueness_gate_passed=(
            2 * NUMERATOR_BOUND * DENOMINATOR_BOUND < 1 << precision_bits
        ),
        reconstructed_numerator=None if pair is None else pair[0],
        reconstructed_denominator=None if pair is None else pair[1],
    )


def audit_schedule(start_branch: int, word: Sequence[int]) -> ScheduleResult:
    normalized_word = tuple(int(value) for value in word)
    if len(normalized_word) != 3 or not stays_positive(
        start_branch, normalized_word
    ):
        raise ValueError("invalid positive period-three schedule")
    rows = tuple(
        audit_precision(start_branch, normalized_word, precision)
        for precision in PRECISIONS
    )
    pairs = tuple(
        None
        if row.reconstructed_numerator is None
        else (row.reconstructed_numerator, row.reconstructed_denominator)
        for row in rows
    )
    repeated = pairs[0] is not None and pairs[0] == pairs[1]
    pair = pairs[0] if repeated else None
    return ScheduleResult(
        increment_word=normalized_word,
        start_branch=start_branch,
        cycle_gain=sum(normalized_word),
        rows=rows,
        repeated_pair_at_both_precisions=repeated,
        repeated_numerator=None if pair is None else pair[0],
        repeated_denominator=None if pair is None else pair[1],
        repeated_pair_is_positive_integer=(
            pair is not None and pair[1] == 1 and pair[0] > 0
        ),
    )


def row_dict(row: ReconstructionRow) -> dict[str, Any]:
    return asdict(row)


def schedule_dict(result: ScheduleResult) -> dict[str, Any]:
    return {
        "increment_word": list(result.increment_word),
        "start_branch": result.start_branch,
        "cycle_gain": result.cycle_gain,
        "rows": [row_dict(row) for row in result.rows],
        "repeated_pair_at_both_precisions": (
            result.repeated_pair_at_both_precisions
        ),
        "repeated_numerator": result.repeated_numerator,
        "repeated_denominator": result.repeated_denominator,
        "repeated_pair_is_positive_integer": (
            result.repeated_pair_is_positive_integer
        ),
    }


def result_digest(results: Iterable[ScheduleResult]) -> str:
    digest = hashlib.sha256()
    for result in results:
        digest.update(
            json.dumps(
                schedule_dict(result), sort_keys=True, separators=(",", ":")
            ).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def scan() -> dict[str, Any]:
    words = words_in_box(INCREMENT_ABS_BOUND)
    schedules = [
        (word, start)
        for word in words
        for start in range(1, MAX_START_BRANCH + 1)
        if stays_positive(start, word)
    ]
    results = [audit_schedule(start, word) for word, start in schedules]
    candidates = [
        {
            "increment_word": list(result.increment_word),
            "start_branch": result.start_branch,
            "numerator": result.repeated_numerator,
            "denominator": result.repeated_denominator,
            "positive_integer": result.repeated_pair_is_positive_integer,
            "status": "finite_repeated_rational_reconstruction_only",
        }
        for result in results
        if result.repeated_pair_at_both_precisions
    ]
    if len(results) != 71:
        raise AssertionError("configured period-three box no longer has 71 schedules")
    if any(not row.backward_equals_direct for result in results for row in result.rows):
        raise AssertionError("independent residue check was lost")
    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [
                -INCREMENT_ABS_BOUND,
                INCREMENT_ABS_BOUND,
            ],
            "start_branches": [1, MAX_START_BRANCH],
            "cycle_boundary": CYCLE_BOUNDARY,
            "precision_bits": list(PRECISIONS),
            "signed_numerator_absolute_bound": NUMERATOR_BOUND,
            "positive_odd_denominator_bound": DENOMINATOR_BOUND,
            "numerator_bound_bits": NUMERATOR_BOUND_BITS,
            "denominator_bound_bits": DENOMINATOR_BOUND_BITS,
        },
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(results),
        "exact_residue_rows_checked": len(results) * len(PRECISIONS),
        "schedule_sha256": result_digest(results),
        "all_backward_residues_equal_direct_series": True,
        "all_uniqueness_gates_passed": all(
            row.uniqueness_gate_passed
            for result in results
            for row in result.rows
        ),
        "single_precision_reconstructions": sum(
            row.reconstructed_numerator is not None
            for result in results
            for row in result.rows
        ),
        "repeated_rational_candidate_count": len(candidates),
        "repeated_positive_integer_candidate_count": sum(
            bool(candidate["positive_integer"]) for candidate in candidates
        ),
        "candidates": candidates,
        "schedule_results": [schedule_dict(result) for result in results],
        "claim_scope": (
            "finite exact 2-adic rational reconstruction at q=0 and the two "
            "displayed precisions; a repeated pair would not prove equality "
            "to the infinite future series or an infinite EC17 recurrence"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any]) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized rational-reconstruction artifact schema")
    bounds = artifact.get("bounds", {})
    expected = {
        "increment_components": [-1, 1],
        "start_branches": [1, 8],
        "cycle_boundary": 0,
        "precision_bits": [2048, 4096],
        "signed_numerator_absolute_bound": NUMERATOR_BOUND,
        "positive_odd_denominator_bound": DENOMINATOR_BOUND,
        "numerator_bound_bits": 512,
        "denominator_bound_bits": 512,
    }
    if bounds != expected:
        raise ValueError("artifact bounds do not match the audited probe")
    return scan()


def verify_artifact(path: Path) -> None:
    artifact = json.loads(path.read_text())
    rebuilt = reconstruct(artifact)
    for key, value in rebuilt.items():
        if artifact.get(key) != value:
            raise ValueError(f"artifact mismatch at {key}")
    if artifact.get("counterexample", "missing") is not None:
        raise ValueError("finite rational reconstruction claims a counterexample")


def selftest() -> None:
    precision = 128
    bound = 1 << 24
    modulus = 1 << precision
    for numerator, denominator in (
        (17, 3),
        (-17, 3),
        (1_234_567, 99_991),
        (-1_234_567, 99_991),
    ):
        residue = numerator * pow(denominator, -1, modulus) % modulus
        if rational_reconstruct(
            residue, precision, bound, bound
        ) != (numerator, denominator):
            raise AssertionError("known rational failed reconstruction")
    if rational_reconstruct(0, precision, bound, bound) != (0, 1):
        raise AssertionError("zero rational failed reconstruction")

    # Exhaust the small uniqueness box, including negative numerators.  This
    # checks completeness rather than only recognition of a few examples.
    small_precision = 16
    small_bound = 16
    small_modulus = 1 << small_precision
    for denominator in range(1, small_bound + 1, 2):
        for numerator in range(-small_bound, small_bound + 1):
            if gcd(abs(numerator), denominator) != 1:
                continue
            residue = (
                numerator * pow(denominator, -1, small_modulus)
            ) % small_modulus
            if rational_reconstruct(
                residue,
                small_precision,
                small_bound,
                small_bound,
            ) != (numerator, denominator):
                raise AssertionError("small rational box failed reconstruction")
    try:
        rational_reconstruct(1, 16, 1 << 8, 1 << 8)
    except ValueError:
        pass
    else:
        raise AssertionError("failed uniqueness gate was accepted")

    word = (1, 1, 0)
    start = 8
    test_precision = 256
    backward, _, _ = backward_residue(start, word, test_precision)
    direct = direct_series_residue(start, word, test_precision)
    if backward != direct:
        raise AssertionError("independent residue self-test failed")


def write_artifact(path: Path, artifact: dict[str, Any]) -> None:
    result = dict(artifact)
    result["generated_at"] = datetime.now(timezone.utc).isoformat()
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("--output", type=Path, required=True)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "selftest":
        selftest()
        print("period-three rational-reconstruction self-test passed")
        return
    if args.command == "build":
        selftest()
        artifact = scan()
        write_artifact(args.output, artifact)
        print(json.dumps({
            "artifact": str(args.output),
            "positive_schedules_checked": artifact[
                "positive_schedules_checked"
            ],
            "exact_residue_rows_checked": artifact[
                "exact_residue_rows_checked"
            ],
            "repeated_rational_candidate_count": artifact[
                "repeated_rational_candidate_count"
            ],
            "counterexample": artifact["counterexample"],
        }, indent=2, sort_keys=True))
        return
    verify_artifact(args.artifact)
    print("period-three rational-reconstruction artifact verified")


if __name__ == "__main__":
    main()
