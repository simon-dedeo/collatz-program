#!/usr/bin/env python3
"""Exact nine-cycle carry audit for one period-three EC17 schedule.

This is the concrete QM119 test case: increment word ``(1,1,0)``, starting
branch ``8``, and source cycles ``q = 0 (mod 9)``, ``q >= 99``.  Nine exact
three-step EC17 cycles force their forward output to be ``13 mod 27``.  The
normalized future residue at cycle ``q+9`` matches that output modulo
``2^(U(q)-M(q))``; its quotient carry is divisible by 27 exactly when the
future residue matches the required mod-27 class.

The worker reconstructs this reduction with exact integers.  A finite run of
nonzero carries is only a theorem-facing diagnostic, never a cofinal result or
a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from breakoff_ether_period3_normalized_margin import sharp_upper_budget_bits
from breakoff_ether_period3_sieve import backward_residue


SCHEMA = "collatz-breakoff-ether-period3-nine-cycle-carry-v1"
WORD = (1, 1, 0)
START_BRANCH = 8
CYCLE_GAIN = 2
MODULUS = 27
REQUIRED_RESIDUE = 13
MINIMUM_SOURCE_CYCLE = 99
CLOCK_PERIOD = 9


@dataclass(frozen=True)
class NineCycleCarryRow:
    source_cycle: int
    target_cycle: int
    source_budget_bits: int
    target_budget_bits: int
    nine_cycle_binary_exponent: int
    nine_cycle_ternary_exponent: int
    carry_precision_bits: int
    source_residue_mod_27: int
    exact_forward_image_mod_27: int
    target_residue_mod_27: int
    carry_mod_27: int
    carry_sign: int
    signed_carry_bits: int
    source_residue_sha256: str
    target_residue_sha256: str
    exact_forward_image_sha256: str
    signed_carry_sha256: str


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def digest_signed(value: int) -> str:
    sign = b"-" if value < 0 else b"+"
    magnitude = abs(value)
    data = magnitude.to_bytes(max(1, (magnitude.bit_length() + 7) // 8), "big")
    return hashlib.sha256(sign + data).hexdigest()


def one_cycle_exponents(cycle: int) -> tuple[int, int]:
    return 277 + 48 * cycle, 195 + 36 * cycle


def one_cycle_defect(cycle: int) -> int:
    return 17 * (
        3 ** (136 + 24 * cycle)
        + 2 ** (87 + 16 * cycle) * 3 ** (71 + 12 * cycle)
        + 2 ** (182 + 32 * cycle)
    )


def compose_nine(cycle: int) -> tuple[int, int, int]:
    """Return ``M,Q,D9`` in ``2^M*y = 3^Q*x + D9``."""

    binary_sum = 0
    ternary_sum = 0
    defect = 0
    for offset in range(9):
        current = cycle + offset
        binary, ternary = one_cycle_exponents(current)
        defect = 3 ** ternary * defect + 2 ** binary_sum * one_cycle_defect(current)
        binary_sum += binary
        ternary_sum += ternary
    if binary_sum != 432 * cycle + 4221:
        raise AssertionError("nine-cycle binary exponent did not close")
    if ternary_sum != 324 * cycle + 3051:
        raise AssertionError("nine-cycle ternary exponent did not close")
    return binary_sum, ternary_sum, defect


def audit_row(cycle: int) -> NineCycleCarryRow:
    if cycle < MINIMUM_SOURCE_CYCLE or cycle % CLOCK_PERIOD:
        raise ValueError("QM119 row requires q >= 99 and q = 0 mod 9")
    target_cycle = cycle + CLOCK_PERIOD
    source_budget = sharp_upper_budget_bits(START_BRANCH, WORD, cycle)
    target_budget = sharp_upper_budget_bits(START_BRANCH, WORD, target_cycle)
    binary, ternary, defect = compose_nine(cycle)
    carry_precision = source_budget - binary
    if carry_precision < 1:
        raise AssertionError("QM119 carry precision is not positive")
    if pow(2, binary, MODULUS) != MODULUS - 1:
        raise AssertionError("nine-cycle binary coefficient is not -1 mod 27")
    if defect % MODULUS != 14:
        raise AssertionError("nine-cycle defect is not 14 mod 27")
    source_residue, _, _ = backward_residue(
        START_BRANCH + CYCLE_GAIN * cycle, WORD, source_budget
    )
    target_residue, _, _ = backward_residue(
        START_BRANCH + CYCLE_GAIN * target_cycle, WORD, target_budget
    )
    numerator = 3 ** ternary * source_residue + defect
    if numerator % (1 << binary):
        raise AssertionError("source residue did not execute nine exact cycles")
    forward_image = numerator >> binary
    if forward_image % MODULUS != REQUIRED_RESIDUE:
        raise AssertionError("exact forward image missed 13 mod 27")
    difference = target_residue - forward_image
    if difference % (1 << carry_precision):
        raise AssertionError("future residues disagree below the carry boundary")
    carry = difference >> carry_precision
    if ((target_residue % MODULUS == REQUIRED_RESIDUE)
            != (carry % MODULUS == 0)):
        raise AssertionError("mod-27 carry equivalence failed")
    return NineCycleCarryRow(
        source_cycle=cycle,
        target_cycle=target_cycle,
        source_budget_bits=source_budget,
        target_budget_bits=target_budget,
        nine_cycle_binary_exponent=binary,
        nine_cycle_ternary_exponent=ternary,
        carry_precision_bits=carry_precision,
        source_residue_mod_27=source_residue % MODULUS,
        exact_forward_image_mod_27=forward_image % MODULUS,
        target_residue_mod_27=target_residue % MODULUS,
        carry_mod_27=carry % MODULUS,
        carry_sign=(carry > 0) - (carry < 0),
        signed_carry_bits=abs(carry).bit_length(),
        source_residue_sha256=digest_natural(source_residue),
        target_residue_sha256=digest_natural(target_residue),
        exact_forward_image_sha256=digest_natural(forward_image),
        signed_carry_sha256=digest_signed(carry),
    )


def row_digest(rows: Iterable[NineCycleCarryRow]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(
            json.dumps(asdict(row), sort_keys=True, separators=(",", ":")).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def scan(minimum_cycle: int, maximum_cycle: int) -> dict[str, Any]:
    if (
        minimum_cycle < MINIMUM_SOURCE_CYCLE
        or minimum_cycle % CLOCK_PERIOD
        or maximum_cycle < minimum_cycle
        or maximum_cycle % CLOCK_PERIOD
    ):
        raise ValueError("cycle endpoints must be multiples of 9 with 99 <= min <= max")
    rows = [
        audit_row(cycle)
        for cycle in range(minimum_cycle, maximum_cycle + 1, CLOCK_PERIOD)
    ]
    return {
        "schema": SCHEMA,
        "schedule": {
            "increment_word": list(WORD),
            "start_branch": START_BRANCH,
            "cycle_gain": CYCLE_GAIN,
        },
        "bounds": {
            "source_cycles": [minimum_cycle, maximum_cycle, CLOCK_PERIOD],
            "target_cycles": [
                minimum_cycle + CLOCK_PERIOD,
                maximum_cycle + CLOCK_PERIOD,
                CLOCK_PERIOD,
            ],
        },
        "exact_rows_checked": len(rows),
        "row_sha256": row_digest(rows),
        "all_exact_forward_images_equal_13_mod_27": all(
            row.exact_forward_image_mod_27 == REQUIRED_RESIDUE for row in rows
        ),
        "all_target_residues_failed_required_mod_27": all(
            row.target_residue_mod_27 != REQUIRED_RESIDUE for row in rows
        ),
        "all_carries_nonzero_mod_27": all(row.carry_mod_27 != 0 for row in rows),
        "minimum_carry_precision_bits": min(
            row.carry_precision_bits for row in rows
        ),
        "rows": [asdict(row) for row in rows],
        "theorem_interface": (
            "QM119: for q >= 99 with q = 0 mod 9, the exact nine-cycle image "
            "is 13 mod 27 and r_(q+9) = 13 mod 27 iff the signed canonical "
            "cross-cycle carry is 0 mod 27"
        ),
        "claim_scope": (
            "finite exact cross-cycle carry rows; all-q nondivisibility by 27 "
            "remains an unproved arithmetic target"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any]) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized nine-cycle carry artifact schema")
    source_cycles = artifact["bounds"]["source_cycles"]
    if source_cycles[2] != CLOCK_PERIOD:
        raise ValueError("unexpected source-cycle step")
    return scan(int(source_cycles[0]), int(source_cycles[1]))


def verify_artifact(path: Path) -> None:
    artifact = json.loads(path.read_text())
    reconstructed = reconstruct(artifact)
    for key, value in reconstructed.items():
        if artifact.get(key) != value:
            raise ValueError(f"artifact mismatch at {key}")
    if artifact.get("counterexample", "missing") is not None:
        raise ValueError("nine-cycle carry artifact claims a counterexample")


def selftest() -> None:
    row = audit_row(99)
    if (
        row.source_budget_bits != 47120
        or row.nine_cycle_binary_exponent != 46989
        or row.carry_precision_bits != 131
        or row.exact_forward_image_mod_27 != 13
        or row.target_residue_mod_27 != 2
        or row.carry_mod_27 != 14
    ):
        raise AssertionError("q=99 QM119 regression changed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("--min-cycle", type=int, default=99)
    build.add_argument("--max-cycle", type=int, default=243)
    build.add_argument("--output", type=Path, required=True)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "selftest":
        selftest()
        print("nine-cycle period-three carry self-test passed")
        return
    if args.command == "build":
        artifact = scan(args.min_cycle, args.max_cycle)
        artifact["generated_at"] = datetime.now(timezone.utc).isoformat()
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps({
            "artifact": str(args.output),
            "exact_rows_checked": artifact["exact_rows_checked"],
            "all_carries_nonzero_mod_27": artifact["all_carries_nonzero_mod_27"],
            "counterexample": artifact["counterexample"],
        }, indent=2, sort_keys=True))
        return
    verify_artifact(args.artifact)
    print("nine-cycle period-three carry artifact verified")


if __name__ == "__main__":
    main()
