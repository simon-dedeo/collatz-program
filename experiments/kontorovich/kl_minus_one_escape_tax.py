#!/usr/bin/env python3
"""Exact finite audit of the KL-calibrated minus-one escape tax.

The research theorem in ``docs/notes/kl-calibrated-escape.md`` says that an
outward edge which leaves a critical KL minimizing policy must pay for its
positive time shift through a potential ratio.  The pure class-8 self-loop at
the 3-adic point ``-1`` is the canonical test case.

This worker does not solve for a critical eigenvector.  It reads the already
certified rational KL subeigenvectors at levels 12 through 19, SHA-checks every
sidecar, and makes only exact integer comparisons on the fiber above ``-1``.
The reported approach to equality is finite evidence, not an asymptotic
theorem and not a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
KL_DIR = ROOT / "experiments" / "kl"
DEFAULT_ARTIFACT = Path(__file__).with_name("kl_minus_one_escape_tax_audit.json")
LEVELS = tuple(range(12, 20))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def reduced_pair(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def load_certificate(level: int) -> tuple[dict[str, Any], Any, dict[str, str]]:
    cert_path = KL_DIR / f"cert_k{level}.json"
    with cert_path.open() as handle:
        cert = json.load(handle)
    if cert["k"] != level:
        raise AssertionError(f"level mismatch in {cert_path}")

    inputs = {"certificate": str(cert_path.relative_to(ROOT)),
              "certificate_sha256": sha256(cert_path)}
    if "C" in cert:
        vector = cert["C"]
    else:
        vector_path = cert_path.with_name(cert["C_file"])
        actual_hash = sha256(vector_path)
        if actual_hash != cert["C_sha256"]:
            raise AssertionError(f"sidecar hash mismatch at level {level}")
        vector = np.load(vector_path, mmap_mode="r")
        inputs.update({"vector": str(vector_path.relative_to(ROOT)),
                       "vector_sha256": actual_hash})
    if len(vector) != 3 ** (level - 1):
        raise AssertionError(f"wrong vector length at level {level}")
    return cert, vector, inputs


def c_at(vector: Any, state: int) -> int:
    if state < 2 or state % 3 != 2:
        raise AssertionError(f"invalid KL state {state}")
    return int(vector[(state - 2) // 3])


def vector_extrema(vector: Any) -> tuple[int, int]:
    """Return exact extrema for either an inline list or an mmap sidecar."""
    if isinstance(vector, np.ndarray):
        return int(vector.min()), int(vector.max())
    return min(vector), max(vector)


def audit_level(level: int) -> dict[str, Any]:
    cert, vector, inputs = load_certificate(level)
    modulus = 3 ** level
    parent_modulus = 3 ** (level - 1)

    # The parent of -1 is -1 modulo 3^(k-1).  Its three canonical lifts are
    # 3^(k-1)-1, 2*3^(k-1)-1, and 3^k-1; the last is the self-lift -1.
    lift_states = [
        parent_modulus - 1,
        2 * parent_modulus - 1,
        modulus - 1,
    ]
    lift_values = [c_at(vector, state) for state in lift_states]
    minimum = min(lift_values)
    minimum_lift = lift_values.index(minimum)
    self_value = lift_values[2]
    potential_minimum, potential_maximum = vector_extrema(vector)
    condition_number = Fraction(potential_maximum, potential_minimum)

    deviation = Fraction(self_value, minimum)
    certified_weight = Fraction(cert["B8"], cert["SC_W"])
    surplus = deviation / certified_weight
    cross_margin = self_value * cert["SC_W"] - minimum * cert["B8"]
    if cross_margin <= 0:
        raise AssertionError(f"minus-one deviation misses B8 at level {level}")

    return {
        "level": level,
        "inputs": inputs,
        "lambda_lower": reduced_pair(Fraction(cert["A"], cert["SC_L"])),
        "class8_weight_lower": reduced_pair(certified_weight),
        "lift_states": lift_states,
        "lift_values": lift_values,
        "minimum_lift_index": minimum_lift,
        "self_lift_index": 2,
        "potential_minimum": potential_minimum,
        "potential_maximum": potential_maximum,
        "potential_condition_number": reduced_pair(condition_number),
        "potential_condition_number_decimal": format(
            float(condition_number), ".15g"
        ),
        "deviation_factor": reduced_pair(deviation),
        "deviation_over_weight": reduced_pair(surplus),
        "deviation_over_weight_decimal": format(float(surplus), ".15g"),
        "strict_cross_margin": cross_margin,
    }


def verify_minus_one_rail(length: int, payload: int) -> None:
    if length <= 0 or payload <= 0:
        raise AssertionError("rail inputs must be positive")
    states = [3 ** j * 2 ** (length - j) * payload - 1
              for j in range(length + 1)]
    for source, target in zip(states, states[1:]):
        if source % 2 != 1:
            raise AssertionError("minus-one rail source is not odd")
        if (3 * source + 1) // 2 != target:
            raise AssertionError("minus-one rail identity failed")
        if not source < target:
            raise AssertionError("minus-one rail did not grow")
    if states[0] != 2 ** length * payload - 1:
        raise AssertionError("minus-one rail start mismatch")
    if states[-1] != 3 ** length * payload - 1:
        raise AssertionError("minus-one rail endpoint mismatch")


def build_artifact() -> dict[str, Any]:
    rows = [audit_level(level) for level in LEVELS]
    surpluses = [
        Fraction(row["deviation_over_weight"]["numerator"],
                 row["deviation_over_weight"]["denominator"])
        for row in rows
    ]
    if not all(left > right for left, right in zip(surpluses, surpluses[1:])):
        raise AssertionError("finite escape-tax surplus is not strictly decreasing")
    condition_numbers = [
        Fraction(row["potential_condition_number"]["numerator"],
                 row["potential_condition_number"]["denominator"])
        for row in rows
    ]
    if not all(left < right for left, right in
               zip(condition_numbers, condition_numbers[1:])):
        raise AssertionError("finite potential condition numbers do not increase")
    for length in range(1, 65):
        for payload in range(1, 65):
            verify_minus_one_rail(length, payload)

    return {
        "schema": "kl-minus-one-escape-tax-v2",
        "scope": {
            "levels": list(LEVELS),
            "exact_claim": (
                "For every stored level, c(-1)/minFiber(-1) is strictly larger "
                "than the certificate's rational class-8 lower weight.  The "
                "eight exact surplus ratios are strictly decreasing, while "
                "the eight exact potential condition numbers are strictly "
                "increasing."
            ),
            "finite_evidence": (
                "The deviation tax of the nonordinary -1 self-loop approaches "
                "the certified class-8 weight over levels 12 through 19."
            ),
            "nonclaim": (
                "No limit, infinite positive orbit, or Collatz counterexample "
                "is established."
            ),
        },
        "rows": rows,
        "all_strict": True,
        "surplus_strictly_decreasing": True,
        "condition_number_strictly_increasing": True,
        "rail_regression": {"length_max": 64, "payload_max": 64,
                            "all_exact": True},
        "counterexample": None,
    }


def canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def command_build() -> None:
    print(canonical_bytes(build_artifact()).decode(), end="")


def command_verify(path: Path) -> None:
    expected = canonical_bytes(build_artifact())
    actual = path.read_bytes()
    if actual != expected:
        raise AssertionError(f"artifact mismatch: {path}")
    print(f"verified {path}")
    print(f"sha256 {hashlib.sha256(actual).hexdigest()}")


def command_selftest() -> None:
    for length, payload in ((1, 1), (7, 3), (32, 17), (64, 64)):
        verify_minus_one_rail(length, payload)
    artifact = build_artifact()
    if artifact["counterexample"] is not None:
        raise AssertionError("unexpected counterexample field")
    print("selftest passed")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("build")
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("artifact", nargs="?", type=Path,
                               default=DEFAULT_ARTIFACT)
    subparsers.add_parser("selftest")
    args = parser.parse_args()

    if args.command == "build":
        command_build()
    elif args.command == "verify":
        command_verify(args.artifact)
    else:
        command_selftest()


if __name__ == "__main__":
    main()
