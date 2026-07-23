#!/usr/bin/env python3
"""Exact finite audit of the EC17 boundary clock versus KL full-lift edges.

This checker deliberately audits only the proposed *boundary-core* bridge.
It does not identify the EC17 core with an ordinary Collatz state, does not
compile the packet-level glider, and does not attach a KL tax to a pair which
has not passed one of the exact KL edge congruences below.

At ternary depth ``d`` put

    Y_d = {m mod 3^d : m = 2 mod 3}.

The EC17 predecessor congruence fixes the normalized boundary state

    m(n) = 34 * 2^(-(8*n+15)) mod 3^d.

Consequently a branch increment ``delta`` gives

    m(n+delta) = 4^(-4*delta) * m(n) mod 3^d.

For a pair ``y = u*m``, the three KL full-lift tests are

    transport: y = 4*m,
    class 2:   m = 2 (mod 9),  3*y = 4*m-2 (mod 3^d),
    class 8:   m = 8 (mod 9),  3*y = 2*m-1 (mod 3^d).

The script also exhausts a bounded box of abstract KL predecessor words.
Their defect updates are exactly the updates in KLControllerReset:

    T: (D,r) -> (4D,r),
    R: (D,r) -> (4D+2*3^r,r+1),
    A: (D,r) -> (2D+3^r,r+1).

It regression-checks ``D >= 3^r-2^r`` for every enumerated word and checks
the EC17 constants 17 and 34 against the exact r=17 lower bound.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import asdict, dataclass
from itertools import product
from pathlib import Path
from typing import Iterable, Sequence


SCHEMA = "collatz-ec17-kl-boundary-bridge-audit-v1"
DEFAULT_INCREMENTS = (-1, 1, 1)
EDGE_LABELS = ("transport", "r2", "r8")


@dataclass(frozen=True)
class EdgeCounts:
    transport: int
    r2: int
    r8: int
    no_kl_edge: int


def parse_increments(text: str) -> tuple[int, int, int]:
    try:
        values = tuple(int(piece.strip()) for piece in text.split(","))
    except ValueError as error:
        raise argparse.ArgumentTypeError("increments must be three integers") from error
    if len(values) != 3:
        raise argparse.ArgumentTypeError("increments must contain exactly three integers")
    return values  # type: ignore[return-value]


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def y_states(depth: int) -> tuple[int, ...]:
    if depth < 2:
        raise ValueError("edge classification requires ternary depth at least two")
    return tuple(range(2, 3**depth, 3))


def required_state(branch: int, depth: int) -> int:
    if branch < 1:
        raise ValueError("EC17 branches must be positive")
    modulus = 3**depth
    exponent = 8 * branch + 15
    state = 34 * pow(2, -exponent, modulus) % modulus
    if state % 3 != 2:
        raise AssertionError("required EC17 state left Y_d")
    if pow(2, exponent, modulus) * state % modulus != 34 % modulus:
        raise AssertionError("required EC17 coefficient congruence failed")
    return state


def v3_capped(value: int, cap: int) -> int:
    if cap < 0:
        raise ValueError("negative valuation cap")
    value = abs(value)
    if value == 0:
        return cap
    exponent = 0
    while exponent < cap and value % 3 == 0:
        value //= 3
        exponent += 1
    return exponent


def edge_hits(source: int, target: int, depth: int) -> tuple[str, ...]:
    modulus = 3**depth
    hits: list[str] = []
    if (target - 4 * source) % modulus == 0:
        hits.append("transport")
    if source % 9 == 2 and (3 * target - (4 * source - 2)) % modulus == 0:
        hits.append("r2")
    if source % 9 == 8 and (3 * target - (2 * source - 1)) % modulus == 0:
        hits.append("r8")
    return tuple(hits)


def count_edges(pairs: Iterable[tuple[int, int]], depth: int) -> EdgeCounts:
    counts = {label: 0 for label in EDGE_LABELS}
    no_edge = 0
    for source, target in pairs:
        hits = edge_hits(source, target, depth)
        if not hits:
            no_edge += 1
        for label in hits:
            counts[label] += 1
    return EdgeCounts(
        transport=counts["transport"],
        r2=counts["r2"],
        r8=counts["r8"],
        no_kl_edge=no_edge,
    )


def classify_increment(delta: int, depth: int) -> dict[str, object]:
    modulus = 3**depth
    states = y_states(depth)
    multiplier = pow(4, -4 * delta, modulus)
    if multiplier % 3 != 1:
        raise AssertionError("EC17 clock multiplier is not a principal 3-adic unit")

    r2_coefficient = (3 * multiplier - 4) % modulus
    r8_coefficient = (3 * multiplier - 2) % modulus
    if math.gcd(r2_coefficient, modulus) != 1:
        raise AssertionError("class-2 chord coefficient is not a unit")
    if math.gcd(r8_coefficient, modulus) != 1:
        raise AssertionError("class-8 chord coefficient is not a unit")

    r2_solution = (-2 * pow(r2_coefficient, -1, modulus)) % modulus
    r8_solution = (-1 * pow(r8_coefficient, -1, modulus)) % modulus
    if r2_solution % 9 != 2:
        raise AssertionError("unique class-2 solution is not 2 modulo 9")
    if r8_solution % 9 != 8:
        raise AssertionError("unique class-8 solution is not 8 modulo 9")

    pairs = tuple((state, multiplier * state % modulus) for state in states)
    counts = count_edges(pairs, depth)
    expected_transport = len(states) if multiplier == 4 % modulus else 0
    if counts.transport != expected_transport:
        raise AssertionError("transport classification disagreed with unit cancellation")
    if counts.r2 != 1 or counts.r8 != 1:
        raise AssertionError("chord unit equations did not have exactly one solution")

    r2_hits = tuple(pair for pair in pairs if "r2" in edge_hits(*pair, depth))
    r8_hits = tuple(pair for pair in pairs if "r8" in edge_hits(*pair, depth))
    if r2_hits != ((r2_solution, multiplier * r2_solution % modulus),):
        raise AssertionError("class-2 inverse solution disagreed with enumeration")
    if r8_hits != ((r8_solution, multiplier * r8_solution % modulus),):
        raise AssertionError("class-8 inverse solution disagreed with enumeration")

    return {
        "increment": delta,
        "multiplier_mod_3_power": multiplier,
        "transport_exponent_mod_order": (-4 * delta) % (3 ** (depth - 1)),
        "r2_coefficient_mod_3_power": r2_coefficient,
        "r8_coefficient_mod_3_power": r8_coefficient,
        "r2_coefficient_is_unit": True,
        "r8_coefficient_is_unit": True,
        "r2_unique_source": r2_solution,
        "r8_unique_source": r8_solution,
        "global_counts": asdict(counts),
    }


def schedule_audit(
    depth: int, start_branch: int, increments: Sequence[int]
) -> dict[str, object]:
    if len(increments) != 3:
        raise ValueError("period-three schedule needs three increments")
    gain = sum(increments)
    if gain < 0:
        raise ValueError("negative cycle gain cannot keep positive branches cofinally")
    levels = [start_branch]
    for delta in increments:
        levels.append(levels[-1] + delta)
    if min(levels) < 1:
        raise ValueError("the initial period-three cycle leaves positive branches")

    modulus = 3**depth
    order = 3 ** (depth - 1)
    macro_multiplier = pow(4, -4 * gain, modulus)
    predicted_orbit_length = 3 ** (
        depth - 1 - min(v3_capped(gain, depth - 1), depth - 1)
    )

    macro_states: list[int] = []
    state = required_state(start_branch, depth)
    first = state
    while not macro_states or state != first:
        if state in macro_states:
            raise AssertionError("macro orbit repeated away from its start")
        macro_states.append(state)
        state = macro_multiplier * state % modulus
        if len(macro_states) > order:
            raise AssertionError("macro orbit exceeded Y_d")
    if len(macro_states) != predicted_orbit_length:
        raise AssertionError("macro orbit length disagreed with the order formula")
    if gain % 3 != 0 and set(macro_states) != set(y_states(depth)):
        raise AssertionError("unit-gain macro orbit did not traverse all of Y_d")

    # Reconstruct every phase state independently from its EC17 coefficient
    # clock, then compare it to the multiplicative phase relation.
    phase_rows: list[dict[str, object]] = []
    prefix = 0
    for phase, delta in enumerate(increments):
        pairs: list[tuple[int, int]] = []
        clock_multiplier = pow(4, -4 * delta, modulus)
        for cycle in range(predicted_orbit_length):
            source_branch = start_branch + gain * cycle + prefix
            target_branch = source_branch + delta
            source = required_state(source_branch, depth)
            target = required_state(target_branch, depth)
            if target != clock_multiplier * source % modulus:
                raise AssertionError("phase coefficient clock failed")
            pairs.append((source, target))
        counts = count_edges(pairs, depth)
        if gain % 3 != 0:
            global_counts = classify_increment(delta, depth)["global_counts"]
            if asdict(counts) != global_counts:
                raise AssertionError("full phase orbit disagreed with global classification")
        hits = [
            {
                "source": source,
                "target": target,
                "edges": list(edge_hits(source, target, depth)),
            }
            for source, target in pairs
            if edge_hits(source, target, depth)
        ]
        phase_rows.append(
            {
                "phase": phase,
                "increment": delta,
                "source_prefix_increment": prefix,
                "clock_multiplier_mod_3_power": clock_multiplier,
                "counts_on_macro_orbit": asdict(counts),
                "edge_hits": hits,
            }
        )
        prefix += delta

    return {
        "depth": depth,
        "modulus": modulus,
        "state_count": order,
        "start_branch": start_branch,
        "increments": list(increments),
        "cycle_gain": gain,
        "macro_multiplier_mod_3_power": macro_multiplier,
        "predicted_macro_orbit_length": predicted_orbit_length,
        "observed_macro_orbit_length": len(macro_states),
        "macro_orbit_is_all_Y": set(macro_states) == set(y_states(depth)),
        "macro_states": macro_states,
        "phase_rows": phase_rows,
        "increment_classifications": [
            classify_increment(delta, depth) for delta in increments
        ],
    }


def defect_step(data: tuple[int, int], letter: str) -> tuple[int, int]:
    defect, divided = data
    if letter == "T":
        return 4 * defect, divided
    if letter == "R":
        return 4 * defect + 2 * 3**divided, divided + 1
    if letter == "A":
        return 2 * defect + 3**divided, divided + 1
    raise ValueError("unknown KL word letter")


def defect_word(word: Sequence[str]) -> tuple[int, int]:
    data = (0, 0)
    for letter in word:
        data = defect_step(data, letter)
    return data


def defect_regression(max_word_length: int) -> dict[str, object]:
    if max_word_length < 0:
        raise ValueError("negative word-length bound")
    words_checked = 0
    minima: dict[int, tuple[int, str]] = {}
    for length in range(max_word_length + 1):
        for letters in product("TRA", repeat=length):
            words_checked += 1
            defect, divided = defect_word(letters)
            lower = 3**divided - 2**divided
            if defect < lower:
                raise AssertionError(
                    f"defect lower bound failed on {''.join(letters)!r}"
                )
            witness = "".join(letters)
            current = minima.get(divided)
            if current is None or defect < current[0]:
                minima[divided] = (defect, witness)

    minimum_rows: list[dict[str, object]] = []
    for divided in sorted(minima):
        observed, witness = minima[divided]
        sharp_lower = 3**divided - 2**divided
        if observed != sharp_lower:
            raise AssertionError("bounded box missed the sharp all-advanced witness")
        minimum_rows.append(
            {
                "divided_count": divided,
                "observed_minimum_defect": observed,
                "sharp_lower_bound": sharp_lower,
                "first_minimizing_word": witness,
            }
        )

    r = 17
    lower17 = 3**r - 2**r
    if not 17 < lower17 or not 34 < lower17:
        raise AssertionError("EC17 defect mismatch regression failed")
    return {
        "alphabet": {
            "T": "transport: D -> 4D",
            "R": "retarded: D -> 4D+2*3^r",
            "A": "advanced: D -> 2D+3^r",
        },
        "maximum_word_length": max_word_length,
        "words_checked": words_checked,
        "minimum_by_divided_count": minimum_rows,
        "ec17_mismatch": {
            "divided_count_lower_bound": r,
            "sharp_defect_lower_bound_at_17": lower17,
            "raw_core_defect": 17,
            "raw_core_defect_is_too_small": True,
            "doubled_kl_state_defect": 34,
            "doubled_kl_state_defect_is_too_small": True,
        },
    }


def regression_rows(max_word_length: int) -> dict[str, object]:
    rows = [schedule_audit(depth, 2, DEFAULT_INCREMENTS) for depth in (3, 4)]
    for row in rows:
        expected_none = row["state_count"] - 2  # type: ignore[operator]
        for phase in row["phase_rows"]:  # type: ignore[assignment]
            counts = phase["counts_on_macro_orbit"]
            expected = {
                "transport": 0,
                "r2": 1,
                "r8": 1,
                "no_kl_edge": expected_none,
            }
            if counts != expected:
                raise AssertionError("d=3,4 period-three count regression changed")
    return {
        "period_three_minus_one_one_one": rows,
        "defect": defect_regression(max_word_length),
    }


def build_artifact(
    depth: int,
    start_branch: int,
    increments: Sequence[int],
    max_word_length: int,
) -> dict[str, object]:
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "scope": (
            "finite exact EC17 coefficient-clock, odometer-order, and KL-edge "
            "congruence audit; exhaustive abstract KL defect regression only "
            "through the stated word-length bound; no packet compiler, infinite "
            "ray, Haar-tax theorem, or Collatz counterexample claim"
        ),
        "counterexample": None,
        "tax_ready": False,
        "requested_audit": schedule_audit(depth, start_branch, increments),
        "fixed_regressions": regression_rows(max_word_length),
    }


def write_artifact(path: Path, artifact: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")


def verify_artifact(path: Path) -> None:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unrecognized EC17/KL bridge audit schema")
    requested = expected["requested_audit"]
    defect = expected["fixed_regressions"]["defect"]
    actual = build_artifact(
        int(requested["depth"]),
        int(requested["start_branch"]),
        tuple(int(value) for value in requested["increments"]),
        int(defect["maximum_word_length"]),
    )
    if actual != expected:
        raise AssertionError("artifact reconstruction disagreed")


def add_common_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--start-branch", type=int, default=2)
    parser.add_argument(
        "--increments", type=parse_increments, default=DEFAULT_INCREMENTS
    )
    parser.add_argument("--max-word-length", type=int, default=9)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    selftest = subparsers.add_parser("selftest")
    selftest.add_argument("--max-word-length", type=int, default=8)

    build = subparsers.add_parser("build")
    add_common_arguments(build)
    build.add_argument("artifact", type=Path)

    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)

    args = parser.parse_args()
    if args.command == "selftest":
        regression_rows(args.max_word_length)
        print("EC17/KL boundary bridge audit self-test: PASS")
    elif args.command == "build":
        artifact = build_artifact(
            args.depth,
            args.start_branch,
            args.increments,
            args.max_word_length,
        )
        write_artifact(args.artifact, artifact)
        print(f"wrote exact EC17/KL boundary bridge audit: {args.artifact}")
    elif args.command == "verify":
        verify_artifact(args.artifact)
        print(f"verified exact EC17/KL boundary bridge audit: {args.artifact}")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
