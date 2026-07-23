#!/usr/bin/env python3
"""Exact first-passage code for the minimal outward shortcut system.

For a shortcut parity word ``w``, let ``S`` be its length and ``O`` its
number of odd source states.  Its affine slope is ``3^O/2^S``.  The minimal
outward code consists of all words for which

    3^O > 2^S

for the first time at the final letter.  It is prefix-free.  Concatenating
its words gives strict multiplicative growth without invoking the YAH/tag
compiler.  An ordinary positive integer admitting infinitely many such
blocks would therefore be a Collatz counterexample.

The second audit follows every positive source through a stated bound to the
terminal 1--2 cycle.  Increasing-source exhaustion then computes the exact
minimum ordinary address ``h_n`` for every block depth reached and a strict
lower bound for the next one.  This directly measures the atomic construction
gate; it is not an unstructured search for long stopping times.

This worker counts the first-passage code by ``(S,O)`` rather than enumerating
its exponentially many words.  Under fair binary parity measure it certifies
the two exact stopped-mass identities

    P_N + A_N = 1,
    Q_N + R_N = 1,

where ``P`` is ordinary Kraft mass, ``A`` is uncrossed mass, ``Q`` is tilted
mass ``sum 3^O/4^S`` of words crossing by depth ``N``, and ``R`` is the
remaining tilted mass.  The second equality is the stopped martingale
identity: an even extension has weight factor ``1/4`` and an odd extension
has factor ``3/4``.

The infinite tilted mass is therefore critical, not supercritical.  Standard
negative-drift/optional-stopping reasoning gives ``R_N -> 0`` and total
tilted mass one; the artifact checks the exact finite identities and records
the residual at a stated bound.  It does not infer an ordinary survivor.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "collatz-outward-first-passage-v2"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def decimal_ratio(numerator: int, denominator: int, digits: int = 18) -> str:
    integer, remainder = divmod(numerator, denominator)
    places = []
    for _ in range(digits):
        remainder *= 10
        digit, remainder = divmod(remainder, denominator)
        places.append(str(digit))
    return f"{integer}." + "".join(places)


def accelerated_odd_step(value: int) -> int:
    if value <= 0 or value % 2 == 0:
        raise ValueError("accelerated odd step requires a positive odd input")
    value = 3 * value + 1
    while value % 2 == 0:
        value //= 2
    return value


def source_profile(
    source: int, maximum_shortcut_steps: int, keep_boundaries: bool = False
) -> dict[str, Any]:
    """Count complete first-passage blocks on one ordinary shortcut orbit.

    Reaching 1 or 2 is handled exactly rather than by an arbitrary orbit
    horizon.  At state 1 there can be at most one final crossing: the next
    odd letter multiplies the pending slope by 3/2, after which the 1--2
    cycle has two-letter multiplier 3/4.  At state 2 no future crossing is
    possible because the first new letter is even.
    """

    if source <= 0:
        raise ValueError("source must be positive")
    if maximum_shortcut_steps < 1:
        raise ValueError("shortcut step limit must be positive")

    value = source
    block_length = 0
    block_odds = 0
    block_count = 0
    shortcut_steps = 0
    accelerated_steps = 0
    boundaries: list[dict[str, int]] = []

    def record_boundary() -> None:
        if keep_boundaries:
            boundaries.append(
                {
                    "block_depth": block_count,
                    "shortcut_steps": shortcut_steps,
                    "accelerated_steps": accelerated_steps,
                    "state": value,
                    "block_length": block_length,
                    "block_odd_count": block_odds,
                }
            )

    while shortcut_steps < maximum_shortcut_steps:
        if value == 1:
            if 3 ** (block_odds + 1) > 2 ** (block_length + 1):
                block_length += 1
                block_odds += 1
                shortcut_steps += 1
                accelerated_steps += 1
                value = 2
                block_count += 1
                record_boundary()
            return {
                "source": source,
                "first_passage_blocks": block_count,
                "shortcut_steps_to_terminal_cycle": shortcut_steps,
                "accelerated_steps_to_terminal_cycle": accelerated_steps,
                "terminal_cycle_state": value,
                "boundaries": boundaries,
            }
        if value == 2:
            return {
                "source": source,
                "first_passage_blocks": block_count,
                "shortcut_steps_to_terminal_cycle": shortcut_steps,
                "accelerated_steps_to_terminal_cycle": accelerated_steps,
                "terminal_cycle_state": value,
                "boundaries": boundaries,
            }

        odd = value % 2
        block_length += 1
        shortcut_steps += 1
        if odd:
            block_odds += 1
            accelerated_steps += 1
            value = (3 * value + 1) // 2
        else:
            value //= 2

        if 3**block_odds > 2**block_length:
            block_count += 1
            record_boundary()
            block_length = 0
            block_odds = 0

    raise AssertionError(
        f"source {source} did not reach the terminal cycle within "
        f"{maximum_shortcut_steps} shortcut steps"
    )


def minimum_address_regression(
    maximum_seed: int, maximum_shortcut_steps: int
) -> dict[str, Any]:
    """Exhaust the exact monotone minimum-address sequence below a seed cap."""

    if maximum_seed < 1:
        raise ValueError("maximum seed must be positive")

    record_rows: list[dict[str, int]] = []
    certified_h: list[dict[str, int]] = []
    record_depth = 0
    for source in range(1, maximum_seed + 1):
        profile = source_profile(source, maximum_shortcut_steps)
        depth = int(profile["first_passage_blocks"])
        if depth <= record_depth:
            continue
        record_rows.append(
            {
                "source": source,
                "first_passage_blocks": depth,
                "shortcut_steps_to_terminal_cycle": int(
                    profile["shortcut_steps_to_terminal_cycle"]
                ),
                "accelerated_steps_to_terminal_cycle": int(
                    profile["accelerated_steps_to_terminal_cycle"]
                ),
            }
        )
        for block_depth in range(record_depth + 1, depth + 1):
            certified_h.append(
                {"block_depth": block_depth, "minimum_address": source}
            )
        record_depth = depth

    champion = source_profile(
        int(record_rows[-1]["source"]), maximum_shortcut_steps, True
    )
    odd_boundaries = [
        row for row in champion["boundaries"] if int(row["state"]) % 2 == 1
    ]
    if not odd_boundaries:
        raise AssertionError("record seed has no odd first-passage boundary")
    visual = odd_boundaries[-1]
    replay = int(champion["source"])
    for _ in range(int(visual["accelerated_steps"])):
        replay = accelerated_odd_step(replay)
    if replay != int(visual["state"]):
        raise AssertionError("accelerated visualizer witness did not replay")

    return {
        "meaning": (
            "h_n is the least positive ordinary seed completing n successive "
            "first-passage blocks; exhaustive increasing-seed replay certifies "
            "every displayed minimum"
        ),
        "maximum_seed": maximum_seed,
        "maximum_shortcut_steps_per_seed": maximum_shortcut_steps,
        "all_scanned_sources_reached_terminal_cycle": True,
        "record_rows": record_rows,
        "certified_h_values": certified_h,
        "greatest_certified_block_depth": record_depth,
        "next_minimum_address_strict_lower_bound": {
            "block_depth": record_depth + 1,
            "strictly_greater_than": maximum_seed,
        },
        "visualizer_prefix": {
            "collatz_source": int(champion["source"]),
            "collatz_target": int(visual["state"]),
            "accelerated_steps": int(visual["accelerated_steps"]),
            "first_passage_blocks": int(visual["block_depth"]),
            "shortcut_steps": int(visual["shortcut_steps"]),
            "scope": (
                "exact finite prefix of the record minimum-address seed; "
                "the complete ordinary orbit reaches the 1--2 cycle"
            ),
        },
    }


def first_passage_audit(maximum_length: int) -> dict[str, Any]:
    if maximum_length < 1:
        raise ValueError("maximum word length must be positive")

    # alive[O] counts length-(depth-1) words that have never yet had outward
    # slope.  The state is sufficient because the slope test depends only on
    # length and odd count.
    alive = {0: 1}
    crossing_by_length: list[dict[str, Any]] = []
    crossing_rows: list[tuple[int, int, int]] = []

    for depth in range(1, maximum_length + 1):
        following: dict[int, int] = {}
        crossing_count = 0
        crossing_odd_histogram: dict[int, int] = {}
        for odd_count, count in alive.items():
            # Even extension.
            following[odd_count] = following.get(odd_count, 0) + count

            # Odd extension.  This is the only way to cross the outward
            # boundary, because an even extension strictly decreases slope.
            next_odd = odd_count + 1
            if 3**next_odd > 2**depth:
                crossing_count += count
                crossing_odd_histogram[next_odd] = (
                    crossing_odd_histogram.get(next_odd, 0) + count
                )
                crossing_rows.append((depth, next_odd, count))
            else:
                following[next_odd] = following.get(next_odd, 0) + count
        alive = following
        if crossing_count or depth <= 6:
            crossing_by_length.append(
                {
                    "length": depth,
                    "first_passage_words": str(crossing_count),
                    "odd_count_histogram": {
                        str(odd): str(count)
                        for odd, count in sorted(crossing_odd_histogram.items())
                    },
                }
            )

    ordinary_denominator = 2**maximum_length
    ordinary_cross_numerator = sum(
        count * 2 ** (maximum_length - depth)
        for depth, _odd, count in crossing_rows
    )
    ordinary_alive_numerator = sum(alive.values())
    if ordinary_cross_numerator + ordinary_alive_numerator != ordinary_denominator:
        raise AssertionError("ordinary stopped-mass identity failed")

    tilted_denominator = 4**maximum_length
    tilted_cross_numerator = sum(
        count * 3**odd * 4 ** (maximum_length - depth)
        for depth, odd, count in crossing_rows
    )
    tilted_alive_numerator = sum(
        count * 3**odd for odd, count in alive.items()
    )
    if tilted_cross_numerator + tilted_alive_numerator != tilted_denominator:
        raise AssertionError("tilted stopped-martingale identity failed")

    # Under the tilted cylinder law q(w)=3^O/4^S, odd bits have probability
    # 3/4 and the log-slope drift is positive.  Thus a first passage occurs
    # almost surely.  A first-passage word overshoots from slope <=1 by one
    # odd factor 3/2, so its final slope lies in (1,3/2].  Consequently its
    # ordinary mass p=q/slope lies between (2/3)q and q.  The live tilted
    # residual therefore gives an exact bracket for the full ordinary Kraft
    # mass without enumerating the infinite tail.
    ordinary_partial = Fraction(
        ordinary_cross_numerator, ordinary_denominator
    )
    tilted_residual = Fraction(tilted_alive_numerator, tilted_denominator)
    ordinary_limit_lower = ordinary_partial + Fraction(2, 3) * tilted_residual
    ordinary_limit_upper = ordinary_partial + tilted_residual
    if not ordinary_limit_lower < ordinary_limit_upper < 1:
        raise AssertionError("ordinary first-passage limit bracket failed")

    # The bounded signed-controller code already in the repository is
    # exactly the first three nonempty layers of this canonical code.
    first_nonempty = [
        (int(row["length"]), int(row["first_passage_words"]))
        for row in crossing_by_length
        if int(row["first_passage_words"])
    ][:3]
    if first_nonempty != [(1, 1), (3, 1), (6, 2)]:
        raise AssertionError("minimal four-word outward code changed")

    return {
        "definition": (
            "all parity words w with 3^odd(w)>2^len(w) and "
            "3^odd(u)<=2^len(u) for every proper prefix u"
        ),
        "prefix_free": True,
        "maximality": (
            "every outward parity word has a unique first-passage prefix, "
            "so replacing it by that prefix shows this code dominates every "
            "outward prefix-free code in both ordinary and tilted mass"
        ),
        "minimal_layers": {
            "length_word_counts": [[1, 1], [3, 1], [6, 2]],
            "literal_words": ["1", "011", "001111", "010111"],
            "ordinary_kraft_mass": "21/32",
            "tilted_mass": "1905/2048",
        },
        "bound": maximum_length,
        "crossing_by_length": crossing_by_length,
        "ordinary_stopped_mass": {
            "crossed_numerator": str(ordinary_cross_numerator),
            "alive_numerator": str(ordinary_alive_numerator),
            "denominator": str(ordinary_denominator),
            "identity": "P_N+A_N=1",
            "crossed_decimal_diagnostic": decimal_ratio(
                ordinary_cross_numerator, ordinary_denominator
            ),
        },
        "tilted_stopped_mass": {
            "crossed_numerator": str(tilted_cross_numerator),
            "alive_numerator": str(tilted_alive_numerator),
            "denominator": str(tilted_denominator),
            "identity": "Q_N+R_N=1",
            "crossed_decimal_diagnostic": decimal_ratio(
                tilted_cross_numerator, tilted_denominator
            ),
            "alive_decimal_diagnostic": decimal_ratio(
                tilted_alive_numerator, tilted_denominator
            ),
        },
        "full_ordinary_kraft_bracket": {
            "lower": str(ordinary_limit_lower),
            "upper": str(ordinary_limit_upper),
            "lower_decimal_diagnostic": decimal_ratio(
                ordinary_limit_lower.numerator,
                ordinary_limit_lower.denominator,
            ),
            "upper_decimal_diagnostic": decimal_ratio(
                ordinary_limit_upper.numerator,
                ordinary_limit_upper.denominator,
            ),
            "proof": (
                "the unobserved tilted tail has mass R_N; first-passage "
                "overshoot gives 1<slope<=3/2 and hence (2/3)q<=p<q"
            ),
        },
        "infinite_theorem_boundary": (
            "the fair-parity slope is a nonnegative martingale; on uncrossed "
            "paths it is at most one and tends to zero almost surely by the "
            "negative log drift, so dominated convergence gives total tilted "
            "first-passage mass exactly one"
        ),
        "mass_to_atom_gate": (
            "branching criticality alone does not give an ordinary seed; a "
            "projectively consistent schedule measure would suffice if the "
            "nondecreasing canonical least residues had uniformly bounded "
            "first moment, because then one residue tower is eventually "
            "constant"
        ),
        "claim_scope": (
            "exact finite first-passage and stopped-mass identities at the "
            "stated bound; no infinite ordinary survivor and no Collatz "
            "counterexample"
        ),
        "counterexample": None,
    }


def build_artifact(
    maximum_length: int, maximum_seed: int, maximum_shortcut_steps: int
) -> dict[str, Any]:
    data = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": first_passage_audit(maximum_length),
        "minimum_address_regression": minimum_address_regression(
            maximum_seed, maximum_shortcut_steps
        ),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected outward first-passage schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    regression = expected["minimum_address_regression"]
    actual = build_artifact(
        int(expected["audit"]["bound"]),
        int(regression["maximum_seed"]),
        int(regression["maximum_shortcut_steps_per_seed"]),
    )
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if expected["audit"]["counterexample"] is not None:
        raise AssertionError("first-passage artifact claims a counterexample")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": expected["worker_sha256"],
        "bound": expected["audit"]["bound"],
        "maximum_seed": regression["maximum_seed"],
        "greatest_certified_block_depth": regression[
            "greatest_certified_block_depth"
        ],
        "counterexample": None,
    }


def selftest() -> None:
    tiny = first_passage_audit(6)
    if tiny["ordinary_stopped_mass"]["crossed_numerator"] != "42":
        raise AssertionError("tiny ordinary first-passage mass changed")
    if tiny["tilted_stopped_mass"]["crossed_numerator"] != "3810":
        raise AssertionError("tiny tilted first-passage mass changed")
    addresses = minimum_address_regression(100, 1_000)
    if addresses["greatest_certified_block_depth"] != 15:
        raise AssertionError("tiny minimum-address depth changed")
    if addresses["certified_h_values"][4] != {
        "block_depth": 5,
        "minimum_address": 27,
    }:
        raise AssertionError("tiny minimum-address record changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-length", type=int, default=256)
    build.add_argument("--maximum-seed", type=int, default=300_000)
    build.add_argument("--maximum-shortcut-steps", type=int, default=10_000)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward first-passage selftest: PASS")
        return 0
    if args.command == "build":
        artifact = build_artifact(
            args.maximum_length, args.maximum_seed, args.maximum_shortcut_steps
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), indent=2, sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return 0
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    raise SystemExit(main())
