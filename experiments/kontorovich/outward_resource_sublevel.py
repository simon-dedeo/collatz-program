#!/usr/bin/env python3
"""Exact coercive mixed-base resource audit for first-passage survivors.

For a positive ordinary seed ``n``, write uniquely

    n + 1 = 2^a * 3^b * u,    gcd(u, 6) = 1,

and define ``R(n) = a + b + u``.  The resource is coercive because
``R(n) <= B`` implies ``n + 1 <= B * 6^B``.  Its sublevel is therefore the
finite, exactly enumerable set of triples ``(a,b,u)`` with
``a+b+u <= B``.

The worker enumerates that sublevel rather than an interval of seeds.  Every
seed is literally replayed under the shortcut Collatz map, and first-passage
blocks are counted only when ``3^O > 2^S`` first becomes true.  At ``B=128``
the audit identifies a resource-127 seed surviving 136 blocks and proves by
exhaustion that no resource-at-most-128 seed survives 137 blocks.  This is an
exact obstruction to one proposed uniform moment bound, not a Collatz result.
Every artifact records ``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "collatz-outward-resource-sublevel-v1"
DEFAULT_RESOURCE_BOUND = 128
DEFAULT_STEP_CAP = 50_000
EXPECTED_EXPLORATORY_PAYLOAD_SHA256 = (
    "f84f55874cc10e7d51fd0ec4f7bcb8f60a4f7c5b3ddbe11fd22d165b7e928cd9"
)


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def integer_sha256(value: int) -> str:
    width = max(1, (value.bit_length() + 7) // 8)
    return hashlib.sha256(value.to_bytes(width, "big")).hexdigest()


def factor_2_3(value: int) -> tuple[int, int, int]:
    if value <= 0:
        raise ValueError("factorization requires a positive integer")
    a = 0
    while value % 2 == 0:
        a += 1
        value //= 2
    b = 0
    while value % 3 == 0:
        b += 1
        value //= 3
    if math.gcd(value, 6) != 1:
        raise AssertionError("primitive factor is not coprime to six")
    return a, b, value


def resource(seed: int) -> int:
    a, b, unit = factor_2_3(seed + 1)
    return a + b + unit


def shortcut_step(value: int) -> int:
    if value <= 0:
        raise ValueError("shortcut Collatz requires a positive integer")
    return (3 * value + 1) // 2 if value % 2 else value // 2


@dataclass(frozen=True)
class Boundary:
    depth: int
    shortcut_steps: int
    accelerated_steps: int
    state: int
    word: str
    word_length: int
    word_odds: int


@dataclass(frozen=True)
class Profile:
    seed: int
    depth: int
    shortcut_steps: int
    accelerated_steps: int
    terminal_state: int
    boundaries: tuple[Boundary, ...]
    stabilization_depth: int | None
    stabilization_steps: int | None
    post_stabilization_blocks: int
    failed_tail_length: int
    failed_tail_odds: int


def source_profile(seed: int, step_cap: int, keep_boundaries: bool = False) -> Profile:
    """Literally replay one seed to 1--2 and count exact first passages."""

    if seed <= 0 or step_cap <= 0:
        raise ValueError("seed and step cap must be positive")
    state = seed
    block_bits: list[str] = []
    block_odds = 0
    depth = 0
    steps = 0
    accelerated = 0
    boundaries: list[Boundary] = []
    stabilization_depth: int | None = None
    stabilization_steps: int | None = None

    def record_boundary() -> None:
        nonlocal stabilization_depth, stabilization_steps
        if stabilization_depth is None and seed < 2**steps:
            stabilization_depth = depth
            stabilization_steps = steps
        if keep_boundaries:
            boundaries.append(
                Boundary(
                    depth,
                    steps,
                    accelerated,
                    state,
                    "".join(block_bits),
                    len(block_bits),
                    block_odds,
                )
            )

    while steps < step_cap:
        if state == 1:
            # There can be one final crossing on the odd 1 -> 2 step.
            block_bits.append("1")
            block_odds += 1
            steps += 1
            accelerated += 1
            state = 2
            if 3**block_odds > 2 ** len(block_bits):
                depth += 1
                record_boundary()
                block_bits = []
                block_odds = 0
            break
        if state == 2:
            break

        odd = state % 2
        block_bits.append("1" if odd else "0")
        block_odds += odd
        steps += 1
        accelerated += odd
        state = shortcut_step(state)
        if 3**block_odds > 2 ** len(block_bits):
            depth += 1
            record_boundary()
            block_bits = []
            block_odds = 0
    else:
        raise AssertionError(
            f"seed {seed} did not reach the terminal cycle within {step_cap} steps"
        )

    if state != 2:
        raise AssertionError("literal replay did not finish at terminal state 2")
    if 3**block_odds > 2 ** len(block_bits):
        raise AssertionError("terminal incomplete tail crossed the outward boundary")
    post = depth - stabilization_depth if stabilization_depth is not None else 0
    return Profile(
        seed,
        depth,
        steps,
        accelerated,
        state,
        tuple(boundaries),
        stabilization_depth,
        stabilization_steps,
        post,
        len(block_bits),
        block_odds,
    )


def profile_summary(profile: Profile) -> dict[str, Any]:
    return {
        "seed": str(profile.seed),
        "seed_sha256": integer_sha256(profile.seed),
        "first_passage_blocks": profile.depth,
        "shortcut_steps_to_terminal_cycle": profile.shortcut_steps,
        "accelerated_steps_to_terminal_cycle": profile.accelerated_steps,
        "terminal_cycle_state": profile.terminal_state,
        "address_stabilization": (
            None
            if profile.stabilization_depth is None
            else {
                "block_depth": profile.stabilization_depth,
                "shortcut_steps": profile.stabilization_steps,
            }
        ),
        "post_address_first_passage_extensions": profile.post_stabilization_blocks,
        "failed_tail": {
            "length": profile.failed_tail_length,
            "odd_count": profile.failed_tail_odds,
            "exact_non_crossing": (
                f"3^{profile.failed_tail_odds}<="
                f"2^{profile.failed_tail_length}"
            ),
        },
    }


def tail_quotient(resource_bound: int, step_cap: int) -> dict[str, Any]:
    """Remove the forced initial word-1 prehistory from the resource sublevel."""

    count = 0
    maximum_depth = -1
    maximum_steps = -1
    champion: Profile | None = None
    champion_coordinates: tuple[int, int] | None = None
    records: list[dict[str, Any]] = []
    for exponent in range(resource_bound):
        for unit in range(1, resource_bound - exponent + 1):
            if math.gcd(unit, 6) != 1:
                continue
            seed = 3**exponent * unit - 1
            if seed < 1:
                continue
            count += 1
            profile = source_profile(seed, step_cap)
            maximum_steps = max(maximum_steps, profile.shortcut_steps)
            if profile.depth > maximum_depth:
                maximum_depth = profile.depth
                champion = profile
                champion_coordinates = (exponent, unit)
                records.append(
                    {
                        "depth": profile.depth,
                        "exponent_a_plus_b": exponent,
                        "unit": unit,
                        "seed": str(seed),
                        "resource": exponent + unit,
                    }
                )
    if champion is None or champion_coordinates is None:
        raise AssertionError("resource tail quotient was empty")
    traced = source_profile(champion.seed, step_cap, True)
    return {
        "meaning": (
            "2^a*3^b*u-1 executes exactly a initial word-1 blocks and then "
            "reaches the quotient tail 3^(a+b)*u-1 with the same resource"
        ),
        "unique_tail_coordinates": count,
        "coordinates": "c=a+b, u coprime to 6, c+u<=B",
        "maximum_tail_first_passage_depth": maximum_depth,
        "maximum_tail_shortcut_steps": maximum_steps,
        "record_rows": records,
        "champion": {
            **profile_summary(traced),
            "exponent_a_plus_b": champion_coordinates[0],
            "unit": champion_coordinates[1],
            "resource": champion_coordinates[0] + champion_coordinates[1],
        },
        "scope": (
            "exact quotient of the displayed resource sublevel; finite tail "
            "depth is not an infinite-orbit conclusion"
        ),
    }


def enumerate_sublevel(resource_bound: int, step_cap: int) -> dict[str, Any]:
    if resource_bound < 2 or step_cap < 1:
        raise ValueError("invalid resource or replay bound")

    count = 0
    maximum_depth = -1
    maximum_steps = -1
    maximum_steps_seed = 0
    records: list[dict[str, Any]] = []
    best: dict[int, tuple[int, int, int]] = {}
    champion_profile: Profile | None = None

    # Unique enumeration because u is required to be coprime to six.
    for a in range(resource_bound):
        for b in range(resource_bound - a):
            for unit in range(1, resource_bound - a - b + 1):
                if math.gcd(unit, 6) != 1:
                    continue
                score = a + b + unit
                seed = 2**a * 3**b * unit - 1
                if seed < 1:
                    continue
                if factor_2_3(seed + 1) != (a, b, unit):
                    raise AssertionError("unique mixed-base factorization changed")
                if resource(seed) != score or score > resource_bound:
                    raise AssertionError("resource-sublevel enumeration changed")
                count += 1
                profile = source_profile(seed, step_cap)
                depth = profile.depth
                if profile.shortcut_steps > maximum_steps:
                    maximum_steps = profile.shortcut_steps
                    maximum_steps_seed = seed
                for target_depth in range(1, depth + 1):
                    candidate = (score, seed, depth)
                    if target_depth not in best or candidate[:2] < best[target_depth][:2]:
                        best[target_depth] = candidate
                if depth > maximum_depth:
                    maximum_depth = depth
                    champion_profile = profile
                    records.append(
                        {
                            "depth": depth,
                            "R": score,
                            "seed": str(seed),
                            "steps": profile.shortcut_steps,
                        }
                    )

    if champion_profile is None:
        raise AssertionError("resource sublevel was empty")
    minima = [
        {
            "depth": depth,
            "R": best[depth][0],
            "seed": str(best[depth][1]),
            "seed_total_depth": best[depth][2],
        }
        for depth in sorted(best)
    ]
    exploratory_payload = {
        "schema": "temporary-resource23plus-sublevel-v1",
        "resource": "v2(n+1)+v3(n+1)+primitive_6(n+1)",
        "resource_bound": resource_bound,
        "step_cap": step_cap,
        "enumerated": count,
        "all_terminated": True,
        "maximum_terminal_steps": maximum_steps,
        "max_depth": maximum_depth,
        "record_rows": records,
        "minima_by_depth": minima,
        "counterexample": None,
    }
    exploratory_digest = hashlib.sha256(canonical_json(exploratory_payload)).hexdigest()

    # Recompute the champion with its literal boundary trace only once.
    champion = source_profile(champion_profile.seed, step_cap, True)
    boundary_words = [row.word for row in champion.boundaries]
    first_nontrivial = next(
        (row for row in champion.boundaries if row.word != "1"), None
    )
    if first_nontrivial is None:
        raise AssertionError("champion has no nontrivial first-passage word")

    next_depth = maximum_depth + 1
    nonempty_witness = 2**next_depth - 1
    nonempty_profile = source_profile(nonempty_witness, step_cap)
    if nonempty_profile.depth < next_depth:
        raise AssertionError("all-odd finite survivor witness lost its depth")

    return {
        **exploratory_payload,
        "exploratory_payload_sha256": exploratory_digest,
        "resource_definition": {
            "factorization": "n+1=2^a*3^b*u, gcd(u,6)=1",
            "formula": "R(n)=a+b+u",
            "coercivity_bound": "R(n)<=B implies n+1<=B*6^B",
            "sublevel_enumeration": (
                "all unique triples a,b>=0, u>=1, gcd(u,6)=1, a+b+u<=B"
            ),
            "one_step_isometry": (
                "odd n and a>=1: S(n)+1=2^(a-1)*3^(b+1)*u, "
                "hence R(S(n))=R(n)"
            ),
        },
        "forced_one_prehistory_quotient": tail_quotient(resource_bound, step_cap),
        "moment_optimization": {
            "resource_minimum_at_maximum_depth": best[maximum_depth][0],
            "minimizing_seed": str(best[maximum_depth][1]),
            "dirac_family_depth_range": [1, maximum_depth],
            "dirac_uniform_moment": resource(champion.seed),
            "next_depth": next_depth,
            "next_depth_resource_lower_bound": resource_bound + 1,
            "proof": (
                "every probability carried by depth-H survivors has R-moment "
                "at least min_{S_H} R; exhaustive emptiness of "
                "S_(max_depth+1) intersect {R<=B} gives the displayed lower bound"
            ),
            "next_depth_nonempty_witness": {
                "seed": str(nonempty_witness),
                "resource": resource(nonempty_witness),
                "first_passage_blocks": nonempty_profile.depth,
                "terminal": nonempty_profile.terminal_state == 2,
            },
        },
        "champion": {
            **profile_summary(champion),
            "resource": resource(champion.seed),
            "factorization": list(factor_2_3(champion.seed + 1)),
            "boundary_word_count": len(boundary_words),
            "boundary_words_sha256": hashlib.sha256(
                "|".join(boundary_words).encode()
            ).hexdigest(),
            "first_nontrivial_word": {
                "depth": first_nontrivial.depth,
                "word": first_nontrivial.word,
            },
        },
        "maximum_terminal_steps_witness": {
            "seed": str(maximum_steps_seed),
            "steps": maximum_steps,
        },
        "first_passage_resource_nonmonotonicity": {
            "first_increase": {
                "source": 134,
                "word": "011",
                "target": 152,
                "source_resource": 8,
                "target_resource": 19,
            },
            "decrease": {
                "source": 6,
                "word": "011",
                "target": 8,
                "source_resource": 7,
                "target_resource": 3,
            },
            "meaning": "R is a coercive seed moment, not a branchwise Lyapunov function",
        },
        "claim_scope": (
            "complete exact resource sublevel at the displayed B and replay cap; "
            "one uniform moment bound is refuted, but no all-B theorem or "
            "infinite ordinary survivor is claimed"
        ),
        "counterexample": None,
    }


def build_artifact(resource_bound: int, step_cap: int) -> dict[str, Any]:
    audit = enumerate_sublevel(resource_bound, step_cap)
    if (
        resource_bound == DEFAULT_RESOURCE_BOUND
        and step_cap == DEFAULT_STEP_CAP
        and audit["exploratory_payload_sha256"]
        != EXPECTED_EXPLORATORY_PAYLOAD_SHA256
    ):
        raise AssertionError("the independently advertised exploratory digest changed")
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": audit,
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    audit = artifact["audit"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "resource_bound": audit["resource_bound"],
        "enumerated": audit["enumerated"],
        "maximum_depth": audit["max_depth"],
        "maximum_quotient_tail_depth": audit["forced_one_prehistory_quotient"][
            "maximum_tail_first_passage_depth"
        ],
        "champion_seed": audit["champion"]["seed"],
        "champion_resource": audit["champion"]["resource"],
        "next_depth_resource_lower_bound": audit["moment_optimization"][
            "next_depth_resource_lower_bound"
        ],
        "exploratory_payload_sha256": audit["exploratory_payload_sha256"],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected resource-sublevel schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256", None)
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    audit = expected["audit"]
    actual = build_artifact(int(audit["resource_bound"]), int(audit["step_cap"]))
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if expected["audit"]["counterexample"] is not None:
        raise AssertionError("resource-sublevel artifact claims a counterexample")
    return report(expected)


def selftest() -> None:
    if factor_2_3(7 * 2**120) != (120, 0, 7):
        raise AssertionError("mixed-base factorization regression failed")
    if resource(7 * 2**120 - 1) != 127:
        raise AssertionError("champion resource regression failed")
    for seed in (1, 3, 5, 7, 15, 27, 135):
        if seed % 2 and resource(shortcut_step(seed)) != resource(seed):
            raise AssertionError("odd-step resource isometry failed")
    tiny = enumerate_sublevel(8, 1_000)
    if tiny["enumerated"] != 48 or tiny["max_depth"] != 14:
        raise AssertionError("tiny resource-sublevel enumeration changed")
    if tiny["forced_one_prehistory_quotient"]["maximum_tail_first_passage_depth"] != 9:
        raise AssertionError("tiny forced-one tail quotient changed")
    increase = source_profile(134, 1_000, True)
    decrease = source_profile(6, 1_000, True)
    if increase.boundaries[0].word != "011" or increase.boundaries[0].state != 152:
        raise AssertionError("first resource-increase witness changed")
    if decrease.boundaries[0].word != "011" or decrease.boundaries[0].state != 8:
        raise AssertionError("resource-decrease witness changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--resource-bound", type=int, default=DEFAULT_RESOURCE_BOUND)
    build.add_argument("--step-cap", type=int, default=DEFAULT_STEP_CAP)
    verify = sub.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    sub.add_parser("selftest")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print(json.dumps({"selftest": "ok", "counterexample": None}, sort_keys=True))
        return
    if args.command == "build":
        artifact = build_artifact(args.resource_bound, args.step_cap)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(report(artifact), indent=2, sort_keys=True))
        return
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
