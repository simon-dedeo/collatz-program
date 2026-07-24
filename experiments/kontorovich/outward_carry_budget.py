#!/usr/bin/env python3
"""Exact finite-subcode dynamic program for coherent extension carry.

For a schedule prefix ``u`` let ``rho_u`` be its canonical dyadic source
residue and ``L_u`` its total bit length.  Extending by a first-passage word
``w`` has one exact natural carry

    rho_(uw) = rho_u + 2^L_u q(u,w).

On a fixed finite word code, an ordinary infinite execution exists iff one
constant bounds the cumulative integer carry along prefixes of every depth.
This worker exhausts the tree below a stated carry budget.  Exhaustion at a
finite depth rejects that budget for that code; it does not reject larger
budgets, the full first-passage language, or the Collatz conjecture.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, NamedTuple, Sequence

try:
    from . import outward_coherent_cegis as coherent
    from . import outward_first_passage as first_passage
except ImportError:
    import outward_coherent_cegis as coherent
    import outward_first_passage as first_passage


SCHEMA = "collatz-outward-carry-budget-v1"
DEFAULT_WORD_LENGTH = 14
DEFAULT_SOURCE_RESIDUE_BOUND = 50
DEFAULT_CARRY_BUDGET = 28
DEFAULT_DEPTH_CAP = 200


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def dependency_sha256(module: Any) -> str:
    return hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()


def integer_sha256(value: int) -> str:
    width = max(1, (value.bit_length() + 7) // 8)
    return hashlib.sha256(value.to_bytes(width, "big")).hexdigest()


class State(NamedTuple):
    rho: int
    length: int
    odd_count: int
    target: int
    carry: int
    path_code: int


ROOT = State(0, 0, 0, 0, 0, 0)


def selected_words(
    maximum_word_length: int, source_residue_bound: int
) -> tuple[list[coherent.WordData], int]:
    words, frontier = coherent.bounded_first_passage_words(maximum_word_length)
    selected = [row for row in words if row.r <= source_residue_bound]
    if not selected:
        raise ValueError("selected finite first-passage subcode is empty")
    return selected, frontier


def extend(state: State, word: coherent.WordData, word_index: int, radix: int) -> State:
    modulus = 2**word.S
    power = 3**state.odd_count
    q = ((word.r - state.target) * pow(power, -1, modulus)) % modulus
    boundary_source = state.target + power * q
    difference = boundary_source - word.r
    if difference < 0 or difference % modulus:
        raise AssertionError("exact carry missed the next word cylinder")
    parameter = difference // modulus
    target = word.b + 3**word.O * parameter
    rho = state.rho + 2**state.length * q
    return State(
        rho,
        state.length + word.S,
        state.odd_count + word.O,
        target,
        state.carry + q,
        state.path_code * radix + word_index,
    )


def decode_path(code: int, depth: int, radix: int) -> list[int]:
    result = [0] * depth
    for index in range(depth - 1, -1, -1):
        code, result[index] = divmod(code, radix)
    if code:
        raise AssertionError("path code exceeded its declared depth")
    return result


def literal_replay(state: State, depth: int, words: list[coherent.WordData]) -> dict[str, Any]:
    indices = decode_path(state.path_code, depth, len(words))
    schedule = [words[index].word for index in indices]
    value = state.rho
    for word in schedule:
        value = coherent.execute_word(word, value)
    if value != state.target:
        raise AssertionError("deepest prefix failed literal schedule replay")
    profile = first_passage.source_profile(state.rho, 100_000, True)
    actual = [str(row["word"]) for row in profile["boundaries"]]
    if actual[:depth] != schedule:
        raise AssertionError("ordinary seed did not realize the decoded schedule")
    return {
        "depth": depth,
        "seed": str(state.rho),
        "seed_bits": state.rho.bit_length(),
        "seed_sha256": integer_sha256(state.rho),
        "total_carry": state.carry,
        "total_bit_length": state.length,
        "total_odd_count": state.odd_count,
        "canonical_target": str(state.target),
        "schedule_indices": indices,
        "schedule_sha256": hashlib.sha256("|".join(schedule).encode()).hexdigest(),
        "ordinary_total_first_passage_blocks": int(profile["first_passage_blocks"]),
        "ordinary_shortcut_steps_to_terminal_cycle": int(
            profile["shortcut_steps_to_terminal_cycle"]
        ),
        "ordinary_terminal_cycle_state": int(profile["terminal_cycle_state"]),
    }


def exhaust(
    maximum_word_length: int,
    source_residue_bound: int,
    carry_budget: int,
    depth_cap: int,
) -> dict[str, Any]:
    if maximum_word_length < 1 or source_residue_bound < 1:
        raise ValueError("word and residue bounds must be positive")
    if carry_budget < 0 or depth_cap < 1:
        raise ValueError("carry budget and depth cap are invalid")
    words, frontier = selected_words(maximum_word_length, source_residue_bound)
    radix = len(words)
    layer = [ROOT]
    rows: list[dict[str, Any]] = []
    total_nodes = 1
    deepest_layer: list[State] = []
    status = "depth_cap"

    for depth in range(1, depth_cap + 1):
        next_layer: list[State] = []
        for state in layer:
            for word_index, word in enumerate(words):
                child = extend(state, word, word_index, radix)
                if child.carry <= carry_budget:
                    next_layer.append(child)
        layer = next_layer
        total_nodes += len(layer)
        rows.append(
            {
                "depth": depth,
                "population": len(layer),
                "minimum_total_carry": (
                    min(state.carry for state in layer) if layer else None
                ),
                "maximum_total_carry": (
                    max(state.carry for state in layer) if layer else None
                ),
                "minimum_seed_bits": (
                    min(state.rho.bit_length() for state in layer) if layer else None
                ),
            }
        )
        if not layer:
            status = "exhausted"
            break
        deepest_layer = layer

    if not deepest_layer:
        raise AssertionError("carry tree had no positive-depth prefix")
    deepest = min(
        deepest_layer,
        key=lambda state: (state.carry, state.rho.bit_length(), state.rho),
    )
    deepest_depth = rows[-2]["depth"] if status == "exhausted" else rows[-1]["depth"]
    word_rows = [
        {
            "word": row.word,
            "S": row.S,
            "O": row.O,
            "r": row.r,
            "b": row.b,
        }
        for row in words
    ]
    return {
        "bounds": {
            "maximum_word_length": maximum_word_length,
            "source_residue_bound": source_residue_bound,
            "carry_budget": carry_budget,
            "depth_cap": depth_cap,
        },
        "finite_subcode": word_rows,
        "finite_subcode_sha256": hashlib.sha256(canonical_json(word_rows)).hexdigest(),
        "unselected_nonoutward_prefix_frontier": frontier,
        "status": status,
        "depth_rows": rows,
        "total_prefix_nodes_checked": total_nodes,
        "maximum_layer_population": max(row["population"] for row in rows),
        "deepest_nonempty_depth": deepest_depth,
        "first_empty_depth": rows[-1]["depth"] if status == "exhausted" else None,
        "deepest_replay_witness": literal_replay(deepest, deepest_depth, words),
        "theorem_interface": (
            "for a fixed finite first-passage subcode, an ordinary infinite "
            "execution exists iff one natural K bounds cumulative exact extension "
            "carry on some compatible prefix at every depth"
        ),
        "bounded_conclusion": (
            f"no schedule in the displayed finite subcode reaches depth "
            f"{rows[-1]['depth']} with total carry <= {carry_budget}"
            if status == "exhausted"
            else "the declared depth cap was reached with surviving prefixes"
        ),
        "claim_scope": (
            "exhaustive exact finite-subcode tree below the displayed carry and "
            "depth bounds; no conclusion for larger budgets or the full language"
        ),
        "counterexample": None,
    }


def build_artifact(args: argparse.Namespace) -> dict[str, Any]:
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "dependency_sha256": {
            "outward_coherent_cegis.py": dependency_sha256(coherent),
            "outward_first_passage.py": dependency_sha256(first_passage),
        },
        "audit": exhaust(
            args.maximum_word_length,
            args.source_residue_bound,
            args.carry_budget,
            args.depth_cap,
        ),
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    audit = artifact["audit"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "finite_subcode": [row["word"] for row in audit["finite_subcode"]],
        "carry_budget": audit["bounds"]["carry_budget"],
        "total_prefix_nodes_checked": audit["total_prefix_nodes_checked"],
        "deepest_nonempty_depth": audit["deepest_nonempty_depth"],
        "first_empty_depth": audit["first_empty_depth"],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected carry-budget schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    dependencies = {
        "outward_coherent_cegis.py": dependency_sha256(coherent),
        "outward_first_passage.py": dependency_sha256(first_passage),
    }
    if expected.get("dependency_sha256") != dependencies:
        raise ValueError("dependency hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256", None)
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    bounds = expected["audit"]["bounds"]
    args = argparse.Namespace(
        maximum_word_length=int(bounds["maximum_word_length"]),
        source_residue_bound=int(bounds["source_residue_bound"]),
        carry_budget=int(bounds["carry_budget"]),
        depth_cap=int(bounds["depth_cap"]),
    )
    actual = build_artifact(args)
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if expected["audit"]["counterexample"] is not None:
        raise AssertionError("carry-budget artifact claims a counterexample")
    return report(expected)


def selftest() -> None:
    words, _ = selected_words(14, 50)
    if [row.word for row in words] != ["1", "011", "010111"]:
        raise AssertionError("tiny finite subcode changed")
    state = ROOT
    reference = coherent.ROOT
    for index in (0, 1, 2, 0):
        state = extend(state, words[index], index, len(words))
        reference = coherent.extend_node(reference, words[index])
        if (state.rho, state.length, state.odd_count, state.target) != (
            reference.rho,
            reference.L,
            reference.Q,
            reference.y,
        ):
            raise AssertionError("compact extension disagrees with reference")
        if state.carry != sum(reference.carries):
            raise AssertionError("compact cumulative carry disagrees with reference")
    tiny = exhaust(8, 50, 4, 20)
    if tiny["status"] != "exhausted" or tiny["first_empty_depth"] != 5:
        raise AssertionError("tiny carry-budget exhaustion changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-word-length", type=int, default=DEFAULT_WORD_LENGTH)
    build.add_argument(
        "--source-residue-bound", type=int, default=DEFAULT_SOURCE_RESIDUE_BOUND
    )
    build.add_argument("--carry-budget", type=int, default=DEFAULT_CARRY_BUDGET)
    build.add_argument("--depth-cap", type=int, default=DEFAULT_DEPTH_CAP)
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
        artifact = build_artifact(args)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(report(artifact), indent=2, sort_keys=True))
        return
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
