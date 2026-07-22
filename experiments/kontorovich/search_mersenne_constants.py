#!/usr/bin/env python3
"""Exact constant-extra search for the -1/Mersenne shadow controller.

For each start level M0 and fixed collision extra e, compile the nested words

    B(M0,e), B(M0+1,e), ...,

where ``B(M,e) = (1,...,1,1+e)`` has length M.  Eventual stabilization of the
canonical seeds is exactly the ordinary-integer gate.  A finite stabilization
run is only a prefix event.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from path_compiler import accelerated_step, compile_path, replay_word
from search_mersenne_shadow import macro_word


def bounded_fate(seed: int, max_steps: int) -> dict[str, object]:
    n = seed
    peak = seed
    seen: dict[int, int] = {}
    for step in range(max_steps + 1):
        if n == 1:
            return {
                "status": "reaches_one",
                "accelerated_steps": step,
                "peak": str(peak),
            }
        if n in seen:
            return {
                "status": "cycle",
                "preperiod": seen[n],
                "period": step - seen[n],
                "cycle_seed": str(n),
                "peak": str(peak),
            }
        if step == max_steps:
            break
        seen[n] = step
        n, _ = accelerated_step(n)
        peak = max(peak, n)
    return {
        "status": "unresolved_within_bound",
        "max_accelerated_steps": max_steps,
        "last_value": str(n),
        "peak": str(peak),
    }


def macro_states(seed: int, start_level: int, extra: int, depth: int) -> list[str]:
    states = [str(seed)]
    n = seed
    for offset in range(depth):
        n = replay_word(n, macro_word(start_level + offset, extra))
        states.append(str(n))
    return states


def event_key(event: dict[str, object] | None) -> tuple[int, int, int]:
    if event is None:
        return (-1, -1, -1)
    return (
        int(event["stable_extensions"]),
        int(event["program_depth"]),
        -int(event["seed"]),
    )


def search(
    *,
    max_start_level: int,
    max_extra: int,
    max_depth: int,
    continuation_steps: int,
) -> dict[str, object]:
    if min(max_start_level, max_extra, max_depth, continuation_steps) < 1:
        raise ValueError("all bounds must be positive")
    compiled_paths = 0
    stabilization_events = 0
    two_extension_events = 0
    best = None
    for start_level in range(1, max_start_level + 1):
        for extra in range(1, max_extra + 1):
            words: list[int] = []
            previous_seed = {1: None, 5: None}
            stable = {1: 0, 5: 0}
            for depth in range(1, max_depth + 1):
                words.extend(macro_word(start_level + depth - 1, extra))
                for residue in (1, 5):
                    compiled = compile_path(tuple(words), residue)
                    compiled_paths += 1
                    if compiled.seed == previous_seed[residue]:
                        stable[residue] += 1
                        stabilization_events += 1
                        if stable[residue] >= 2:
                            two_extension_events += 1
                        event = {
                            "controller_state": "-1",
                            "controller_word": [1],
                            "start_level": start_level,
                            "constant_extra": extra,
                            "program_depth": depth,
                            "residue_mod_6": residue,
                            "seed": str(compiled.seed),
                            "endpoint": str(compiled.endpoint),
                            "stable_extensions": stable[residue],
                            "macro_states": macro_states(
                                compiled.seed, start_level, extra, depth
                            ),
                        }
                        if event_key(event) > event_key(best):
                            best = event
                    else:
                        stable[residue] = 0
                    previous_seed[residue] = compiled.seed
    if best is not None:
        best = dict(best)
        best["continuation"] = bounded_fate(
            int(best["seed"]), continuation_steps
        )
    source = (
        Path(__file__).read_bytes()
        + Path(__file__).with_name("search_mersenne_shadow.py").read_bytes()
        + Path(__file__).with_name("path_compiler.py").read_bytes()
    )
    return {
        "schema": "collatz-mersenne-constant-extra-search-v1",
        "arithmetic": "exact_python_integers",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "bounds": {
            "max_start_level": max_start_level,
            "max_extra": max_extra,
            "max_depth": max_depth,
            "continuation_steps": continuation_steps,
        },
        "compiled_paths": compiled_paths,
        "seed_stabilization_events": stabilization_events,
        "two_extension_stabilization_events": two_extension_events,
        "strongest_seed_stabilization": best,
    }


def selftest() -> None:
    word: list[int] = []
    seeds = []
    for level in range(1, 6):
        word.extend(macro_word(level, 1))
        seeds.append(compile_path(tuple(word), 1).seed)
    assert seeds == [1, 121, 121, 121, 295033]
    assert macro_states(121, 1, 1, 4) == ["121", "91", "103", "175", "445"]
    tiny = search(
        max_start_level=2,
        max_extra=2,
        max_depth=3,
        continuation_steps=1000,
    )
    assert tiny["compiled_paths"] == 2 * 2 * 3 * 2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-start-level", type=int, default=20)
    parser.add_argument("--max-extra", type=int, default=32)
    parser.add_argument("--max-depth", type=int, default=40)
    parser.add_argument("--continuation-steps", type=int, default=100000)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        print("search_mersenne_constants selftest: PASS")
        return
    result = search(
        max_start_level=args.max_start_level,
        max_extra=args.max_extra,
        max_depth=args.max_depth,
        continuation_steps=args.continuation_steps,
    )
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
