#!/usr/bin/env python3
"""Exact periodic-extra search for the -1/Mersenne shadow controller.

The valuation stream is not periodic: macro lengths increase with the counter.
Only the collision-extra controller is periodic.  Affine blocks are kept in
compressed exact form; every seed-stabilization hit is expanded and literally
replayed before it is recorded.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from path_compiler import AffineBlock, affine_block, compile_block, replay_word
from search_mersenne_shadow import bounded_fate, macro_word, trace_program


def primitive_templates(max_period: int, max_extra: int):
    for period in range(1, max_period + 1):
        for template in itertools.product(range(1, max_extra + 1), repeat=period):
            if any(
                period % divisor == 0
                and all(template[i] == template[i % divisor] for i in range(period))
                for divisor in range(1, period)
            ):
                continue
            yield template


def macro_block(level: int, extra: int) -> AffineBlock:
    if level <= 0 or extra <= 0:
        raise ValueError("counter level and collision extra must be positive")
    return AffineBlock(
        steps=level,
        halvings=level + extra,
        constant=pow(3, level) - (1 << level),
    )


def event_key(event: dict[str, object] | None) -> tuple[int, int, int, int]:
    if event is None:
        return (-1, -1, -1, -1)
    return (
        int(event["stable_extensions"]),
        int(event["program_depth"]),
        int(event["start_level"]),
        -int(event["seed"]),
    )


def search(
    *,
    max_start_level: int,
    max_extra: int,
    max_period: int,
    max_depth: int,
    continuation_steps: int,
) -> dict[str, object]:
    if min(
        max_start_level, max_extra, max_period, max_depth, continuation_steps
    ) < 1:
        raise ValueError("all search bounds must be positive")
    templates = list(primitive_templates(max_period, max_extra))
    compiled_paths = 0
    stabilization_events = 0
    two_extension_events = 0
    growing_stabilization_events = 0
    best = None
    best_growing = None

    for start_level in range(1, max_start_level + 1):
        for template in templates:
            block = AffineBlock.identity()
            previous_seed = {1: None, 5: None}
            stable = {1: 0, 5: 0}
            extras: list[int] = []
            for depth in range(1, max_depth + 1):
                extra = template[(depth - 1) % len(template)]
                extras.append(extra)
                block = block.then(macro_block(start_level + depth - 1, extra))
                for residue in (1, 5):
                    compiled = compile_block(block, residue)
                    compiled_paths += 1
                    if compiled.seed == previous_seed[residue]:
                        stable[residue] += 1
                        stabilization_events += 1
                        if stable[residue] >= 2:
                            two_extension_events += 1
                        expanded = tuple(
                            k
                            for offset, collision_extra in enumerate(extras)
                            for k in macro_word(
                                start_level + offset, collision_extra
                            )
                        )
                        endpoint = replay_word(compiled.seed, expanded)
                        if endpoint != compiled.endpoint:
                            raise AssertionError("compressed event failed literal replay")
                        trace = trace_program(
                            compiled.seed, start_level, tuple(extras)
                        )
                        event = {
                            "controller_state": "-1",
                            "controller_word": [1],
                            "start_level": start_level,
                            "primitive_extra_period": list(template),
                            "program_depth": depth,
                            "residue_mod_6": residue,
                            "seed": str(compiled.seed),
                            "endpoint": str(compiled.endpoint),
                            "stable_extensions": stable[residue],
                            "macro_states": trace["states"],
                            "all_macrosteps_grow": trace[
                                "all_macrosteps_grow"
                            ],
                        }
                        if event_key(event) > event_key(best):
                            best = event
                        if trace["all_macrosteps_grow"]:
                            growing_stabilization_events += 1
                            if event_key(event) > event_key(best_growing):
                                best_growing = event
                    else:
                        stable[residue] = 0
                    previous_seed[residue] = compiled.seed

    for event in (best, best_growing):
        if event is not None:
            event["continuation"] = bounded_fate(
                int(event["seed"]), continuation_steps
            )
    source = (
        Path(__file__).read_bytes()
        + Path(__file__).with_name("search_mersenne_shadow.py").read_bytes()
        + Path(__file__).with_name("path_compiler.py").read_bytes()
    )
    return {
        "schema": "collatz-mersenne-periodic-extra-search-v1",
        "arithmetic": "exact_python_integers",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "bounds": {
            "max_start_level": max_start_level,
            "max_extra": max_extra,
            "max_period": max_period,
            "max_depth": max_depth,
            "continuation_steps": continuation_steps,
        },
        "primitive_templates": len(templates),
        "compiled_paths": compiled_paths,
        "seed_stabilization_events": stabilization_events,
        "two_extension_stabilization_events": two_extension_events,
        "growing_seed_stabilization_events": growing_stabilization_events,
        "strongest_seed_stabilization": best,
        "strongest_growing_seed_stabilization": best_growing,
    }


def selftest() -> None:
    assert list(primitive_templates(2, 2)) == [(1,), (2,), (1, 2), (2, 1)]
    for level in range(1, 8):
        for extra in range(1, 6):
            reference = affine_block(macro_word(level, extra))
            assert macro_block(level, extra) == reference
    tiny = search(
        max_start_level=2,
        max_extra=2,
        max_period=2,
        max_depth=5,
        continuation_steps=1000,
    )
    assert tiny["primitive_templates"] == 4
    assert tiny["compiled_paths"] == 2 * 4 * 5 * 2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-start-level", type=int, default=30)
    parser.add_argument("--max-extra", type=int, default=8)
    parser.add_argument("--max-period", type=int, default=3)
    parser.add_argument("--max-depth", type=int, default=80)
    parser.add_argument("--continuation-steps", type=int, default=100000)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        print("search_mersenne_periodic selftest: PASS")
        return
    result = search(
        max_start_level=args.max_start_level,
        max_extra=args.max_extra,
        max_period=args.max_period,
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
