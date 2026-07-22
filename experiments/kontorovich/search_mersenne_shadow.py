#!/usr/bin/env python3
"""Exact one-counter search around the signed Collatz fixed point -1.

The controller ``c=-1, w=(1)`` is the strongest elementary negative shadow:
``P/Q=3/2``.  A positive state ``x=2**M*h-1`` with odd ``h`` follows ``M``
nominal valuation-1 steps, except that the last valuation gains an exact
collision extra ``e``.  The endpoint identity is

    x' = (3**M*h - 1) / 2**e.

The next one-counter level requires ``x'=2**(M+1)*h'-1`` with odd positive
``h'``.  This worker compiles all bounded extra words in both mod-6 classes,
checks the shifted-coordinate identity, and literally replays every positive
path.  Finite outward runs are search events, not counterexamples.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from path_compiler import accelerated_step, compile_path, replay_word, v2


def macro_word(level: int, extra: int) -> tuple[int, ...]:
    if level <= 0 or extra <= 0:
        raise ValueError("counter level and collision extra must be positive")
    return (1,) * (level - 1) + (1 + extra,)


def program_word(start_level: int, extras: tuple[int, ...]) -> tuple[int, ...]:
    out: list[int] = []
    for offset, extra in enumerate(extras):
        out.extend(macro_word(start_level + offset, extra))
    return tuple(out)


def packet_coordinate(state: int, level: int) -> int | None:
    difference = state + 1
    modulus = 1 << level
    if difference <= 0 or difference % modulus:
        return None
    packet = difference // modulus
    return packet if packet % 2 else None


def trace_program(
    seed: int, start_level: int, extras: tuple[int, ...]
) -> dict[str, object]:
    n = seed
    states = [str(seed)]
    first_one_step = 0 if seed == 1 else None
    accelerated_offset = 0
    for offset, extra in enumerate(extras):
        level = start_level + offset
        packet = packet_coordinate(n, level)
        if packet is None:
            raise AssertionError("state misses its claimed -1 shadow class")
        raw_endpoint = pow(3, level) * packet - 1
        if v2(raw_endpoint) != extra:
            raise AssertionError("collision extra disagrees with exact valuation")
        word = macro_word(level, extra)
        endpoint = replay_word(n, word)
        if endpoint != raw_endpoint // (1 << extra):
            raise AssertionError("literal replay disagrees with Mersenne identity")
        if first_one_step is None:
            probe = n
            for index, expected in enumerate(word, start=1):
                probe, actual = accelerated_step(probe)
                if actual != expected:
                    raise AssertionError("literal trace valuation mismatch")
                if probe == 1:
                    first_one_step = accelerated_offset + index
                    break
        accelerated_offset += len(word)
        n = endpoint
        states.append(str(n))
        if offset + 1 < len(extras) and packet_coordinate(n, level + 1) is None:
            raise AssertionError("collision did not replenish the next level")
    integer_states = [int(x) for x in states]
    return {
        "states": states,
        "endpoint": str(n),
        "first_one_step": first_one_step,
        "all_macrosteps_grow": all(
            b > a for a, b in zip(integer_states, integer_states[1:])
        ),
        "terminal_level_aligned": packet_coordinate(
            n, start_level + len(extras)
        )
        is not None,
    }


def automatic_renewals(
    state: int, level: int, max_levels: int = 64
) -> list[dict[str, object]]:
    events = []
    n = state
    for _ in range(max_levels):
        packet = packet_coordinate(n, level)
        if packet is None:
            break
        raw = pow(3, level) * packet - 1
        extra = v2(raw)
        endpoint = raw // (1 << extra)
        aligned = packet_coordinate(endpoint, level + 1) is not None
        events.append(
            {
                "level": level,
                "extra": extra,
                "state": str(n),
                "endpoint": str(endpoint),
                "next_level_aligned": aligned,
                "grows": endpoint > n,
            }
        )
        if not aligned:
            break
        n = endpoint
        level += 1
    return events


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


def stable_key(event: dict[str, object] | None) -> tuple[int, int, int, int]:
    if event is None:
        return (-1, -1, -1, -1)
    return (
        int(event["stable_extensions"]),
        int(event["start_level"]),
        int(event["program_depth"]),
        -int(event["seed"]),
    )


def renewal_key(event: dict[str, object] | None) -> tuple[int, int, int]:
    if event is None:
        return (-1, -1, -1)
    return (
        int(event["start_level"]),
        int(event["program_depth"]),
        -int(event["seed"]),
    )


def search(
    *,
    min_start_level: int,
    max_start_level: int,
    max_extra: int,
    max_program_depth: int,
    continuation_steps: int,
) -> dict[str, object]:
    if not (
        1 <= min_start_level <= max_start_level
        and max_extra >= 1
        and max_program_depth >= 1
        and continuation_steps >= 1
    ):
        raise ValueError("invalid search bounds")

    programs = 0
    compiled_paths = 0
    stabilization_events = 0
    growing_stabilization_events = 0
    terminal_renewal_events = 0
    strongest_stabilization = None
    strongest_growing_stabilization = None
    highest_terminal_renewal = None

    for start_level in range(min_start_level, max_start_level + 1):
        for depth in range(1, max_program_depth + 1):
            for extras in itertools.product(range(1, max_extra + 1), repeat=depth):
                programs += 1
                word = program_word(start_level, extras)
                for residue in (1, 5):
                    compiled = compile_path(word, residue)
                    compiled_paths += 1
                    trace = trace_program(compiled.seed, start_level, extras)
                    stable_extensions = 0
                    if depth > 1:
                        for cut in range(depth - 1, 0, -1):
                            prefix_seed = compile_path(
                                program_word(start_level, extras[:cut]), residue
                            ).seed
                            if prefix_seed != compiled.seed:
                                break
                            stable_extensions += 1
                    event = {
                        "controller_state": "-1",
                        "controller_word": [1],
                        "start_level": start_level,
                        "extras": list(extras),
                        "program_depth": depth,
                        "residue_mod_6": residue,
                        "seed": str(compiled.seed),
                        "endpoint": str(compiled.endpoint),
                        "macro_states": trace["states"],
                        "stable_extensions": stable_extensions,
                        "first_one_step": trace["first_one_step"],
                        "all_macrosteps_grow": trace["all_macrosteps_grow"],
                        "terminal_level_aligned": trace[
                            "terminal_level_aligned"
                        ],
                    }
                    if stable_extensions:
                        stabilization_events += 1
                        if stable_key(event) > stable_key(strongest_stabilization):
                            strongest_stabilization = event
                        if trace["all_macrosteps_grow"]:
                            growing_stabilization_events += 1
                            if stable_key(event) > stable_key(
                                strongest_growing_stabilization
                            ):
                                strongest_growing_stabilization = event
                    if trace["terminal_level_aligned"]:
                        terminal_renewal_events += 1
                        event["automatic_continuation"] = automatic_renewals(
                            compiled.endpoint, start_level + depth
                        )
                        if renewal_key(event) > renewal_key(highest_terminal_renewal):
                            highest_terminal_renewal = event

    if strongest_growing_stabilization is not None:
        strongest_growing_stabilization = dict(strongest_growing_stabilization)
        strongest_growing_stabilization["continuation"] = bounded_fate(
            int(strongest_growing_stabilization["seed"]), continuation_steps
        )

    source = Path(__file__).read_bytes() + Path(__file__).with_name(
        "path_compiler.py"
    ).read_bytes()
    return {
        "schema": "collatz-mersenne-shadow-search-v1",
        "arithmetic": "exact_python_integers",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "bounds": {
            "min_start_level": min_start_level,
            "max_start_level": max_start_level,
            "max_extra": max_extra,
            "max_program_depth": max_program_depth,
            "continuation_steps": continuation_steps,
        },
        "programs": programs,
        "compiled_paths": compiled_paths,
        "seed_stabilization_events": stabilization_events,
        "growing_seed_stabilization_events": growing_stabilization_events,
        "terminal_renewal_events": terminal_renewal_events,
        "strongest_seed_stabilization": strongest_stabilization,
        "strongest_growing_seed_stabilization": strongest_growing_stabilization,
        "highest_start_level_terminal_renewal": highest_terminal_renewal,
    }


def selftest() -> None:
    # 2^7*187635-1 = 24017279 follows three exact outward shadow macros.
    extras = (4, 3, 1)
    seed = 24017279
    trace = trace_program(seed, 7, extras)
    assert trace["states"] == [
        "24017279",
        "25647359",
        "82164223",
        "1579334395",
    ]
    assert trace["all_macrosteps_grow"]
    assert not trace["terminal_level_aligned"]
    compiled = compile_path(program_word(7, extras), 5)
    parent = compile_path(program_word(7, extras[:-1]), 5)
    assert compiled.seed == parent.seed == seed

    tiny = search(
        min_start_level=1,
        max_start_level=2,
        max_extra=2,
        max_program_depth=2,
        continuation_steps=1000,
    )
    # Per level the extra-word tree has 2+2^2 nodes, each in two classes.
    assert tiny["programs"] == 2 * (2 + 4)
    assert tiny["compiled_paths"] == 2 * tiny["programs"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-start-level", type=int, default=1)
    parser.add_argument("--max-start-level", type=int, default=100)
    parser.add_argument("--max-extra", type=int, default=12)
    parser.add_argument("--max-program-depth", type=int, default=3)
    parser.add_argument("--continuation-steps", type=int, default=100000)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        print("search_mersenne_shadow selftest: PASS")
        return
    result = search(
        min_start_level=args.min_start_level,
        max_start_level=args.max_start_level,
        max_extra=args.max_extra,
        max_program_depth=args.max_program_depth,
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
