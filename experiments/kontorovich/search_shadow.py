#!/usr/bin/env python3
"""Exact search for one-counter gliders shadowing negative Collatz cycles.

A negative accelerated cycle supplies a finite controller, not a
counterexample.  If its valuation word has multiplier ``P/Q > 1`` and fixed
negative state ``c``, a positive state

    x = c + Q**M * h

with odd ``h`` shadows the controller for ``M`` repetitions.  At the final
valuation the packet collides with the controller.  If the valuation is larger
than the controller's by ``e``, the exact endpoint is

    (c + P**M * h) / 2**e.

The one-counter glider ansatz asks this endpoint to have the form
``c + Q**(M+1) * h'`` and repeats at the next level.  This program enumerates
bounded extra-valuation programs, compiles their least ordinary positive
seeds, and literally replays every claimed macrostep.  Finite renewal or seed
stabilization is only a search event, never a disproof.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from pathlib import Path

from path_compiler import compile_path, replay_word, v2


@dataclass(frozen=True)
class Controller:
    name: str
    fixed_state: int
    word: tuple[int, ...]

    @property
    def steps(self) -> int:
        return len(self.word)

    @property
    def halvings(self) -> int:
        return sum(self.word)

    @property
    def numerator_multiplier(self) -> int:
        return pow(3, self.steps)

    @property
    def denominator_multiplier(self) -> int:
        return 1 << self.halvings


CONTROLLERS = (
    Controller("minus5", -5, (1, 2)),
    Controller("minus17", -17, (1, 1, 1, 2, 1, 1, 4)),
)


def signed_accelerated_step(n: int) -> tuple[int, int]:
    if n == 0 or n % 2 == 0:
        raise ValueError("signed accelerated step requires a nonzero odd integer")
    a = 3 * n + 1
    k = v2(a)
    return a // (1 << k), k


def validate_controller(controller: Controller) -> None:
    if controller.fixed_state >= 0 or not controller.word:
        raise ValueError("controller must have a negative fixed state and a word")
    n = controller.fixed_state
    for expected in controller.word:
        n, actual = signed_accelerated_step(n)
        if actual != expected:
            raise ValueError(f"{controller.name}: illegal controller valuation word")
    if n != controller.fixed_state:
        raise ValueError(f"{controller.name}: controller word does not close")
    if controller.numerator_multiplier <= controller.denominator_multiplier:
        raise ValueError(f"{controller.name}: controller is not supercritical")


def macro_word(controller: Controller, level: int, extra: int) -> tuple[int, ...]:
    if level <= 0 or extra <= 0:
        raise ValueError("level and collision extra must be positive")
    out = list(controller.word) * level
    out[-1] += extra
    return tuple(out)


def program_word(
    controller: Controller, start_level: int, extras: tuple[int, ...]
) -> tuple[int, ...]:
    out: list[int] = []
    for offset, extra in enumerate(extras):
        out.extend(macro_word(controller, start_level + offset, extra))
    return tuple(out)


def shadow_coordinate(
    controller: Controller, state: int, level: int
) -> int | None:
    modulus = pow(controller.denominator_multiplier, level)
    difference = state - controller.fixed_state
    if difference <= 0 or difference % modulus:
        return None
    packet = difference // modulus
    return packet if packet % 2 else None


def trace_program(
    controller: Controller,
    seed: int,
    start_level: int,
    extras: tuple[int, ...],
) -> dict[str, object]:
    """Replay every macro and verify the shifted-coordinate identity."""
    n = seed
    first_one_step = 0 if n == 1 else None
    accelerated_steps = 0
    states: list[str] = [str(n)]
    packet_bits: list[int] = []
    for offset, extra in enumerate(extras):
        level = start_level + offset
        packet = shadow_coordinate(controller, n, level)
        if packet is None:
            raise AssertionError("program state is not in its claimed shadow class")
        packet_bits.append(packet.bit_length())
        raw_endpoint = (
            controller.fixed_state
            + pow(controller.numerator_multiplier, level) * packet
        )
        if v2(raw_endpoint) != extra:
            raise AssertionError("collision extra disagrees with exact valuation")
        word = macro_word(controller, level, extra)
        endpoint = replay_word(n, word)
        expected = raw_endpoint // (1 << extra)
        if endpoint != expected:
            raise AssertionError("literal macro replay disagrees with packet identity")
        if first_one_step is None:
            probe = n
            for index, k in enumerate(word, start=1):
                probe = (3 * probe + 1) >> k
                if probe == 1:
                    first_one_step = accelerated_steps + index
                    break
        accelerated_steps += len(word)
        n = endpoint
        states.append(str(n))
        if offset + 1 < len(extras):
            next_level = level + 1
            if shadow_coordinate(controller, n, next_level) is None:
                raise AssertionError("program did not replenish the next shadow level")
    return {
        "seed": str(seed),
        "endpoint": str(n),
        "states": states,
        "packet_bit_lengths": packet_bits,
        "first_one_step": first_one_step,
        "accelerated_steps": accelerated_steps,
        "next_level_aligned": shadow_coordinate(
            controller, n, start_level + len(extras)
        )
        is not None,
    }


def event_key(event: dict[str, object] | None) -> tuple[int, int, int]:
    if event is None:
        return (-1, -1, -1)
    return (
        int(event["stable_extensions"]),
        len(event["extras"]),
        -int(event["seed"]),
    )


def search(
    *, max_start_level: int, max_extra: int, max_program_depth: int
) -> dict[str, object]:
    if max_start_level < 1 or max_extra < 1 or max_program_depth < 1:
        raise ValueError("all search bounds must be positive")

    program_prefixes = 0
    compiled_paths = 0
    seed_stabilization_events = 0
    one_avoiding_stabilization_events = 0
    terminal_renewal_events = 0
    best_stabilization = None
    best_one_avoiding_stabilization = None
    best_terminal_renewal = None

    for controller in CONTROLLERS:
        validate_controller(controller)
        for start_level in range(1, max_start_level + 1):
            stack: list[
                tuple[tuple[int, ...], dict[int, int | None], dict[int, int]]
            ] = [((), {1: None, 5: None}, {1: 0, 5: 0})]
            while stack:
                extras, parent_seed, parent_stable = stack.pop()
                if len(extras) == max_program_depth:
                    continue
                for extra in range(1, max_extra + 1):
                    child = extras + (extra,)
                    word = program_word(controller, start_level, child)
                    program_prefixes += 1
                    child_seed: dict[int, int | None] = {}
                    child_stable: dict[int, int] = {}
                    for residue in (1, 5):
                        compiled = compile_path(word, residue)
                        compiled_paths += 1
                        trace = trace_program(
                            controller, compiled.seed, start_level, child
                        )
                        child_seed[residue] = compiled.seed
                        stable = (
                            parent_stable[residue] + 1
                            if compiled.seed == parent_seed[residue]
                            else 0
                        )
                        child_stable[residue] = stable
                        event = {
                            "controller": controller.name,
                            "fixed_state": str(controller.fixed_state),
                            "controller_word": list(controller.word),
                            "start_level": start_level,
                            "extras": list(child),
                            "residue_mod_6": residue,
                            "seed": str(compiled.seed),
                            "endpoint": str(compiled.endpoint),
                            "stable_extensions": stable,
                            "first_one_step": trace["first_one_step"],
                            "next_level_aligned": trace["next_level_aligned"],
                        }
                        if trace["next_level_aligned"]:
                            terminal_renewal_events += 1
                            if event_key(event) > event_key(best_terminal_renewal):
                                best_terminal_renewal = event
                        if stable:
                            seed_stabilization_events += 1
                            if event_key(event) > event_key(best_stabilization):
                                best_stabilization = event
                            if trace["first_one_step"] is None:
                                one_avoiding_stabilization_events += 1
                                if event_key(event) > event_key(
                                    best_one_avoiding_stabilization
                                ):
                                    best_one_avoiding_stabilization = event
                    stack.append((child, child_seed, child_stable))

    source = Path(__file__).read_bytes() + Path(__file__).with_name(
        "path_compiler.py"
    ).read_bytes()
    return {
        "schema": "collatz-negative-shadow-search-v1",
        "arithmetic": "exact_python_integers",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "bounds": {
            "max_start_level": max_start_level,
            "max_extra": max_extra,
            "max_program_depth": max_program_depth,
            "controllers": [controller.name for controller in CONTROLLERS],
        },
        "program_prefixes": program_prefixes,
        "compiled_paths": compiled_paths,
        "seed_stabilization_events": seed_stabilization_events,
        "one_avoiding_seed_stabilization_events": (
            one_avoiding_stabilization_events
        ),
        "terminal_renewal_events": terminal_renewal_events,
        "best_seed_stabilization": best_stabilization,
        "best_one_avoiding_seed_stabilization": (
            best_one_avoiding_stabilization
        ),
        "best_terminal_renewal": best_terminal_renewal,
    }


def selftest() -> None:
    for controller in CONTROLLERS:
        validate_controller(controller)

    controller = CONTROLLERS[0]
    # x=8^2-5=59 shadows -5 for two (1,2) blocks.  The last valuation
    # gains two powers of two, so (1,2,1,4) ends exactly at 19.
    word = macro_word(controller, 2, 2)
    assert word == (1, 2, 1, 4)
    assert shadow_coordinate(controller, 59, 2) == 1
    trace = trace_program(controller, 59, 2, (2,))
    assert trace["endpoint"] == "19"
    assert replay_word(59, word) == 19

    tiny = search(max_start_level=2, max_extra=2, max_program_depth=2)
    # For each of two controllers and two start levels, the extra-word tree
    # has 2+2^2 nodes; every node is compiled in both admissible classes.
    assert tiny["program_prefixes"] == 2 * 2 * (2 + 4)
    assert tiny["compiled_paths"] == 2 * tiny["program_prefixes"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-start-level", type=int, default=6)
    parser.add_argument("--max-extra", type=int, default=8)
    parser.add_argument("--max-program-depth", type=int, default=4)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        print("search_shadow selftest: PASS")
        return
    result = search(
        max_start_level=args.max_start_level,
        max_extra=args.max_extra,
        max_program_depth=args.max_program_depth,
    )
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
