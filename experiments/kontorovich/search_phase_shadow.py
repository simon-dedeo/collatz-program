#!/usr/bin/env python3
"""Exact phase-changing negative-cycle shadow search.

This enlarges ``search_shadow.py`` by allowing each collision to land near a
different phase of the same negative cycle.  A program symbol is a pair
``(phase, extra)``.  At counter level M, phase ``c_i`` emits M copies of the
cycle word rotated to start at ``c_i``, with ``extra`` added to the final
valuation.  The next symbol must begin in the claimed phase at precision
``Q**(M+1)``.  Every compiled positive program is literally replayed.

Finite renewal and finite canonical-seed stabilization remain search events,
not counterexamples.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from pathlib import Path

from path_compiler import accelerated_step, compile_path, replay_word, v2
from search_shadow import signed_accelerated_step


@dataclass(frozen=True)
class NegativeCycle:
    name: str
    base_state: int
    base_word: tuple[int, ...]
    phase_states: tuple[int, ...]

    @property
    def steps(self) -> int:
        return len(self.base_word)

    @property
    def halvings(self) -> int:
        return sum(self.base_word)

    @property
    def numerator_multiplier(self) -> int:
        return pow(3, self.steps)

    @property
    def denominator_multiplier(self) -> int:
        return 1 << self.halvings

    def phase_word(self, phase: int) -> tuple[int, ...]:
        return self.base_word[phase:] + self.base_word[:phase]


def make_cycle(name: str, state: int, word: tuple[int, ...]) -> NegativeCycle:
    phases = []
    n = state
    for expected in word:
        phases.append(n)
        n, actual = signed_accelerated_step(n)
        if actual != expected:
            raise ValueError(f"{name}: base word has an illegal valuation")
    if n != state:
        raise ValueError(f"{name}: base word does not close")
    cycle = NegativeCycle(name, state, word, tuple(phases))
    if cycle.numerator_multiplier <= cycle.denominator_multiplier:
        raise ValueError(f"{name}: negative controller is not supercritical")
    return cycle


CYCLES = {
    "minus5": make_cycle("minus5", -5, (1, 2)),
    "minus17": make_cycle("minus17", -17, (1, 1, 1, 2, 1, 1, 4)),
}


def macro_word(
    cycle: NegativeCycle, phase: int, level: int, extra: int
) -> tuple[int, ...]:
    if not (0 <= phase < cycle.steps) or level <= 0 or extra <= 0:
        raise ValueError("invalid phase, counter level, or collision extra")
    word = list(cycle.phase_word(phase)) * level
    word[-1] += extra
    return tuple(word)


def program_word(
    cycle: NegativeCycle,
    start_level: int,
    program: tuple[tuple[int, int], ...],
) -> tuple[int, ...]:
    out: list[int] = []
    for offset, (phase, extra) in enumerate(program):
        out.extend(macro_word(cycle, phase, start_level + offset, extra))
    return tuple(out)


def phase_coordinate(
    cycle: NegativeCycle, state: int, level: int, phase: int
) -> int | None:
    modulus = pow(cycle.denominator_multiplier, level)
    difference = state - cycle.phase_states[phase]
    if difference <= 0 or difference % modulus:
        return None
    packet = difference // modulus
    return packet if packet % 2 else None


def compatible_phases(
    cycle: NegativeCycle, state: int, level: int
) -> list[int]:
    return [
        phase
        for phase in range(cycle.steps)
        if phase_coordinate(cycle, state, level, phase) is not None
    ]


def trace_program(
    cycle: NegativeCycle,
    seed: int,
    start_level: int,
    program: tuple[tuple[int, int], ...],
) -> dict[str, object]:
    n = seed
    first_one_step = 0 if seed == 1 else None
    ordinary_offset = 0
    states = [str(seed)]
    packet_bit_lengths = []
    for offset, (phase, extra) in enumerate(program):
        level = start_level + offset
        packet = phase_coordinate(cycle, n, level, phase)
        if packet is None:
            raise AssertionError("macro state misses its claimed phase class")
        packet_bit_lengths.append(packet.bit_length())
        control = cycle.phase_states[phase]
        raw_endpoint = control + pow(cycle.numerator_multiplier, level) * packet
        if v2(raw_endpoint) != extra:
            raise AssertionError("collision extra disagrees with exact valuation")
        word = macro_word(cycle, phase, level, extra)
        endpoint = replay_word(n, word)
        if endpoint != raw_endpoint // (1 << extra):
            raise AssertionError("literal replay disagrees with phase packet identity")
        if first_one_step is None:
            probe = n
            for index, expected in enumerate(word, start=1):
                probe, actual = accelerated_step(probe)
                if actual != expected:
                    raise AssertionError("literal trace valuation mismatch")
                if probe == 1:
                    first_one_step = ordinary_offset + index
                    break
        ordinary_offset += len(word)
        n = endpoint
        states.append(str(n))
        if offset + 1 < len(program):
            next_phase = program[offset + 1][0]
            if phase_coordinate(cycle, n, level + 1, next_phase) is None:
                raise AssertionError("collision did not replenish the next phase")
    return {
        "seed": str(seed),
        "endpoint": str(n),
        "states": states,
        "packet_bit_lengths": packet_bit_lengths,
        "first_one_step": first_one_step,
        "accelerated_steps": ordinary_offset,
        "terminal_compatible_phases": compatible_phases(
            cycle, n, start_level + len(program)
        ),
    }


def automatic_renewals(
    cycle: NegativeCycle,
    state: int,
    level: int,
    phase: int,
    max_levels: int,
) -> list[dict[str, object]]:
    events = []
    n = state
    current_phase = phase
    for _ in range(max_levels):
        packet = phase_coordinate(cycle, n, level, current_phase)
        if packet is None:
            break
        control = cycle.phase_states[current_phase]
        raw = control + pow(cycle.numerator_multiplier, level) * packet
        extra = v2(raw)
        endpoint = raw // (1 << extra)
        targets = compatible_phases(cycle, endpoint, level + 1)
        events.append(
            {
                "level": level,
                "phase": current_phase,
                "extra": extra,
                "state": str(n),
                "endpoint": str(endpoint),
                "target_phases": targets,
                "grows": endpoint > n,
            }
        )
        if len(targets) != 1:
            break
        n = endpoint
        current_phase = targets[0]
        level += 1
    return events


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
    cycle_name: str,
    min_start_level: int,
    max_start_level: int,
    max_extra: int,
    max_program_depth: int,
) -> dict[str, object]:
    if cycle_name not in CYCLES:
        raise ValueError("unknown negative cycle")
    if not (
        1 <= min_start_level <= max_start_level
        and max_extra >= 1
        and max_program_depth >= 1
    ):
        raise ValueError("invalid search bounds")
    cycle = CYCLES[cycle_name]
    alphabet = tuple(
        (phase, extra)
        for phase in range(cycle.steps)
        for extra in range(1, max_extra + 1)
    )

    programs = 0
    compiled_paths = 0
    stabilization_events = 0
    one_avoiding_stabilization_events = 0
    terminal_renewal_events = 0
    strongest_stabilization = None
    renewals: list[dict[str, object]] = []

    for start_level in range(min_start_level, max_start_level + 1):
        for depth in range(1, max_program_depth + 1):
            for program in itertools.product(alphabet, repeat=depth):
                programs += 1
                word = program_word(cycle, start_level, program)
                parent_word = (
                    program_word(cycle, start_level, program[:-1])
                    if depth > 1
                    else None
                )
                for residue in (1, 5):
                    compiled = compile_path(word, residue)
                    compiled_paths += 1
                    trace = trace_program(cycle, compiled.seed, start_level, program)
                    stable_extensions = 0
                    if parent_word is not None:
                        parent_seed = compile_path(parent_word, residue).seed
                        if parent_seed == compiled.seed:
                            # Count the terminal suffix of prefixes having the
                            # same canonical ordinary seed.
                            stable_extensions = 1
                            for cut in range(depth - 2, 0, -1):
                                prefix_seed = compile_path(
                                    program_word(cycle, start_level, program[:cut]),
                                    residue,
                                ).seed
                                if prefix_seed != compiled.seed:
                                    break
                                stable_extensions += 1
                    event = {
                        "cycle": cycle.name,
                        "start_level": start_level,
                        "program": [list(symbol) for symbol in program],
                        "program_depth": depth,
                        "residue_mod_6": residue,
                        "seed": str(compiled.seed),
                        "endpoint": str(compiled.endpoint),
                        "stable_extensions": stable_extensions,
                        "first_one_step": trace["first_one_step"],
                        "macro_states": trace["states"],
                        "terminal_compatible_phases": trace[
                            "terminal_compatible_phases"
                        ],
                    }
                    if stable_extensions:
                        stabilization_events += 1
                        if trace["first_one_step"] is None:
                            one_avoiding_stabilization_events += 1
                        if event_key(event) > event_key(strongest_stabilization):
                            strongest_stabilization = event
                    targets = trace["terminal_compatible_phases"]
                    if targets:
                        terminal_renewal_events += 1
                        event["automatic_continuation"] = automatic_renewals(
                            cycle,
                            compiled.endpoint,
                            start_level + depth,
                            targets[0],
                            32,
                        )
                        renewals.append(event)

    source = (
        Path(__file__).read_bytes()
        + Path(__file__).with_name("search_shadow.py").read_bytes()
        + Path(__file__).with_name("path_compiler.py").read_bytes()
    )
    return {
        "schema": "collatz-phase-shadow-search-v1",
        "arithmetic": "exact_python_integers",
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "bounds": {
            "cycle": cycle_name,
            "phase_states": [str(x) for x in cycle.phase_states],
            "min_start_level": min_start_level,
            "max_start_level": max_start_level,
            "max_extra": max_extra,
            "max_program_depth": max_program_depth,
        },
        "programs": programs,
        "compiled_paths": compiled_paths,
        "seed_stabilization_events": stabilization_events,
        "one_avoiding_seed_stabilization_events": (
            one_avoiding_stabilization_events
        ),
        "terminal_renewal_events": terminal_renewal_events,
        "strongest_seed_stabilization": strongest_stabilization,
        "terminal_renewals": renewals,
    }


def selftest() -> None:
    minus5 = CYCLES["minus5"]
    assert minus5.phase_states == (-5, -7)
    assert minus5.phase_word(1) == (2, 1)

    renewal_program = ((0, 3), (0, 3), (1, 1))
    renewal_word = program_word(minus5, 1, renewal_program)
    compiled = compile_path(renewal_word, 5)
    assert compiled.seed == 106807715
    assert compiled.endpoint == 1691641
    trace = trace_program(minus5, compiled.seed, 1, renewal_program)
    assert trace["states"] == [
        "106807715",
        "15019835",
        "2376185",
        "1691641",
    ]
    assert trace["terminal_compatible_phases"] == [1]
    continuation = automatic_renewals(minus5, compiled.endpoint, 4, 1, 4)
    assert continuation[0]["extra"] == 1
    assert continuation[0]["endpoint"] == "1354843"
    assert continuation[0]["target_phases"] == []

    stable_program = ((1, 6), (0, 2), (1, 1))
    stable = compile_path(program_word(minus5, 1, stable_program), 5)
    parent = compile_path(program_word(minus5, 1, stable_program[:-1]), 5)
    assert stable.seed == parent.seed == 90737
    assert stable.endpoint == 361

    tiny = search(
        cycle_name="minus5",
        min_start_level=1,
        max_start_level=1,
        max_extra=2,
        max_program_depth=2,
    )
    # Alphabet size is two phases times two extras: 4+4^2 programs.
    assert tiny["programs"] == 20
    assert tiny["compiled_paths"] == 40


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cycle", choices=tuple(CYCLES), default="minus5")
    parser.add_argument("--min-start-level", type=int, default=1)
    parser.add_argument("--max-start-level", type=int, default=6)
    parser.add_argument("--max-extra", type=int, default=6)
    parser.add_argument("--max-program-depth", type=int, default=3)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        print("search_phase_shadow selftest: PASS")
        return
    result = search(
        cycle_name=args.cycle,
        min_start_level=args.min_start_level,
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
