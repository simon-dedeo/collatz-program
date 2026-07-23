#!/usr/bin/env python3
"""Bounded exact EM/CEGIS on coherent first-passage seed cylinders.

This worker never combines independent depth minima.  A node stores one
nested dyadic cylinder with the exact family meaning

    rho + 2^L z  |->  y + 3^Q z

after its displayed list of first-passage words.  Every edge solves the
unique next lift digit, checks the affine identities, and literally replays
the shortcut orbit.  Triadic phase minima are computed exactly inside the
complete bounded edge population, but are used only as beam witnesses: they
are not claimed to be a sound unbounded forward dominance rule.

The M-step fits the smallest bounded exception-table selector considered on
features built from ``(capped v3(H), primitive(H) mod 3^k)``.  An outer loop
opens one-step word memory, address-carry information, and an additional
dyadic residue only when an exact CEGIS failure collides with the currently
visible feature.  Exact replay supplies the first selector mismatch or halt
as a refinement.  Such a mismatch is not a Collatz counterexample, and every
artifact records ``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mp
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


SCHEMA = "collatz-outward-coherent-cegis-v1"
HALT = "HALT"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def integer_sha256(value: int) -> str:
    width = max(1, (value.bit_length() + 7) // 8)
    return hashlib.sha256(value.to_bytes(width, "big")).hexdigest()


def valuation(value: int, prime: int) -> tuple[int, int]:
    if value <= 0:
        raise ValueError("valuation requires a positive integer")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent, value


def word_affine_constant(word: str) -> int:
    constant = 0
    length = 0
    for bit in word:
        if bit == "1":
            constant = 3 * constant + 2**length
        elif bit != "0":
            raise ValueError("parity words use only 0 and 1")
        length += 1
    return constant


def is_first_passage(word: str) -> bool:
    if not word:
        return False
    odds = 0
    for index, bit in enumerate(word, 1):
        odds += bit == "1"
        outward = 3**odds > 2**index
        if index < len(word) and outward:
            return False
        if index == len(word):
            return outward
    raise AssertionError("unreachable first-passage test")


@dataclass(frozen=True)
class WordData:
    word: str
    S: int
    O: int
    A: int
    r: int
    b: int
    defect: int | None


def make_word_data(word: str) -> WordData:
    if not is_first_passage(word):
        raise ValueError("word is not first-passage")
    S = len(word)
    O = word.count("1")
    A = word_affine_constant(word)
    modulus = 2**S
    r = (-A * pow(3**O, -1, modulus)) % modulus
    numerator = 3**O * r + A
    if numerator % modulus:
        raise AssertionError("canonical word source is not integral")
    b = numerator // modulus
    if not 0 <= b < 3**O:
        raise AssertionError("canonical word target left its range")
    defect_numerator = A + modulus - 3**O
    defect = defect_numerator // 3 if defect_numerator % 3 == 0 else None
    return WordData(word, S, O, A, r, b, defect)


def bounded_first_passage_words(maximum_length: int) -> tuple[list[WordData], int]:
    if maximum_length < 1:
        raise ValueError("word-length bound must be positive")
    words: list[WordData] = []
    frontier = 0

    def visit(prefix: str, odds: int) -> None:
        nonlocal frontier
        length = len(prefix)
        if length and 3**odds > 2**length:
            words.append(make_word_data(prefix))
            return
        if length == maximum_length:
            frontier += 1
            return
        visit(prefix + "0", odds)
        visit(prefix + "1", odds + 1)

    visit("", 0)
    words.sort(key=lambda row: (row.S, row.word))
    return words, frontier


def execute_word(word: str, source: int) -> int:
    if source < 0:
        raise ValueError("shortcut source must be nonnegative")
    state = source
    for bit in word:
        if state % 2 != (bit == "1"):
            raise AssertionError("literal parity replay disagrees with word")
        state = (3 * state + 1) // 2 if bit == "1" else state // 2
    return state


@dataclass(frozen=True)
class Node:
    words: tuple[str, ...]
    rho: int
    L: int
    Q: int
    y: int
    A: int
    carries: tuple[int, ...]

    @property
    def depth(self) -> int:
        return len(self.words)

    @property
    def seed(self) -> int:
        return self.rho if self.rho > 0 else 2**self.L


ROOT = Node((), 0, 0, 0, 0, 0, ())


def node_id(node: Node) -> str:
    payload = [list(node.words), str(node.rho), node.L, node.Q, str(node.y), str(node.A)]
    return hashlib.sha256(canonical_json(payload)).hexdigest()


def check_node(node: Node) -> None:
    if not 0 <= node.rho < 2**node.L:
        raise AssertionError("canonical source residue left its dyadic range")
    if node.Q != sum(word.count("1") for word in node.words):
        raise AssertionError("node odd count changed")
    if node.L != sum(len(word) for word in node.words):
        raise AssertionError("node length changed")
    if 2**node.L * node.y != 3**node.Q * node.rho + node.A:
        raise AssertionError("node affine invariant failed")
    if len(node.carries) != node.depth:
        raise AssertionError("node carry list changed")


def extend_node(node: Node, word: WordData) -> Node:
    check_node(node)
    modulus = 2**word.S
    lift = ((word.r - node.y) * pow(3**node.Q, -1, modulus)) % modulus
    boundary_source = node.y + 3**node.Q * lift
    if boundary_source % modulus != word.r:
        raise AssertionError("extension missed the word cylinder")
    parameter = (boundary_source - word.r) // modulus
    if parameter < 0:
        raise AssertionError("word family parameter became negative")
    target = word.b + 3**word.O * parameter
    if execute_word(word.word, boundary_source) != target:
        raise AssertionError("extension failed literal word replay")
    rho = node.rho + 2**node.L * lift
    child = Node(
        node.words + (word.word,),
        rho,
        node.L + word.S,
        node.Q + word.O,
        target,
        3**word.O * node.A + 2**node.L * word.A,
        node.carries + (lift,),
    )
    check_node(child)
    if child.rho % 2**node.L != node.rho:
        raise AssertionError("child is not nested above its parent")
    if child.rho != node.rho + 2**node.L * lift:
        raise AssertionError("child carry law failed")
    return child


def replay_node(node: Node) -> dict[str, Any]:
    check_node(node)
    state = node.seed
    boundaries: list[dict[str, Any]] = []
    cumulative_length = 0
    cumulative_odds = 0
    stabilization_depth: int | None = None
    for depth, word in enumerate(node.words, 1):
        state = execute_word(word, state)
        cumulative_length += len(word)
        cumulative_odds += word.count("1")
        if state % 3 != 2:
            raise AssertionError("first-passage boundary left class 2 mod 3")
        if stabilization_depth is None and node.rho > 0 and node.seed < 2**cumulative_length:
            stabilization_depth = depth
        charge = (state + 1) // 3
        c, unit = valuation(charge, 3)
        boundaries.append(
            {
                "depth": depth,
                "word": word,
                "state": state,
                "charge": charge,
                "charge_v3": c,
                "charge_unit": unit,
                "cumulative_length": cumulative_length,
                "cumulative_odds": cumulative_odds,
            }
        )
    expected = node.y if node.rho > 0 else node.y + 3**node.Q
    if state != expected:
        raise AssertionError("full node replay missed its affine endpoint")
    return {
        "boundaries": boundaries,
        "stabilization_depth": stabilization_depth,
        "post_address_blocks": (
            node.depth - stabilization_depth if stabilization_depth is not None else 0
        ),
    }


def next_first_passage(
    state: int, maximum_shortcut_steps: int
) -> tuple[str | None, int, int]:
    if maximum_shortcut_steps < 1:
        raise AssertionError("literal rollout exhausted its shortcut-step budget")
    word: list[str] = []
    odds = 0
    for steps in range(1, maximum_shortcut_steps + 1):
        if state == 2:
            return None, state, steps - 1
        if state == 1:
            word.append("1")
            odds += 1
            state = 2
        else:
            odd = state % 2
            word.append("1" if odd else "0")
            if odd:
                odds += 1
                state = (3 * state + 1) // 2
            else:
                state //= 2
        if 3**odds > 2**len(word):
            result = "".join(word)
            if not is_first_passage(result):
                raise AssertionError("literal rollout produced a non-first-passage word")
            return result, state, steps
        if state in (1, 2):
            return None, state, steps
    raise AssertionError("literal rollout reached its shortcut-step cutoff")


def rollout_node(node: Node, extra_blocks: int, maximum_shortcut_steps: int) -> dict[str, Any]:
    maximum_blocks = node.depth + extra_blocks
    state = node.seed
    rows: list[dict[str, Any]] = []
    total_steps = 0
    cumulative_length = 0
    terminal = False
    for depth in range(1, maximum_blocks + 1):
        word, state, steps = next_first_passage(
            state, maximum_shortcut_steps - total_steps
        )
        total_steps += steps
        if word is None:
            terminal = True
            break
        cumulative_length += len(word)
        if depth <= node.depth and word != node.words[depth - 1]:
            raise AssertionError("rollout lost the encoded coherent prefix")
        if state % 3 != 2:
            raise AssertionError("rollout boundary left class 2 mod 3")
        charge = (state + 1) // 3
        c, unit = valuation(charge, 3)
        rows.append(
            {
                "depth": depth,
                "word": word,
                "state": state,
                "charge": charge,
                "charge_v3": c,
                "charge_unit": unit,
                "cumulative_length": cumulative_length,
                "shortcut_steps": total_steps,
            }
        )
    status = "terminal" if terminal else "block_frontier"
    return {
        "rows": rows,
        "status": status,
        "terminal_state": state if terminal else None,
        "shortcut_steps": total_steps,
    }


@dataclass(frozen=True)
class Context:
    charge: int
    previous_word: str
    address_carry: int


ARCHITECTURES: dict[str, tuple[bool, bool, bool]] = {
    "charge": (False, False, False),
    "charge+memory": (True, False, False),
    "charge+carry": (False, True, False),
    "charge+dyadic": (False, False, True),
    "charge+memory+carry": (True, True, False),
    "charge+memory+dyadic": (True, False, True),
    "charge+carry+dyadic": (False, True, True),
    "charge+memory+carry+dyadic": (True, True, True),
}


def architecture_level(name: str) -> int:
    return sum(ARCHITECTURES[name])


def context_feature(
    context: Context,
    precision: int,
    valuation_cap: int,
    architecture: str,
    dyadic_bits: int,
) -> tuple[Any, ...]:
    c, unit = valuation(context.charge, 3)
    key: list[Any] = [min(c, valuation_cap), unit % 3**precision]
    memory, carry, dyadic = ARCHITECTURES[architecture]
    if memory:
        key.append(context.previous_word)
    if carry:
        key.append(0 if context.address_carry == 0 else min(context.address_carry.bit_length(), 16))
    if dyadic:
        key.append(context.charge % 2**dyadic_bits)
    return tuple(key)


def label_key(label: str) -> tuple[int, int, str]:
    return (label == HALT, len(label) if label != HALT else 10**9, label)


def majority(counts: Counter[str]) -> str:
    if not counts:
        return "1"
    return min(counts, key=lambda label: (-counts[label], label_key(label)))


@dataclass(frozen=True)
class Selector:
    precision: int
    valuation_cap: int
    architecture: str
    dyadic_bits: int
    default: str
    table: tuple[tuple[tuple[Any, ...], str], ...]
    weighted_errors: int
    weighted_examples: int
    ambiguous_features: int

    def mapping(self) -> dict[tuple[Any, ...], str]:
        return dict(self.table)

    def key(self, context: Context) -> tuple[Any, ...]:
        return context_feature(
            context,
            self.precision,
            self.valuation_cap,
            self.architecture,
            self.dyadic_bits,
        )

    def predict(self, context: Context) -> str:
        return self.mapping().get(self.key(context), self.default)


@dataclass(frozen=True)
class Example:
    context: Context
    label: str
    weight: int


def selector_examples(nodes: Iterable[Node]) -> list[Example]:
    examples: list[Example] = []
    for node in nodes:
        trace = replay_node(node)["boundaries"]
        for index in range(len(trace) - 1):
            row = trace[index]
            examples.append(
                Example(
                    Context(
                        int(row["charge"]),
                        str(row["word"]),
                        node.seed >> int(row["cumulative_length"]),
                    ),
                    str(trace[index + 1]["word"]),
                    1,
                )
            )
    return examples


def fit_selector(
    examples: list[Example],
    maximum_precision: int,
    maximum_valuation_cap: int,
    maximum_architecture_level: int,
    maximum_dyadic_bits: int,
    maximum_table_entries: int,
) -> tuple[Selector, list[dict[str, Any]]]:
    if maximum_precision < 1 or maximum_valuation_cap < 1:
        raise ValueError("selector bounds must be positive")
    if maximum_dyadic_bits < 1 or maximum_table_entries < 1:
        raise ValueError("selector architecture bounds must be positive")
    best: tuple[tuple[int, int, int, int, int, str], Selector] | None = None
    architecture_best: dict[str, tuple[tuple[int, int, int, int, int, str], Selector]] = {}
    for architecture in ARCHITECTURES:
        if architecture_level(architecture) > maximum_architecture_level:
            continue
        _, _, uses_dyadic = ARCHITECTURES[architecture]
        dyadic_range = range(1, maximum_dyadic_bits + 1) if uses_dyadic else (0,)
        for dyadic_bits in dyadic_range:
            for precision in range(1, maximum_precision + 1):
                for valuation_cap in range(1, maximum_valuation_cap + 1):
                    global_counts: Counter[str] = Counter()
                    counts: dict[tuple[Any, ...], Counter[str]] = defaultdict(Counter)
                    for example in examples:
                        global_counts[example.label] += example.weight
                        key = context_feature(
                            example.context,
                            precision,
                            valuation_cap,
                            architecture,
                            dyadic_bits,
                        )
                        counts[key][example.label] += example.weight
                    default = majority(global_counts)
                    full_map = {key: majority(value) for key, value in counts.items()}
                    # The selector is a charged finite exception table, not a
                    # verbatim memorization of every observed feature.
                    table_map = {
                        key: label for key, label in full_map.items() if label != default
                    }
                    errors = 0
                    for example in examples:
                        key = context_feature(
                            example.context,
                            precision,
                            valuation_cap,
                            architecture,
                            dyadic_bits,
                        )
                        predicted = table_map.get(key, default)
                        errors += example.weight * (predicted != example.label)
                    ambiguous = sum(len(value) > 1 for value in counts.values())
                    table = tuple(
                        (key, table_map[key]) for key in sorted(table_map, key=repr)
                    )
                    if len(table) > maximum_table_entries:
                        continue
                    selector = Selector(
                        precision,
                        valuation_cap,
                        architecture,
                        dyadic_bits,
                        default,
                        table,
                        errors,
                        sum(example.weight for example in examples),
                        ambiguous,
                    )
                    feature_cost = (
                        4 * architecture_level(architecture)
                        + precision
                        + valuation_cap
                        + dyadic_bits
                    )
                    objective = (
                        errors,
                        feature_cost,
                        len(table),
                        precision,
                        valuation_cap,
                        architecture,
                    )
                    previous = architecture_best.get(architecture)
                    if previous is None or objective < previous[0]:
                        architecture_best[architecture] = (objective, selector)
                    if best is None or objective < best[0]:
                        best = (objective, selector)
    if best is None:
        raise AssertionError("selector search produced no model")
    trials = [
        {
            "architecture": architecture,
            "precision": row[1].precision,
            "valuation_cap": row[1].valuation_cap,
            "dyadic_bits": row[1].dyadic_bits,
            "weighted_errors": row[1].weighted_errors,
            "table_entries": len(row[1].table),
            "ambiguous_features": row[1].ambiguous_features,
            "objective": list(row[0][:-1]) + [row[0][-1]],
        }
        for architecture, row in sorted(architecture_best.items())
    ]
    return best[1], trials


def selector_stats(node: Node, selector: Selector) -> tuple[int, int]:
    trace = replay_node(node)["boundaries"]
    matches = 0
    mismatches = 0
    for index in range(len(trace) - 1):
        row = trace[index]
        context = Context(
            int(row["charge"]),
            str(row["word"]),
            node.seed >> int(row["cumulative_length"]),
        )
        predicted = selector.predict(context)
        if predicted == str(trace[index + 1]["word"]):
            matches += 1
        else:
            mismatches += 1
    return matches, mismatches


def node_metrics(node: Node, selector: Selector, recurrence_precision: int) -> dict[str, int]:
    replay = replay_node(node)
    boundaries = replay["boundaries"]
    charge_features = [
        context_feature(
            Context(
                int(row["charge"]),
                str(row["word"]),
                node.seed >> int(row["cumulative_length"]),
            ),
            recurrence_precision,
            8,
            "charge",
            0,
        )
        for row in boundaries
    ]
    recurrence = len(charge_features) - len(set(charge_features))
    zero_run = 0
    for carry in reversed(node.carries):
        if carry != 0:
            break
        zero_run += 1
    matches, mismatches = selector_stats(node, selector)
    halt_prediction = 0
    if boundaries:
        last = boundaries[-1]
        last_context = Context(
            int(last["charge"]),
            str(last["word"]),
            node.seed >> int(last["cumulative_length"]),
        )
        halt_prediction = selector.predict(last_context) == HALT
    carry_bits = sum(carry.bit_length() for carry in node.carries if carry)
    address_bits = node.seed.bit_length()
    score = (
        10_000 * zero_run
        + 2_000 * int(replay["post_address_blocks"])
        + 400 * matches
        - 600 * mismatches
        + 250 * recurrence
        - 5_000 * halt_prediction
        - 20 * address_bits
        - 10 * carry_bits
    )
    return {
        "score_before_phase_bonus": score,
        "zero_carry_suffix": zero_run,
        "post_address_blocks": int(replay["post_address_blocks"]),
        "selector_matches": matches,
        "selector_mismatches": mismatches,
        "selector_predicts_halt_at_frontier": int(halt_prediction),
        "recurring_charge_features": recurrence,
        "address_bits": address_bits,
        "carry_bits": carry_bits,
    }


def expand_parent_task(
    arguments: tuple[Node, list[WordData], Selector, int]
) -> list[tuple[Node, dict[str, int]]]:
    parent, words, selector, recurrence_precision = arguments
    result: list[tuple[Node, dict[str, int]]] = []
    for word in words:
        node = extend_node(parent, word)
        result.append((node, node_metrics(node, selector, recurrence_precision)))
    return result


def verify_inverse_minplus_term(node: Node, words: dict[str, WordData]) -> None:
    if not node.words:
        return
    first = words[node.words[0]]
    target = execute_word(first.word, node.seed)
    difference = target - first.b
    if difference < 0 or difference % 3**first.O:
        raise AssertionError("candidate target left the first-word triadic fiber")
    reconstructed = first.r + 2**first.S * (difference // 3**first.O)
    if reconstructed != node.seed:
        raise AssertionError("bounded inverse min-plus term failed")


def phase_minima(
    candidates: list[Node], precision: int, words: dict[str, WordData]
) -> tuple[dict[str, Any], dict[str, int]]:
    minima: dict[tuple[int, int], Node] = {}
    for node in candidates:
        verify_inverse_minplus_term(node, words)
        for exponent in range(1, precision + 1):
            phase = node.seed % 3**exponent
            key = (exponent, phase)
            previous = minima.get(key)
            if previous is None or (node.seed, node_id(node)) < (
                previous.seed,
                node_id(previous),
            ):
                minima[key] = node
    winner_counts: Counter[str] = Counter(node_id(node) for node in minima.values())
    rows = [
        {
            "precision": exponent,
            "phase": phase,
            "minimum_source": str(node.seed),
            "node_id": node_id(node),
        }
        for (exponent, phase), node in sorted(minima.items())
    ]
    return {
        "scope": "exact minima only inside the complete displayed bounded edge population",
        "entries": len(rows),
        "rows_sha256": hashlib.sha256(canonical_json(rows)).hexdigest(),
    }, dict(winner_counts)


def selector_record(selector: Selector) -> dict[str, Any]:
    return {
        "precision": selector.precision,
        "valuation_cap": selector.valuation_cap,
        "architecture": selector.architecture,
        "architecture_level": architecture_level(selector.architecture),
        "dyadic_bits": selector.dyadic_bits,
        "default": selector.default,
        "table": [
            {"feature": list(key), "action": label}
            for key, label in selector.table
        ],
        "weighted_errors": selector.weighted_errors,
        "weighted_examples": selector.weighted_examples,
        "ambiguous_features": selector.ambiguous_features,
    }


def first_selector_failure(
    node: Node,
    selector: Selector,
    extra_blocks: int,
    maximum_shortcut_steps: int,
    maximum_word_length: int,
) -> tuple[dict[str, Any] | None, dict[str, Any], Example | None]:
    rollout = rollout_node(node, extra_blocks, maximum_shortcut_steps)
    rows = rollout["rows"]
    labelled: list[tuple[Context, str, int]] = []
    for index in range(len(rows) - 1):
        row = rows[index]
        labelled.append(
            (
                Context(
                    int(row["charge"]),
                    str(row["word"]),
                    node.seed >> int(row["cumulative_length"]),
                ),
                str(rows[index + 1]["word"]),
                index + 1,
            )
        )
    if rollout["status"] == "terminal" and rows:
        row = rows[-1]
        labelled.append(
            (
                Context(
                    int(row["charge"]),
                    str(row["word"]),
                    node.seed >> int(row["cumulative_length"]),
                ),
                HALT,
                len(rows),
            )
        )
    for context, actual, boundary_depth in labelled:
        predicted = selector.predict(context)
        if predicted == actual:
            continue
        current_feature = selector.key(context)
        failure = {
            "boundary_depth": boundary_depth,
            "kind": "exact_halt" if actual == HALT else "selector_mismatch",
            "predicted": predicted,
            "actual": actual,
            "actual_word_exceeds_bound": actual != HALT and len(actual) > maximum_word_length,
            "charge_bits": context.charge.bit_length(),
            "charge_sha256": integer_sha256(context.charge),
            "previous_word": context.previous_word,
            "address_carry_bits": context.address_carry.bit_length(),
            "architecture": selector.architecture,
            "feature": list(current_feature),
        }
        return failure, rollout, Example(context, actual, 50)
    return None, rollout, None


def champion_record(
    node: Node,
    metrics: dict[str, int],
    selector: Selector,
    failure: dict[str, Any] | None,
    rollout: dict[str, Any],
) -> dict[str, Any]:
    replay = replay_node(node)
    boundary_rows = []
    for row in replay["boundaries"]:
        boundary_rows.append(
            {
                **{key: row[key] for key in (
                    "depth", "word", "charge_v3", "cumulative_length", "cumulative_odds"
                )},
                "state": str(row["state"]),
                "charge": str(row["charge"]),
                "charge_unit_mod_selector_precision": int(row["charge_unit"])
                % 3**selector.precision,
            }
        )
    rollout_rows = [
        {
            "depth": row["depth"],
            "word": row["word"],
            "state_bits": int(row["state"]).bit_length(),
            "state_sha256": integer_sha256(int(row["state"])),
            "charge_v3": row["charge_v3"],
        }
        for row in rollout["rows"]
    ]
    return {
        "node_id": node_id(node),
        "seed": str(node.seed),
        "rho": str(node.rho),
        "total_length": node.L,
        "total_odd_count": node.Q,
        "canonical_endpoint": str(node.y),
        "affine_constant": str(node.A),
        "words": list(node.words),
        "carries": [str(value) for value in node.carries],
        "metrics": metrics,
        "stabilization_depth": replay["stabilization_depth"],
        "boundaries": boundary_rows,
        "rollout": {
            "status": rollout["status"],
            "terminal_state": rollout["terminal_state"],
            "shortcut_steps": rollout["shortcut_steps"],
            "rows": rollout_rows,
        },
        "first_selector_failure": failure,
    }


def exact_cegis(args: argparse.Namespace) -> dict[str, Any]:
    if args.maximum_depth < 1 or args.beam_width < 1:
        raise ValueError("depth and beam bounds must be positive")
    if args.phase_precision < 1 or args.selector_max_precision < 1:
        raise ValueError("precision bounds must be positive")
    if args.rollout_blocks < 0 or args.maximum_shortcut_steps < 1:
        raise ValueError("rollout bounds are invalid")
    if args.precision_step_interval < 1 or args.processes < 1:
        raise ValueError("step interval and process count must be positive")
    words, word_frontier = bounded_first_passage_words(args.maximum_word_length)
    word_map = {row.word: row for row in words}
    if not words:
        raise AssertionError("bounded word table is empty")
    beam = [ROOT]
    counterexamples: list[Example] = []
    depth_rows: list[dict[str, Any]] = []
    allowed_precision = 1
    allowed_architecture_level = 0
    selector, architecture_trials = fit_selector(
        [],
        allowed_precision,
        args.selector_valuation_cap,
        allowed_architecture_level,
        args.selector_max_dyadic_bits,
        args.selector_max_table_entries,
    )
    last_failure: dict[str, Any] | None = None
    last_rollout: dict[str, Any] = {"rows": [], "status": "block_frontier", "terminal_state": None, "shortcut_steps": 0}
    metrics_by_id: dict[str, dict[str, int]] = {node_id(ROOT): {"score": 0}}
    pool = mp.Pool(args.processes) if args.processes > 1 else None

    for depth in range(1, args.maximum_depth + 1):
        parent_beam_size = len(beam)
        examples = selector_examples(beam) + counterexamples
        selector, architecture_trials = fit_selector(
            examples,
            allowed_precision,
            args.selector_valuation_cap,
            allowed_architecture_level,
            args.selector_max_dyadic_bits,
            args.selector_max_table_entries,
        )
        tasks = [
            (parent, words, selector, args.phase_precision) for parent in beam
        ]
        pieces = (
            pool.map(expand_parent_task, tasks, chunksize=1)
            if pool is not None
            else [expand_parent_task(task) for task in tasks]
        )
        candidate_metrics = [row for piece in pieces for row in piece]
        candidates = [row[0] for row in candidate_metrics]
        if not candidates:
            raise AssertionError("beam extension produced no candidate")

        phase_record, phase_counts = phase_minima(
            candidates, args.phase_precision, word_map
        )
        scored: list[tuple[int, str, Node, dict[str, int]]] = []
        for node, metrics in candidate_metrics:
            phase_wins = int(phase_counts.get(node_id(node), 0))
            metrics["phase_minimum_wins"] = phase_wins
            metrics["score"] = metrics["score_before_phase_bonus"] + 150 * phase_wins
            scored.append((metrics["score"], node_id(node), node, metrics))
        scored.sort(key=lambda row: (-row[0], row[2].seed, row[1]))

        phase_winners = [row for row in scored if row[3]["phase_minimum_wins"] > 0]
        selected: list[tuple[int, str, Node, dict[str, int]]] = []
        selected_ids: set[str] = set()
        for row in phase_winners + scored:
            identifier = row[1]
            if identifier in selected_ids:
                continue
            selected.append(row)
            selected_ids.add(identifier)
            if len(selected) == args.beam_width:
                break
        selected.sort(key=lambda row: (-row[0], row[2].seed, row[1]))
        beam = [row[2] for row in selected]
        metrics_by_id = {row[1]: row[3] for row in selected}
        champion = beam[0]
        champion_metrics = metrics_by_id[node_id(champion)]
        failure, rollout, example = first_selector_failure(
            champion,
            selector,
            args.rollout_blocks,
            args.maximum_shortcut_steps,
            args.maximum_word_length,
        )
        last_failure = failure
        last_rollout = rollout
        refinement_added = False
        architecture_collision = False
        if example is not None:
            raw = (example.context, example.label)
            if raw not in {(row.context, row.label) for row in counterexamples}:
                failure_key = selector.key(example.context)
                prior_labels = {
                    row.label for row in examples if selector.key(row.context) == failure_key
                }
                architecture_collision = bool(prior_labels - {example.label})
                counterexamples.append(example)
                refinement_added = True
        precision_before = allowed_precision
        architecture_before = allowed_architecture_level
        if architecture_collision:
            allowed_architecture_level = min(3, allowed_architecture_level + 1)
            allowed_precision = min(args.selector_max_precision, allowed_precision + 1)
        if depth % args.precision_step_interval == 0:
            allowed_precision = min(args.selector_max_precision, allowed_precision + 1)

        depth_rows.append(
            {
                "depth": depth,
                "parent_beam_size": parent_beam_size,
                "bounded_word_count": len(words),
                "candidate_population": len(candidates),
                "retained_beam_size": len(beam),
                "phase_minplus": phase_record,
                "phase_winners_retained": sum(
                    metrics_by_id[node_id(node)]["phase_minimum_wins"] > 0 for node in beam
                ),
                "selector": selector_record(selector),
                "architecture_trials": architecture_trials,
                "allowed_architecture_level_before_refinement": architecture_before,
                "allowed_architecture_level_after_refinement": allowed_architecture_level,
                "architecture_collision": architecture_collision,
                "allowed_precision_before_refinement": precision_before,
                "allowed_precision_after_refinement": allowed_precision,
                "cegis_refinement_added": refinement_added,
                "first_failure": failure,
                "champion_node_id": node_id(champion),
                "champion_seed": str(champion.seed),
                "champion_metrics": champion_metrics,
            }
        )

    if pool is not None:
        pool.close()
        pool.join()

    final_examples = selector_examples(beam) + counterexamples
    selector, final_architecture_trials = fit_selector(
        final_examples,
        allowed_precision,
        args.selector_valuation_cap,
        allowed_architecture_level,
        args.selector_max_dyadic_bits,
        args.selector_max_table_entries,
    )
    rescored = []
    for node in beam:
        metrics = node_metrics(node, selector, args.phase_precision)
        metrics["phase_minimum_wins"] = metrics_by_id[node_id(node)]["phase_minimum_wins"]
        metrics["score"] = metrics["score_before_phase_bonus"] + 150 * metrics["phase_minimum_wins"]
        rescored.append((metrics["score"], node.seed, node_id(node), node, metrics))
    rescored.sort(key=lambda row: (-row[0], row[1], row[2]))
    _, _, _, champion, champion_metrics = rescored[0]
    last_failure, last_rollout, _ = first_selector_failure(
        champion,
        selector,
        args.rollout_blocks,
        args.maximum_shortcut_steps,
        args.maximum_word_length,
    )

    word_rows = [
        {
            "word": row.word,
            "S": row.S,
            "O": row.O,
            "A": row.A,
            "r": row.r,
            "b": row.b,
            "defect": row.defect,
        }
        for row in words
    ]
    return {
        "meaning": (
            "bounded exact arithmetic EM/CEGIS over ancestry-compatible "
            "first-passage dyadic cylinders"
        ),
        "bounds": {
            "maximum_depth": args.maximum_depth,
            "beam_width": args.beam_width,
            "maximum_word_length": args.maximum_word_length,
            "phase_precision": args.phase_precision,
            "selector_max_precision": args.selector_max_precision,
            "selector_valuation_cap": args.selector_valuation_cap,
            "selector_max_dyadic_bits": args.selector_max_dyadic_bits,
            "selector_max_table_entries": args.selector_max_table_entries,
            "precision_step_interval": args.precision_step_interval,
            "rollout_blocks": args.rollout_blocks,
            "maximum_shortcut_steps": args.maximum_shortcut_steps,
            "processes": args.processes,
        },
        "word_table": {
            "complete_scope": "all first-passage words of length at most the displayed bound",
            "words": word_rows,
            "nonoutward_prefix_frontier_at_length_bound": word_frontier,
            "unbounded_table_complete": False,
        },
        "beam_semantics": {
            "node_family": "rho+2^L*z maps to y+3^Q*z after its word list",
            "coherent_ancestry_required": True,
            "phase_minima_scope": (
                "exact inside each complete bounded candidate population; "
                "ranking/retention heuristic only"
            ),
            "levelwise_minima_are_not_claimed_coherent": True,
        },
        "depth_rows": depth_rows,
        "cegis_counterexamples": [
            {
                "charge_bits": example.context.charge.bit_length(),
                "charge_sha256": integer_sha256(example.context.charge),
                "previous_word": example.context.previous_word,
                "address_carry_bits": example.context.address_carry.bit_length(),
                "actual": example.label,
                "weight": example.weight,
            }
            for example in counterexamples
        ],
        "final_selector": selector_record(selector),
        "final_architecture_trials": final_architecture_trials,
        "champion": champion_record(
            champion, champion_metrics, selector, last_failure, last_rollout
        ),
        "compact_parametric_invariant": None,
        "counterexample": None,
        "claim_scope": (
            "finite beam, word, depth, precision, and replay bounds; selector "
            "failures refine a heuristic and never prove nontermination"
        ),
    }


def build_artifact(args: argparse.Namespace) -> dict[str, Any]:
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": exact_cegis(args),
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    audit = artifact["audit"]
    champion = audit["champion"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "depth": audit["bounds"]["maximum_depth"],
        "beam_width": audit["bounds"]["beam_width"],
        "word_count": len(audit["word_table"]["words"]),
        "champion_seed": champion["seed"],
        "champion_zero_carry_suffix": champion["metrics"]["zero_carry_suffix"],
        "champion_post_address_blocks": champion["metrics"]["post_address_blocks"],
        "compact_parametric_invariant": audit["compact_parametric_invariant"],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    if stored.get("schema") != SCHEMA:
        raise ValueError("unsupported coherent CEGIS schema")
    bounds = stored["audit"]["bounds"]
    args = argparse.Namespace(**bounds)
    rebuilt = build_artifact(args)
    if rebuilt != stored:
        raise AssertionError("coherent CEGIS artifact failed reconstruction")
    return report(stored)


def selftest() -> None:
    words, frontier = bounded_first_passage_words(8)
    if [row.word for row in words] != ["1", "011", "001111", "010111"]:
        raise AssertionError("small first-passage table changed")
    if frontier <= 0:
        raise AssertionError("bounded word table hid its frontier")
    node = ROOT
    for word in words[:3]:
        child = extend_node(node, word)
        if child.rho % 2**node.L != node.rho:
            raise AssertionError("selftest lost nested coherence")
        node = child
    replay_node(node)
    args = argparse.Namespace(
        maximum_depth=5,
        beam_width=16,
        maximum_word_length=8,
        phase_precision=2,
        selector_max_precision=2,
        selector_valuation_cap=3,
        selector_max_dyadic_bits=3,
        selector_max_table_entries=32,
        precision_step_interval=2,
        rollout_blocks=5,
        maximum_shortcut_steps=10_000,
        processes=1,
    )
    audit = exact_cegis(args)
    if audit["counterexample"] is not None or audit["compact_parametric_invariant"] is not None:
        raise AssertionError("bounded CEGIS selftest overclaimed")
    if len(audit["depth_rows"]) != 5:
        raise AssertionError("bounded CEGIS depth changed")


def add_bounds(command: argparse.ArgumentParser) -> None:
    command.add_argument("--maximum-depth", type=int, default=16)
    command.add_argument("--beam-width", type=int, default=128)
    command.add_argument("--maximum-word-length", type=int, default=12)
    command.add_argument("--phase-precision", type=int, default=3)
    command.add_argument("--selector-max-precision", type=int, default=4)
    command.add_argument("--selector-valuation-cap", type=int, default=6)
    command.add_argument("--selector-max-dyadic-bits", type=int, default=6)
    command.add_argument("--selector-max-table-entries", type=int, default=256)
    command.add_argument("--precision-step-interval", type=int, default=4)
    command.add_argument("--rollout-blocks", type=int, default=16)
    command.add_argument("--maximum-shortcut-steps", type=int, default=100_000)
    command.add_argument("--processes", type=int, default=1)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("selftest")
    probe = sub.add_parser("probe")
    build = sub.add_parser("build")
    verify = sub.add_parser("verify")
    add_bounds(probe)
    add_bounds(build)
    build.add_argument("artifact", type=Path)
    verify.add_argument("artifact", type=Path)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward coherent CEGIS selftest: PASS")
        return 0
    if args.command == "probe":
        artifact = build_artifact(args)
        print(json.dumps(report(artifact), indent=2, sort_keys=True))
        return 0
    if args.command == "build":
        artifact = build_artifact(args)
        args.artifact.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return 0
    print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
