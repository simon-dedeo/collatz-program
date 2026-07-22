#!/usr/bin/env python3
"""Exact loop certificates for the Yolcu--Aaronson--Heule Collatz SRS.

The 11-rule string rewriting system ``T`` is globally terminating iff the
Collatz conjecture holds (Yolcu--Aaronson--Heule, Theorem 3.17).  A finite
context loop

    u  ->+  left ++ u ++ right

therefore gives a particularly sharp counterexample certificate: context
closure repeats the same nonempty derivation forever.  This worker replays
such certificates one literal rule application at a time and performs two
small, explicitly bounded searches for them.  It does not infer anything
from a long Collatz trajectory.

The ASCII rule table is pinned to the authors' public artifact at commit
8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340.  Its symbols are

    a=f, b=t, c=/, d=., e=0, f=1, g=2.

Only the Python standard library is used.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from collections import Counter, deque
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence


SCHEMA = "yah_context_loop_audit_v1"
UPSTREAM_COMMIT = "8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340"
UPSTREAM_RULES_URL = (
    "https://github.com/emreyolcu/rewriting-collatz/"
    f"blob/{UPSTREAM_COMMIT}/rules/collatz-T.srs"
)
PAPER_URL = "https://arxiv.org/abs/2105.14697"

ALPHABET = "abcdefg"
DIGIT_ALPHABET = "abefg"


@dataclass(frozen=True)
class Rule:
    name: str
    lhs: str
    rhs: str
    family: str
    paper: str


RULES: tuple[Rule, ...] = (
    Rule("DT_f", "ad", "d", "DT", "f. -> ."),
    Rule("DT_t", "bd", "gd", "DT", "t. -> 2."),
    Rule("A_f0", "ae", "ea", "A", "f0 -> 0f"),
    Rule("A_f1", "af", "eb", "A", "f1 -> 0t"),
    Rule("A_f2", "ag", "fa", "A", "f2 -> 1f"),
    Rule("A_t0", "be", "fb", "A", "t0 -> 1t"),
    Rule("A_t1", "bf", "ga", "A", "t1 -> 2f"),
    Rule("A_t2", "bg", "gb", "A", "t2 -> 2t"),
    Rule("B_0", "ce", "cb", "B", "/0 -> /t"),
    Rule("B_1", "cf", "caa", "B", "/1 -> /ff"),
    Rule("B_2", "cg", "cab", "B", "/2 -> /ft"),
)
RULE_BY_NAME = {rule.name: rule for rule in RULES}


def canonical_json(data: Any) -> bytes:
    return json.dumps(data, sort_keys=True, separators=(",", ":")).encode()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rule_table() -> list[dict[str, str]]:
    return [
        {
            "name": rule.name,
            "lhs": rule.lhs,
            "rhs": rule.rhs,
            "family": rule.family,
            "paper": rule.paper,
        }
        for rule in RULES
    ]


def validate_word(word: str) -> None:
    if not isinstance(word, str) or any(symbol not in ALPHABET for symbol in word):
        raise ValueError(f"not a word over {ALPHABET!r}: {word!r}")


def boundary_diagnostics(word: str) -> dict[str, int]:
    """Return the exact marker/flank data used by the Lean boundary no-go."""

    validate_word(word)
    first_slash = word.find("c")
    last_dot = word.rfind("d")
    return {
        "slash_count": word.count("c"),
        "dot_count": word.count("d"),
        "first_slash_offset": first_slash if first_slash >= 0 else len(word),
        "last_dot_suffix_length": (
            len(word) - last_dot - 1 if last_dot >= 0 else len(word)
        ),
    }


def apply_step(word: str, rule_name: str, position: int) -> str:
    validate_word(word)
    if rule_name not in RULE_BY_NAME:
        raise ValueError(f"unknown rule {rule_name!r}")
    if not isinstance(position, int) or isinstance(position, bool):
        raise ValueError("rewrite position must be an integer")
    rule = RULE_BY_NAME[rule_name]
    if position < 0 or position + len(rule.lhs) > len(word):
        raise ValueError(f"rewrite position {position} is out of range for {word!r}")
    if word[position : position + len(rule.lhs)] != rule.lhs:
        raise ValueError(
            f"rule {rule.name} expects {rule.lhs!r} at {position} in {word!r}"
        )
    return word[:position] + rule.rhs + word[position + len(rule.lhs) :]


def rewrite_successors(word: str) -> Iterator[tuple[str, int, str]]:
    """Yield every literal one-step rewrite, including overlapping redexes."""

    for rule in RULES:
        start = 0
        while True:
            position = word.find(rule.lhs, start)
            if position < 0:
                break
            yield rule.name, position, apply_step(word, rule.name, position)
            start = position + 1


def replay_trace(start: str, steps: Sequence[dict[str, Any]]) -> tuple[str, list[str]]:
    validate_word(start)
    word = start
    states = [word]
    for index, step in enumerate(steps):
        if set(step) != {"rule", "position"}:
            raise ValueError(f"step {index} has unexpected fields")
        word = apply_step(word, step["rule"], step["position"])
        states.append(word)
    return word, states


def substitute_word(word: str, morphism: dict[str, str]) -> str:
    validate_word(word)
    if set(morphism) != set(ALPHABET):
        raise ValueError("a morphism must define every YAH symbol exactly once")
    for image in morphism.values():
        validate_word(image)
        if not image:
            raise ValueError("morphism images must be nonempty")
    return "".join(morphism[symbol] for symbol in word)


def verify_rule_simulating_morphism(
    morphism: dict[str, str], rule_simulations: dict[str, list[dict[str, Any]]]
) -> dict[str, Any]:
    """Check ``sigma(lhs) ->+ sigma(rhs)`` for every rule.

    Requiring a nonempty simulation for every rule is a simple productivity
    condition: applying ``sigma`` repeatedly to a nonempty derivation can
    never collapse all of its rewrite steps.
    """

    if set(rule_simulations) != set(RULE_BY_NAME):
        raise ValueError("rule-simulation table does not cover the 11 rules")
    simulation_lengths: dict[str, int] = {}
    for rule in RULES:
        steps = rule_simulations[rule.name]
        if not isinstance(steps, list) or not steps:
            raise ValueError(f"simulation of {rule.name} must be nonempty")
        source = substitute_word(rule.lhs, morphism)
        target = substitute_word(rule.rhs, morphism)
        endpoint, _ = replay_trace(source, steps)
        if endpoint != target:
            raise ValueError(
                f"simulation of {rule.name} ends at {endpoint!r}, not {target!r}"
            )
        simulation_lengths[rule.name] = len(steps)
    return {
        "morphism": dict(sorted(morphism.items())),
        "image_lengths": {symbol: len(morphism[symbol]) for symbol in ALPHABET},
        "simulation_lengths": simulation_lengths,
    }


def verify_morphic_context_loop_certificate(certificate: dict[str, Any]) -> dict[str, Any]:
    """Check the scale-reproducing form ``u ->+ L sigma(u) R``.

    Together with a productive rule-simulating morphism, applying ``sigma``
    to the seed derivation supplies the next nonempty derivation at every
    scale.  This is the string-rewriting analogue of a morphic glider.
    """

    expected = {
        "kind",
        "start",
        "steps",
        "left_context",
        "right_context",
        "morphism",
        "rule_simulations",
    }
    if set(certificate) != expected:
        raise ValueError("morphic-loop certificate has unexpected fields")
    if certificate["kind"] != "morphic_context_loop":
        raise ValueError("unsupported morphic-loop certificate kind")
    morphism_meta = verify_rule_simulating_morphism(
        certificate["morphism"], certificate["rule_simulations"]
    )
    start = certificate["start"]
    left = certificate["left_context"]
    right = certificate["right_context"]
    steps = certificate["steps"]
    validate_word(start)
    validate_word(left)
    validate_word(right)
    if not start or not isinstance(steps, list) or not steps:
        raise ValueError("a morphic loop needs a nonempty core and derivation")
    endpoint, states = replay_trace(start, steps)
    reproduced = substitute_word(start, certificate["morphism"])
    expected_endpoint = left + reproduced + right
    if endpoint != expected_endpoint:
        raise ValueError(
            f"endpoint {endpoint!r} is not the advertised morphic context "
            f"{expected_endpoint!r}"
        )
    return {
        "start": start,
        "endpoint": endpoint,
        "start_boundary_diagnostics": boundary_diagnostics(start),
        "endpoint_boundary_diagnostics": boundary_diagnostics(endpoint),
        "left_context": left,
        "right_context": right,
        "seed_steps": len(steps),
        "maximum_seed_trace_length": max(map(len, states)),
        "morphism": morphism_meta,
    }


def verify_context_loop_certificate(
    certificate: dict[str, Any], *, require_yah_rules: bool = True
) -> dict[str, Any]:
    """Replay ``u ->+ left ++ u ++ right`` and return exact metadata.

    ``require_yah_rules`` is false only in the internal toy-system self-test;
    public certificates always use the fixed YAH table above.
    """

    expected = {"kind", "start", "steps", "left_context", "right_context"}
    if set(certificate) != expected:
        raise ValueError("context-loop certificate has unexpected fields")
    if certificate["kind"] != "literal_context_loop":
        raise ValueError("unsupported loop certificate kind")
    start = certificate["start"]
    left = certificate["left_context"]
    right = certificate["right_context"]
    steps = certificate["steps"]
    validate_word(start)
    validate_word(left)
    validate_word(right)
    if not start:
        raise ValueError("the reproduced word must be nonempty")
    if not isinstance(steps, list) or not steps:
        raise ValueError("a loop must contain at least one rewrite step")
    if not require_yah_rules:
        raise ValueError("toy rules use the separate internal verifier")
    endpoint, states = replay_trace(start, steps)
    expected_endpoint = left + start + right
    if endpoint != expected_endpoint:
        raise ValueError(
            f"endpoint {endpoint!r} is not the advertised context {expected_endpoint!r}"
        )
    families = Counter(RULE_BY_NAME[step["rule"]].family for step in steps)
    return {
        "start": start,
        "endpoint": endpoint,
        "start_boundary_diagnostics": boundary_diagnostics(start),
        "endpoint_boundary_diagnostics": boundary_diagnostics(endpoint),
        "left_context": left,
        "right_context": right,
        "steps": len(steps),
        "max_word_length": max(map(len, states)),
        "rule_family_counts": dict(sorted(families.items())),
        "strict_context_growth": bool(left or right),
    }


def verify_loop_certificate(certificate: dict[str, Any]) -> dict[str, Any]:
    kind = certificate.get("kind")
    if kind == "literal_context_loop":
        return verify_context_loop_certificate(certificate)
    if kind == "morphic_context_loop":
        return verify_morphic_context_loop_certificate(certificate)
    raise ValueError(f"unsupported loop certificate kind {kind!r}")


def _verify_toy_context_loop() -> None:
    """Exercise the context-loop logic on the toy SRS x -> xx."""

    start = "x"
    endpoint = "xx"
    left = ""
    right = "x"
    if endpoint != left + start + right:
        raise AssertionError("toy context loop did not reproduce its core")
    current = start
    for _ in range(9):
        current = current.replace("x", "xx", 1)
    if len(current) != 10:
        raise AssertionError("toy context loop did not iterate")


def is_canonical(word: str) -> bool:
    return (
        len(word) >= 2
        and word[0] == "c"
        and word[-1] == "d"
        and all(symbol in DIGIT_ALPHABET for symbol in word[1:-1])
    )


def canonical_value(word: str) -> int:
    """Evaluate a canonical mixed-base word using the paper's functions."""

    if not is_canonical(word):
        raise ValueError(f"not a canonical mixed-base word: {word!r}")
    value = 1
    for symbol in word[1:-1]:
        if symbol == "a":
            value = 2 * value
        elif symbol == "b":
            value = 2 * value + 1
        elif symbol == "e":
            value = 3 * value
        elif symbol == "f":
            value = 3 * value + 1
        elif symbol == "g":
            value = 3 * value + 2
        else:  # pragma: no cover - guarded by is_canonical
            raise AssertionError(symbol)
    return value


def shortcut_collatz(value: int) -> int:
    if value <= 0:
        raise ValueError("shortcut Collatz is used only on positive integers")
    return value // 2 if value % 2 == 0 else (3 * value + 1) // 2


PAPER_12_TRACE: tuple[dict[str, Any], ...] = (
    {"rule": "A_f0", "position": 2},
    {"rule": "DT_f", "position": 3},
    {"rule": "A_f0", "position": 1},
    {"rule": "DT_f", "position": 2},
    {"rule": "B_0", "position": 0},
    {"rule": "DT_t", "position": 1},
    {"rule": "B_2", "position": 0},
    {"rule": "DT_t", "position": 2},
    {"rule": "A_f2", "position": 1},
    {"rule": "B_1", "position": 0},
    {"rule": "DT_f", "position": 3},
    {"rule": "DT_f", "position": 2},
    {"rule": "DT_f", "position": 1},
)


def paper_trace_regression() -> dict[str, Any]:
    start = "caaed"  # /ff0. = 12
    endpoint, states = replay_trace(start, PAPER_12_TRACE)
    if endpoint != "cd":
        raise AssertionError("paper example did not terminate at /.")
    values = [canonical_value(state) for state in states]
    dynamic_values = [values[0]]
    for index, step in enumerate(PAPER_12_TRACE):
        before = values[index]
        after = values[index + 1]
        family = RULE_BY_NAME[step["rule"]].family
        if family == "DT":
            if after != shortcut_collatz(before):
                raise AssertionError(f"dynamic rule failed at paper step {index}")
            dynamic_values.append(after)
        elif after != before:
            raise AssertionError(f"auxiliary rule changed value at paper step {index}")
    expected = [12, 6, 3, 5, 8, 4, 2, 1]
    if dynamic_values != expected:
        raise AssertionError((dynamic_values, expected))
    return {
        "start": start,
        "start_value": 12,
        "endpoint": endpoint,
        "endpoint_value": 1,
        "rewrite_steps": len(PAPER_12_TRACE),
        "dynamic_values": dynamic_values,
        "trace": list(PAPER_12_TRACE),
    }


def enumerate_one_delimiter_pair(max_length: int) -> Iterator[str]:
    """Words with one c=/, one later d=., and ordinary symbols elsewhere."""

    if max_length < 2:
        return
    for length in range(2, max_length + 1):
        for c_position in range(length):
            for d_position in range(c_position + 1, length):
                other_positions = [
                    position
                    for position in range(length)
                    if position not in (c_position, d_position)
                ]
                for digits in itertools.product(DIGIT_ALPHABET, repeat=length - 2):
                    chars = [""] * length
                    chars[c_position] = "c"
                    chars[d_position] = "d"
                    for position, digit in zip(other_positions, digits):
                        chars[position] = digit
                    yield "".join(chars)


def _shortest_trace_with_length_cap(
    source: str, target: str, max_length: int
) -> tuple[list[dict[str, Any]] | None, int]:
    """Exhaust finite reachability without leaving the stated length cap."""

    if source == target:
        return [], 0
    queue: deque[str] = deque([source])
    parent: dict[str, tuple[str, str, int]] = {}
    visited = {source}
    expanded = 0
    while queue:
        word = queue.popleft()
        expanded += 1
        for rule_name, position, nxt in rewrite_successors(word):
            if len(nxt) > max_length or nxt in visited:
                continue
            parent[nxt] = (word, rule_name, position)
            if nxt == target:
                reverse_steps: list[dict[str, Any]] = []
                cursor = nxt
                while cursor != source:
                    previous, used_rule, used_position = parent[cursor]
                    reverse_steps.append(
                        {"rule": used_rule, "position": used_position}
                    )
                    cursor = previous
                reverse_steps.reverse()
                return reverse_steps, expanded
            visited.add(nxt)
            queue.append(nxt)
    return None, expanded


def exhaustive_letter_endomorphism_search() -> dict[str, Any]:
    """Classify one-symbol simulations fixing the two delimiters.

    For images of an A-rule there is no delimiter and all rewrites preserve
    length.  For a DT-rule image there is a dot but no slash and its two-letter
    source cannot grow.  For a B-rule image there is a slash but no dot, so
    length can grow but can never shrink.  Consequently a path to the fixed
    target cannot pass above ``max(len(source), len(target))``.  The finite
    reachability searches below are therefore complete, not depth cutoffs.
    """

    cache: dict[
        tuple[str, str, int], tuple[list[dict[str, Any]] | None, int]
    ] = {}
    successful: list[dict[str, Any]] = []
    obligations_considered = 0
    morphisms_checked = 0

    for images in itertools.product(DIGIT_ALPHABET, repeat=len(DIGIT_ALPHABET)):
        morphisms_checked += 1
        morphism = dict(zip(DIGIT_ALPHABET, images))
        morphism.update({"c": "c", "d": "d"})
        simulations: dict[str, list[dict[str, Any]]] = {}
        accepted = True
        for rule in RULES:
            obligations_considered += 1
            source = substitute_word(rule.lhs, morphism)
            target = substitute_word(rule.rhs, morphism)
            cap = max(len(source), len(target))
            key = (source, target, cap)
            if key not in cache:
                cache[key] = _shortest_trace_with_length_cap(source, target, cap)
            trace, _ = cache[key]
            if trace is None:
                accepted = False
                break
            simulations[rule.name] = trace
        if accepted:
            productive = all(simulations[rule.name] for rule in RULES)
            record = {
                "morphism": dict(sorted(morphism.items())),
                "productive": productive,
                "rule_simulations": simulations,
            }
            if productive:
                verify_rule_simulating_morphism(morphism, simulations)
            successful.append(record)

    identity = {symbol: symbol for symbol in ALPHABET}
    nontrivial = [record for record in successful if record["morphism"] != identity]
    productive = [record for record in successful if record["productive"]]
    return {
        "class": (
            "nonerasing letter-to-letter morphisms fixing c=/ and d=. and "
            "mapping each of abefg into abefg"
        ),
        "morphisms_checked": morphisms_checked,
        "rule_obligations_considered_after_short_circuit": obligations_considered,
        "distinct_finite_reachability_queries": len(cache),
        "finite_reachability_states_expanded": sum(meta[1] for meta in cache.values()),
        "length_cap_completeness": (
            "A images preserve length; DT images cannot grow; B images cannot "
            "shrink, so no successful path can leave its source/target length cap"
        ),
        "successful_simulations": successful,
        "successful_simulation_count": len(successful),
        "productive_simulation_count": len(productive),
        "nontrivial_simulation_count": len(nontrivial),
        "verdict": (
            "identity is the unique letter-to-letter rule-simulating morphism"
            if len(successful) == 1
            and successful[0]["morphism"] == identity
            and successful[0]["productive"]
            else "letter endomorphism classification changed"
        ),
    }


def exhaustive_uniform_block_endomorphism_search(block_width: int) -> dict[str, Any]:
    """Classify fixed-width digit-block simulations by exact CSP search.

    Delimiters remain fixed while every ordinary symbol is replaced by a word
    of the same positive width.  Failed fully-instantiated rule obligations
    are sound pruning clauses, so the recursive search still exhausts all
    ``(5^block_width)^5`` morphisms.
    """

    if block_width < 1:
        raise ValueError("block width must be positive")
    domain = tuple(
        "".join(symbols)
        for symbols in itertools.product(DIGIT_ALPHABET, repeat=block_width)
    )
    variables = tuple(DIGIT_ALPHABET)
    order = ("a", "b", "e", "f", "g")
    rule_variables = {
        rule.name: tuple(
            symbol for symbol in variables if symbol in set(rule.lhs + rule.rhs)
        )
        for rule in RULES
    }
    cache: dict[
        tuple[str, str, int], tuple[list[dict[str, Any]] | None, int]
    ] = {}
    obligations_considered = 0

    def obligation(
        rule: Rule, assignment: dict[str, str]
    ) -> list[dict[str, Any]] | None:
        nonlocal obligations_considered
        obligations_considered += 1
        mapping = dict(assignment)
        mapping.update({"c": "c", "d": "d"})
        source = "".join(mapping[symbol] for symbol in rule.lhs)
        target = "".join(mapping[symbol] for symbol in rule.rhs)
        cap = max(len(source), len(target))
        key = (source, target, cap)
        if key not in cache:
            cache[key] = _shortest_trace_with_length_cap(source, target, cap)
        return cache[key][0]

    a_candidates = tuple(
        image
        for image in domain
        if obligation(RULE_BY_NAME["DT_f"], {"a": image}) is not None
    )
    successful: list[dict[str, Any]] = []
    search_nodes = 0

    def recurse(index: int, assignment: dict[str, str]) -> None:
        nonlocal search_nodes
        search_nodes += 1
        if index == len(order):
            simulations: dict[str, list[dict[str, Any]]] = {}
            for rule in RULES:
                trace = obligation(rule, assignment)
                if trace is None:
                    return
                simulations[rule.name] = trace
            morphism = dict(assignment)
            morphism.update({"c": "c", "d": "d"})
            productive = all(simulations[rule.name] for rule in RULES)
            if productive:
                verify_rule_simulating_morphism(morphism, simulations)
            successful.append(
                {
                    "morphism": dict(sorted(morphism.items())),
                    "productive": productive,
                    "rule_simulations": simulations,
                }
            )
            return

        variable = order[index]
        images = a_candidates if variable == "a" else domain
        for image in images:
            assignment[variable] = image
            accepted = True
            for rule in RULES:
                needed = rule_variables[rule.name]
                if variable in needed and all(symbol in assignment for symbol in needed):
                    if obligation(rule, assignment) is None:
                        accepted = False
                        break
            if accepted:
                recurse(index + 1, assignment)
            del assignment[variable]

    recurse(0, {})
    return {
        "class": (
            "uniform nonerasing digit-block morphisms of width "
            f"{block_width}, fixing c=/ and d=."
        ),
        "block_width": block_width,
        "image_domain_size": len(domain),
        "morphisms_covered": len(domain) ** len(variables),
        "dt_f_accepted_a_images": list(a_candidates),
        "constraint_search_nodes": search_nodes,
        "rule_obligations_considered": obligations_considered,
        "distinct_finite_reachability_queries": len(cache),
        "finite_reachability_states_expanded": sum(meta[1] for meta in cache.values()),
        "length_cap_completeness": (
            "A images preserve length; DT images contain no slash and cannot "
            "grow; B images contain no dot and cannot shrink"
        ),
        "successful_simulations": successful,
        "successful_simulation_count": len(successful),
        "productive_simulation_count": sum(
            1 for record in successful if record["productive"]
        ),
        "verdict": (
            "no rule-simulating morphism in the stated uniform block class"
            if not successful
            else "uniform block simulations found"
        ),
    }


def _extract_cycle(
    adjacency: dict[str, tuple[tuple[str, str, int], ...]],
    remaining: set[str],
) -> dict[str, Any]:
    """Extract one literal cycle from the nonempty Kahn remainder."""

    color: dict[str, int] = {}
    parent: dict[str, tuple[str, str, int]] = {}
    sys.setrecursionlimit(max(sys.getrecursionlimit(), len(remaining) + 100))

    def visit(word: str) -> tuple[str, str] | None:
        color[word] = 1
        for nxt, rule_name, position in adjacency[word]:
            if nxt not in remaining:
                continue
            if color.get(nxt, 0) == 0:
                parent[nxt] = (word, rule_name, position)
                found = visit(nxt)
                if found is not None:
                    return found
            elif color.get(nxt) == 1:
                parent[nxt] = (word, rule_name, position)
                return word, nxt
        color[word] = 2
        return None

    found: tuple[str, str] | None = None
    for root in sorted(remaining):
        if color.get(root, 0) == 0:
            found = visit(root)
            if found is not None:
                break
    if found is None:  # pragma: no cover - Kahn remainder must contain a cycle
        raise AssertionError("nonempty topological remainder had no cycle")
    tail, head = found
    reverse_nodes = [tail]
    while reverse_nodes[-1] != head:
        reverse_nodes.append(parent[reverse_nodes[-1]][0])
    nodes = list(reversed(reverse_nodes))
    steps: list[dict[str, Any]] = []
    for index in range(len(nodes) - 1):
        child = nodes[index + 1]
        par, rule_name, position = parent[child]
        if par != nodes[index]:
            raise AssertionError("cycle parent reconstruction failed")
        steps.append({"rule": rule_name, "position": position})
    closing = next(
        (edge for edge in adjacency[nodes[-1]] if edge[0] == head), None
    )
    if closing is None:
        raise AssertionError("cycle closing edge vanished")
    steps.append({"rule": closing[1], "position": closing[2]})
    certificate = {
        "kind": "literal_context_loop",
        "start": head,
        "steps": steps,
        "left_context": "",
        "right_context": "",
    }
    verify_context_loop_certificate(certificate)
    return certificate


def exhaustive_bounded_cycle_search(max_word_length: int) -> dict[str, Any]:
    """Exhaust the induced rewrite graph in the stated finite word class."""

    words = tuple(enumerate_one_delimiter_pair(max_word_length))
    nodes = set(words)
    adjacency: dict[str, tuple[tuple[str, str, int], ...]] = {}
    indegree = {word: 0 for word in words}
    raw_applications = 0
    pruned_by_length = 0
    unique_edges = 0
    family_applications: Counter[str] = Counter()
    boundary_diagnostic_checks = 0
    boundary_diagnostic_violations: list[dict[str, Any]] = []

    for word in words:
        endpoint_edges: dict[str, tuple[str, str, int]] = {}
        for rule_name, position, nxt in rewrite_successors(word):
            raw_applications += 1
            family_applications[RULE_BY_NAME[rule_name].family] += 1
            boundary_diagnostic_checks += 1
            before = boundary_diagnostics(word)
            after = boundary_diagnostics(nxt)
            if before != after and not boundary_diagnostic_violations:
                boundary_diagnostic_violations.append(
                    {
                        "start": word,
                        "endpoint": nxt,
                        "rule": rule_name,
                        "position": position,
                        "start_diagnostics": before,
                        "endpoint_diagnostics": after,
                    }
                )
            if len(nxt) > max_word_length:
                pruned_by_length += 1
                continue
            if nxt not in nodes:
                raise AssertionError("rewrite escaped the one-delimiter-pair class")
            endpoint_edges.setdefault(nxt, (nxt, rule_name, position))
        edges = tuple(endpoint_edges[key] for key in sorted(endpoint_edges))
        adjacency[word] = edges
        unique_edges += len(edges)
        for nxt, _, _ in edges:
            indegree[nxt] += 1

    queue = deque(sorted(word for word in words if indegree[word] == 0))
    removed = 0
    longest = {word: 0 for word in words}
    longest_parent: dict[str, tuple[str, str, int]] = {}
    longest_path = 0
    while queue:
        word = queue.popleft()
        removed += 1
        for nxt, _, _ in adjacency[word]:
            candidate = longest[word] + 1
            if candidate > longest[nxt]:
                longest[nxt] = candidate
                edge = next(edge for edge in adjacency[word] if edge[0] == nxt)
                longest_parent[nxt] = (word, edge[1], edge[2])
                longest_path = max(longest_path, candidate)
            indegree[nxt] -= 1
            if indegree[nxt] == 0:
                queue.append(nxt)

    remaining = {word for word in words if indegree[word] > 0}
    candidate = _extract_cycle(adjacency, remaining) if remaining else None
    longest_witness: dict[str, Any] | None = None
    if not remaining:
        endpoint = max(words, key=lambda word: (longest[word], word))
        reverse_steps: list[dict[str, Any]] = []
        start = endpoint
        while start in longest_parent:
            previous, rule_name, position = longest_parent[start]
            reverse_steps.append({"rule": rule_name, "position": position})
            start = previous
        steps = list(reversed(reverse_steps))
        replayed_endpoint, states = replay_trace(start, steps)
        if replayed_endpoint != endpoint or len(steps) != longest_path:
            raise AssertionError("longest induced path reconstruction failed")
        families = Counter(RULE_BY_NAME[step["rule"]].family for step in steps)
        longest_witness = {
            "start": start,
            "endpoint": endpoint,
            "start_boundary_diagnostics": boundary_diagnostics(start),
            "endpoint_boundary_diagnostics": boundary_diagnostics(endpoint),
            "steps": steps,
            "edge_count": len(steps),
            "maximum_word_length": max(map(len, states)),
            "rule_family_counts": dict(sorted(families.items())),
            "trace_sha256": sha256_bytes(canonical_json(states)),
        }
    return {
        "class": "exactly one c=/ and one later d=.; all other symbols in abefg",
        "max_word_length": max_word_length,
        "state_count": len(words),
        "raw_rule_applications": raw_applications,
        "boundary_diagnostic_rule_checks": boundary_diagnostic_checks,
        "boundary_diagnostic_violation_count": len(boundary_diagnostic_violations),
        "first_boundary_diagnostic_violation": (
            boundary_diagnostic_violations[0]
            if boundary_diagnostic_violations
            else None
        ),
        "unique_induced_edges": unique_edges,
        "applications_pruned_above_length_bound": pruned_by_length,
        "rule_family_application_counts": dict(sorted(family_applications.items())),
        "topologically_removed_states": removed,
        "cycle_core_states": len(remaining),
        "longest_induced_path_edges": longest_path if not remaining else None,
        "longest_induced_path_witness": longest_witness,
        "context_loop_certificate": candidate,
        "verdict": (
            "cycle_found"
            if candidate is not None
            else "no literal rewrite cycle in the stated induced finite graph"
        ),
    }


def _reconstruct_path(
    start: str,
    current: str,
    parent: dict[str, tuple[str, str, int]],
    final_rule: str,
    final_position: int,
) -> list[dict[str, Any]]:
    reverse_steps: list[dict[str, Any]] = []
    word = current
    while word != start:
        previous, rule_name, position = parent[word]
        reverse_steps.append({"rule": rule_name, "position": position})
        word = previous
    reverse_steps.reverse()
    reverse_steps.append({"rule": final_rule, "position": final_position})
    return reverse_steps


def bounded_context_loop_search(
    max_seed_length: int, max_steps: int, max_path_word_length: int
) -> dict[str, Any]:
    """Exhaust bounded paths from short cores and test ``u ->+ L u R``."""

    seeds = tuple(enumerate_one_delimiter_pair(max_seed_length))
    total_reached = 0
    total_expanded = 0
    transitions_considered = 0
    transitions_pruned_by_length = 0
    maximum_reached_length = 0
    first_certificate: dict[str, Any] | None = None

    for seed in seeds:
        queue: deque[tuple[str, int]] = deque([(seed, 0)])
        visited = {seed}
        parent: dict[str, tuple[str, str, int]] = {}
        while queue:
            word, depth = queue.popleft()
            total_expanded += 1
            maximum_reached_length = max(maximum_reached_length, len(word))
            if depth >= max_steps:
                continue
            for rule_name, position, nxt in rewrite_successors(word):
                transitions_considered += 1
                if len(nxt) > max_path_word_length:
                    transitions_pruned_by_length += 1
                    continue
                occurrence = nxt.find(seed)
                if occurrence >= 0:
                    steps = _reconstruct_path(
                        seed, word, parent, rule_name, position
                    )
                    certificate = {
                        "kind": "literal_context_loop",
                        "start": seed,
                        "steps": steps,
                        "left_context": nxt[:occurrence],
                        "right_context": nxt[occurrence + len(seed) :],
                    }
                    verify_context_loop_certificate(certificate)
                    first_certificate = certificate
                    break
                if nxt not in visited:
                    visited.add(nxt)
                    parent[nxt] = (word, rule_name, position)
                    queue.append((nxt, depth + 1))
            if first_certificate is not None:
                break
        total_reached += len(visited)
        if first_certificate is not None:
            break

    return {
        "seed_class": "exactly one c=/ and one later d=.; all other symbols in abefg",
        "max_seed_length": max_seed_length,
        "max_rewrite_steps": max_steps,
        "max_intermediate_word_length": max_path_word_length,
        "seed_count": len(seeds),
        "seeds_completed": len(seeds) if first_certificate is None else None,
        "total_distinct_reached_states_across_seeds": total_reached,
        "total_expanded_states_across_seeds": total_expanded,
        "transitions_considered": transitions_considered,
        "transitions_pruned_above_length_bound": transitions_pruned_by_length,
        "maximum_reached_word_length": maximum_reached_length,
        "context_loop_certificate": first_certificate,
        "verdict": (
            "context_loop_found"
            if first_certificate is not None
            else "no literal context loop in the stated bounded path class"
        ),
    }


def worker_sha256() -> str:
    return sha256_bytes(Path(__file__).read_bytes())


def build_artifact(
    max_graph_length: int,
    max_seed_length: int,
    max_steps: int,
    max_path_length: int,
) -> dict[str, Any]:
    if max_graph_length < 2 or max_seed_length < 2:
        raise ValueError("word bounds must be at least two")
    if max_steps < 1 or max_path_length < max_seed_length:
        raise ValueError("invalid path bounds")
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "upstream": {
            "paper": PAPER_URL,
            "authors_repository_commit": UPSTREAM_COMMIT,
            "rules_url": UPSTREAM_RULES_URL,
            "ascii_symbol_map": {
                "a": "f",
                "b": "t",
                "c": "/",
                "d": ".",
                "e": "0",
                "f": "1",
                "g": "2",
            },
        },
        "rules": rule_table(),
        "rule_table_sha256": sha256_bytes(canonical_json(rule_table())),
        "certificate_contract": {
            "forms": [
                "u ->+ left_context ++ u ++ right_context",
                (
                    "u ->+ left_context ++ sigma(u) ++ right_context, where "
                    "every sigma(rule) has a nonempty replayed simulation"
                ),
            ],
            "soundness": (
                "context closure iterates a literal loop; a productive rule-simulating "
                "morphism iterates a morphic loop at successively larger scales; "
                "Yolcu--Aaronson--Heule Theorem 3.17 is the external seam from "
                "nontermination of T to failure of Collatz"
            ),
            "candidate": None,
        },
        "paper_example_12_to_1": paper_trace_regression(),
        "letter_endomorphism_search": exhaustive_letter_endomorphism_search(),
        "uniform_two_block_endomorphism_search": (
            exhaustive_uniform_block_endomorphism_search(2)
        ),
        "induced_cycle_search": exhaustive_bounded_cycle_search(max_graph_length),
        "bounded_context_loop_search": bounded_context_loop_search(
            max_seed_length, max_steps, max_path_length
        ),
    }
    candidate = data["induced_cycle_search"]["context_loop_certificate"]
    if candidate is None:
        candidate = data["bounded_context_loop_search"]["context_loop_certificate"]
    data["certificate_contract"]["candidate"] = candidate
    payload = dict(data)
    data["artifact_sha256"] = sha256_bytes(canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema",
        "generated_at_utc",
        "worker_sha256",
        "upstream",
        "rules",
        "rule_table_sha256",
        "certificate_contract",
        "paper_example_12_to_1",
        "letter_endomorphism_search",
        "uniform_two_block_endomorphism_search",
        "induced_cycle_search",
        "bounded_context_loop_search",
        "artifact_sha256",
    }
    if set(data) != required:
        raise ValueError("artifact has unexpected top-level fields")
    if data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["rules"] != rule_table():
        raise ValueError("rule table mismatch")
    if data["rule_table_sha256"] != sha256_bytes(canonical_json(rule_table())):
        raise ValueError("rule table hash mismatch")
    payload = dict(data)
    advertised_hash = payload.pop("artifact_sha256")
    if advertised_hash != sha256_bytes(canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    if data["paper_example_12_to_1"] != paper_trace_regression():
        raise ValueError("paper semantic regression mismatch")
    rebuilt_endomorphisms = exhaustive_letter_endomorphism_search()
    if rebuilt_endomorphisms != data["letter_endomorphism_search"]:
        raise ValueError("letter-endomorphism search replay mismatch")
    rebuilt_two_blocks = exhaustive_uniform_block_endomorphism_search(2)
    if rebuilt_two_blocks != data["uniform_two_block_endomorphism_search"]:
        raise ValueError("uniform two-block endomorphism search replay mismatch")

    graph_bound = data["induced_cycle_search"]["max_word_length"]
    rebuilt_graph = exhaustive_bounded_cycle_search(graph_bound)
    if rebuilt_graph != data["induced_cycle_search"]:
        raise ValueError("induced cycle-search replay mismatch")

    context = data["bounded_context_loop_search"]
    rebuilt_context = bounded_context_loop_search(
        context["max_seed_length"],
        context["max_rewrite_steps"],
        context["max_intermediate_word_length"],
    )
    if rebuilt_context != context:
        raise ValueError("context-loop search replay mismatch")

    candidate = data["certificate_contract"]["candidate"]
    if candidate is not None:
        verify_loop_certificate(candidate)
    expected_candidate = rebuilt_graph["context_loop_certificate"]
    if expected_candidate is None:
        expected_candidate = rebuilt_context["context_loop_certificate"]
    if candidate != expected_candidate:
        raise ValueError("advertised candidate does not match bounded searches")
    return {
        "worker_sha256": data["worker_sha256"],
        "artifact_sha256": data["artifact_sha256"],
        "graph_states": rebuilt_graph["state_count"],
        "graph_edges": rebuilt_graph["unique_induced_edges"],
        "context_seeds": rebuilt_context["seed_count"],
        "context_transitions": rebuilt_context["transitions_considered"],
        "letter_endomorphisms": rebuilt_endomorphisms[
            "successful_simulation_count"
        ],
        "uniform_two_block_endomorphisms": rebuilt_two_blocks[
            "successful_simulation_count"
        ],
        "candidate": candidate,
    }


def selftest() -> None:
    if len(RULES) != 11 or len(RULE_BY_NAME) != 11:
        raise AssertionError("the YAH rule table must contain 11 distinct rules")
    _verify_toy_context_loop()
    identity = {symbol: symbol for symbol in ALPHABET}
    identity_simulations = {
        rule.name: [{"rule": rule.name, "position": 0}] for rule in RULES
    }
    verify_rule_simulating_morphism(identity, identity_simulations)
    regression = paper_trace_regression()
    if regression["dynamic_values"] != [12, 6, 3, 5, 8, 4, 2, 1]:
        raise AssertionError("paper trace regression changed")
    try:
        apply_step("cfd", "B_1", 1)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid rewrite position was accepted")
    bogus = {
        "kind": "literal_context_loop",
        "start": "cfd",
        "steps": [{"rule": "B_1", "position": 0}],
        "left_context": "",
        "right_context": "",
    }
    try:
        verify_context_loop_certificate(bogus)
    except ValueError:
        pass
    else:
        raise AssertionError("a non-reproducing rewrite was accepted as a loop")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")

    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-graph-length", type=int, default=7)
    build.add_argument("--max-seed-length", type=int, default=5)
    build.add_argument("--max-steps", type=int, default=12)
    build.add_argument("--max-path-length", type=int, default=10)

    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)

    check = subparsers.add_parser("check-loop")
    check.add_argument("certificate", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "selftest":
        selftest()
        print("selftest: ok")
        return 0
    if args.command == "build":
        selftest()
        artifact = build_artifact(
            args.max_graph_length,
            args.max_seed_length,
            args.max_steps,
            args.max_path_length,
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    if args.command == "check-loop":
        certificate = json.loads(args.certificate.read_text())
        print(json.dumps(verify_loop_certificate(certificate), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
