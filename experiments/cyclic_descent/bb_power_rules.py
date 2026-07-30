#!/usr/bin/env python3
"""Busy-Beaver-style symbolic rule mining for Collatz power charts.

This program is a *rule miner and exact validator*, not a Collatz solver.
It uses the architecture of the bbchallenge validators:

* configurations are affine power words ``A(r) + B(r) k``;
* primitive steps are exact Syracuse/component rewrites;
* chain rules compress an unbounded number of even or odd steps;
* guards are proved by a finite eventual-period automaton, never sampling;
* candidate charts are learned from the concrete cyclic miner's last frontier;
* every emitted rule is replayed independently from its JSON description.

The expression language is a finite rational linear combination of ``base^r``.
It is closed under the four primitive affine operations, counter shifts, and
the two Collatz chain rules.  Positive bases are arbitrary: a second-level
macro may therefore create ``6^r``, ``9^r``, and so on.

A search report is scoped to its displayed template/path bounds.  Even a
closed symbolic transition graph would still need base rules and a global
size-change rank before it became a termination certificate.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
import json
from math import gcd, lcm
from pathlib import Path
import sys
from typing import Iterable


HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import cyclic_descent as concrete  # noqa: E402


@dataclass(frozen=True)
class ExpPoly:
    """A normalized sum ``sum coefficient[base] * base^r``."""

    terms: tuple[tuple[int, Fraction], ...] = ()

    @staticmethod
    def make(terms: dict[int, Fraction | int]) -> "ExpPoly":
        cleaned = []
        for base, coefficient in terms.items():
            coefficient = Fraction(coefficient)
            if base <= 0:
                raise ValueError("exponential bases must be positive")
            if coefficient:
                cleaned.append((base, coefficient))
        return ExpPoly(tuple(sorted(cleaned)))

    @staticmethod
    def constant(value: int | Fraction) -> "ExpPoly":
        return ExpPoly.make({1: Fraction(value)})

    @staticmethod
    def monomial(coefficient: int, base: int) -> "ExpPoly":
        return ExpPoly.make({base: Fraction(coefficient)})

    def as_dict(self) -> dict[int, Fraction]:
        return dict(self.terms)

    def __add__(self, other: "ExpPoly") -> "ExpPoly":
        out = self.as_dict()
        for base, coefficient in other.terms:
            out[base] = out.get(base, Fraction()) + coefficient
        return ExpPoly.make(out)

    def __sub__(self, other: "ExpPoly") -> "ExpPoly":
        return self + other.scale(-1)

    def scale(self, coefficient: int | Fraction) -> "ExpPoly":
        coefficient = Fraction(coefficient)
        return ExpPoly.make({b: c * coefficient for b, c in self.terms})

    def shift(self, delta: int) -> "ExpPoly":
        """Return the expression ``r |-> self(r+delta)`` exactly."""
        return ExpPoly.make(
            {
                base: coefficient * Fraction(base) ** delta
                for base, coefficient in self.terms
            }
        )

    def evaluate(self, r: int) -> Fraction:
        if r < 0:
            raise ValueError("negative exponent parameter")
        return sum((c * base**r for base, c in self.terms), Fraction())

    def denominator(self) -> int:
        return reduce(lcm, (c.denominator for _, c in self.terms), 1)

    def residue_cycle(
        self, modulus: int, start: int, stride: int = 1
    ) -> tuple[set[int], dict]:
        """All residues on ``r=start+stride*n``, with an exact cycle proof.

        If D clears denominators, the vector ``base^r mod modulus*D`` is a
        finite deterministic state.  Repetition proves that every later
        residue has been checked, including the non-coprime preperiod.
        """
        if modulus <= 0 or start < 0 or stride <= 0:
            raise ValueError("bad residue-cycle parameters")
        denominator = self.denominator()
        lifted_modulus = modulus * denominator
        integer_coefficients = {
            base: int(coefficient * denominator)
            for base, coefficient in self.terms
        }
        bases = tuple(sorted(integer_coefficients))
        state = tuple(pow(base, start, lifted_modulus) for base in bases)
        multipliers = tuple(pow(base, stride, lifted_modulus) for base in bases)
        seen: dict[tuple[int, ...], int] = {}
        residues: set[int] = set()
        states = 0
        while state not in seen:
            seen[state] = states
            numerator = sum(
                integer_coefficients[base] * value
                for base, value in zip(bases, state)
            ) % lifted_modulus
            if numerator % denominator:
                raise ValueError(
                    f"expression is not integer-valued at guarded state {states}"
                )
            residues.add((numerator // denominator) % modulus)
            state = tuple(
                value * multiplier % lifted_modulus
                for value, multiplier in zip(state, multipliers)
            )
            states += 1
        return residues, {
            "modulus": modulus,
            "denominator": denominator,
            "guard_start": start,
            "guard_stride": stride,
            "preperiod": seen[state],
            "period": states - seen[state],
            "states_checked": states,
            "residues": sorted(residues),
        }

    def positive_on_guard_by_coefficients(self, start: int) -> bool:
        """A deliberately simple, proof-producing positivity criterion."""
        value = self.evaluate(start)
        return value > 0 and all(c >= 0 for base, c in self.terms if base != 1)

    def to_json(self) -> list[dict]:
        return [
            {"base": base, "numerator": c.numerator, "denominator": c.denominator}
            for base, c in self.terms
        ]

    @staticmethod
    def from_json(data: list[dict]) -> "ExpPoly":
        return ExpPoly.make(
            {
                item["base"]: Fraction(item["numerator"], item["denominator"])
                for item in data
            }
        )

    def display(self) -> str:
        if not self.terms:
            return "0"
        pieces = []
        for base, coefficient in self.terms:
            atom = "1" if base == 1 else f"{base}^r"
            pieces.append(f"{coefficient}*{atom}")
        return " + ".join(pieces).replace(" + -", " - ")


@dataclass(frozen=True)
class SymbolicPair:
    base: ExpPoly
    step: ExpPoly

    def to_json(self) -> dict:
        return {"base": self.base.to_json(), "step": self.step.to_json()}

    @staticmethod
    def from_json(data: dict) -> "SymbolicPair":
        return SymbolicPair(
            ExpPoly.from_json(data["base"]), ExpPoly.from_json(data["step"])
        )


@dataclass(frozen=True)
class Guard:
    start: int
    stride: int = 1

    def to_json(self) -> dict:
        return {"start": self.start, "stride": self.stride}


@dataclass(frozen=True)
class Template:
    name: str
    pair: SymbolicPair
    guard: Guard
    origin: str
    base_safe: bool

    def to_json(self) -> dict:
        return {
            "name": self.name,
            "pair": self.pair.to_json(),
            "guard": self.guard.to_json(),
            "origin": self.origin,
            "base_safe": self.base_safe,
        }


PRIMITIVES = ("E", "O", "I0", "I1")


def primitive(pair: SymbolicPair, op: str, guard: Guard) -> tuple[SymbolicPair, list[dict]]:
    a, b = pair.base, pair.step
    checks = []
    if op == "E":
        ra, ca = a.residue_cycle(2, guard.start, guard.stride)
        rb, cb = b.residue_cycle(2, guard.start, guard.stride)
        checks += [ca, cb]
        if ra != {0} or rb != {0}:
            raise ValueError("E parity guard fails")
        out = SymbolicPair(a.scale(Fraction(1, 2)), b.scale(Fraction(1, 2)))
    elif op == "O":
        ra, ca = a.residue_cycle(2, guard.start, guard.stride)
        rb, cb = b.residue_cycle(2, guard.start, guard.stride)
        checks += [ca, cb]
        if ra != {1} or rb != {0}:
            raise ValueError("O parity guard fails")
        out = SymbolicPair(
            (a.scale(3) + ExpPoly.constant(1)).scale(Fraction(1, 2)),
            b.scale(Fraction(3, 2)),
        )
    elif op == "I0":
        out = SymbolicPair(a.scale(2), b.scale(2))
    elif op == "I1":
        ra, ca = a.residue_cycle(3, guard.start, guard.stride)
        rb, cb = b.residue_cycle(3, guard.start, guard.stride)
        checks += [ca, cb]
        if ra != {2} or rb != {0}:
            raise ValueError("I1 congruence guard fails")
        out = SymbolicPair(
            (a.scale(2) - ExpPoly.constant(1)).scale(Fraction(1, 3)),
            b.scale(Fraction(2, 3)),
        )
    else:
        raise ValueError(f"unknown primitive {op}")
    if not out.base.positive_on_guard_by_coefficients(guard.start):
        raise ValueError("simple positivity proof failed")
    return out, checks


def divide_bases(expr: ExpPoly, divisor: int) -> ExpPoly:
    """Recognize ``expr(r)=divisor^r*out(r)`` coefficientwise."""
    out: dict[int, Fraction] = {}
    for base, coefficient in expr.terms:
        if base % divisor:
            raise ValueError("expression lacks the requested exponential factor")
        target = base // divisor
        out[target] = out.get(target, Fraction()) + coefficient
    return ExpPoly.make(out)


def chain(pair: SymbolicPair, kind: str, guard: Guard) -> SymbolicPair:
    """Apply an exact unbounded Syracuse chain rule."""
    if kind == "EVEN_CHAIN":
        quotient = SymbolicPair(
            divide_bases(pair.base, 2), divide_bases(pair.step, 2)
        )
        if not quotient.base.positive_on_guard_by_coefficients(guard.start):
            raise ValueError("even-chain quotient positivity fails")
        return quotient
    if kind == "ODD_CHAIN":
        xbase = divide_bases(pair.base + ExpPoly.constant(1), 2)
        xstep = divide_bases(pair.step, 2)
        if not xbase.positive_on_guard_by_coefficients(guard.start):
            raise ValueError("odd-chain quotient positivity fails")
        return SymbolicPair(
            ExpPoly.make({3 * b: c for b, c in xbase.terms})
            - ExpPoly.constant(1),
            ExpPoly.make({3 * b: c for b, c in xstep.terms}),
        )
    raise ValueError(f"unknown chain rule {kind}")


def replay(pair: SymbolicPair, path: list[dict], guard: Guard) -> tuple[SymbolicPair, list[dict]]:
    checks: list[dict] = []
    for step in path:
        kind = step["kind"]
        if kind == "primitive":
            pair, step_checks = primitive(pair, step["op"], guard)
            checks.extend(step_checks)
        elif kind == "chain":
            pair = chain(pair, step["op"], guard)
        else:
            raise ValueError(f"unknown proof step kind {kind}")
    return pair, checks


def split_pair(pair: SymbolicPair, radix: int, digit: int) -> SymbolicPair:
    return SymbolicPair(
        pair.base + pair.step.scale(digit), pair.step.scale(radix)
    )


def vp(n: int, prime: int) -> int:
    out = 0
    while n and n % prime == 0:
        n //= prime
        out += 1
    return out


def learn_frontier(bound: int, path_depth: int) -> tuple[list[tuple[int, int]], dict]:
    bounds = concrete.SearchBounds(
        base_limit=bound,
        step_limit=bound,
        walk_base_limit=8 * bound,
        walk_step_limit=16 * bound,
        path_depth=path_depth,
        max_split_power=4,
    )
    miner = concrete.Miner(bounds)
    _live, rounds = miner.greatest_fixed_point()
    last = max(miner.death_round.values())
    frontier = [
        miner.states[state]
        for state, death in miner.death_round.items()
        if death >= last - 1
    ]
    normalized: Counter[tuple[int, int]] = Counter()
    scaling: Counter[str] = Counter()
    for a, b in frontier:
        e2 = min(vp(a, 2), vp(b, 2))
        e3 = min(vp(a, 3), vp(b, 3))
        normalized[(a // 2**e2, b // 2**e2)] += 1
        if e2:
            scaling["common_power_2"] += 1
        if e3:
            scaling["common_power_3"] += 1
        if min(vp(a + 1, 2), vp(b, 2)):
            scaling["odd_run_power_2"] += 1
    cores = [pair for pair, _count in normalized.most_common(12)]
    report = {
        "concrete_bounds": bounds.__dict__,
        "states": len(miner.states),
        "pruning_rounds": len(rounds),
        "last_round": last,
        "two_last_round_frontier_states": len(frontier),
        "scaling_signals": dict(scaling),
        "learned_dyadic_cores": [
            {"core": list(pair), "multiplicity": count}
            for pair, count in normalized.most_common(20)
        ],
    }
    return cores, report


def stopping_base_safe(n: int) -> bool:
    return concrete.orbit_to_one(n) is not None


def verify_base_safe(template: Template) -> bool:
    """Independently recognize the two admitted zero-tail proof schemas."""
    terms = template.pair.base.terms
    if len(terms) != 1:
        return False
    base, coefficient = terms[0]
    if coefficient.denominator != 1 or coefficient <= 0:
        return False
    core = coefficient.numerator
    if concrete.orbit_to_one(core) is None:
        return False
    # Constant base, or 2^r*core followed by the checked EVEN_CHAIN.
    return base == 1 or base == 2


def build_templates(cores: list[tuple[int, int]]) -> list[Template]:
    templates: list[Template] = [
        Template(
            "root",
            SymbolicPair(ExpPoly.constant(1), ExpPoly.constant(1)),
            Guard(0),
            "distinguished root chart 1+k",
            True,
        )
    ]
    seen = {templates[0].pair}
    for a, b in cores:
        variants = [
            (
                f"c_{a}_{b}",
                SymbolicPair(ExpPoly.constant(a), ExpPoly.constant(b)),
                Guard(0),
                "constant frontier core",
                stopping_base_safe(a),
            ),
            (
                f"d_{a}_{b}",
                SymbolicPair(ExpPoly.monomial(a, 2), ExpPoly.monomial(b, 2)),
                Guard(1),
                "common dyadic scale learned from frontier",
                stopping_base_safe(a),
            ),
            (
                f"dm_{a}_{b}",
                SymbolicPair(
                    ExpPoly.monomial(a, 2) - ExpPoly.constant(1),
                    ExpPoly.monomial(b, 2),
                ),
                Guard(1),
                "dyadic odd-run chart learned from frontier core",
                False,
            ),
            (
                f"tm_{a}_{b}",
                SymbolicPair(
                    ExpPoly.monomial(a, 3) - ExpPoly.constant(1),
                    ExpPoly.monomial(b, 3),
                ),
                Guard(1),
                "ternary image of dyadic odd-run chart",
                False,
            ),
        ]
        for name, pair, guard, origin, base_safe in variants:
            if pair in seen:
                continue
            seen.add(pair)
            templates.append(Template(name, pair, guard, origin, base_safe))
    return templates


def match_target(
    finish: SymbolicPair,
    target: Template,
    source_guard: Guard,
    max_u: int,
    max_v: int,
    shifts: Iterable[int],
) -> list[dict]:
    matches = []
    for delta in shifts:
        if source_guard.start + delta < target.guard.start:
            continue
        ta = target.pair.base.shift(delta)
        tb = target.pair.step.shift(delta)
        for u in range(1, max_u + 1):
            if finish.step != tb.scale(u):
                continue
            for v in range(max_v + 1):
                if finish.base == ta + tb.scale(v):
                    matches.append(
                        {
                            "target": target.name,
                            "counter_map": {"kind": "shift", "delta": delta},
                            "tail_map": {"u": u, "v": v},
                        }
                    )
    return matches


def symbolic_bfs(
    start: SymbolicPair,
    guard: Guard,
    depth: int,
    state_cap: int,
) -> dict[SymbolicPair, list[dict]]:
    found = {start: []}
    queue = deque([start])
    while queue and len(found) < state_cap:
        pair = queue.popleft()
        path = found[pair]
        if len(path) >= depth:
            continue
        for op in PRIMITIVES:
            try:
                nxt, _checks = primitive(pair, op, guard)
            except ValueError:
                continue
            if nxt not in found:
                found[nxt] = path + [{"kind": "primitive", "op": op}]
                queue.append(nxt)
        for op in ("EVEN_CHAIN", "ODD_CHAIN"):
            try:
                nxt = chain(pair, op, guard)
            except ValueError:
                continue
            if nxt not in found:
                found[nxt] = path + [{"kind": "chain", "op": op}]
                queue.append(nxt)
    return found


def discover_rules(
    templates: list[Template],
    depth: int,
    state_cap: int,
    max_u: int,
    max_v: int,
    rule_cap: int,
) -> tuple[list[dict], dict]:
    rules = []
    branches_searched = 0
    symbolic_states = 0
    for source in templates:
        for digit in (0, 1):
            branches_searched += 1
            start = split_pair(source.pair, 2, digit)
            found = symbolic_bfs(start, source.guard, depth, state_cap)
            symbolic_states += len(found)
            candidates = []
            for finish, path in found.items():
                for target in templates:
                    for match in match_target(
                        finish,
                        target,
                        source.guard,
                        max_u,
                        max_v,
                        shifts=(-2, -1, 0, 1, 2),
                    ):
                        if not path and match["target"] == source.name:
                            continue
                        candidates.append((len(path), path, finish, match))
            candidates.sort(
                key=lambda item: (
                    item[0],
                    item[3]["tail_map"]["u"] + item[3]["tail_map"]["v"],
                    item[3]["target"],
                )
            )
            for _cost, path, finish, match in candidates[:rule_cap]:
                _replay, checks = replay(start, path, source.guard)
                rules.append(
                    {
                        "source": source.name,
                        "guard": source.guard.to_json(),
                        "split": {"radix": 2, "digit": digit},
                        "start": start.to_json(),
                        "path": path,
                        "finish": finish.to_json(),
                        **match,
                        "residue_automata": checks,
                    }
                )
    by_source_digit = Counter((r["source"], r["split"]["digit"]) for r in rules)
    complete_modes = [
        source.name
        for source in templates
        if by_source_digit[source.name, 0] and by_source_digit[source.name, 1]
    ]
    stats = {
        "branches_searched": branches_searched,
        "symbolic_states_explored": symbolic_states,
        "rules_retained": len(rules),
        "templates_with_both_binary_branches": complete_modes,
        "base_safe_complete_modes": [
            t.name for t in templates if t.base_safe and t.name in complete_modes
        ],
        "rules_using_unbounded_chain": sum(
            any(step["kind"] == "chain" for step in rule["path"]) for rule in rules
        ),
    }
    return rules, stats


def solve_size_change(
    templates: list[Template],
    rules: list[dict],
    weight_limit: int,
    constant_limit: int,
    timeout_ms: int,
    phases: int = 1,
) -> tuple[dict, dict | None]:
    """Search for a closed base-safe rule table with a lexicographic rank.

    Every phase at chart i is ``er_i*r + tail_i*k + constant_i``. Since every
    transition is affine in ``r,t``, universal strict decrease or equality is
    decided by coefficient constraints. The vector decreases
    lexicographically: an earlier phase is equal and the selected phase is
    strict. This is the size-change analogue of nested BB induction rules.
    """
    if phases <= 0:
        raise ValueError("rank must have at least one phase")
    z3 = concrete.z3
    safe = {template.name: template for template in templates if template.base_safe}
    root = "root"
    candidate_table: dict[tuple[str, int], list[tuple[int, dict]]] = {}
    for index, rule in enumerate(rules):
        if rule["source"] in safe and rule["target"] in safe:
            candidate_table.setdefault(
                (rule["source"], rule["split"]["digit"]), []
            ).append((index, rule))
    basic = {
        "rank_form": (
            "exponent_weight*r + tail_weight*k + constant"
            if phases == 1
            else f"lexicographic vector of {phases} affine two-counter phases"
        ),
        "rank_phases": phases,
        "base_safe_templates": len(safe),
        "base_safe_candidate_rules": sum(len(v) for v in candidate_table.values()),
        "rank_weight_limit": weight_limit,
        "rank_constant_limit": constant_limit,
        "timeout_ms": timeout_ms,
    }
    if z3 is None:
        return {"status": "z3-unavailable", **basic}, None

    # Boolean greatest-fixed-point prepass before arithmetic synthesis.
    live = set(safe)
    rounds = 0
    while True:
        dead = [
            source
            for source in live
            if any(
                not any(rule["target"] in live for _idx, rule in candidate_table.get((source, digit), []))
                for digit in (0, 1)
            )
        ]
        if not dead:
            break
        live.difference_update(dead)
        rounds += 1
    basic.update(
        {
            "boolean_prepass_rounds": rounds,
            "boolean_prepass_live": len(live),
            "boolean_prepass_root_live": root in live,
        }
    )
    if root not in live:
        return {"status": "unsat-boolean-prepass", **basic}, None

    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    use = {name: z3.Bool(f"bb_use_{name}") for name in live}
    er = [
        {name: z3.Int(f"bb_er_{phase}_{name}") for name in live}
        for phase in range(phases)
    ]
    tk = [
        {name: z3.Int(f"bb_tk_{phase}_{name}") for name in live}
        for phase in range(phases)
    ]
    const = [
        {name: z3.Int(f"bb_c_{phase}_{name}") for name in live}
        for phase in range(phases)
    ]
    takes: dict[int, object] = {}
    solver.add(use[root])
    for name in sorted(live):
        for phase in range(phases):
            solver.add(er[phase][name] >= 0, er[phase][name] <= weight_limit)
            solver.add(tk[phase][name] >= 0, tk[phase][name] <= weight_limit)
            solver.add(const[phase][name] >= 0, const[phase][name] <= constant_limit)
        solver.add(
            sum(er[phase][name] + tk[phase][name] for phase in range(phases)) >= 1
        )
        for digit in (0, 1):
            choices = []
            for index, rule in candidate_table.get((name, digit), []):
                target = rule["target"]
                if target not in live:
                    continue
                take = z3.Bool(f"bb_take_{index}")
                takes[index] = take
                choices.append(take)
                solver.add(z3.Implies(take, use[name]))
                solver.add(z3.Implies(take, use[target]))
                delta = rule["counter_map"]["delta"]
                u, v = rule["tail_map"]["u"], rule["tail_map"]["v"]
                rmin = safe[name].guard.start
                tmin = 1 if digit == 0 else 0
                strict = []
                equal = []
                for phase in range(phases):
                    exponent_gap = er[phase][name] - er[phase][target]
                    tail_gap = 2 * tk[phase][name] - u * tk[phase][target]
                    source_endpoint = (
                        er[phase][name] * rmin
                        + tk[phase][name] * (2 * tmin + digit)
                        + const[phase][name]
                    )
                    target_endpoint = (
                        er[phase][target] * (rmin + delta)
                        + tk[phase][target] * (u * tmin + v)
                        + const[phase][target]
                    )
                    strict.append(
                        z3.And(
                            exponent_gap >= 0,
                            tail_gap >= 0,
                            target_endpoint < source_endpoint,
                        )
                    )
                    equal.append(
                        z3.And(
                            exponent_gap == 0,
                            tail_gap == 0,
                            target_endpoint == source_endpoint,
                        )
                    )
                lex_decrease = z3.Or(
                    [z3.And(*(equal[:phase] + [strict[phase]])) for phase in range(phases)]
                )
                solver.add(z3.Implies(take, lex_decrease))
            solver.add(z3.Implies(use[name], z3.Or(choices)))
    status = solver.check()
    report = {"status": str(status), **basic}
    if status != z3.sat:
        return report, None
    model = solver.model()
    reached = {root}
    todo = deque([root])
    selected_rules = []
    while todo:
        source = todo.popleft()
        for digit in (0, 1):
            choice = next(
                (index, rule)
                for index, rule in candidate_table[source, digit]
                if index in takes
                and z3.is_true(model.eval(takes[index], model_completion=True))
            )
            index, rule = choice
            selected_rules.append(index)
            if rule["target"] not in reached:
                reached.add(rule["target"])
                todo.append(rule["target"])
    certificate = {
        "root": root,
        "states": [
            {
                "name": name,
                "rank_phases": [
                    {
                        "exponent_weight": model.eval(er[phase][name]).as_long(),
                        "tail_weight": model.eval(tk[phase][name]).as_long(),
                        "constant": model.eval(const[phase][name]).as_long(),
                    }
                    for phase in range(phases)
                ],
            }
            for name in sorted(reached)
        ],
        "rule_indices": selected_rules,
    }
    report.update(
        {
            "certificate_states": len(reached),
            "certificate_rules": len(selected_rules),
        }
    )
    return report, certificate


def verify_report(data: dict) -> dict:
    if data.get("format") != "collatz-bb-power-rule-atlas-v1":
        raise ValueError("unsupported report format")
    templates = {
        item["name"]: Template(
            item["name"],
            SymbolicPair.from_json(item["pair"]),
            Guard(**item["guard"]),
            item["origin"],
            item["base_safe"],
        )
        for item in data["templates"]
    }
    if len(templates) != len(data["templates"]):
        raise ValueError("duplicate template name")
    checked_safe_bases = 0
    for template in templates.values():
        if template.base_safe:
            if not verify_base_safe(template):
                raise ValueError(
                    f"template {template.name}: unsupported base-safe assertion"
                )
            checked_safe_bases += 1
    chain_rules = 0
    automaton_states = 0
    for index, rule in enumerate(data["rules"]):
        source = templates[rule["source"]]
        guard = Guard(**rule["guard"])
        if guard != source.guard:
            raise ValueError(f"rule {index}: source guard mismatch")
        split = rule["split"]
        if split["radix"] != 2 or split["digit"] not in (0, 1):
            raise ValueError(f"rule {index}: malformed binary split")
        start = split_pair(source.pair, split["radix"], split["digit"])
        if start != SymbolicPair.from_json(rule["start"]):
            raise ValueError(f"rule {index}: split identity fails")
        finish, checks = replay(start, rule["path"], guard)
        if finish != SymbolicPair.from_json(rule["finish"]):
            raise ValueError(f"rule {index}: proof replay fails")
        target = templates[rule["target"]]
        counter_map = rule["counter_map"]
        if counter_map["kind"] != "shift":
            raise ValueError(f"rule {index}: unsupported counter map")
        delta = counter_map["delta"]
        if guard.start + delta < target.guard.start:
            raise ValueError(f"rule {index}: target exponent leaves its guard")
        ta = target.pair.base.shift(delta)
        tb = target.pair.step.shift(delta)
        u, v = rule["tail_map"]["u"], rule["tail_map"]["v"]
        if u <= 0 or v < 0:
            raise ValueError(f"rule {index}: invalid natural tail map")
        expected = SymbolicPair(ta + tb.scale(v), tb.scale(u))
        if finish != expected:
            raise ValueError(f"rule {index}: target substitution identity fails")
        if checks != rule["residue_automata"]:
            raise ValueError(f"rule {index}: residue proof changed on replay")
        automaton_states += sum(check["states_checked"] for check in checks)
        chain_rules += any(step["kind"] == "chain" for step in rule["path"])
    return {
        "verified": True,
        "templates": len(templates),
        "rules": len(data["rules"]),
        "rules_using_unbounded_chain": chain_rules,
        "base_safe_templates_rechecked": checked_safe_bases,
        "residue_automaton_states_replayed": automaton_states,
        "scope": "symbolic transition atlas only; no root termination certificate",
    }


def forward_program_audit(data: dict) -> dict:
    """Audit whether the atlas contains a positive-time forward language.

    Component certificates may use inverse moves and zero-step identities.
    Neither is legal when the same rules are reinterpreted as a program for a
    single forward orbit.  This audit keeps only nonempty paths made from E/O
    or the two forward chain rules, then computes the exact greatest subset
    having at least one target for each binary tail digit.
    """
    verification = verify_report(data)
    template_names = {item["name"] for item in data["templates"]}

    def positive_forward(rule: dict) -> bool:
        if not rule["path"]:
            return False
        return all(
            step["kind"] == "chain"
            or (step["kind"] == "primitive" and step["op"] in ("E", "O"))
            for step in rule["path"]
        )

    forward = [rule for rule in data["rules"] if positive_forward(rule)]
    by_branch: dict[tuple[str, int], list[dict]] = {}
    for rule in forward:
        by_branch.setdefault((rule["source"], rule["split"]["digit"]), []).append(rule)
    initially_complete = {
        name
        for name in template_names
        if all(by_branch.get((name, digit)) for digit in (0, 1))
    }
    live = set(template_names)
    rounds = []
    while True:
        dead = {
            source
            for source in live
            if any(
                not any(
                    rule["target"] in live
                    for rule in by_branch.get((source, digit), [])
                )
                for digit in (0, 1)
            )
        }
        if not dead:
            break
        live.difference_update(dead)
        rounds.append(
            {
                "round": len(rounds) + 1,
                "removed": len(dead),
                "remaining": len(live),
                "root_live": "root" in live,
                "removed_templates": sorted(dead),
            }
        )
    return {
        "format": "collatz-bb-forward-program-audit-v1",
        "claim_scope": (
            "Exact only for the templates and retained rule cap in the source "
            "atlas. Empty closure does not rule out a larger forward language."
        ),
        "source_atlas_verification": verification,
        "templates": len(template_names),
        "atlas_rules": len(data["rules"]),
        "positive_time_forward_rules": len(forward),
        "positive_time_forward_chain_rules": sum(
            any(step["kind"] == "chain" for step in rule["path"])
            for rule in forward
        ),
        "initially_branch_complete_templates": len(initially_complete),
        "greatest_fixed_point_rounds": rounds,
        "greatest_fixed_point_templates": sorted(live),
        "greatest_fixed_point_size": len(live),
        "root_survives": "root" in live,
    }


def cmd_mine(args: argparse.Namespace) -> int:
    cores, frontier = learn_frontier(args.bound, args.concrete_path_depth)
    templates = build_templates(cores)
    rules, stats = discover_rules(
        templates,
        args.symbolic_depth,
        args.state_cap,
        args.max_u,
        args.max_v,
        args.rule_cap,
    )
    affine_rank, affine_certificate = solve_size_change(
        templates,
        rules,
        args.rank_weight_limit,
        args.rank_constant_limit,
        args.timeout_ms,
        phases=1,
    )
    lex_rank, lex_certificate = solve_size_change(
        templates,
        rules,
        args.rank_weight_limit,
        args.rank_constant_limit,
        args.timeout_ms,
        phases=2,
    )
    size_change = {
        "affine": affine_rank,
        "lexicographic_two_phase": lex_rank,
    }
    certificate = affine_certificate or lex_certificate
    report = {
        "format": "collatz-bb-power-rule-atlas-v1",
        "claim_scope": (
            "Every displayed macro rule is exact for all exponents and tails in "
            "its guard. This is a transition atlas, not a closed Collatz proof: "
            "unsafe chart bases and global size-change closure remain open."
        ),
        "grammar": {
            "expression": "finite rational sum of base^r",
            "primitive_steps": list(PRIMITIVES),
            "chain_rules": ["EVEN_CHAIN", "ODD_CHAIN"],
            "symbolic_depth": args.symbolic_depth,
            "symbolic_state_cap_per_branch": args.state_cap,
            "max_tail_u": args.max_u,
            "max_tail_v": args.max_v,
            "rule_cap_per_branch": args.rule_cap,
        },
        "frontier_learning": frontier,
        "templates": [template.to_json() for template in templates],
        "rules": rules,
        "search_statistics": stats,
        "size_change_search": size_change,
        "candidate_termination_certificate": certificate,
    }
    verification = verify_report(report)
    report["independent_verification"] = verification
    output = Path(args.output)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"output": str(output), **stats, **verification}, indent=2))
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    data = json.loads(Path(args.report).read_text())
    print(json.dumps(verify_report(data), indent=2, sort_keys=True))
    return 0


def cmd_forward_audit(args: argparse.Namespace) -> int:
    data = json.loads(Path(args.report).read_text())
    audit = forward_program_audit(data)
    if args.output:
        Path(args.output).write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, indent=2, sort_keys=True))
    return 0


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(required=True)
    mine = sub.add_parser("mine", help="learn templates, mine, and verify rules")
    mine.add_argument("--bound", type=int, default=96)
    mine.add_argument("--concrete-path-depth", type=int, default=14)
    mine.add_argument("--symbolic-depth", type=int, default=5)
    mine.add_argument("--state-cap", type=int, default=600)
    mine.add_argument("--max-u", type=int, default=6)
    mine.add_argument("--max-v", type=int, default=6)
    mine.add_argument("--rule-cap", type=int, default=24)
    mine.add_argument("--rank-weight-limit", type=int, default=64)
    mine.add_argument("--rank-constant-limit", type=int, default=128)
    mine.add_argument("--timeout-ms", type=int, default=120000)
    mine.add_argument(
        "--output", default=str(HERE / "bb_power_rule_audit.json")
    )
    mine.set_defaults(func=cmd_mine)
    verify = sub.add_parser("verify", help="independently replay a JSON atlas")
    verify.add_argument("report")
    verify.set_defaults(func=cmd_verify)
    forward = sub.add_parser(
        "forward-audit",
        help="remove inverse/zero-time rules and audit forward closure",
    )
    forward.add_argument("report")
    forward.add_argument("--output")
    forward.set_defaults(func=cmd_forward_audit)
    return p


if __name__ == "__main__":
    arguments = parser().parse_args()
    raise SystemExit(arguments.func(arguments))
