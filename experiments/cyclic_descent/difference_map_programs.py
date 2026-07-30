#!/usr/bin/env python3
"""Difference-map search for self-reproducing forward Collatz programs.

This is an untrusted candidate generator with an exact post-checker.  A
program is a cycle of positive-time forward macro-rules between symbolic power
charts.  Four projections act on separate copies of a continuous edge-choice
vector:

* semantic: one exact forward rule per program position;
* closure: a composable directed cycle;
* reproduction: a cycle with expanding tail or active exponent resource;
* ordinary: cycles with low-amplitude exact nested residue cylinders, or
  (jackpot) an ordinary periodic point / exact invariant arithmetic ray.

Projection onto the consensus diagonal and Elser's difference-map update try
to make the four copies agree.  A small numerical residual is never a result.
Only ``exact_invariant_ray`` in the independently replayed output would be a
counterexample certificate, and none is expected.

The finite-depth ordinary projection is deliberately diagnostic.  Exact
blockwise modular lifting constructs its least witness and reports its binary
length, giving a graded boundary amplitude instead of confusing a long 2-adic
prefix with an ordinary infinite orbit.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
import json
import math
from pathlib import Path
import random
import sys
from typing import Iterable

import numpy as np


HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import bb_power_rules as bb  # noqa: E402


@dataclass(frozen=True)
class Edge:
    index: int
    rule: dict
    source: str
    target: str
    digit: int
    delta: int
    u: int
    v: int

    def tail_apply(self, k: int) -> int | None:
        if k % 2 != self.digit:
            return None
        return self.u * ((k - self.digit) // 2) + self.v


@dataclass(frozen=True)
class CycleAnalysis:
    productive: bool
    exponent_delta: int
    tail_alpha_num: int
    tail_alpha_den: int
    tail_beta_num: int
    tail_beta_den: int
    active_exponent: bool
    ordinary_depth: int
    ordinary_seed: int | None
    ordinary_r0: int | None
    ordinary_seed_bits: int | None
    boundary_one_density: float | None
    periodic_point: dict | None
    invariant_ray: dict | None
    invariant_ray_obstruction: str | None


def positive_forward(rule: dict) -> bool:
    return bool(rule["path"]) and all(
        step["kind"] == "chain"
        or (step["kind"] == "primitive" and step["op"] in ("E", "O"))
        for step in rule["path"]
    )


def exponent_active(template: bb.Template) -> bool:
    return any(
        base > 1 and coefficient
        for expr in (template.pair.base, template.pair.step)
        for base, coefficient in expr.terms
    )


def build_library(args: argparse.Namespace) -> tuple[list[bb.Template], list[Edge], dict]:
    cores, frontier = bb.learn_frontier(args.bound, args.concrete_path_depth)
    templates = bb.build_templates(cores)
    rules, stats = bb.discover_rules(
        templates,
        args.symbolic_depth,
        args.symbolic_state_cap,
        args.max_u,
        args.max_v,
        args.rule_cap,
    )
    template_by_name = {template.name: template for template in templates}
    filtered = [rule for rule in rules if positive_forward(rule)]

    # A counter shift into an r-independent chart has no semantic content and
    # otherwise creates fake reproductive gain.  Keep its canonical delta 0.
    filtered = [
        rule
        for rule in filtered
        if exponent_active(template_by_name[rule["target"]])
        or rule["counter_map"]["delta"] == 0
    ]
    unique: dict[tuple, dict] = {}
    for rule in filtered:
        key = (
            rule["source"],
            rule["target"],
            rule["split"]["digit"],
            rule["counter_map"]["delta"],
            rule["tail_map"]["u"],
            rule["tail_map"]["v"],
            tuple((step["kind"], step["op"]) for step in rule["path"]),
        )
        unique.setdefault(key, rule)
    edges = []
    for index, rule in enumerate(unique.values()):
        edges.append(
            Edge(
                index=index,
                rule=rule,
                source=rule["source"],
                target=rule["target"],
                digit=rule["split"]["digit"],
                delta=rule["counter_map"]["delta"],
                u=rule["tail_map"]["u"],
                v=rule["tail_map"]["v"],
            )
        )
    live = set(template_by_name)
    closure_rounds = []
    while True:
        dead = {
            source
            for source in live
            if any(
                not any(
                    edge.source == source
                    and edge.digit == digit
                    and edge.target in live
                    for edge in edges
                )
                for digit in (0, 1)
            )
        }
        if not dead:
            break
        live.difference_update(dead)
        closure_rounds.append(
            {
                "removed": len(dead),
                "remaining": len(live),
                "root_live": "root" in live,
            }
        )
    library = {
        "frontier_learning": frontier,
        "symbolic_search": stats,
        "templates": len(templates),
        "rules_before_forward_filter": len(rules),
        "positive_forward_canonical_edges": len(edges),
        "forward_closure_rounds": closure_rounds,
        "forward_closed_templates": len(live),
        "forward_closed_root_survives": "root" in live,
    }
    return templates, edges, library


def sample_cycle_pool(
    edges: list[Edge],
    length: int,
    target_size: int,
    seed: int,
    attempts_factor: int,
) -> list[tuple[int, ...]]:
    rng = random.Random(seed)
    outgoing: dict[str, list[int]] = defaultdict(list)
    closing: dict[tuple[str, str], list[int]] = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge.index)
        closing[edge.source, edge.target].append(edge.index)
    nodes = sorted(outgoing)
    cycles: set[tuple[int, ...]] = set()

    # Include repeated self-rules, the most important tail-consumption probes.
    for edge in edges:
        if edge.source == edge.target:
            cycles.add(tuple([edge.index] * length))

    attempts = max(target_size * attempts_factor, 1000)
    for _ in range(attempts):
        start = rng.choice(nodes)
        current = start
        path = []
        ok = True
        for _position in range(length - 1):
            options = outgoing.get(current, [])
            if not options:
                ok = False
                break
            edge_index = rng.choice(options)
            path.append(edge_index)
            current = edges[edge_index].target
        if not ok:
            continue
        options = closing.get((current, start), [])
        if not options:
            continue
        path.append(rng.choice(options))
        cycles.add(tuple(path))
        if len(cycles) >= target_size:
            break
    return sorted(cycles)


def exhaustive_cycle_pool(edges: list[Edge], length: int) -> list[tuple[int, ...]]:
    """Enumerate every based directed edge-cycle of the requested length."""
    outgoing: dict[str, list[int]] = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge.index)
    cycles: list[tuple[int, ...]] = []

    def extend(start: str, current: str, path: list[int]) -> None:
        if len(path) == length:
            if current == start:
                cycles.append(tuple(path))
            return
        for edge_index in outgoing.get(current, []):
            edge = edges[edge_index]
            path.append(edge_index)
            extend(start, edge.target, path)
            path.pop()

    for start in sorted(outgoing):
        extend(start, start, [])
    return cycles


def compose_tail(cycle: Iterable[Edge]) -> tuple[Fraction, Fraction]:
    alpha = Fraction(1)
    beta = Fraction(0)
    for edge in cycle:
        alpha = Fraction(edge.u, 2) * alpha
        beta = Fraction(edge.u, 2) * (beta - edge.digit) + edge.v
    return alpha, beta


def minimal_r0(cycle: list[Edge], templates: dict[str, bb.Template]) -> int | None:
    partial = 0
    r0 = 0
    for edge in cycle:
        r0 = max(r0, templates[edge.source].guard.start - partial)
        partial += edge.delta
    if partial < 0:
        return None
    return r0


def decoded_value(template: bb.Template, r: int, k: int) -> int | None:
    if r < template.guard.start or k < 0:
        return None
    value = template.pair.base.evaluate(r) + template.pair.step.evaluate(r) * k
    if value.denominator != 1:
        return None
    return value.numerator


def replay_cycle_tail(cycle: list[Edge], k: int) -> int | None:
    for edge in cycle:
        k = edge.tail_apply(k)
        if k is None:
            return None
    return k


def ordinary_cylinder(
    cycle: list[Edge],
    templates: dict[str, bb.Template],
    depth: int,
) -> dict | None:
    """Lift the unique finite repeated-word cylinder to depth ``depth``.

    When all tail multipliers are odd, a length-L program word selects one
    residue modulo 2^L.  Hensel-style block lifting then gives the unique
    residue modulo 2^(L*d) that executes the word d times.  This avoids a
    misleading bounded search for what can be a very large ordinary witness.
    """
    if depth <= 0 or any(edge.u % 2 == 0 for edge in cycle):
        return None
    r0 = minimal_r0(cycle, templates)
    if r0 is None:
        return None
    block_modulus = 1 << len(cycle)
    legal_residues = [
        residue
        for residue in range(block_modulus)
        if replay_cycle_tail(cycle, residue) is not None
    ]
    if len(legal_residues) != 1:
        return None
    residue = legal_residues[0]
    alpha, beta = compose_tail(cycle)
    numerator_a = alpha * block_modulus
    numerator_b = beta * block_modulus
    if numerator_a.denominator != 1 or numerator_b.denominator != 1:
        return None
    a = numerator_a.numerator
    b = numerator_b.numerator
    modulus = block_modulus
    lift_blocks = [residue]
    for _round in range(1, depth):
        scale = modulus // block_modulus
        discrepancy = a * residue + b - block_modulus * residue
        divisor = block_modulus * scale
        if discrepancy % divisor:
            return None
        digit = (-discrepancy // divisor * pow(a, -1, block_modulus)) % block_modulus
        residue += digit * modulus
        modulus *= block_modulus
        lift_blocks.append(digit)

    # Pick the least member of the cylinder whose decoded start exceeds 2.
    seed = residue
    start_template = templates[cycle[0].source]
    start_value = decoded_value(start_template, r0, seed)
    while start_value is None or start_value <= 2:
        seed += modulus
        start_value = decoded_value(start_template, r0, seed)

    # Independent exact replay of the claimed number of program rounds.
    k = seed
    r = r0
    for _round in range(depth):
        for edge in cycle:
            if r < templates[edge.source].guard.start:
                return None
            k = edge.tail_apply(k)
            if k is None:
                return None
            r += edge.delta
            value = decoded_value(templates[edge.target], r, k)
            if value is None or value <= 2:
                return None
    bits = max(1, seed.bit_length())
    return {
        "depth": depth,
        "seed": seed,
        "seed_bits": bits,
        "one_bits": seed.bit_count(),
        "one_density": seed.bit_count() / bits,
        "residue": residue,
        "modulus": modulus,
        "block_modulus": block_modulus,
        "lift_blocks": lift_blocks,
        "exponent_start": r0,
    }


def exact_periodic_point(
    cycle: list[Edge], templates: dict[str, bb.Template]
) -> dict | None:
    """Check the rational fixed point of the composite tail map exactly."""
    r0 = minimal_r0(cycle, templates)
    if r0 is None or sum(edge.delta for edge in cycle) != 0:
        return None
    alpha, beta = compose_tail(cycle)
    if alpha == 1:
        return None
    fixed = beta / (1 - alpha)
    if fixed.denominator != 1 or fixed < 0:
        return None
    k = fixed.numerator
    if replay_cycle_tail(cycle, k) != k:
        return None
    value = decoded_value(templates[cycle[0].source], r0, k)
    if value is None:
        return None
    return {"k": k, "exponent": r0, "decoded_value": value}


def exact_invariant_ray(
    cycle: list[Edge],
    templates: dict[str, bb.Template],
    modulus_limit: int,
) -> dict | None:
    """Find an invariant ordinary ray ``k=a+M*t, t>=1`` exactly."""
    r0 = minimal_r0(cycle, templates)
    if r0 is None:
        return None
    exponent_delta = sum(edge.delta for edge in cycle)
    start_template = templates[cycle[0].source]
    active = exponent_active(start_template)
    for modulus in range(1, modulus_limit + 1):
        for residue in range(modulus):
            alpha = modulus
            beta = residue
            partial_r = r0
            legal = True
            for edge in cycle:
                if alpha % 2 or beta % 2 != edge.digit:
                    legal = False
                    break
                alpha = edge.u * (alpha // 2)
                beta = edge.u * ((beta - edge.digit) // 2) + edge.v
                partial_r += edge.delta
                if partial_r < templates[edge.target].guard.start:
                    legal = False
                    break
                # t=1 is the smallest member used in the ray.
                value = decoded_value(templates[edge.target], partial_r, alpha + beta)
                if value is None or value <= 2:
                    legal = False
                    break
            if not legal:
                continue
            if alpha % modulus or (beta - residue) % modulus:
                continue
            tail_u = alpha // modulus
            tail_v = (beta - residue) // modulus
            if tail_u < 1 or tail_v < 0:
                continue
            productive = tail_u > 1 or tail_v > 0 or (exponent_delta > 0 and active)
            if not productive:
                continue
            start_k = residue + modulus
            start_value = decoded_value(start_template, r0, start_k)
            if start_value is None or start_value <= 2:
                continue
            return {
                "modulus": modulus,
                "residue": residue,
                "tail_parameter_starts_at": 1,
                "tail_parameter_map": {"u": tail_u, "v": tail_v},
                "exponent_start": r0,
                "exponent_delta": exponent_delta,
                "start_k": start_k,
                "start_value": start_value,
            }
    return None


def analyze_cycle(
    cycle_indices: tuple[int, ...],
    edges: list[Edge],
    templates: dict[str, bb.Template],
    args: argparse.Namespace,
) -> CycleAnalysis:
    cycle = [edges[index] for index in cycle_indices]
    alpha, beta = compose_tail(cycle)
    exponent_delta = sum(edge.delta for edge in cycle)
    active = exponent_active(templates[cycle[0].source])
    productive = alpha > 1 or (alpha == 1 and beta > 0) or (
        exponent_delta > 0 and active and alpha > 0
    )
    cylinder = ordinary_cylinder(cycle, templates, args.cylinder_depth)
    periodic = exact_periodic_point(cycle, templates)
    invariant = None
    obstruction = None
    if productive:
        if all(edge.u % 2 == 1 for edge in cycle):
            obstruction = (
                "The repeated word has slope A/2^L with A odd and L>0; "
                "it cannot map any full arithmetic ray to itself."
            )
        else:
            invariant = exact_invariant_ray(cycle, templates, args.modulus_limit)
    return CycleAnalysis(
        productive=productive,
        exponent_delta=exponent_delta,
        tail_alpha_num=alpha.numerator,
        tail_alpha_den=alpha.denominator,
        tail_beta_num=beta.numerator,
        tail_beta_den=beta.denominator,
        active_exponent=active,
        ordinary_depth=0 if cylinder is None else cylinder["depth"],
        ordinary_seed=None if cylinder is None else cylinder["seed"],
        ordinary_r0=None if cylinder is None else cylinder["exponent_start"],
        ordinary_seed_bits=None if cylinder is None else cylinder["seed_bits"],
        boundary_one_density=None if cylinder is None else cylinder["one_density"],
        periodic_point=periodic,
        invariant_ray=invariant,
        invariant_ray_obstruction=obstruction,
    )


class DifferenceMap:
    def __init__(
        self,
        edge_count: int,
        pool: np.ndarray,
        productive: np.ndarray,
        ordinary: np.ndarray,
        invariant: np.ndarray,
        beta: float,
    ):
        self.edge_count = edge_count
        self.pool = pool
        self.length = pool.shape[1]
        self.productive = productive
        self.ordinary = ordinary
        self.invariant = invariant
        self.beta = beta

    def one_hot(self, edge_indices: np.ndarray) -> np.ndarray:
        out = np.zeros((self.length, self.edge_count), dtype=np.float64)
        out[np.arange(self.length), edge_indices] = 1.0
        return out

    def project_semantic(self, x: np.ndarray) -> tuple[np.ndarray, int]:
        indices = np.argmax(x, axis=1)
        return self.one_hot(indices), -1

    def project_cycles(self, x: np.ndarray, subset: np.ndarray) -> tuple[np.ndarray, int]:
        if not len(subset):
            raise ValueError("projection set is empty")
        candidates = self.pool[subset]
        scores = x[np.arange(self.length)[None, :], candidates].sum(axis=1)
        local = int(np.argmax(scores))
        pool_index = int(subset[local])
        return self.one_hot(self.pool[pool_index]), pool_index

    def project_A(self, x: np.ndarray) -> tuple[np.ndarray, tuple[int, int, int, int]]:
        out = np.empty_like(x)
        out[0], semantic = self.project_semantic(x[0])
        all_indices = np.arange(len(self.pool), dtype=np.int64)
        out[1], closure = self.project_cycles(x[1], all_indices)
        out[2], reproduction = self.project_cycles(x[2], self.productive)
        target = self.invariant if len(self.invariant) else self.ordinary
        out[3], ordinary = self.project_cycles(x[3], target)
        return out, (semantic, closure, reproduction, ordinary)

    @staticmethod
    def project_B(x: np.ndarray) -> np.ndarray:
        consensus = x.mean(axis=0)
        return np.repeat(consensus[None, :, :], 4, axis=0)

    def run(self, seed: int, iterations: int) -> dict:
        rng = np.random.default_rng(seed)
        x = rng.normal(0.0, 0.05, size=(4, self.length, self.edge_count))
        best = None
        for iteration in range(iterations):
            pa, _ = self.project_A(x)
            pb = self.project_B(x)
            f_a = pa - (pa - x) / self.beta
            f_b = pb + (pb - x) / self.beta
            y_a, choices = self.project_A(f_b)
            y_b = self.project_B(f_a)
            displacement = y_a - y_b
            residual = float(np.linalg.norm(displacement) / math.sqrt(displacement.size))
            x = x + self.beta * displacement
            consensus_cycle = choices[1] if choices[1:] == (choices[1],) * 3 else None
            record = {
                "iteration": iteration + 1,
                "residual": residual,
                "projection_choices": list(choices),
                "consensus_cycle": consensus_cycle,
            }
            if best is None or residual < best["residual"]:
                best = record
            if consensus_cycle is not None and residual < 1e-12:
                break
        assert best is not None
        return {"seed": seed, "best": best, "iterations_run": iteration + 1}


def verify_cycle(
    cycle_indices: tuple[int, ...],
    edges: list[Edge],
    templates: dict[str, bb.Template],
    analysis: CycleAnalysis,
    args: argparse.Namespace,
) -> dict:
    cycle = [edges[index] for index in cycle_indices]
    for position, edge in enumerate(cycle):
        following = cycle[(position + 1) % len(cycle)]
        if edge.target != following.source:
            raise ValueError("cycle is not composable")
        if not positive_forward(edge.rule):
            raise ValueError("cycle contains a non-forward or zero-time rule")
        source = templates[edge.source]
        target = templates[edge.target]
        start = bb.split_pair(source.pair, 2, edge.digit)
        finish, _checks = bb.replay(start, edge.rule["path"], source.guard)
        shifted_base = target.pair.base.shift(edge.delta)
        shifted_step = target.pair.step.shift(edge.delta)
        expected = bb.SymbolicPair(
            shifted_base + shifted_step.scale(edge.v), shifted_step.scale(edge.u)
        )
        if finish != expected:
            raise ValueError("exact rule replay failed")
    replayed = analyze_cycle(cycle_indices, edges, templates, args)
    if replayed != analysis:
        raise ValueError("cycle analysis changed on independent replay")
    return {
        "verified": True,
        "positive_time_forward_rules": len(cycle),
        "productive": analysis.productive,
        "ordinary_depth": analysis.ordinary_depth,
        "ordinary_seed_bits": analysis.ordinary_seed_bits,
        "exact_periodic_point": analysis.periodic_point,
        "exact_invariant_ray": analysis.invariant_ray,
        "invariant_ray_obstruction": analysis.invariant_ray_obstruction,
    }


def cycle_to_json(
    cycle_index: int,
    pool: list[tuple[int, ...]],
    analyses: list[CycleAnalysis],
    edges: list[Edge],
    verification: dict,
) -> dict:
    cycle = pool[cycle_index]
    analysis = analyses[cycle_index]
    return {
        "cycle_index": cycle_index,
        "edge_indices": list(cycle),
        "rules": [
            {
                "source": edges[index].source,
                "digit": edges[index].digit,
                "target": edges[index].target,
                "counter_delta": edges[index].delta,
                "tail_map": {"u": edges[index].u, "v": edges[index].v},
                "path": edges[index].rule["path"],
            }
            for index in cycle
        ],
        "analysis": {
            "productive": analysis.productive,
            "exponent_delta": analysis.exponent_delta,
            "tail_map": {
                "alpha": [analysis.tail_alpha_num, analysis.tail_alpha_den],
                "beta": [analysis.tail_beta_num, analysis.tail_beta_den],
            },
            "active_exponent": analysis.active_exponent,
            "ordinary_depth": analysis.ordinary_depth,
            "ordinary_seed": analysis.ordinary_seed,
            "ordinary_seed_bits": analysis.ordinary_seed_bits,
            "boundary_one_density": analysis.boundary_one_density,
            "ordinary_r0": analysis.ordinary_r0,
            "periodic_point": analysis.periodic_point,
            "invariant_ray": analysis.invariant_ray,
            "invariant_ray_obstruction": analysis.invariant_ray_obstruction,
        },
        "verification": verification,
    }


def cmd_search(args: argparse.Namespace) -> int:
    templates_list, edges, library = build_library(args)
    templates = {template.name: template for template in templates_list}
    if args.pool_mode == "exhaustive":
        pool = exhaustive_cycle_pool(edges, args.cycle_length)
    else:
        pool = sample_cycle_pool(
            edges,
            args.cycle_length,
            args.pool_size,
            args.seed,
            args.attempts_factor,
        )
    if not pool:
        raise RuntimeError("cycle pool is empty")
    analyses = [analyze_cycle(cycle, edges, templates, args) for cycle in pool]
    productive = np.array(
        [index for index, analysis in enumerate(analyses) if analysis.productive],
        dtype=np.int64,
    )
    invariant = np.array(
        [
            index
            for index, analysis in enumerate(analyses)
            if analysis.invariant_ray
            or (
                analysis.periodic_point
                and analysis.periodic_point["decoded_value"] > 2
            )
        ],
        dtype=np.int64,
    )
    ordinary_ranked = sorted(
        (
            index
            for index, analysis in enumerate(analyses)
            if analysis.ordinary_seed_bits is not None
        ),
        key=lambda index: (
            analyses[index].ordinary_seed_bits,
            analyses[index].boundary_one_density,
        ),
    )
    ordinary = np.asarray(
        ordinary_ranked[: args.ordinary_pool_size], dtype=np.int64
    )
    if not len(productive):
        raise RuntimeError("no productive cycle in sampled pool")
    if not len(ordinary) and not len(invariant):
        raise RuntimeError("no exact finite ordinary cylinder in sampled pool")

    engine = DifferenceMap(
        len(edges),
        np.asarray(pool, dtype=np.int64),
        productive,
        ordinary,
        invariant,
        args.beta,
    )
    runs = [
        engine.run(args.seed + 1009 * restart, args.iterations)
        for restart in range(args.restarts)
    ]
    runs.sort(key=lambda run: run["best"]["residual"])

    ranked_cycles = sorted(
        range(len(pool)),
        key=lambda index: (
            analyses[index].invariant_ray is not None,
            analyses[index].productive,
            -(analyses[index].ordinary_seed_bits or 10**9),
            -(analyses[index].boundary_one_density or 1.0),
            analyses[index].periodic_point is not None,
        ),
        reverse=True,
    )
    selected_cycles: list[int] = []
    for run in runs:
        best = run["best"]
        suggestions = [best["consensus_cycle"], *best["projection_choices"][1:]]
        for index in suggestions:
            if index is not None and index not in selected_cycles:
                selected_cycles.append(index)
    for index in ranked_cycles:
        if index not in selected_cycles:
            selected_cycles.append(index)
        if len(selected_cycles) >= args.report_cycles:
            break
    selected_cycles = selected_cycles[: args.report_cycles]
    cycle_reports = []
    for index in selected_cycles:
        verification = verify_cycle(pool[index], edges, templates, analyses[index], args)
        cycle_reports.append(
            cycle_to_json(index, pool, analyses, edges, verification)
        )

    depth_histogram = Counter(analysis.ordinary_depth for analysis in analyses)
    bit_histogram = Counter(
        analysis.ordinary_seed_bits
        for analysis in analyses
        if analysis.ordinary_seed_bits is not None
    )
    jackpot_verifications = [
        verify_cycle(pool[index], edges, templates, analyses[index], args)
        for index in invariant
    ]
    report = {
        "format": "collatz-difference-map-program-search-v1",
        "claim_scope": (
            "Untrusted nonconvex search in the displayed finite symbolic grammar. "
            "Finite ordinary cylinders and their bit lengths are diagnostic only. "
            "A result would require an independently replayed nontrivial exact "
            "periodic point or invariant ray; none is claimed unless one of those "
            "fields is non-null and decodes above 2."
        ),
        "parameters": {
            key: value for key, value in vars(args).items() if key != "func"
        },
        "library": library,
        "cycle_pool": {
            "cycles": len(pool),
            "productive_cycles": len(productive),
            "ordinary_projection_cycles": len(ordinary),
            "exact_invariant_cycles": len(invariant),
            "ordinary_depth_histogram": {
                str(depth): count for depth, count in sorted(depth_histogram.items())
            },
            "ordinary_seed_bit_histogram": {
                str(bits): count for bits, count in sorted(bit_histogram.items())
            },
        },
        "difference_map_runs": runs,
        "best_exactly_replayed_cycles": cycle_reports,
        "jackpot_verifications": jackpot_verifications,
        "counterexample_found": bool(len(invariant))
        and all(item["verified"] for item in jackpot_verifications),
    }
    output = Path(args.output)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    summary = {
        "output": str(output),
        "edges": len(edges),
        **report["cycle_pool"],
        "best_residual": runs[0]["best"]["residual"],
        "counterexample_found": report["counterexample_found"],
        "best_ordinary_depth": max(depth_histogram),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    report = json.loads(Path(args.report).read_text())
    if report.get("format") != "collatz-difference-map-program-search-v1":
        raise ValueError("unexpected report format")
    parameters = argparse.Namespace(**report["parameters"])
    templates_list, edges, library = build_library(parameters)
    templates = {template.name: template for template in templates_list}
    if parameters.pool_mode == "exhaustive":
        pool = exhaustive_cycle_pool(edges, parameters.cycle_length)
    else:
        pool = sample_cycle_pool(
            edges,
            parameters.cycle_length,
            parameters.pool_size,
            parameters.seed,
            parameters.attempts_factor,
        )
    analyses = [analyze_cycle(cycle, edges, templates, parameters) for cycle in pool]
    summary = report["cycle_pool"]
    checks = {
        "cycles": len(pool),
        "productive_cycles": sum(analysis.productive for analysis in analyses),
        "exact_invariant_cycles": sum(
            bool(analysis.invariant_ray)
            or bool(
                analysis.periodic_point
                and analysis.periodic_point["decoded_value"] > 2
            )
            for analysis in analyses
        ),
        "ordinary_depth_histogram": {
            str(key): value
            for key, value in sorted(
                Counter(analysis.ordinary_depth for analysis in analyses).items()
            )
        },
        "ordinary_seed_bit_histogram": {
            str(key): value
            for key, value in sorted(
                Counter(
                    analysis.ordinary_seed_bits
                    for analysis in analyses
                    if analysis.ordinary_seed_bits is not None
                ).items()
            )
        },
    }
    for key, value in checks.items():
        if summary[key] != value:
            raise ValueError(f"summary mismatch for {key}")
    if library != report["library"]:
        raise ValueError("expanded library summary mismatch")
    for item in report["best_exactly_replayed_cycles"]:
        index = item["cycle_index"]
        if list(pool[index]) != item["edge_indices"]:
            raise ValueError("reported cycle index mismatch")
        verify_cycle(pool[index], edges, templates, analyses[index], parameters)
    result = {
        "verified": True,
        "report": str(args.report),
        "exact_cycles_reenumerated": len(pool),
        "reported_cycles_replayed": len(report["best_exactly_replayed_cycles"]),
        "counterexample_found": bool(checks["exact_invariant_cycles"]),
        "scope": "exact discrete atlas and certificates; numerical residuals not certified",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(required=True)
    search = sub.add_parser("search")
    search.add_argument("--bound", type=int, default=96)
    search.add_argument("--concrete-path-depth", type=int, default=14)
    search.add_argument("--symbolic-depth", type=int, default=6)
    search.add_argument("--symbolic-state-cap", type=int, default=1200)
    search.add_argument("--max-u", type=int, default=12)
    search.add_argument("--max-v", type=int, default=12)
    search.add_argument("--rule-cap", type=int, default=64)
    search.add_argument("--cycle-length", type=int, default=6)
    search.add_argument(
        "--pool-mode", choices=("sample", "exhaustive"), default="sample"
    )
    search.add_argument("--pool-size", type=int, default=20000)
    search.add_argument("--attempts-factor", type=int, default=40)
    search.add_argument("--cylinder-depth", type=int, default=32)
    search.add_argument("--ordinary-pool-size", type=int, default=1000)
    search.add_argument("--modulus-limit", type=int, default=64)
    search.add_argument("--beta", type=float, default=1.0)
    search.add_argument("--iterations", type=int, default=300)
    search.add_argument("--restarts", type=int, default=16)
    search.add_argument("--seed", type=int, default=197)
    search.add_argument("--report-cycles", type=int, default=12)
    search.add_argument(
        "--output", default=str(HERE / "difference_map_program_audit.json")
    )
    search.set_defaults(func=cmd_search)
    verify = sub.add_parser("verify")
    verify.add_argument("report")
    verify.set_defaults(func=cmd_verify)
    return p


if __name__ == "__main__":
    arguments = parser().parse_args()
    raise SystemExit(arguments.func(arguments))
