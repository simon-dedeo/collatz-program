#!/usr/bin/env python3
"""Mine and verify finite cyclic-tail certificates for Syracuse termination.

This is theorem synthesis, not trajectory evidence.  A state `(a,b)` denotes
the infinite family `a+b*k`.  At a state the certificate chooses a radix
`q=2^p`, writes `k=q*t+d`, transports `a+b*(q*t+d)` through exact uniform
Syracuse forward/inverse operations to a target family `c+e*t`, and recurses
on the strictly smaller tail `t`.  Base parameters are replayed to `1`.

If a finite certificate rooted at `(1,1)` is found, the independent `verify`
command checks it using integer arithmetic; `ComponentCyclicTail.lean` proves
that any such certificate implies the Syracuse conjecture.

A bounded UNSAT report means only that no certificate exists in the stated
finite state/path grammar.  It is not evidence against Collatz.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from functools import lru_cache
import json
from pathlib import Path
import sys
from typing import Iterable

try:
    import z3
except ImportError:  # verification deliberately does not require z3
    z3 = None


Pair = tuple[int, int]
OPS = ("E", "O", "I0", "I1")


def syracuse(n: int) -> int:
    if n < 0:
        raise ValueError("Syracuse state must be nonnegative")
    return (3 * n + 1) // 2 if n & 1 else n // 2


def orbit_to_one(n: int, limit: int = 100_000) -> list[int] | None:
    """Return the exact orbit prefix ending in 1, or None at the limit."""
    if n <= 0:
        return None
    orbit = [n]
    for _ in range(limit):
        if orbit[-1] == 1:
            return orbit
        orbit.append(syracuse(orbit[-1]))
    return None


def apply_op(pair: Pair, op: str) -> Pair:
    """Apply one exact uniform family operation.

    E/O are forward Syracuse branches.  I0 is the even inverse `n -> 2n`.
    I1 is the odd inverse `n -> (2n-1)/3`.  Preconditions ensure the
    operation is valid simultaneously for every nonnegative tail parameter.
    """
    a, b = pair
    if a <= 0 or b <= 0:
        raise ValueError(f"nonpositive affine family {pair}")
    if op == "E":
        if b % 2 or a % 2:
            raise ValueError(f"E invalid on {pair}")
        return a // 2, b // 2
    if op == "O":
        if b % 2 or a % 2 != 1:
            raise ValueError(f"O invalid on {pair}")
        return (3 * a + 1) // 2, 3 * b // 2
    if op == "I0":
        return 2 * a, 2 * b
    if op == "I1":
        if a % 3 != 2 or b % 3:
            raise ValueError(f"I1 invalid on {pair}")
        return (2 * a - 1) // 3, 2 * b // 3
    raise ValueError(f"unknown operation {op!r}")


def neighbors(pair: Pair) -> Iterable[tuple[Pair, str]]:
    a, b = pair
    if b % 2 == 0:
        if a % 2 == 0:
            yield apply_op(pair, "E"), "E"
        else:
            yield apply_op(pair, "O"), "O"
    yield apply_op(pair, "I0"), "I0"
    if a % 3 == 2 and b % 3 == 0:
        yield apply_op(pair, "I1"), "I1"


def apply_path(pair: Pair, path: Iterable[str]) -> Pair:
    for op in path:
        pair = apply_op(pair, op)
    return pair


@dataclass(frozen=True)
class SearchBounds:
    base_limit: int
    step_limit: int
    walk_base_limit: int
    walk_step_limit: int
    path_depth: int
    max_split_power: int


class Miner:
    def __init__(self, bounds: SearchBounds):
        self.bounds = bounds
        self.base_orbits: dict[int, list[int]] = {}
        for a in range(1, bounds.base_limit + 1):
            orbit = orbit_to_one(a)
            if orbit is not None:
                self.base_orbits[a] = orbit
        self.states: list[Pair] = [
            (a, b)
            for a in sorted(self.base_orbits)
            for b in range(1, bounds.step_limit + 1)
        ]
        self.state_id = {pair: i for i, pair in enumerate(self.states)}

    @lru_cache(maxsize=None)
    def walk_pairs_from(self, start: Pair) -> tuple[tuple[Pair, tuple[str, ...]], ...]:
        """All pairs found by a bounded exact component walk."""
        queue: deque[tuple[Pair, tuple[str, ...]]] = deque([(start, ())])
        seen = {start}
        found: dict[Pair, tuple[str, ...]] = {}
        while queue:
            pair, path = queue.popleft()
            found[pair] = path
            if len(path) >= self.bounds.path_depth:
                continue
            for nxt, op in neighbors(pair):
                if (
                    nxt[0] <= self.bounds.walk_base_limit
                    and nxt[1] <= self.bounds.walk_step_limit
                    and nxt not in seen
                ):
                    seen.add(nxt)
                    queue.append((nxt, path + (op,)))
        return tuple(sorted(found.items()))

    @lru_cache(maxsize=None)
    def paths_from(self, start: Pair) -> tuple[tuple[int, tuple[str, ...]], ...]:
        """All exact in-universe targets in the bounded component walk."""
        hits = []
        for pair, path in self.walk_pairs_from(start):
            target = self.state_id.get(pair)
            if target is not None:
                hits.append((target, path))
        return tuple(hits)

    def branch_start(self, state: int, power: int, digit: int) -> Pair:
        a, b = self.states[state]
        q = 1 << power
        if not (0 <= digit < q):
            raise ValueError("digit outside split radix")
        return a + b * digit, b * q

    def branch_paths(
        self, state: int, power: int, digit: int
    ) -> tuple[tuple[int, tuple[str, ...]], ...]:
        return self.paths_from(self.branch_start(state, power, digit))

    def mode_works(self, state: int, power: int, live: set[int]) -> bool:
        q = 1 << power
        return all(
            any(target in live for target, _ in self.branch_paths(state, power, d))
            for d in range(q)
        )

    def greatest_fixed_point(self) -> tuple[set[int], list[dict]]:
        """Exact greatest closed subset of the bounded candidate graph."""
        live = set(range(len(self.states)))
        rounds: list[dict] = []
        self.death_round: dict[int, int] = {}
        while True:
            dead = []
            for state in sorted(live):
                if not any(
                    self.mode_works(state, power, live)
                    for power in range(1, self.bounds.max_split_power + 1)
                ):
                    dead.append(state)
            if not dead:
                return live, rounds
            for state in dead:
                live.remove(state)
                self.death_round[state] = len(rounds) + 1
            rounds.append(
                {
                    "round": len(rounds) + 1,
                    "removed": len(dead),
                    "remaining": len(live),
                    "root_live": self.state_id.get((1, 1)) in live,
                    "sample_removed": [list(self.states[i]) for i in dead[:16]],
                }
            )

    def z3_status(self) -> str:
        """Independently encode bounded closure as constrained Horn-style SAT."""
        if z3 is None:
            return "z3-unavailable"
        root = self.state_id.get((1, 1))
        if root is None:
            return "root-outside-universe"
        use = [z3.Bool(f"use_{i}") for i in range(len(self.states))]
        solver = z3.Solver()
        solver.add(use[root])
        for state in range(len(self.states)):
            modes = []
            for power in range(1, self.bounds.max_split_power + 1):
                branch_requirements = []
                for digit in range(1 << power):
                    targets = [
                        use[target]
                        for target, _ in self.branch_paths(state, power, digit)
                    ]
                    branch_requirements.append(z3.Or(targets))
                modes.append(z3.And(branch_requirements))
            solver.add(z3.Implies(use[state], z3.Or(modes)))
        return str(solver.check())

    def extract_certificate(self, live: set[int]) -> dict:
        root = self.state_id[(1, 1)]
        if root not in live:
            raise ValueError("root is not in the closed set")

        # Reachable subgraph under a deterministic least-cost choice.
        chosen: dict[int, tuple[int, list[tuple[int, tuple[str, ...]]]]] = {}
        todo = deque([root])
        reached = {root}
        while todo:
            state = todo.popleft()
            alternatives = []
            for power in range(1, self.bounds.max_split_power + 1):
                branches = []
                total_cost = 0
                ok = True
                for digit in range(1 << power):
                    options = [
                        (target, path)
                        for target, path in self.branch_paths(state, power, digit)
                        if target in live
                    ]
                    if not options:
                        ok = False
                        break
                    target, path = min(
                        options,
                        key=lambda item: (
                            len(item[1]),
                            sum(self.states[item[0]]),
                            self.states[item[0]],
                        ),
                    )
                    total_cost += len(path)
                    branches.append((target, path))
                if ok:
                    alternatives.append((total_cost, power, branches))
            _, power, branches = min(alternatives)
            chosen[state] = power, branches
            for target, _ in branches:
                if target not in reached:
                    reached.add(target)
                    todo.append(target)

        renumber = {old: new for new, old in enumerate(sorted(reached))}
        cert_states = []
        for old in sorted(reached):
            a, b = self.states[old]
            power, branches = chosen[old]
            cert_states.append(
                {
                    "id": renumber[old],
                    "base": a,
                    "step": b,
                    "base_orbit": self.base_orbits[a],
                    "split_power": power,
                    "branches": [
                        {
                            "digit": digit,
                            "target": renumber[target],
                            "path": list(path),
                        }
                        for digit, (target, path) in enumerate(branches)
                    ],
                }
            )
        return {
            "format": "collatz-cyclic-tail-certificate-v1",
            "root": renumber[root],
            "states": cert_states,
            "search_bounds": self.bounds.__dict__,
        }

    def root_obstructions(self, live: set[int]) -> list[dict]:
        root = self.state_id.get((1, 1))
        if root is None:
            return []
        report = []
        for power in range(1, self.bounds.max_split_power + 1):
            digits = []
            for digit in range(1 << power):
                paths = self.branch_paths(root, power, digit)
                surviving = [self.states[t] for t, _ in paths if t in live]
                ranked = sorted(
                    (
                        (self.death_round.get(target, sys.maxsize), target, path)
                        for target, path in paths
                    ),
                    reverse=True,
                )
                best_round = ranked[0][0] if ranked else 0
                digits.append(
                    {
                        "digit": digit,
                        "candidate_targets": len(paths),
                        "live_targets": [list(p) for p in surviving[:16]],
                        "latest_target_death_round": (
                            None if best_round == sys.maxsize else best_round
                        ),
                        "latest_targets": [
                            {
                                "state": list(self.states[target]),
                                "death_round": (
                                    None if death == sys.maxsize else death
                                ),
                                "path": list(path),
                            }
                            for death, target, path in ranked[:5]
                            if death == best_round
                        ],
                    }
                )
            finite_rounds = [
                digit["latest_target_death_round"]
                for digit in digits
                if digit["latest_target_death_round"] is not None
            ]
            report.append(
                {
                    "split_power": power,
                    "mode_bottleneck_round": min(finite_rounds) if finite_rounds else None,
                    "digits": digits,
                }
            )
        return report

    @lru_cache(maxsize=None)
    def ranked_branch_candidates(
        self,
        state: int,
        power: int,
        digit: int,
        max_u: int,
        max_v: int,
        cap: int,
    ) -> tuple[tuple[int, int, int, tuple[str, ...]], ...]:
        """Candidate `(target,u,v,path)` reparameterizations.

        If the component walk ends at `C+E*t`, a target `(c,e)` is admissible
        when `C+E*t = c+e*(u*t+v)` with natural `u,v`.
        """
        candidates: dict[tuple[int, int, int], tuple[str, ...]] = {}
        start = self.branch_start(state, power, digit)
        for (constant, slope), path in self.walk_pairs_from(start):
            for target_step in range(1, min(self.bounds.step_limit, slope) + 1):
                if slope % target_step:
                    continue
                u = slope // target_step
                if u > max_u:
                    continue
                residue = constant % target_step
                target_base = residue if residue else target_step
                while target_base <= min(constant, self.bounds.base_limit):
                    target = self.state_id.get((target_base, target_step))
                    if target is not None:
                        v = (constant - target_base) // target_step
                        if v <= max_v:
                            key = (target, u, v)
                            old = candidates.get(key)
                            if old is None or len(path) < len(old):
                                candidates[key] = path
                    target_base += target_step
        ranked = sorted(
            (
                (target, u, v, path)
                for (target, u, v), path in candidates.items()
            ),
            key=lambda item: (
                len(item[3]),
                item[1] + item[2],
                sum(self.states[item[0]]),
                self.states[item[0]],
            ),
        )
        return tuple(ranked[:cap])

    def solve_ranked(
        self,
        rank_weight_limit: int,
        rank_const_limit: int,
        max_u: int,
        max_v: int,
        edge_cap: int,
        timeout_ms: int,
    ) -> tuple[str, dict | None, dict]:
        """Synthesize a closed graph and affine size-change rank with Z3."""
        if z3 is None:
            return "z3-unavailable", None, {}
        root = self.state_id.get((1, 1))
        if root is None:
            return "root-outside-universe", None, {}
        count = len(self.states)
        modes: dict[tuple[int, int], object] = {}
        takes: dict[tuple[int, int, int, int], object] = {}
        candidate_table: dict[
            tuple[int, int, int],
            tuple[tuple[int, int, int, tuple[str, ...]], ...],
        ] = {}
        # First compute the exact greatest closed subset after forgetting the
        # rank inequalities.  This is a cheap CHC reachability prepass and
        # avoids asking SMT to rediscover pure Boolean dead states.
        for state in range(count):
            for power in range(1, self.bounds.max_split_power + 1):
                q = 1 << power
                for digit in range(q):
                    candidates = self.ranked_branch_candidates(
                        state, power, digit, max_u, max_v, edge_cap
                    )
                    candidate_table[state, power, digit] = candidates
        live = set(range(count))
        prepass_rounds = 0
        while True:
            dead = []
            for state in live:
                if not any(
                    all(
                        any(
                            target in live
                            for target, _u, _v, _path in candidate_table[
                                state, power, digit
                            ]
                        )
                        for digit in range(1 << power)
                    )
                    for power in range(1, self.bounds.max_split_power + 1)
                ):
                    dead.append(state)
            if not dead:
                break
            live.difference_update(dead)
            prepass_rounds += 1
        basic_stats = {
            "states": count,
            "prepass_live_states": len(live),
            "prepass_rounds": prepass_rounds,
            "prepass_root_live": root in live,
            "rank_weight_limit": rank_weight_limit,
            "rank_const_limit": rank_const_limit,
            "max_reparam_u": max_u,
            "max_reparam_v": max_v,
            "edge_cap_per_branch": edge_cap,
            "timeout_ms": timeout_ms,
            "candidate_edges": sum(len(v) for v in candidate_table.values()),
        }
        if root not in live:
            return "unsat-prepass", None, {"z3_status": "not-run", **basic_stats}

        use = {i: z3.Bool(f"r_use_{i}") for i in live}
        weight = {i: z3.Int(f"rank_w_{i}") for i in live}
        const = {i: z3.Int(f"rank_c_{i}") for i in live}
        solver = z3.Solver()
        solver.set(timeout=timeout_ms)
        solver.add(use[root])
        for state in sorted(live):
            solver.add(weight[state] >= 1, weight[state] <= rank_weight_limit)
            solver.add(const[state] >= 0, const[state] <= rank_const_limit)
            state_modes = []
            for power in range(1, self.bounds.max_split_power + 1):
                mode = z3.Bool(f"mode_{state}_{power}")
                modes[state, power] = mode
                state_modes.append(mode)
                solver.add(z3.Implies(mode, use[state]))
                q = 1 << power
                for digit in range(q):
                    candidates = tuple(
                        candidate
                        for candidate in candidate_table[state, power, digit]
                        if candidate[0] in live
                    )
                    candidate_table[state, power, digit] = candidates
                    choices = []
                    for index, (target, u, v, _path) in enumerate(candidates):
                        take = z3.Bool(f"take_{state}_{power}_{digit}_{index}")
                        takes[state, power, digit, index] = take
                        choices.append(take)
                        solver.add(z3.Implies(take, mode))
                        solver.add(z3.Implies(take, use[target]))
                        # For every t >= tmin, rank(target,u*t+v) is below
                        # rank(state,q*t+digit).  Nonnegative slope difference
                        # plus the endpoint inequality is necessary/sufficient.
                        tmin = 1 if digit == 0 else 0
                        solver.add(
                            z3.Implies(
                                take,
                                weight[state] * q - weight[target] * u >= 0,
                            )
                        )
                        solver.add(
                            z3.Implies(
                                take,
                                weight[target] * (u * tmin + v) + const[target]
                                < weight[state] * (q * tmin + digit) + const[state],
                            )
                        )
                    solver.add(z3.Implies(mode, z3.Or(choices)))
            solver.add(z3.Implies(use[state], z3.Or(state_modes)))
        status = solver.check()
        stats = {
            "z3_status": str(status),
            **basic_stats,
        }
        if status != z3.sat:
            return str(status), None, stats
        model = solver.model()
        reached = {root}
        todo = deque([root])
        selected: dict[int, tuple[int, list[tuple[int, int, int, tuple[str, ...]]]]] = {}
        while todo:
            state = todo.popleft()
            power = next(
                power
                for power in range(1, self.bounds.max_split_power + 1)
                if z3.is_true(model.eval(modes[state, power], model_completion=True))
            )
            branches = []
            for digit in range(1 << power):
                candidates = candidate_table[state, power, digit]
                index = next(
                    index
                    for index in range(len(candidates))
                    if z3.is_true(
                        model.eval(
                            takes[state, power, digit, index], model_completion=True
                        )
                    )
                )
                target, u, v, path = candidates[index]
                branches.append((target, u, v, path))
                if target not in reached:
                    reached.add(target)
                    todo.append(target)
            selected[state] = power, branches
        renumber = {old: new for new, old in enumerate(sorted(reached))}
        cert_states = []
        for old in sorted(reached):
            a, b = self.states[old]
            power, branches = selected[old]
            cert_states.append(
                {
                    "id": renumber[old],
                    "base": a,
                    "step": b,
                    "base_orbit": self.base_orbits[a],
                    "rank_weight": model.eval(weight[old]).as_long(),
                    "rank_constant": model.eval(const[old]).as_long(),
                    "split_power": power,
                    "branches": [
                        {
                            "digit": digit,
                            "target": renumber[target],
                            "param_u": u,
                            "param_v": v,
                            "path": list(path),
                        }
                        for digit, (target, u, v, path) in enumerate(branches)
                    ],
                }
            )
        certificate = {
            "format": "collatz-ranked-tail-certificate-v1",
            "root": renumber[root],
            "states": cert_states,
            "search_bounds": self.bounds.__dict__,
            "solver_bounds": stats,
        }
        return "sat", certificate, stats


def verify_certificate(data: dict) -> dict:
    if data.get("format") != "collatz-cyclic-tail-certificate-v1":
        raise ValueError("unsupported certificate format")
    states = data.get("states")
    if not isinstance(states, list) or not states:
        raise ValueError("certificate has no states")
    by_id = {state["id"]: state for state in states}
    if set(by_id) != set(range(len(states))):
        raise ValueError("state identifiers must be contiguous")
    root = by_id[data["root"]]
    if (root["base"], root["step"]) != (1, 1):
        raise ValueError("root must parametrize 1+k")

    checked_branches = 0
    for state_id, state in sorted(by_id.items()):
        a, b = state["base"], state["step"]
        if a <= 0 or b <= 0:
            raise ValueError(f"state {state_id} has nonpositive coefficients")
        orbit = state["base_orbit"]
        if not orbit or orbit[0] != a or orbit[-1] != 1:
            raise ValueError(f"state {state_id} has malformed base orbit")
        for x, y in zip(orbit, orbit[1:]):
            if syracuse(x) != y:
                raise ValueError(f"state {state_id} has invalid base step {x}->{y}")
        power = state["split_power"]
        if not isinstance(power, int) or power <= 0:
            raise ValueError(f"state {state_id} has invalid split power")
        q = 1 << power
        branches = state["branches"]
        if len(branches) != q or {br["digit"] for br in branches} != set(range(q)):
            raise ValueError(f"state {state_id} does not partition every digit")
        for branch in branches:
            digit = branch["digit"]
            target = by_id[branch["target"]]
            path = branch["path"]
            if any(op not in OPS for op in path):
                raise ValueError(f"state {state_id}, digit {digit}: unknown operation")
            start = (a + b * digit, b * q)
            finish = apply_path(start, path)
            expected = (target["base"], target["step"])
            if finish != expected:
                raise ValueError(
                    f"state {state_id}, digit {digit}: path gives {finish}, "
                    f"expected {expected}"
                )
            # Independent spot identities catch accidental path semantics bugs.
            for tail in (0, 1, 2, 7, 31):
                left = start[0] + start[1] * tail
                right = expected[0] + expected[1] * tail
                # Replay the family operation path pointwise, allowing inverses.
                point = left
                for op in path:
                    if op in ("E", "O"):
                        point = syracuse(point)
                    elif op == "I0":
                        point = 2 * point
                    else:
                        if point % 3 != 2:
                            raise ValueError("pointwise I1 divisibility failure")
                        point = (2 * point - 1) // 3
                if point != right:
                    raise ValueError("pointwise affine replay failed")
            checked_branches += 1
    return {
        "verified": True,
        "states": len(states),
        "branches": checked_branches,
        "root_family": "1+k",
    }


def verify_ranked_certificate(data: dict) -> dict:
    if data.get("format") != "collatz-ranked-tail-certificate-v1":
        raise ValueError("unsupported ranked certificate format")
    states = data.get("states")
    if not isinstance(states, list) or not states:
        raise ValueError("ranked certificate has no states")
    by_id = {state["id"]: state for state in states}
    if set(by_id) != set(range(len(states))):
        raise ValueError("state identifiers must be contiguous")
    root = by_id[data["root"]]
    if (root["base"], root["step"]) != (1, 1):
        raise ValueError("root must parametrize 1+k")
    checked_branches = 0
    for state_id, state in sorted(by_id.items()):
        a, b = state["base"], state["step"]
        weight, rank_const = state["rank_weight"], state["rank_constant"]
        if a <= 0 or b <= 0 or weight <= 0 or rank_const < 0:
            raise ValueError(f"state {state_id} has invalid coefficients")
        orbit = state["base_orbit"]
        if not orbit or orbit[0] != a or orbit[-1] != 1:
            raise ValueError(f"state {state_id} has malformed base orbit")
        for x, y in zip(orbit, orbit[1:]):
            if syracuse(x) != y:
                raise ValueError(f"state {state_id} has invalid base step {x}->{y}")
        power = state["split_power"]
        if not isinstance(power, int) or power <= 0:
            raise ValueError(f"state {state_id} has invalid split power")
        q = 1 << power
        branches = state["branches"]
        if len(branches) != q or {br["digit"] for br in branches} != set(range(q)):
            raise ValueError(f"state {state_id} does not partition every digit")
        for branch in branches:
            digit = branch["digit"]
            target = by_id[branch["target"]]
            u, v = branch["param_u"], branch["param_v"]
            path = branch["path"]
            if u < 0 or v < 0 or any(op not in OPS for op in path):
                raise ValueError(f"state {state_id}, digit {digit}: malformed edge")
            start = (a + b * digit, b * q)
            finish = apply_path(start, path)
            expected = (
                target["base"] + target["step"] * v,
                target["step"] * u,
            )
            if finish != expected:
                raise ValueError(
                    f"state {state_id}, digit {digit}: path gives {finish}, "
                    f"expected reparameterized target {expected}"
                )
            target_weight = target["rank_weight"]
            target_const = target["rank_constant"]
            slope_gap = weight * q - target_weight * u
            tmin = 1 if digit == 0 else 0
            source_rank = weight * (q * tmin + digit) + rank_const
            target_rank = target_weight * (u * tmin + v) + target_const
            if slope_gap < 0 or not target_rank < source_rank:
                raise ValueError(
                    f"state {state_id}, digit {digit}: affine rank does not "
                    "decrease for every legal tail"
                )
            for tail in (tmin, tmin + 1, tmin + 2, tmin + 7, tmin + 31):
                left = start[0] + start[1] * tail
                right = target["base"] + target["step"] * (u * tail + v)
                point = left
                for op in path:
                    if op in ("E", "O"):
                        point = syracuse(point)
                    elif op == "I0":
                        point = 2 * point
                    else:
                        if point % 3 != 2:
                            raise ValueError("pointwise I1 divisibility failure")
                        point = (2 * point - 1) // 3
                if point != right:
                    raise ValueError("pointwise ranked-edge replay failed")
                if not (
                    target_weight * (u * tail + v) + target_const
                    < weight * (q * tail + digit) + rank_const
                ):
                    raise ValueError("pointwise rank replay failed")
            checked_branches += 1
    return {
        "verified": True,
        "states": len(states),
        "branches": checked_branches,
        "root_family": "1+k",
        "rank": "state-dependent affine natural rank",
    }


def make_bounds(args: argparse.Namespace) -> SearchBounds:
    return SearchBounds(
        base_limit=args.base_limit,
        step_limit=args.step_limit,
        walk_base_limit=args.walk_base_limit,
        walk_step_limit=args.walk_step_limit,
        path_depth=args.path_depth,
        max_split_power=args.max_split_power,
    )


def cmd_mine(args: argparse.Namespace) -> int:
    miner = Miner(make_bounds(args))
    live, rounds = miner.greatest_fixed_point()
    root_id = miner.state_id.get((1, 1))
    root_live = root_id in live if root_id is not None else False
    report = {
        "format": "collatz-cyclic-tail-search-audit-v1",
        "claim_scope": (
            "Exact only for the displayed finite state universe, split powers, "
            "and bounded component-walk grammar. Bounded UNSAT is not a Collatz result."
        ),
        "bounds": miner.bounds.__dict__,
        "states": len(miner.states),
        "base_cases_reaching_one": len(miner.base_orbits),
        "fixed_point_rounds": rounds,
        "live_states": len(live),
        "root_live": root_live,
        "path_cache": {
            "queries": miner.paths_from.cache_info().misses,
            "hits": miner.paths_from.cache_info().hits,
        },
    }
    if args.z3_check:
        report["z3_status"] = miner.z3_status()
    if root_live:
        certificate = miner.extract_certificate(live)
        verification = verify_certificate(certificate)
        report["result"] = "certificate"
        report["verification"] = verification
        if args.certificate:
            Path(args.certificate).write_text(
                json.dumps(certificate, indent=2, sort_keys=True) + "\n"
            )
    else:
        report["result"] = "bounded-unsat"
        # At the final fixed point this is normally empty; preserve root-local
        # candidate counts to expose whether state bounds or path bounds bite.
        report["root_obligations_against_final_live_set"] = miner.root_obstructions(live)
    if args.output:
        Path(args.output).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    data = json.loads(Path(args.certificate).read_text())
    if data.get("format") == "collatz-ranked-tail-certificate-v1":
        result = verify_ranked_certificate(data)
    else:
        result = verify_certificate(data)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def cmd_mine_ranked(args: argparse.Namespace) -> int:
    miner = Miner(make_bounds(args))
    status, certificate, stats = miner.solve_ranked(
        rank_weight_limit=args.rank_weight_limit,
        rank_const_limit=args.rank_const_limit,
        max_u=args.max_reparam_u,
        max_v=args.max_reparam_v,
        edge_cap=args.edge_cap,
        timeout_ms=args.timeout_ms,
    )
    report = {
        "format": "collatz-ranked-tail-search-audit-v1",
        "claim_scope": (
            "Exact only for the displayed bounded states, component walks, "
            "reparameterizations, edge cap, and affine-rank bounds. UNSAT or "
            "UNKNOWN is not a Collatz result."
        ),
        "bounds": miner.bounds.__dict__,
        "solver": stats,
        "result": status,
        "walk_cache_queries": miner.walk_pairs_from.cache_info().misses,
    }
    if certificate is not None:
        verification = verify_ranked_certificate(certificate)
        report["verification"] = verification
        if args.certificate:
            Path(args.certificate).write_text(
                json.dumps(certificate, indent=2, sort_keys=True) + "\n"
            )
    if args.output:
        Path(args.output).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    mine = sub.add_parser("mine", help="search a bounded cyclic-tail grammar")
    mine.add_argument("--base-limit", type=int, default=96)
    mine.add_argument("--step-limit", type=int, default=96)
    mine.add_argument("--walk-base-limit", type=int, default=768)
    mine.add_argument("--walk-step-limit", type=int, default=1536)
    mine.add_argument("--path-depth", type=int, default=14)
    mine.add_argument("--max-split-power", type=int, default=4)
    mine.add_argument("--z3-check", action="store_true")
    mine.add_argument("--output")
    mine.add_argument("--certificate")
    mine.set_defaults(func=cmd_mine)
    ranked = sub.add_parser(
        "mine-ranked", help="synthesize reparameterized edges and an affine rank"
    )
    ranked.add_argument("--base-limit", type=int, default=16)
    ranked.add_argument("--step-limit", type=int, default=16)
    ranked.add_argument("--walk-base-limit", type=int, default=128)
    ranked.add_argument("--walk-step-limit", type=int, default=256)
    ranked.add_argument("--path-depth", type=int, default=10)
    ranked.add_argument("--max-split-power", type=int, default=2)
    ranked.add_argument("--rank-weight-limit", type=int, default=32)
    ranked.add_argument("--rank-const-limit", type=int, default=64)
    ranked.add_argument("--max-reparam-u", type=int, default=16)
    ranked.add_argument("--max-reparam-v", type=int, default=16)
    ranked.add_argument("--edge-cap", type=int, default=24)
    ranked.add_argument("--timeout-ms", type=int, default=120000)
    ranked.add_argument("--output")
    ranked.add_argument("--certificate")
    ranked.set_defaults(func=cmd_mine_ranked)
    verify = sub.add_parser("verify", help="independently replay a certificate")
    verify.add_argument("certificate")
    verify.set_defaults(func=cmd_verify)
    return p


def main() -> int:
    args = parser().parse_args()
    numeric = [
        getattr(args, name)
        for name in (
            "base_limit",
            "step_limit",
            "walk_base_limit",
            "walk_step_limit",
            "path_depth",
            "max_split_power",
        )
        if hasattr(args, name)
    ]
    if any(value <= 0 for value in numeric):
        raise SystemExit("all search bounds must be positive")
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
