#!/usr/bin/env python3
"""Exact reduction of the three-word carry problem to a zero-carry map.

For the finite first-passage alphabet ``{1,011,010111}``, every nonroot
canonical boundary is ``y = 3 H - 1``.  A zero extension carry is possible
exactly when the positive charge ``H`` belongs to one of three disjoint
dyadic cylinders, and then the next charge is

    A: H = 0  (mod 2)   -> 3 H / 2,
    B: H = 5  (mod 8)   -> (9 H + 3) / 8,
    C: H = 49 (mod 64)  -> (81 H + 63) / 64.

This worker checks that reduction against every per-budget witness in the
exact carry-budget artifact.  It also records the full-branch 2-adic coding,
the strict positive growth of every defined branch, and the universal
eventually-periodic obstruction.  These identities focus the unbounded
construction target; they do not produce an infinite ordinary orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence

try:
    from . import outward_carry_budget as carry
except ImportError:
    import outward_carry_budget as carry


SCHEMA = "collatz-outward-zero-carry-map-v1"
DEFAULT_CARRY_ARTIFACT = Path(__file__).with_name(
    "outward_carry_budget_audit.json"
)


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_sha256() -> str:
    return file_sha256(Path(__file__))


def valuation(value: int, prime: int) -> tuple[int, int]:
    if value <= 0 or prime <= 1:
        raise ValueError("valuation requires a positive integer and base")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent, value


@dataclass(frozen=True)
class ReducedState:
    D: int
    c: int
    z: int

    @property
    def M(self) -> int:
        return 3 ** (self.D - 1)

    @property
    def charge(self) -> int:
        return 3**self.c * self.z


@dataclass(frozen=True)
class Branch:
    tag: str
    word: str
    denominator: int
    multiplier: int
    constant: int
    residue: int

    @property
    def bit_cost(self) -> int:
        return self.denominator.bit_length() - 1

    @property
    def odd_count(self) -> int:
        exponent, unit = valuation(self.multiplier, 3)
        if unit != 1:
            raise AssertionError("branch multiplier is not a power of three")
        return exponent


BRANCHES = (
    Branch("A", "1", 2, 3, 0, 0),
    Branch("B", "011", 8, 9, 3, 5),
    Branch("C", "010111", 64, 81, 63, 49),
)


def reduce_state(state: carry.State) -> ReducedState:
    if state.length <= 0 or (state.target + 1) % 3:
        raise ValueError("only nonroot completed boundaries have a charge")
    charge = (state.target + 1) // 3
    c, z = valuation(charge, 3)
    D = state.odd_count - c
    result = ReducedState(D, c, z)
    if D < 1 or not 1 <= z <= result.M or z % 3 == 0:
        raise AssertionError("canonical boundary left the reduced state space")
    return result


def reduced_extend(state: ReducedState, word_index: int) -> tuple[int, ReducedState]:
    """Lossless nonroot transition, including its exact natural carry q."""

    D, c, z, M = state.D, state.c, state.z, state.M
    if word_index == 0:
        q = z % 2
        child = ReducedState(D, c + 1, (z + M * q) // 2)
    elif word_index == 1:
        q = ((5 * pow(3**c, -1, 8) - z) * pow(M, -1, 8)) % 8
        child = ReducedState(
            D + c + 1,
            1,
            (3 ** (c + 1) * (z + M * q) + 1) // 8,
        )
    elif word_index == 2:
        q = ((49 * pow(3**c, -1, 64) - z) * pow(M, -1, 64)) % 64
        child = ReducedState(
            D + c + 2,
            2,
            (3 ** (c + 2) * (z + M * q) + 7) // 64,
        )
    else:
        raise ValueError("the reduced alphabet has exactly three words")
    if child.D < 1 or not 1 <= child.z <= child.M or child.z % 3 == 0:
        raise AssertionError("reduced transition left the canonical state space")
    return q, child


def charge_step(charge: int) -> tuple[str, int] | None:
    if charge <= 0:
        raise ValueError("zero-carry charge must be positive")
    for branch in BRANCHES:
        if charge % branch.denominator == branch.residue:
            numerator = branch.multiplier * charge + branch.constant
            if numerator % branch.denominator:
                raise AssertionError("branch cylinder missed integrality")
            output = numerator // branch.denominator
            if output <= charge:
                raise AssertionError("defined zero-carry branch did not grow")
            return branch.tag, output
    return None


def zero_reduced_step(c: int, z: int) -> tuple[str, int, int] | None:
    if c < 0 or z <= 0 or z % 3 == 0:
        raise ValueError("zero-carry reduced state is invalid")
    result = charge_step(3**c * z)
    if result is None:
        return None
    tag, output = result
    new_c, new_z = valuation(output, 3)
    return tag, new_c, new_z


def branch_by_tag(tag: str) -> Branch:
    for branch in BRANCHES:
        if branch.tag == tag:
            return branch
    raise ValueError("unknown zero-carry tag")


def compose_macro(tags: Sequence[str]) -> tuple[int, int, int]:
    """Return (a,b,d) for H |-> (a H+b)/d."""

    a, b, d = 1, 0, 1
    for tag in tags:
        branch = branch_by_tag(tag)
        a, b, d = (
            branch.multiplier * a,
            branch.multiplier * b + branch.constant * d,
            branch.denominator * d,
        )
    return a, b, d


def inverse_branch(tag: str, target: int, precision: int) -> int:
    """The unique 2-adic predecessor modulo 2^precision."""

    if precision < 1:
        raise ValueError("2-adic precision must be positive")
    branch = branch_by_tag(tag)
    modulus = 2**precision
    return (
        (branch.denominator * target - branch.constant)
        * pow(branch.multiplier, -1, modulus)
    ) % modulus


def validate_carry_witnesses(path: Path) -> dict[str, Any]:
    artifact = json.loads(path.read_text())
    if artifact.get("schema") != carry.SCHEMA:
        raise ValueError("unexpected carry artifact schema")
    advertised = artifact.get("artifact_sha256")
    payload = dict(artifact)
    payload.pop("artifact_sha256", None)
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("carry artifact self-hash mismatch")
    words, _ = carry.selected_words(14, 50)
    if [word.word for word in words] != [branch.word for branch in BRANCHES]:
        raise AssertionError("carry alphabet and reduced alphabet disagree")

    witness_rows = 0
    edges_checked = 0
    nonroot_edges_checked = 0
    terminal: dict[str, Any] | None = None
    for row in artifact["audit"]["budget_frontier"]:
        witness = row["witness"]
        if witness is None:
            continue
        witness_rows += 1
        indices = [int(index) for index in witness["schedule_indices"]]
        state = carry.ROOT
        reduced: ReducedState | None = None
        for index in indices:
            parent = state
            state = carry.extend(state, words[index], index, len(words))
            edges_checked += 1
            child_reduced = reduce_state(state)
            if reduced is not None:
                q, predicted = reduced_extend(reduced, index)
                if q != state.carry - parent.carry or predicted != child_reduced:
                    raise AssertionError("reduced recurrence disagrees with carry edge")
                if q == 0:
                    zero = zero_reduced_step(reduced.c, reduced.z)
                    if zero is None or zero[0] != BRANCHES[index].tag:
                        raise AssertionError("zero-carry charge map lost its branch")
                    if 3 ** zero[1] * zero[2] != child_reduced.charge:
                        raise AssertionError("zero-carry charge output disagrees")
                nonroot_edges_checked += 1
            reduced = child_reduced
        if state.rho != int(witness["seed"]):
            raise AssertionError("budget witness seed changed under replay")
        if state.target != int(witness["canonical_target"]):
            raise AssertionError("budget witness target changed under replay")
        if state.carry != int(witness["total_carry"]):
            raise AssertionError("budget witness carry changed under replay")
        if row["carry_budget"] == artifact["audit"]["bounds"]["carry_budget"]:
            if reduced is None:
                raise AssertionError("deepest witness was empty")
            next_costs = [reduced_extend(reduced, index)[0] for index in range(3)]
            terminal = {
                "carry_budget": int(row["carry_budget"]),
                "depth": len(indices),
                "D": reduced.D,
                "c": reduced.c,
                "z_mod_64": reduced.z % 64,
                "charge_bits": reduced.charge.bit_length(),
                "next_carries": next_costs,
                "zero_carry_defined": charge_step(reduced.charge) is not None,
            }
    if terminal is None:
        raise AssertionError("carry artifact had no terminal budget witness")
    return {
        "carry_artifact_sha256": advertised,
        "carry_artifact_file_sha256": file_sha256(path),
        "budget_witnesses_replayed": witness_rows,
        "witness_edges_checked": edges_checked,
        "nonroot_reduced_edges_checked": nonroot_edges_checked,
        "maximum_budget_terminal": terminal,
    }


def symbolic_audit(maximum_macro_length: int) -> dict[str, Any]:
    if maximum_macro_length < 1:
        raise ValueError("macro audit length must be positive")
    residues = []
    for branch in BRANCHES:
        sample = branch.residue
        output = charge_step(sample if sample > 0 else branch.denominator)
        residues.append(
            {
                "tag": branch.tag,
                "word": branch.word,
                "domain": f"H={branch.residue} mod {branch.denominator}",
                "map": (
                    f"H' = ({branch.multiplier}*H+{branch.constant})/"
                    f"{branch.denominator}"
                ),
                "strict_growth_numerator": (
                    branch.multiplier - branch.denominator
                ),
                "inverse_coding": (
                    f"H=({branch.denominator}*H'-{branch.constant})/"
                    f"{branch.multiplier} in Z_2"
                ),
                "sample_check": list(output) if output is not None else None,
            }
        )

    macros_checked = 0
    recharge_macros = 0
    closest_fixed_point: tuple[Fraction, str] | None = None
    for length in range(1, maximum_macro_length + 1):
        for tags in itertools.product("ABC", repeat=length):
            macros_checked += 1
            a, b, d = compose_macro(tags)
            if a <= d or b < 0:
                raise AssertionError("outward macro lost strict slope")
            fixed = Fraction(-b, a - d)
            if b == 0:
                if set(tags) != {"A"} or fixed != 0:
                    raise AssertionError("only the all-A macro may have zero defect")
            else:
                recharge_macros += 1
                if fixed >= 0:
                    raise AssertionError("recharge macro has nonnegative fixed point")
                if closest_fixed_point is None or fixed > closest_fixed_point[0]:
                    closest_fixed_point = (fixed, "".join(tags))
            # If this macro repeated integrally forever, the integer
            # N=(a-d)H+b would be divisible by d^n for every n, hence N=0.
            if (a - d) <= 0 or d & (d - 1):
                raise AssertionError("periodic obstruction lost its power-of-two base")

    # Each branch cylinder is a full 2-adic branch: its inverse maps every
    # target residue to exactly one source residue at increased precision.
    inverse_checks = 0
    for precision in range(1, 13):
        modulus = 2**precision
        for branch in BRANCHES:
            for target in range(min(modulus, 64)):
                source = inverse_branch(branch.tag, target, precision + branch.bit_cost)
                if source % branch.denominator != branch.residue:
                    raise AssertionError("inverse branch missed its source cylinder")
                numerator = branch.multiplier * source + branch.constant
                if numerator % branch.denominator:
                    raise AssertionError("inverse branch is not integral")
                if (numerator // branch.denominator - target) % modulus:
                    raise AssertionError("inverse branch missed its target residue")
                inverse_checks += 1

    return {
        "branches": residues,
        "undefined_residue_count_mod_64": sum(
            charge_step(residue if residue else 64) is None
            for residue in range(64)
        ),
        "defined_residue_count_mod_64": 41,
        "exact_haar_survival_mass_at_block_depth_n": "(41/64)^n",
        "similarity_dimension_equation": "2^(-s)+8^(-s)+64^(-s)=1",
        "full_branch_inverse_checks": inverse_checks,
        "periodic_macro_regression": {
            "maximum_macro_length": maximum_macro_length,
            "macros_checked": macros_checked,
            "macros_with_positive_defect": recharge_macros,
            "closest_negative_fixed_point": (
                {
                    "value": str(closest_fixed_point[0]),
                    "macro": closest_fixed_point[1],
                }
                if closest_fixed_point is not None
                else None
            ),
            "universal_reason": (
                "for F(H)=(aH+b)/d with a>d and gcd(a,d)=1, integral "
                "iteration makes (a-d)H+b divisible by d^n for every n; "
                "therefore H=-b/(a-d)<=0"
            ),
        },
        "architecture_conclusion": (
            "the survivor set is a thin three-branch 2-adic full shift with "
            "empty cylinder interior; a positive ordinary orbit requires an "
            "aperiodic recursively defined address whose 2-adic code is a "
            "nonnegative integer"
        ),
    }


def build_artifact(carry_artifact: Path, maximum_macro_length: int) -> dict[str, Any]:
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "dependency_sha256": {
            "outward_carry_budget.py": file_sha256(Path(carry.__file__)),
        },
        "exact_reduction_validation": validate_carry_witnesses(carry_artifact),
        "symbolic_audit": symbolic_audit(maximum_macro_length),
        "theorem_interface": {
            "bounded_carry_normal_form": (
                "an infinite execution in the three-word subcode exists iff a "
                "finite prefix reaches a positive charge with an infinite "
                "zero-carry orbit"
            ),
            "ordinary_seed_from_charge": "x=3*H-1",
            "height_growth": "every defined zero-carry branch has H'>H",
            "counter_growth": (
                "an infinite orbit has H tending to infinity and infinitely "
                "many recharge branches; D tends to infinity, while carry is "
                "zero and the local v3 counter may reset"
            ),
            "unbounded_obligation": (
                "construct one positive natural in the thin 2-adic survivor "
                "set and prove every branch is defined"
            ),
        },
        "claim_scope": (
            "exact identities, exact replay of the stated carry witnesses, and "
            "a universal periodic-address obstruction; no infinite orbit is supplied"
        ),
        "counterexample": None,
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    validation = artifact["exact_reduction_validation"]
    periodic = artifact["symbolic_audit"]["periodic_macro_regression"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "carry_artifact_sha256": validation["carry_artifact_sha256"],
        "nonroot_reduced_edges_checked": validation["nonroot_reduced_edges_checked"],
        "maximum_budget_terminal": validation["maximum_budget_terminal"],
        "periodic_macros_regression_checked": periodic["macros_checked"],
        "counterexample": artifact["counterexample"],
    }


def verify_artifact(path: Path, carry_artifact: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected zero-carry schema")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256", None)
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("zero-carry artifact self-hash mismatch")
    maximum_macro_length = int(
        expected["symbolic_audit"]["periodic_macro_regression"][
            "maximum_macro_length"
        ]
    )
    actual = build_artifact(carry_artifact, maximum_macro_length)
    if actual != expected:
        raise AssertionError("zero-carry artifact differs from recomputation")
    if expected.get("counterexample") is not None:
        raise AssertionError("zero-carry audit claims a counterexample")
    return report(expected)


def selftest() -> None:
    if charge_step(2) != ("A", 3):
        raise AssertionError("A branch changed")
    if charge_step(5) != ("B", 6):
        raise AssertionError("B branch changed")
    if charge_step(49) != ("C", 63):
        raise AssertionError("C branch changed")
    if charge_step(1) is not None:
        raise AssertionError("undefined charge became defined")
    words, _ = carry.selected_words(14, 50)
    state = carry.ROOT
    for index in (2, 0, 1, 0):
        parent_reduced = reduce_state(state) if state.length else None
        parent = state
        state = carry.extend(state, words[index], index, len(words))
        if parent_reduced is not None:
            q, predicted = reduced_extend(parent_reduced, index)
            if q != state.carry - parent.carry or predicted != reduce_state(state):
                raise AssertionError("tiny reduced transition changed")
    audit = symbolic_audit(4)
    if audit["periodic_macro_regression"]["macros_checked"] != 120:
        raise AssertionError("tiny periodic macro count changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("selftest")
    build = sub.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--carry-artifact", type=Path, default=DEFAULT_CARRY_ARTIFACT)
    build.add_argument("--maximum-macro-length", type=int, default=10)
    verify = sub.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    verify.add_argument("--carry-artifact", type=Path, default=DEFAULT_CARRY_ARTIFACT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print(json.dumps({"selftest": "ok", "counterexample": None}, sort_keys=True))
        return
    if args.command == "build":
        artifact = build_artifact(args.carry_artifact, args.maximum_macro_length)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(report(artifact), indent=2, sort_keys=True))
        return
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact, args.carry_artifact), indent=2, sort_keys=True))
        return
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()
