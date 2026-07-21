#!/usr/bin/env python3
"""Exact finite countermodel to split-time preservation of KL invariant (3.4).

The model is intentionally abstract: it refutes the generic inference from
"every old critical assignment respects principal bounds" plus local validity
of a substituted split to the same property after splitting.  It does not by
itself assert that these particular values occur in a concrete KL function
family.
"""

from dataclasses import dataclass
from itertools import product
from typing import TypeAlias


@dataclass(frozen=True)
class Leaf:
    name: str
    value: int


@dataclass(frozen=True)
class Principal:
    name: str
    bound: int
    body: "Tree"


@dataclass(frozen=True)
class Add:
    left: "Tree"
    right: "Tree"


@dataclass(frozen=True)
class Inf:
    alternatives: tuple["Tree", ...]


Tree: TypeAlias = Leaf | Principal | Add | Inf


@dataclass(frozen=True)
class Assignment:
    selected_sum: int
    # Each pair is (principal name, bound, selected sum below that principal).
    principal_checks: tuple[tuple[str, int, int], ...] = ()

    def respects_principal_bounds(self) -> bool:
        return all(selected <= bound for _, bound, selected in self.principal_checks)


def evaluate(tree: Tree) -> int:
    if isinstance(tree, Leaf):
        return tree.value
    if isinstance(tree, Principal):
        return evaluate(tree.body)
    if isinstance(tree, Add):
        return evaluate(tree.left) + evaluate(tree.right)
    return min(evaluate(child) for child in tree.alternatives)


def critical_assignments(tree: Tree) -> tuple[Assignment, ...]:
    """Enumerate all assignments attaining every syntactic minimum."""

    if isinstance(tree, Leaf):
        return (Assignment(tree.value),)
    if isinstance(tree, Principal):
        return tuple(
            Assignment(
                child.selected_sum,
                ((tree.name, tree.bound, child.selected_sum),)
                + child.principal_checks,
            )
            for child in critical_assignments(tree.body)
        )
    if isinstance(tree, Add):
        return tuple(
            Assignment(
                left.selected_sum + right.selected_sum,
                left.principal_checks + right.principal_checks,
            )
            for left, right in product(
                critical_assignments(tree.left),
                critical_assignments(tree.right),
            )
        )
    minimum = evaluate(tree)
    return tuple(
        assignment
        for child in tree.alternatives
        if evaluate(child) == minimum
        for assignment in critical_assignments(child)
    )


def main() -> None:
    # Old tree: inf (principal P (add (leaf L) (leaf X))) (leaf B).
    old_left = Principal("P", 5, Add(Leaf("L", 9), Leaf("X", 1)))
    old_tree = Inf((old_left, Leaf("B", 8)))

    # The right alternative is the unique old critical choice, so no selected
    # path traverses P and the assignment-specific principal invariant is
    # vacuous there.
    assert evaluate(old_left) == 10
    assert evaluate(old_tree) == 8
    old_critical = critical_assignments(old_tree)
    assert len(old_critical) == 1
    assert old_critical[0] == Assignment(8)
    assert all(a.respects_principal_bounds() for a in old_critical)

    # Split L by a KL-shaped add: transport value 2 plus min(3,3,3).
    split_body = Add(
        Leaf("transport", 2),
        Inf(tuple(Leaf(f"branch{j}", 3) for j in range(3))),
    )
    assert evaluate(split_body) == 5
    assert evaluate(split_body) <= 9  # local split validity at L

    new_left = Principal("P", 5, Add(split_body, Leaf("X", 1)))
    new_tree = Inf((new_left, Leaf("B", 8)))
    assert evaluate(new_left) == 6
    assert evaluate(new_tree) == 6
    assert evaluate(new_left) < 8  # the formerly inactive alternative activates

    # All three tied branch choices now traverse P and violate its bound.
    new_critical = critical_assignments(new_tree)
    assert len(new_critical) == 3
    assert all(a.selected_sum == 6 for a in new_critical)
    assert all(not a.respects_principal_bounds() for a in new_critical)
    assert all(a.principal_checks == (("P", 5, 6),) for a in new_critical)

    print("PASS: every old critical assignment avoids principal P")
    print("PASS: the substituted KL-shaped split is locally valid (5 <= 9)")
    print("PASS: splitting activates the outer-min alternative (6 < 8)")
    print("VERDICT: every new critical assignment violates P's bound (6 > 5)")
    print("SCOPE: this refutes the generic split-invariant induction, not KL termination")


if __name__ == "__main__":
    main()
