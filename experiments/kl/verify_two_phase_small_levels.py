#!/usr/bin/env python3
"""Exact small-level check of the split-all-then-prune KL repair.

This is a bounded verification, not the all-k termination proof.  It builds
the Phase-A history tree for every advanced root at k=2,3,4.  Nonnegative
branch children which are strictly above an earlier same-residue principal
ancestor are marked bad rather than immediately deleted.  Phase B is evaluated
bottom-up:

* a bad leaf has no good policy;
* an addition has a good policy only when both children do;
* a minimum has a good policy when at least one child does.

The surviving literal maxima reproduce KL Table 1: 8, 84, and 12,829.  Exact
shift signs use integer comparisons of powers of two and three through the
shared obstruction checker.
"""

from dataclasses import dataclass
from functools import lru_cache

from verify_all_three_deletion import (
    ADVANCED,
    RETARDED,
    TRANSPORT,
    Shift,
    branch_lifts,
    deletion_blockers,
    sign,
    transport,
)


@dataclass(frozen=True)
class Outcome:
    """Summary of one unfolded Phase-A subtree and its compiled good policies."""

    dead: bool
    raw_literals: int
    pruned_literals: int
    max_expansions: int


def update_minimum(
    minima: dict[int, Shift], state: int, shift: Shift
) -> dict[int, Shift]:
    updated = minima.copy()
    old = updated.get(state)
    if old is None or sign(shift - old) < 0:
        updated[state] = shift
    return updated


def analyze_level(k: int) -> dict[int, Outcome]:
    modulus = 3**k

    @lru_cache(maxsize=None)
    def visit(
        state: int,
        shift: Shift,
        minima_items: tuple[tuple[int, Shift], ...],
    ) -> Outcome:
        minima = dict(minima_items)
        if sign(shift) < 0:
            return Outcome(False, 1, 1, 0)

        transport_state = transport(state, modulus)
        transport_shift = shift + TRANSPORT
        transport_minima = update_minimum(
            minima, transport_state, transport_shift
        )
        transport_outcome = visit(
            transport_state,
            transport_shift,
            tuple(sorted(transport_minima.items())),
        )

        kind = "B2" if state % 9 == 2 else "B8" if state % 9 == 8 else None
        if kind is None:
            return Outcome(
                transport_outcome.dead,
                transport_outcome.raw_literals,
                transport_outcome.pruned_literals,
                1 + transport_outcome.max_expansions,
            )

        branch_shift = shift + (RETARDED if kind == "B2" else ADVANCED)
        branch_outcomes: list[Outcome] = []
        for target in branch_lifts(state, k, kind):
            old = minima.get(target)
            marked_bad = (
                sign(branch_shift) >= 0
                and old is not None
                and sign(branch_shift - old) > 0
            )
            if marked_bad:
                branch_outcomes.append(Outcome(True, 1, 0, 0))
                continue

            branch_minima = update_minimum(minima, target, branch_shift)
            branch_outcomes.append(
                visit(
                    target,
                    branch_shift,
                    tuple(sorted(branch_minima.items())),
                )
            )

        # Every additive assignment uses both sides; a minimum policy may use
        # any one live alternative.
        branch_minimum_dead = all(outcome.dead for outcome in branch_outcomes)
        whole_dead = transport_outcome.dead or branch_minimum_dead
        raw_literals = transport_outcome.raw_literals + sum(
            outcome.raw_literals for outcome in branch_outcomes
        )
        pruned_literals = 0
        if not whole_dead:
            pruned_literals = transport_outcome.pruned_literals + sum(
                outcome.pruned_literals
                for outcome in branch_outcomes
                if not outcome.dead
            )
        return Outcome(
            whole_dead,
            raw_literals,
            pruned_literals,
            1
            + max(
                transport_outcome.max_expansions,
                *(outcome.max_expansions for outcome in branch_outcomes),
            ),
        )

    return {
        root: visit(root, Shift(0, 0), ((root, Shift(0, 0)),))
        for root in range(8, modulus, 9)
    }


def replay_branch_path(
    k: int,
    root: int,
    steps: tuple[tuple[str, int, int, Shift], ...],
) -> list[tuple[int, Shift]]:
    """Replay an exact all-branch path and return all principal occurrences."""

    state = root
    shift = Shift(0, 0)
    history = [(state, shift)]
    for kind, lift, target, expected_shift in steps:
        lifts = branch_lifts(state, k, kind)
        assert lifts[lift] == target
        shift = shift + (RETARDED if kind == "B2" else ADVANCED)
        assert shift == expected_shift
        assert sign(shift) > 0
        state = target
        history.append((state, shift))
    return history


def verify_occurrence_sensitive_marks() -> None:
    """The same label can be bad or good under different ancestor histories."""

    p1 = replay_branch_path(
        4,
        26,
        (
            ("B8", 1, 44, Shift(-1, 1)),
            ("B8", 2, 56, Shift(-2, 2)),
            ("B2", 2, 74, Shift(-4, 3)),
            ("B2", 2, 71, Shift(-6, 4)),
            ("B8", 2, 74, Shift(-7, 5)),
        ),
    )
    p2 = replay_branch_path(
        4,
        26,
        (
            ("B8", 2, 71, Shift(-1, 1)),
            ("B8", 2, 74, Shift(-2, 2)),
            ("B2", 1, 44, Shift(-4, 3)),
            ("B8", 2, 56, Shift(-5, 4)),
            ("B2", 2, 74, Shift(-7, 5)),
        ),
    )
    assert p1[-1] == p2[-1] == (74, Shift(-7, 5))
    assert deletion_blockers(p1[:-1], *p1[-1])
    assert not deletion_blockers(p2[:-1], *p2[-1])
    assert sign(Shift(-3, 2)) > 0  # P1: 9 > 8
    assert sign(Shift(-5, 3)) < 0  # P2: 27 < 32
    print(
        "PASS k=4: identical label 74@(-7,5) is bad on P1 and live on P2; "
        "marks must be occurrence-indexed"
    )


def main() -> None:
    verify_occurrence_sensitive_marks()
    expected_max_literals = {2: 8, 3: 84, 4: 12_829}
    for k, expected in expected_max_literals.items():
        outcomes = analyze_level(k)
        assert outcomes
        assert all(not outcome.dead for outcome in outcomes.values())
        observed = max(outcome.pruned_literals for outcome in outcomes.values())
        assert observed == expected
        largest_roots = [
            root
            for root, outcome in outcomes.items()
            if outcome.pruned_literals == observed
        ]
        print(
            f"PASS k={k}: every advanced root has a good complete policy; "
            f"max literals={observed:,} at root(s) {largest_roots}"
        )
    print("VERDICT: two-phase policy compilation reproduces KL Table 1 at k=2..4")
    print("SCOPE: bounded exact evidence only; all-k soundness still requires Lean")


if __name__ == "__main__":
    main()
