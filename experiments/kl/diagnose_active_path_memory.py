#!/usr/bin/env python3
"""Exact finite predictive-memory control for the k=12 active KL support.

This is deliberately a *tangent/support-lineage diagnostic*.  On a strict
selected-policy cell the nonlinear KL map has an active Jacobian.  Its support
has one transport successor from every coordinate and two extra branch
successors from a selected coordinate.  It is not itself a nonlinear
evolution of a KL profile.

For terminal fiber ``u`` put

    d_u = sum_a C[u+a*n] - 3 min_a C[u+a*n].

The checker places mass ``d_u`` on the selected child of that fiber and uses a
locally normalized support kernel: a nonselected coordinate takes transport
with probability one, while a selected coordinate chooses transport, B2, or
B8 with probability 1/3 each.  At a fixed total horizon every path weight
therefore has common denominator ``3^horizon`` and an exact integer
numerator.  This normalization describes a random lineage in the active
support; it discards the unequal KL amplitudes.

After four burn-in edges, the bounded state is

    (coordinate mod 9, sibling digit, local minimizing label).

The longer history is the suffix of the preceding edge word.  The script
computes exact Bayes--Brier gains for a two-edge future, proves the mandatory
next-edge gain is exactly zero, and evaluates a three-fold blocked holdout by
the low ternary digit of the starting fiber.  The small in-sample gains all
turn negative out of block.  This is a finite stop-rule against interpreting
fine path partitions as growing hidden memory, not an all-level invariant.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Callable, Iterable, NamedTuple

import numpy as np


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "cert_k12.json"
EXPECTED_MANIFEST_SHA256 = (
    "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f"
)
LEVEL = 12
BURN_IN = 4
FUTURE_HORIZON = 2
TOTAL_STEPS = BURN_IN + FUTURE_HORIZON
EXPECTED_POLICY_COUNTS = (20_037, 19_545, 19_467)
EXPECTED_TOTAL_DEFECT = 71_965_439_552_517_488
EXPECTED_PATH_COUNT = 2_663_871

# Exact computations are rendered as floats only after all comparisons.  The
# pinned decimal gates make accidental changes to indexing or labels visible.
EXPECTED_IN_SAMPLE_H4 = {
    "future edge word": 0.000_214_843_918_524,
    "endpoint policy": 0.000_737_432_505_162,
    "endpoint selected": 0.000_587_771_050_529,
    "endpoint defect bin": 0.001_062_030_547_31,
}
EXPECTED_HOLDOUT_MEAN = {
    "future edge word": (
        -0.000_099_322_085_548_771_78,
        -0.000_154_084_086_210_962,
        -0.000_237_463_009_953_794_48,
        -0.000_146_848_715_578_137_29,
    ),
    "endpoint policy": (
        -0.000_250_657_641_782_056_53,
        -0.000_589_103_014_250_643_4,
        -0.000_656_810_134_343_215_8,
        -0.000_452_306_925_263_525_5,
    ),
    "endpoint defect bin": (
        -0.000_736_570_222_511_488,
        -0.001_130_502_383_290_203,
        -0.001_020_951_891_082_913,
        -0.001_090_460_706_385_718_5,
    ),
}
EXPECTED_HOLDOUT_COVERAGE = (
    1.0,
    0.879_204_482_119_470_2,
    0.734_468_172_168_494_2,
    0.303_382_477_463_621_8,
)



class Row(NamedTuple):
    past_word: int
    bounded_state: int
    future_word: int
    endpoint_policy: int
    endpoint_selected: int
    endpoint_defect_bin: int
    origin_digit: int
    weight: int


Label = Callable[[Row], int]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_record() -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    actual_hash = sha256(MANIFEST)
    if actual_hash != EXPECTED_MANIFEST_SHA256:
        raise AssertionError(f"k=12 manifest hash mismatch: {actual_hash}")
    manifest = json.loads(MANIFEST.read_text())
    if int(manifest["k"]) != LEVEL or not isinstance(manifest.get("C"), list):
        raise AssertionError("the pinned portable k=12 source changed")
    vector = np.asarray(manifest["C"], dtype=np.int64)
    size = 3 ** (LEVEL - 1)
    if vector.shape != (size,) or int(vector.min()) <= 0:
        raise AssertionError("the pinned vector has the wrong shape or sign")

    parent_size = size // 3
    children = vector.reshape(3, parent_size)
    policy = np.argmin(children, axis=0).astype(np.int8)
    ordered = np.sort(children, axis=0)
    if np.any(ordered[0] == ordered[1]):
        raise AssertionError("the pinned minimizing policy is not strict")
    counts = tuple(map(int, np.bincount(policy, minlength=3)))
    if counts != EXPECTED_POLICY_COUNTS:
        raise AssertionError(f"minimizing-policy counts changed: {counts}")

    parent_mass = children.sum(axis=0, dtype=np.int64)
    if int(ordered[0].max()) > np.iinfo(np.int64).max // 3:
        raise OverflowError("three times a fiber minimum no longer fits int64")
    defect = parent_mass - 3 * ordered[0]
    # Use Python integers for the total even though this pinned record is
    # comfortably inside int64; no wraparound is part of the trust boundary.
    defect_total = sum(map(int, defect))
    if defect_total != EXPECTED_TOTAL_DEFECT or int(defect.min()) <= 0:
        raise AssertionError("terminal fiber-defect data changed")
    return vector, policy, parent_mass, defect


def expand_paths(
    vector: np.ndarray, policy: np.ndarray, defect: np.ndarray
) -> tuple[np.ndarray, ...]:
    """Return exact common-denominator path numerators and path labels."""

    size = len(vector)
    parent_size = size // 3
    inverse_four = pow(4, -1, size)
    inverse_four_parent = pow(4, -1, parent_size)
    inverse_two_parent = pow(2, -1, parent_size)

    if int(defect.max()) * 3**TOTAL_STEPS > np.iinfo(np.int64).max:
        raise OverflowError("path numerators no longer fit exact int64")

    parents = np.arange(parent_size, dtype=np.int64)
    coordinates = parents + policy.astype(np.int64) * parent_size
    weights = defect.copy()
    edge_codes = np.zeros(parent_size, dtype=np.int16)
    origins = (parents % 3).astype(np.int8)
    current_coordinates: np.ndarray | None = None

    for step in range(TOTAL_STEPS):
        current_parents = coordinates % parent_size
        selected = coordinates // parent_size == policy[current_parents]

        transport = (inverse_four * (coordinates - 2)) % size
        # Multiplication by three supplies the common denominator on a
        # deterministic transport step.  A selected step has three children,
        # each with numerator unchanged.
        transport_weights = np.where(selected, weights, 3 * weights)
        transport_codes = 3 * edge_codes

        branch_parents = current_parents[selected]
        branch_weights = weights[selected]
        branch_codes = 3 * edge_codes[selected]
        branch_2 = 3 * (
            (inverse_four_parent * branch_parents) % parent_size
        )
        branch_8 = 3 * (
            (inverse_two_parent * ((branch_parents - 1) % parent_size))
            % parent_size
        ) + 2

        if current_coordinates is not None:
            current_coordinates = np.concatenate(
                (
                    current_coordinates,
                    current_coordinates[selected],
                    current_coordinates[selected],
                )
            )
        origins = np.concatenate((origins, origins[selected], origins[selected]))
        coordinates = np.concatenate((transport, branch_2, branch_8))
        weights = np.concatenate(
            (transport_weights, branch_weights, branch_weights)
        )
        edge_codes = np.concatenate(
            (transport_codes, branch_codes + 1, branch_codes + 2)
        )
        if step + 1 == BURN_IN:
            current_coordinates = coordinates.copy()

    if current_coordinates is None or len(coordinates) != EXPECTED_PATH_COUNT:
        raise AssertionError("active-support path count changed")
    expected_weight = int(defect.sum()) * 3**TOTAL_STEPS
    if sum(map(int, weights)) != expected_weight:
        raise AssertionError("locally normalized path mass is not conserved")
    return coordinates, current_coordinates, weights, edge_codes, origins


def aggregate_rows(
    coordinates: np.ndarray,
    current_coordinates: np.ndarray,
    weights: np.ndarray,
    edge_codes: np.ndarray,
    origins: np.ndarray,
    policy: np.ndarray,
    parent_mass: np.ndarray,
    defect: np.ndarray,
) -> list[Row]:
    parent_size = len(policy)
    past = edge_codes // 3**FUTURE_HORIZON
    future = edge_codes % 3**FUTURE_HORIZON

    current_parent = current_coordinates % parent_size
    bounded_state = (
        ((current_coordinates % 9) * 3 + current_coordinates // parent_size) * 3
        + policy[current_parent]
    ).astype(np.int16)

    endpoint_parent = coordinates % parent_size
    endpoint_policy = policy[endpoint_parent]
    endpoint_selected = (
        coordinates // parent_size == endpoint_policy
    ).astype(np.int8)
    endpoint_defect_bin = (
        (20 * defect[endpoint_parent] > parent_mass[endpoint_parent]).astype(
            np.int8
        )
        + (10 * defect[endpoint_parent] > parent_mass[endpoint_parent]).astype(
            np.int8
        )
    )

    # Packing first avoids millions of Python tuple allocations.  Decode only
    # the distinct rows after exact integer aggregation.
    packed = past.astype(np.int64)
    for values, radix in (
        (bounded_state, 81),
        (future, 9),
        (endpoint_policy, 3),
        (endpoint_selected, 2),
        (endpoint_defect_bin, 3),
        (origins, 3),
    ):
        packed = packed * radix + values.astype(np.int64)

    totals: dict[int, int] = defaultdict(int)
    for key, weight in zip(packed, weights, strict=True):
        totals[int(key)] += int(weight)

    rows: list[Row] = []
    for key, weight in totals.items():
        value = key
        origin = value % 3
        value //= 3
        defect_bin = value % 3
        value //= 3
        selected = value % 2
        value //= 2
        endpoint = value % 3
        value //= 3
        future_word = value % 9
        value //= 9
        state = value % 81
        past_word = value // 81
        rows.append(
            Row(
                past_word,
                state,
                future_word,
                endpoint,
                selected,
                defect_bin,
                origin,
                weight,
            )
        )
    return rows


def exact_in_sample_gain(
    rows: Iterable[Row], history: int, label: Label
) -> tuple[Fraction, Fraction]:
    hsy: dict[tuple[int, int, int], int] = defaultdict(int)
    hs: dict[tuple[int, int], int] = defaultdict(int)
    sy: dict[tuple[int, int], int] = defaultdict(int)
    state_mass: dict[int, int] = defaultdict(int)
    total = 0
    modulus = 3**history
    for row in rows:
        state = row.bounded_state
        weight = row.weight
        context = row.past_word % modulus if history else 0
        target = label(row)
        hsy[context, state, target] += weight
        hs[context, state] += weight
        sy[state, target] += weight
        state_mass[state] += weight
        total += weight

    fine_power = sum(
        (Fraction(weight * weight, hs[context, state])
         for (context, state, _), weight in hsy.items()),
        Fraction(),
    )
    coarse_power = sum(
        (Fraction(weight * weight, state_mass[state])
         for (state, _), weight in sy.items()),
        Fraction(),
    )
    gain = (fine_power - coarse_power) / total
    coarse_risk = Fraction(1) - coarse_power / total
    relative_gain = gain / coarse_risk if coarse_risk else Fraction()
    return gain, relative_gain


def exact_holdout_gain(
    rows: Iterable[Row], history: int, label: Label, label_count: int,
    held_out_origin: int,
) -> tuple[Fraction, Fraction, Fraction]:
    train_hsy: dict[tuple[int, int, int], int] = defaultdict(int)
    train_hs: dict[tuple[int, int], int] = defaultdict(int)
    train_sy: dict[tuple[int, int], int] = defaultdict(int)
    train_state: dict[int, int] = defaultdict(int)
    test: dict[tuple[int, int, int], int] = defaultdict(int)
    modulus = 3**history

    for row in rows:
        state = row.bounded_state
        weight = row.weight
        context = row.past_word % modulus if history else 0
        target = label(row)
        if row.origin_digit == held_out_origin:
            test[context, state, target] += weight
        else:
            train_hsy[context, state, target] += weight
            train_hs[context, state] += weight
            train_sy[state, target] += weight
            train_state[state] += weight

    total = sum(test.values())
    covered = sum(
        weight
        for (context, state, _), weight in test.items()
        if (context, state) in train_hs
    )
    coarse_risk = Fraction()
    gain = Fraction()
    labels = range(label_count)

    for (context, state, target), weight in test.items():
        if state not in train_state:
            raise AssertionError("a held-out bounded state has no training mass")
        coarse = tuple(
            Fraction(train_sy.get((state, value), 0), train_state[state])
            for value in labels
        )
        if (context, state) in train_hs:
            fine = tuple(
                Fraction(
                    train_hsy.get((context, state, value), 0),
                    train_hs[context, state],
                )
                for value in labels
            )
        else:
            # An unseen long context gets the bounded-state predictor.  This
            # makes the reported coverage explicit and does not penalize fine
            # prediction merely for being undefined.
            fine = coarse

        coarse_score = (
            Fraction(1) - 2 * coarse[target] + sum(x * x for x in coarse)
        )
        fine_score = Fraction(1) - 2 * fine[target] + sum(x * x for x in fine)
        coarse_risk += weight * coarse_score
        gain += weight * (coarse_score - fine_score)

    return gain / total, gain / coarse_risk, Fraction(covered, total)


def check_close(actual: float, expected: float, name: str) -> None:
    if abs(actual - expected) > 5e-15:
        raise AssertionError(f"{name} changed: {actual:.17g} != {expected:.17g}")


def main() -> None:
    vector, policy, parent_mass, defect = load_record()
    print("PASS: SHA-pinned strict k=12 selected record and fiber defects")

    paths = expand_paths(vector, policy, defect)
    rows = aggregate_rows(
        *paths, policy=policy, parent_mass=parent_mass, defect=defect
    )
    print(
        "PASS: exact locally normalized active-support paths "
        f"({EXPECTED_PATH_COUNT:,} terminal paths, {len(rows):,} table rows)"
    )

    labels: dict[str, tuple[Label, int]] = {
        "next edge": (lambda row: row.future_word // 3, 3),
        "future edge word": (lambda row: row.future_word, 9),
        "endpoint policy": (lambda row: row.endpoint_policy, 3),
        "endpoint selected": (lambda row: row.endpoint_selected, 2),
        "endpoint defect bin": (lambda row: row.endpoint_defect_bin, 3),
    }

    for history in range(1, BURN_IN + 1):
        gain, _ = exact_in_sample_gain(rows, history, labels["next edge"][0])
        if gain != 0:
            raise AssertionError(
                f"next-edge bug-null failed at history {history}: {gain}"
            )
    print("PASS: exact next-edge Bayes--Brier gain is zero for h=1,...,4")

    print("IN-SAMPLE exact Bayes--Brier gain (absolute; relative to S-only risk)")
    print("  label                      h=1          h=2          h=3          h=4")
    for name in (
        "future edge word",
        "endpoint policy",
        "endpoint selected",
        "endpoint defect bin",
    ):
        values: list[str] = []
        final_gain = 0.0
        label = labels[name][0]
        for history in range(1, BURN_IN + 1):
            gain, relative = exact_in_sample_gain(rows, history, label)
            final_gain = float(gain)
            values.append(f"{float(gain):.6g}/{float(relative):.6g}")
        check_close(final_gain, EXPECTED_IN_SAMPLE_H4[name], f"{name} h=4")
        print(f"  {name:<25} " + "  ".join(f"{value:>19}" for value in values))

    print(
        "BLOCKED holdout mean over origin digit 0,1,2 "
        "(absolute gain; fine-context coverage)"
    )
    print("  label                      h=1          h=2          h=3          h=4")
    for name in (
        "future edge word",
        "endpoint policy",
        "endpoint defect bin",
    ):
        label, label_count = labels[name]
        values = []
        for history in range(1, BURN_IN + 1):
            folds = [
                exact_holdout_gain(rows, history, label, label_count, origin)
                for origin in range(3)
            ]
            if any(gain >= 0 for gain, _, _ in folds):
                raise AssertionError(
                    f"{name} h={history} is not negative in every holdout fold"
                )
            mean_gain = sum(float(gain) for gain, _, _ in folds) / 3
            mean_coverage = sum(float(coverage) for _, _, coverage in folds) / 3
            check_close(
                mean_gain,
                EXPECTED_HOLDOUT_MEAN[name][history - 1],
                f"{name} holdout h={history}",
            )
            check_close(
                mean_coverage,
                EXPECTED_HOLDOUT_COVERAGE[history - 1],
                f"holdout coverage h={history}",
            )
            values.append(f"{mean_gain:.6g}/{mean_coverage:.4f}")
        print(f"  {name:<25} " + "  ".join(f"{value:>19}" for value in values))

    print("PASS: every blocked-holdout gain is negative in every fold")
    print(
        "CONCLUSION: the active-support lineage has tiny in-sample long-history "
        "gain but no held-out evidence of growing predictive memory.  This is "
        "a same-policy tangent diagnostic, not nonlinear KL defect dynamics."
    )


if __name__ == "__main__":
    main()
