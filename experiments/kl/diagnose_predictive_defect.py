#!/usr/bin/env python3
"""Exact finite predictive-memory diagnostic for selected KL defect fields.

For one level-k certificate C, aggregate along the 3-adic genealogy

    A_j(p) = sum_{i == p (mod 3^(j-1))} C[i].

At every nonterminal genealogy node put

    d_j(p) = A_j(p) - 3 min_a A_(j+1)(p+a 3^(j-1)).

The main probability law samples a future node with weight d_j(p).  This is
the normalized *fiber* defect field; it does not use coordinate excesses, so
the selected child is not definitionally assigned zero sampling mass.

At a cut j and refinement horizon r, a sampled future node v at f=j+r has
ancestor p=v mod 3^(j-1).  We ask how much L older, disjoint ternary digits
predict three fixed-alphabet future labels beyond a bounded current state:

* the r-trit descendant location;
* the future minimum/argmin label (seven masks, including ties); and
* a defect-severity bin using the fixed rational thresholds
  1/200, 1/100, 1/50, 1/25, 2/25.

The principal current state is the rolling two-trit window R_2.  Two stronger
controls add (i) the exact bounded transport/branch carry signature and (ii)
the current minimum mask and severity bin.  The carry signature is derived
from the literal maps, not called a carry merely because it is a digit block.

Every partition and contingency mass is an exact integer.  The primary score
is the Bayes/Brier collision gain

  sum_(s,h,y) W_shy^2/(W W_sh) - sum_(s,y) W_sy^2/(W W_s).

Rather than form an enormous common denominator, the script encloses each
score by exact rational endpoints using integer quotient/remainder arithmetic.
The printed mutual information uses logarithms of the exact integer cells and
is explicitly floating.  Nested histories supply short-block Markov nulls.
Whole child triples are also permuted inside current-state (or one-step-history)
strata, preserving the corresponding exact weighted marginals and the full
parent-ID/oracle heterogeneity while destroying their association with older
history.

The portable default is k=12,...,15.  SHA-pinned local sidecars make higher
levels available with ``--levels 16 17 18 19``; use ``--headline-only`` or
``--skip-surrogates`` first because terminal arrays grow exponentially.

This is a finite selected-record diagnostic.  Coarse genealogy minima are not
lower-level KL policies, different k records are not one trajectory, and the
floating information values are not all-level estimates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np

from multiscale_genealogy import load_certificate


HERE = Path(__file__).resolve().parent
DEFAULT_LEVELS = (12, 13, 14, 15)
MANIFEST_SHA256 = {
    12: "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f",
    13: "32f22a8bfc6e7962443ce0da0fd28bdb5d2a56748e0ea832a9135a45391fc7b7",
    14: "08ac51b3f259798b9bf979388ec5f7f590c26025cc323ee331867d20d616285f",
    15: "fdf28dbd79aa50334e4f643e51232bebb46d32e6e18d40acd144101613c87ae1",
    16: "5e4aa8081659c0d33ce0b50a6c3a211d62c508fcccc602dd2b33fa07dede170e",
    17: "56cf23c9ea2e61006535a3a65f952136c671d8f770df37dbc647d0133c462183",
    18: "4c064a165c680f4eab05b58b1cd49ba27de37fa15c3b093ea70bda711b406a6f",
    19: "a37716cc508410ec6043ff153c2f2b2527b25b53220fa9827d79d3145f0641fb",
}
EXPECTED_POLICY_COUNTS = {
    12: (20_037, 19_545, 19_467),
    13: (58_821, 58_835, 59_491),
    14: (176_945, 177_415, 177_081),
    15: (531_226, 532_339, 530_758),
}
SEVERITY_THRESHOLDS = ((1, 200), (1, 100), (1, 50), (1, 25), (2, 25))
SEVERITY_CARD = len(SEVERITY_THRESHOLDS) + 1
MASK_CARD = 7
MASK_TO_LABEL = np.asarray((-1, 0, 1, 3, 2, 4, 5, 6), dtype=np.int8)
RADIX = 1 << 20
FLOAT_EXACT_INT = 2**53 - 1
INT64_MAX = np.iinfo(np.int64).max
SCORE_SCALE = 10**15
BITS = math.log(2.0)


@dataclass(frozen=True)
class Features:
    defect: np.ndarray
    mask: np.ndarray
    label: np.ndarray
    severity: np.ndarray


@dataclass(frozen=True)
class ScoreInterval:
    lower_num: int
    upper_num: int
    denominator: int

    @property
    def lower(self) -> float:
        return self.lower_num / self.denominator

    @property
    def upper(self) -> float:
        return self.upper_num / self.denominator

    @property
    def midpoint(self) -> float:
        return (self.lower_num + self.upper_num) / (2 * self.denominator)


@dataclass(frozen=True)
class Metric:
    gain: ScoreInterval
    gain_float: float
    cmi_bits: float
    conditional_entropy_bits: float
    contexts: int
    singleton_mass_fraction: float
    mass_below_eight_fraction: float
    exact_independence: bool
    table_digest: str


@dataclass(frozen=True)
class HeldoutMetric:
    gain: ScoreInterval
    coverage: float


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def as_python_ints(values: np.ndarray) -> Iterable[int]:
    return (int(value) for value in values)


def coarsen_exact(children: np.ndarray) -> np.ndarray:
    if len(children) % 3:
        raise AssertionError("3-adic level length is not divisible by three")
    triples = children.reshape(3, -1)
    if children.dtype != object and int(children.max()) <= INT64_MAX // 3:
        parents = triples.sum(axis=0, dtype=np.int64)
        if not np.array_equal(
            parents,
            triples[0] + triples[1] + triples[2],
        ):
            raise AssertionError("vectorized child sum failed")
        return parents
    parents = np.fromiter(
        (
            int(triples[0, index])
            + int(triples[1, index])
            + int(triples[2, index])
            for index in range(triples.shape[1])
        ),
        dtype=object,
        count=triples.shape[1],
    )
    if max(as_python_ints(parents), default=0) <= INT64_MAX:
        return parents.astype(np.int64)
    return parents


def exact_threshold(
    defect: np.ndarray, parent: np.ndarray, numerator: int, denominator: int
) -> np.ndarray:
    """Classify defect/(3 parent) > numerator/denominator exactly."""

    multiplier = max(denominator, 3 * numerator)
    if (
        parent.dtype != object
        and defect.dtype != object
        and int(parent.max(initial=0)) <= INT64_MAX // multiplier
        and int(defect.max(initial=0)) <= INT64_MAX // multiplier
    ):
        return denominator * defect > 3 * numerator * parent
    return np.fromiter(
        (
            denominator * int(value) > 3 * numerator * int(total)
            for value, total in zip(defect, parent, strict=True)
        ),
        dtype=bool,
        count=len(parent),
    )


def make_features(parent: np.ndarray, children: np.ndarray) -> Features:
    triples = children.reshape(3, -1)
    if triples.shape[1] != len(parent):
        raise AssertionError("feature parent/child shape mismatch")
    minima = triples.min(axis=0)
    defect = parent - 3 * minima
    if any(int(value) < 0 for value in defect):
        raise AssertionError("negative fiber defect")
    mask = (
        (triples[0] == minima).astype(np.int8)
        + 2 * (triples[1] == minima).astype(np.int8)
        + 4 * (triples[2] == minima).astype(np.int8)
    )
    if np.any((mask < 1) | (mask > 7)):
        raise AssertionError("invalid minimum mask")
    severity = np.zeros(len(parent), dtype=np.int8)
    for numerator, denominator in SEVERITY_THRESHOLDS:
        severity += exact_threshold(defect, parent, numerator, denominator)
    label = MASK_TO_LABEL[mask]
    if np.any(label < 0):
        raise AssertionError("minimum-mask encoding failed")
    return Features(defect=defect, mask=mask, label=label, severity=severity)


def build_hierarchy(
    level: int, minimum_level: int
) -> tuple[dict[int, np.ndarray], dict[int, Features], str]:
    values, source_name, source_sha, hash_verified, _ = load_certificate(
        level, verify_sha=True
    )
    if not hash_verified:
        raise AssertionError("certificate loader did not verify its source")
    manifest = HERE / f"cert_k{level}.json"
    if level in MANIFEST_SHA256:
        actual = sha256(manifest)
        if actual != MANIFEST_SHA256[level]:
            raise AssertionError(f"k={level} manifest hash changed: {actual}")

    hierarchy: dict[int, np.ndarray] = {level: np.asarray(values)}
    for depth in range(level - 1, minimum_level - 1, -1):
        hierarchy[depth] = coarsen_exact(hierarchy[depth + 1])
    features = {
        depth: make_features(hierarchy[depth], hierarchy[depth + 1])
        for depth in range(minimum_level, level)
    }
    terminal = features[level - 1]
    if np.any(~np.isin(terminal.mask, np.asarray((1, 2, 4), dtype=np.int8))):
        raise AssertionError("terminal certificate has a tied minimum")
    if level in EXPECTED_POLICY_COUNTS:
        counts = tuple(
            int(np.count_nonzero(terminal.label == label)) for label in range(3)
        )
        if counts != EXPECTED_POLICY_COUNTS[level]:
            raise AssertionError(f"k={level} policy counts changed: {counts}")
    return hierarchy, features, f"{source_name}:{source_sha}"


def recent_window(indices: np.ndarray, depth: int, width: int) -> np.ndarray:
    digit_count = depth - 1
    if digit_count < width:
        raise ValueError("recent window is wider than the current residue")
    return indices // (3 ** (digit_count - width))


def carry_signature(indices: np.ndarray, depth: int) -> np.ndarray:
    """Exact finite signature of the transport and optional branch map.

    The signature records the row residue mod 9, the outgoing row type, the
    carry discarded by ``4p+2 mod 3^(depth-1)``, and the carry discarded by
    the type-2/type-8 branch target map (with one neutral sentinel).  Its
    alphabet has a fixed declared size 9*3*4*5=540 at every depth.
    """

    digit_count = depth - 1
    modulus = 3**digit_count
    branch_modulus = modulus // 3
    index = indices.astype(np.int64, copy=False)
    transport_raw = 4 * index + 2
    transport_source = transport_raw % modulus
    transport_carry = transport_raw // modulus
    if not np.array_equal(transport_source, (4 * index + 2) % modulus):
        raise AssertionError("transport carry reconstruction failed")

    kind = index % 3
    branch_carry = np.full(len(index), -1, dtype=np.int64)
    type_two = kind == 0
    quotient_two = index[type_two] // 3
    branch_raw_two = 4 * quotient_two
    if not np.array_equal(
        branch_raw_two % branch_modulus,
        (4 * quotient_two) % branch_modulus,
    ):
        raise AssertionError("type-2 branch carry reconstruction failed")
    branch_carry[type_two] = branch_raw_two // branch_modulus

    type_eight = kind == 2
    quotient_eight = (index[type_eight] - 2) // 3
    branch_raw_eight = 2 * quotient_eight + 1
    if not np.array_equal(
        branch_raw_eight % branch_modulus,
        (2 * quotient_eight + 1) % branch_modulus,
    ):
        raise AssertionError("type-8 branch carry reconstruction failed")
    branch_carry[type_eight] = branch_raw_eight // branch_modulus
    if np.any((transport_carry < 0) | (transport_carry >= 4)) or np.any(
        (branch_carry < -1) | (branch_carry >= 4)
    ):
        raise AssertionError("carry escaped its fixed alphabet")
    result = (
        (((index % 9) * 3 + kind) * 4 + transport_carry) * 5
        + (branch_carry + 1)
    )
    return result.astype(np.int16)


CARRY_CARD = 9 * 3 * 4 * 5


def state_codes(
    indices: np.ndarray,
    depth: int,
    features: Features,
    width: int,
    variant: str,
) -> tuple[np.ndarray, int]:
    recent = recent_window(indices, depth, width).astype(np.int64)
    recent_card = 3**width
    if variant == "recent":
        return recent, recent_card
    if variant == "transport":
        modulus = 3 ** (depth - 1)
        transport_carry = (4 * indices + 2) // modulus
        if np.any((transport_carry < 0) | (transport_carry >= 4)):
            raise AssertionError("transport carry escaped its fixed alphabet")
        return recent * 4 + transport_carry, recent_card * 4
    signature = carry_signature(indices, depth).astype(np.int64)
    code = recent * CARRY_CARD + signature
    card = recent_card * CARRY_CARD
    if variant == "carry":
        return code, card
    if variant == "current":
        code = (code * MASK_CARD + features.label[indices]) * SEVERITY_CARD
        code += features.severity[indices]
        return code, card * MASK_CARD * SEVERITY_CARD
    raise ValueError(f"unknown state variant {variant!r}")


def history_codes(
    indices: np.ndarray,
    current_depth: int,
    history_length: int,
    width: int,
) -> tuple[np.ndarray, int]:
    code = np.zeros(len(indices), dtype=np.int64)
    for step in range(1, history_length + 1):
        exponent = current_depth - 1 - width - step
        if exponent < 0:
            raise ValueError("history overlaps the root boundary")
        digit = (indices // (3**exponent)) % 3
        code = 3 * code + digit
    return code, 3**history_length


def dense_state_codes(codes: np.ndarray, declared_card: int) -> tuple[np.ndarray, int]:
    if np.any((codes < 0) | (codes >= declared_card)):
        raise AssertionError("state code escaped declared alphabet")
    present = np.zeros(declared_card, dtype=bool)
    present[codes] = True
    lookup = np.full(declared_card, -1, dtype=np.int64)
    lookup[present] = np.arange(int(present.sum()), dtype=np.int64)
    dense = lookup[codes]
    if np.any(dense < 0):
        raise AssertionError("state densification failed")
    return dense, int(present.sum())


def exact_bincount(
    codes: np.ndarray, weights: np.ndarray, cardinality: int
) -> tuple[np.ndarray, np.ndarray]:
    """Return exact radix-high/low integer sums as binary64 integer arrays."""

    if len(codes) != len(weights):
        raise AssertionError("code/weight length mismatch")
    if np.any((codes < 0) | (codes >= cardinality)):
        raise AssertionError("contingency code escaped declared cardinality")
    if weights.dtype == object:
        high = np.fromiter(
            (int(value) // RADIX for value in weights),
            dtype=np.int64,
            count=len(weights),
        )
        low = np.fromiter(
            (int(value) % RADIX for value in weights),
            dtype=np.int64,
            count=len(weights),
        )
    else:
        if np.any(weights < 0):
            raise AssertionError("negative predictive weight")
        high = weights // RADIX
        low = weights - high * RADIX
    high_total = sum(as_python_ints(high))
    low_total = sum(as_python_ints(low))
    if high_total > FLOAT_EXACT_INT or low_total > FLOAT_EXACT_INT:
        raise OverflowError(
            "radix limbs exceed the binary64 exact-integer range; "
            "increase RADIX or add chunking"
        )
    high_bins = np.bincount(
        codes, weights=high.astype(np.float64), minlength=cardinality
    )
    low_bins = np.bincount(
        codes, weights=low.astype(np.float64), minlength=cardinality
    )
    if np.any(high_bins != np.floor(high_bins)) or np.any(
        low_bins != np.floor(low_bins)
    ):
        raise AssertionError("binary64 limb accumulation lost integrality")
    if int(high_bins.sum()) != high_total or int(low_bins.sum()) != low_total:
        raise AssertionError("exact histogram total mismatch")
    return high_bins, low_bins


def unpack_masses(high: np.ndarray, low: np.ndarray) -> list[int]:
    return [
        int(high_part) * RADIX + int(low_part)
        for high_part, low_part in zip(high, low, strict=True)
    ]


def table_hash(*tables: tuple[np.ndarray, np.ndarray]) -> str:
    digest = hashlib.sha256()
    for high, low in tables:
        nonzero = np.flatnonzero((high != 0) | (low != 0))
        for index in nonzero:
            digest.update(int(index).to_bytes(8, "little", signed=False))
            value = int(high[index]) * RADIX + int(low[index])
            encoded = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "little")
            digest.update(len(encoded).to_bytes(4, "little"))
            digest.update(encoded)
        digest.update(b"|")
    return digest.hexdigest()


def score_numerators(
    joint_masses: list[int], context_masses: list[int], y_card: int
) -> tuple[int, int, float]:
    if len(joint_masses) != len(context_masses) * y_card:
        raise AssertionError("score table shape mismatch")
    quotient_sum = 0
    remainder_count = 0
    floating_terms: list[float] = []
    for context, total in enumerate(context_masses):
        start = context * y_card
        cells = joint_masses[start : start + y_card]
        if sum(cells) != total:
            raise AssertionError("joint row does not reproduce context mass")
        if total == 0:
            continue
        square_sum = sum(value * value for value in cells)
        quotient, remainder = divmod(SCORE_SCALE * square_sum, total)
        quotient_sum += quotient
        remainder_count += int(remainder != 0)
        floating_terms.append(square_sum / total)
    return quotient_sum, remainder_count, math.fsum(floating_terms)


def conditional_information_bits(
    s_masses: list[int],
    sh_masses: list[int],
    sy_masses: list[int],
    shy_masses: list[int],
    h_card: int,
    y_card: int,
    total: int,
) -> tuple[float, float, bool]:
    information_terms: list[float] = []
    entropy_terms: list[float] = []
    independent = True
    for state, state_mass in enumerate(s_masses):
        if state_mass == 0:
            continue
        for label in range(y_card):
            value = sy_masses[state * y_card + label]
            if value:
                probability = value / total
                entropy_terms.append(
                    -probability * math.log(value / state_mass)
                )
        for history in range(h_card):
            context = state * h_card + history
            context_mass = sh_masses[context]
            if context_mass == 0:
                continue
            for label in range(y_card):
                joint = shy_masses[context * y_card + label]
                marginal = sy_masses[state * y_card + label]
                if joint * state_mass != marginal * context_mass:
                    independent = False
                if joint:
                    information_terms.append(
                        (joint / total)
                        * math.log(
                            (joint * state_mass) / (context_mass * marginal)
                        )
                    )
    return (
        math.fsum(information_terms) / BITS,
        math.fsum(entropy_terms) / BITS,
        independent,
    )


def metric(
    state: np.ndarray,
    state_card: int,
    history: np.ndarray,
    history_card: int,
    target: np.ndarray,
    target_card: int,
    weights: np.ndarray,
    ancestor_count: int,
) -> Metric:
    dense_state, observed_states = dense_state_codes(state, state_card)
    sh = dense_state * history_card + history
    sy = dense_state * target_card + target
    shy = sh * target_card + target
    s_table = exact_bincount(dense_state, weights, observed_states)
    sh_table = exact_bincount(sh, weights, observed_states * history_card)
    sy_table = exact_bincount(sy, weights, observed_states * target_card)
    shy_table = exact_bincount(
        shy, weights, observed_states * history_card * target_card
    )
    s_masses = unpack_masses(*s_table)
    sh_masses = unpack_masses(*sh_table)
    sy_masses = unpack_masses(*sy_table)
    shy_masses = unpack_masses(*shy_table)
    total = sum(s_masses)
    if total <= 0 or sum(sh_masses) != total or sum(sy_masses) != total:
        raise AssertionError("contingency totals disagree")
    if sum(shy_masses) != total or total != sum(as_python_ints(weights)):
        raise AssertionError("joint contingency lost weight")

    fine_q, fine_r, fine_float = score_numerators(
        shy_masses, sh_masses, target_card
    )
    coarse_q, coarse_r, coarse_float = score_numerators(
        sy_masses, s_masses, target_card
    )
    denominator = SCORE_SCALE * total
    gain = ScoreInterval(
        lower_num=fine_q - coarse_q - coarse_r,
        upper_num=fine_q + fine_r - coarse_q,
        denominator=denominator,
    )
    cmi_bits, conditional_entropy_bits, independent = conditional_information_bits(
        s_masses,
        sh_masses,
        sy_masses,
        shy_masses,
        history_card,
        target_card,
        total,
    )
    if gain.upper < -1e-15:
        raise AssertionError("Brier gain is negative")
    if independent and (abs(cmi_bits) > 2e-12 or gain.lower > 0 or gain.upper < 0):
        raise AssertionError("exact-independence null did not score zero")

    # Context support is counted in distinct current ancestors, not repeated
    # future descendants.  All future labels under one ancestor share S,H.
    current_sh = sh[:ancestor_count]
    # For the block layout v=p+location*ancestor_count, the first block has
    # exactly one representative of every ancestor.
    support = np.bincount(
        current_sh, minlength=observed_states * history_card
    )
    if int(support.sum()) != ancestor_count:
        raise AssertionError("ancestor context support mismatch")
    singleton = support == 1
    below_eight = (support > 0) & (support < 8)
    singleton_mass = sum(
        mass for mass, flag in zip(sh_masses, singleton, strict=True) if flag
    )
    below_eight_mass = sum(
        mass for mass, flag in zip(sh_masses, below_eight, strict=True) if flag
    )
    return Metric(
        gain=gain,
        gain_float=(fine_float - coarse_float) / total,
        cmi_bits=cmi_bits,
        conditional_entropy_bits=conditional_entropy_bits,
        contexts=int(np.count_nonzero(support)),
        singleton_mass_fraction=singleton_mass / total,
        mass_below_eight_fraction=below_eight_mass / total,
        exact_independence=independent,
        table_digest=table_hash(s_table, sh_table, sy_table, shy_table),
    )


def predictive_utility_numerators(
    train_joint: list[int],
    train_context: list[int],
    test_joint: list[int],
    y_card: int,
) -> tuple[int, int, int]:
    """Enclose unnormalized held-out quadratic utility exactly.

    For a training conditional law q and test masses n_y, the (constant-free)
    Brier utility is ``sum_y n_y (2 q_y-||q||_2^2)``.  Each context contributes
    one rational with denominator equal to the squared training mass.
    """

    if len(train_joint) != len(train_context) * y_card:
        raise AssertionError("held-out training table shape mismatch")
    if len(test_joint) != len(train_joint):
        raise AssertionError("held-out test table shape mismatch")
    quotient_sum = 0
    remainder_count = 0
    test_total = 0
    for context, train_total in enumerate(train_context):
        if train_total == 0:
            continue
        start = context * y_card
        train = train_joint[start : start + y_card]
        test = test_joint[start : start + y_card]
        if sum(train) != train_total:
            raise AssertionError("held-out train row mismatch")
        row_test_total = sum(test)
        test_total += row_test_total
        if row_test_total == 0:
            continue
        cross = sum(left * right for left, right in zip(test, train, strict=True))
        train_square = sum(value * value for value in train)
        numerator = (
            2 * train_total * cross - row_test_total * train_square
        )
        denominator = train_total * train_total
        quotient, remainder = divmod(SCORE_SCALE * numerator, denominator)
        quotient_sum += quotient
        remainder_count += int(remainder != 0)
    return quotient_sum, remainder_count, test_total


def blocked_heldout_brier(
    state: np.ndarray,
    state_card: int,
    history: np.ndarray,
    history_card: int,
    target: np.ndarray,
    target_card: int,
    weights: np.ndarray,
    folds: np.ndarray,
) -> HeldoutMetric:
    """Three-fold exact Brier gain, training on the other two digit blocks."""

    dense_state, observed_states = dense_state_codes(state, state_card)
    context = dense_state * history_card + history
    context_target = context * target_card + target
    state_target = dense_state * target_card + target
    context_card = observed_states * history_card
    total_weight = sum(as_python_ints(weights))
    fine_q = fine_r = base_q = base_r = covered_total = 0
    for fold in range(3):
        train = folds != fold
        test = folds == fold
        train_context_table = exact_bincount(
            context[train], weights[train], context_card
        )
        train_joint_table = exact_bincount(
            context_target[train],
            weights[train],
            context_card * target_card,
        )
        train_state_table = exact_bincount(
            dense_state[train], weights[train], observed_states
        )
        train_state_joint_table = exact_bincount(
            state_target[train],
            weights[train],
            observed_states * target_card,
        )
        test_joint_table = exact_bincount(
            context_target[test],
            weights[test],
            context_card * target_card,
        )
        train_context = unpack_masses(*train_context_table)
        train_joint = unpack_masses(*train_joint_table)
        train_state = unpack_masses(*train_state_table)
        train_state_joint = unpack_masses(*train_state_joint_table)
        test_joint = unpack_masses(*test_joint_table)

        # Fine coverage requires that the exact (S,H) context occurred in the
        # two training folds.  Evaluate the baseline on precisely the same
        # covered test mass.
        covered_state_joint = [0] * (observed_states * target_card)
        covered_joint = [0] * len(test_joint)
        for context_index, train_mass in enumerate(train_context):
            if train_mass == 0:
                continue
            state_index = context_index // history_card
            start = context_index * target_card
            for label in range(target_card):
                value = test_joint[start + label]
                covered_joint[start + label] = value
                covered_state_joint[state_index * target_card + label] += value
        fq, fr, fine_total = predictive_utility_numerators(
            train_joint, train_context, covered_joint, target_card
        )
        bq, br, base_total = predictive_utility_numerators(
            train_state_joint,
            train_state,
            covered_state_joint,
            target_card,
        )
        if fine_total != base_total:
            raise AssertionError("fine/base held-out coverage differs")
        fine_q += fq
        fine_r += fr
        base_q += bq
        base_r += br
        covered_total += fine_total
    if covered_total <= 0:
        raise AssertionError("blocked holdout has zero covered mass")
    return HeldoutMetric(
        gain=ScoreInterval(
            lower_num=fine_q - base_q - base_r,
            upper_num=fine_q + fine_r - base_q,
            denominator=SCORE_SCALE * covered_total,
        ),
        coverage=covered_total / total_weight,
    )


def terminal_blocked_holdouts(
    level: int,
    width: int,
    history_length: int,
    features: dict[int, Features],
    state_variant: str = "transport",
) -> dict[str, HeldoutMetric]:
    future_depth = level - 1
    current_depth = future_depth - 1
    ancestor_count = 3 ** (current_depth - 1)
    future_count = 3 * ancestor_count
    parents = np.arange(ancestor_count, dtype=np.int64)
    future_indices = np.arange(future_count, dtype=np.int64)
    ancestors = future_indices % ancestor_count
    state, state_card = state_codes(
        ancestors,
        current_depth,
        features[current_depth],
        width,
        state_variant,
    )
    history, history_card = history_codes(
        ancestors, current_depth, history_length, width
    )
    # The lowest residue digit is disjoint from the rolling top window and the
    # preceding top-history block.  It is not explicitly present in the
    # recommended R_2+transport-carry state and supplies a spatially blocked
    # fold.  (The carry is a derived bounded variable, not a digit alias.)
    parent_fold = parents % 3
    folds = np.tile(parent_fold, 3)
    targets = targets_for_cut(
        future_indices, ancestor_count, features[future_depth], 1
    )
    weights = np.asarray(features[future_depth].defect)
    return {
        name: blocked_heldout_brier(
            state,
            state_card,
            history,
            history_card,
            target,
            target_card,
            weights,
            folds,
        )
        for name, (target, target_card) in targets.items()
    }


def parent_oracle_metric(
    state: np.ndarray,
    state_card: int,
    target: np.ndarray,
    target_card: int,
    weights: np.ndarray,
    ancestor_count: int,
) -> Metric:
    """Conditional gain of the complete current parent address.

    This is an intentionally overpowered lookup oracle.  It measures the
    heterogeneity of whole child triples and is *not* a finite-description
    memory statistic.
    """

    dense_state, observed_states = dense_state_codes(state, state_card)
    parent = np.arange(len(target), dtype=np.int64) % ancestor_count
    parent_target = parent * target_card + target
    state_target = dense_state * target_card + target
    s_table = exact_bincount(dense_state, weights, observed_states)
    sy_table = exact_bincount(
        state_target, weights, observed_states * target_card
    )
    p_table = exact_bincount(parent, weights, ancestor_count)
    py_table = exact_bincount(
        parent_target, weights, ancestor_count * target_card
    )
    s_masses = unpack_masses(*s_table)
    sy_masses = unpack_masses(*sy_table)
    p_masses = unpack_masses(*p_table)
    py_masses = unpack_masses(*py_table)
    total = sum(s_masses)
    if total != sum(p_masses) or total != sum(py_masses):
        raise AssertionError("oracle contingency totals disagree")
    fine_q, fine_r, fine_float = score_numerators(
        py_masses, p_masses, target_card
    )
    coarse_q, coarse_r, coarse_float = score_numerators(
        sy_masses, s_masses, target_card
    )
    information_terms: list[float] = []
    entropy_terms: list[float] = []
    state_on_parent = dense_state[:ancestor_count]
    if not np.array_equal(dense_state, np.tile(state_on_parent, len(target) // ancestor_count)):
        raise AssertionError("oracle state is not constant on descendant blocks")
    for state_index, state_mass in enumerate(s_masses):
        if state_mass == 0:
            continue
        for label in range(target_card):
            value = sy_masses[state_index * target_card + label]
            if value:
                entropy_terms.append(
                    -(value / total) * math.log(value / state_mass)
                )
    independent = True
    for parent_index, parent_mass in enumerate(p_masses):
        if parent_mass == 0:
            continue
        state_index = int(state_on_parent[parent_index])
        state_mass = s_masses[state_index]
        for label in range(target_card):
            joint = py_masses[parent_index * target_card + label]
            marginal = sy_masses[state_index * target_card + label]
            if joint * state_mass != marginal * parent_mass:
                independent = False
            if joint:
                information_terms.append(
                    (joint / total)
                    * math.log(
                        (joint * state_mass) / (parent_mass * marginal)
                    )
                )
    return Metric(
        gain=ScoreInterval(
            lower_num=fine_q - coarse_q - coarse_r,
            upper_num=fine_q + fine_r - coarse_q,
            denominator=SCORE_SCALE * total,
        ),
        gain_float=(fine_float - coarse_float) / total,
        cmi_bits=math.fsum(information_terms) / BITS,
        conditional_entropy_bits=math.fsum(entropy_terms) / BITS,
        contexts=ancestor_count,
        singleton_mass_fraction=1.0,
        mass_below_eight_fraction=1.0,
        exact_independence=independent,
        table_digest=table_hash(s_table, sy_table, p_table, py_table),
    )


def terminal_parent_oracles(
    level: int,
    width: int,
    features: dict[int, Features],
    state_variant: str = "transport",
) -> dict[str, Metric]:
    future_depth = level - 1
    current_depth = future_depth - 1
    ancestor_count = 3 ** (current_depth - 1)
    future_count = 3 * ancestor_count
    future_indices = np.arange(future_count, dtype=np.int64)
    ancestors = future_indices % ancestor_count
    state, state_card = state_codes(
        ancestors,
        current_depth,
        features[current_depth],
        width,
        state_variant,
    )
    targets = targets_for_cut(
        future_indices, ancestor_count, features[future_depth], 1
    )
    weights = np.asarray(features[future_depth].defect)
    return {
        name: parent_oracle_metric(
            state,
            state_card,
            target,
            target_card,
            weights,
            ancestor_count,
        )
        for name, (target, target_card) in targets.items()
    }


def targets_for_cut(
    future_indices: np.ndarray,
    ancestor_count: int,
    future: Features,
    horizon: int,
) -> dict[str, tuple[np.ndarray, int]]:
    location = future_indices // ancestor_count
    if int(location.max(initial=0)) >= 3**horizon:
        raise AssertionError("future location escaped refinement horizon")
    return {
        "location": (location.astype(np.int64), 3**horizon),
        "policy": (future.label[future_indices].astype(np.int64), MASK_CARD),
        "severity": (
            future.severity[future_indices].astype(np.int64),
            SEVERITY_CARD,
        ),
    }


def analyze_cut(
    level: int,
    current_depth: int,
    horizon: int,
    history_length: int,
    width: int,
    state_variant: str,
    hierarchy: dict[int, np.ndarray],
    features: dict[int, Features],
    weight_kind: str = "defect",
) -> dict[str, Metric]:
    future_depth = current_depth + horizon
    future_count = 3 ** (future_depth - 1)
    ancestor_count = 3 ** (current_depth - 1)
    future_indices = np.arange(future_count, dtype=np.int64)
    ancestors = future_indices % ancestor_count
    state, state_card = state_codes(
        ancestors,
        current_depth,
        features[current_depth],
        width,
        state_variant,
    )
    history, history_card = history_codes(
        ancestors, current_depth, history_length, width
    )
    targets = targets_for_cut(
        future_indices, ancestor_count, features[future_depth], horizon
    )
    if weight_kind == "defect":
        weights = np.asarray(features[future_depth].defect)
    elif weight_kind == "mass":
        weights = np.asarray(hierarchy[future_depth])
    elif weight_kind == "uniform":
        weights = np.ones(future_count, dtype=np.int64)
    else:
        raise ValueError(f"unknown weight kind {weight_kind!r}")
    if len(weights) != future_count:
        raise AssertionError("future weight length mismatch")
    return {
        name: metric(
            state,
            state_card,
            history,
            history_card,
            target,
            target_card,
            weights,
            ancestor_count,
        )
        for name, (target, target_card) in targets.items()
    }


def permute_parent_triples(
    state_on_parents: np.ndarray, seed: int
) -> np.ndarray:
    """A deterministic bijection of parents inside every current-state cell."""

    result = np.empty(len(state_on_parents), dtype=np.int64)
    for state in np.unique(state_on_parents):
        indices = np.flatnonzero(state_on_parents == state)
        size = len(indices)
        if size <= 1:
            result[indices] = indices
            continue
        multiplier = (0x9E3779B1 + 2 * seed) % size
        if multiplier == 0:
            multiplier = 1
        while math.gcd(multiplier, size) != 1:
            multiplier = (multiplier + 1) % size
            if multiplier == 0:
                multiplier = 1
        shift = (0x85EBCA77 * (seed + 1)) % size
        ranks = (multiplier * np.arange(size, dtype=np.int64) + shift) % size
        result[indices] = indices[ranks]
    if np.unique(result).shape[0] != len(result):
        raise AssertionError("stratified parent map is not a permutation")
    if np.any(state_on_parents[result] != state_on_parents):
        raise AssertionError("stratified permutation changed current state")
    return result


def surrogate_metrics(
    level: int,
    width: int,
    history_length: int,
    preserve_history: int,
    features: dict[int, Features],
    hierarchy: dict[int, np.ndarray],
    seeds: tuple[int, ...] = (1, 2, 3),
) -> dict[str, list[Metric]]:
    """Permute complete r=1 child triples within S or (S,H_q) strata."""

    future_depth = level - 1
    current_depth = future_depth - 1
    ancestor_count = 3 ** (current_depth - 1)
    future_count = 3 * ancestor_count
    parents = np.arange(ancestor_count, dtype=np.int64)
    future_indices = np.arange(future_count, dtype=np.int64)
    ancestors = future_indices % ancestor_count
    state_parent, state_card = state_codes(
        parents,
        current_depth,
        features[current_depth],
        width,
        "recent",
    )
    history_parent, history_card = history_codes(
        parents, current_depth, history_length, width
    )
    if preserve_history:
        short, short_card = history_codes(
            parents, current_depth, preserve_history, width
        )
        strata = state_parent * short_card + short
    else:
        strata = state_parent
    state = np.tile(state_parent, 3)
    history = np.tile(history_parent, 3)
    targets = targets_for_cut(
        future_indices, ancestor_count, features[future_depth], 1
    )
    original_weights = np.asarray(features[future_depth].defect)
    original_state_target: dict[str, str] = {}
    output = {name: [] for name in targets}
    for seed in seeds:
        source_parent = permute_parent_triples(strata, seed)
        source = np.concatenate(
            (source_parent, source_parent + ancestor_count, source_parent + 2 * ancestor_count)
        )
        weights = original_weights[source]
        for name, (target, target_card) in targets.items():
            permuted_target = target[source]
            result = metric(
                state,
                state_card,
                history,
                history_card,
                permuted_target,
                target_card,
                weights,
                ancestor_count,
            )
            output[name].append(result)
            # The exact (S,Y) weighted marginal must be invariant because
            # whole triples move only within S (or a refinement of S).
            dense, observed = dense_state_codes(state, state_card)
            original_code = dense * target_card + target
            permuted_code = dense * target_card + permuted_target
            original_table = exact_bincount(
                original_code,
                original_weights,
                observed * target_card,
            )
            permuted_table = exact_bincount(
                permuted_code,
                weights,
                observed * target_card,
            )
            if not (
                np.array_equal(original_table[0], permuted_table[0])
                and np.array_equal(original_table[1], permuted_table[1])
            ):
                raise AssertionError("surrogate changed the exact S-Y marginal")
            original_state_target.setdefault(name, table_hash(original_table))
            if original_state_target[name] != table_hash(permuted_table):
                raise AssertionError("surrogate marginal digest changed")
    return output


def print_metric(prefix: str, result: Metric) -> None:
    explained = (
        result.cmi_bits / result.conditional_entropy_bits
        if result.conditional_entropy_bits > 0
        else 0.0
    )
    print(
        f"{prefix} Brier=[{result.gain.lower:.9g},{result.gain.upper:.9g}] "
        f"CMI={result.cmi_bits:.9g} bits ({explained:.3%} of H(Y|S)); "
        f"contexts={result.contexts:,}, singleton_mass={result.singleton_mass_fraction:.3g}, "
        f"mass_support<8={result.mass_below_eight_fraction:.3g}"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", nargs="+", type=int, default=DEFAULT_LEVELS)
    parser.add_argument("--horizons", nargs="+", type=int, default=(1, 2, 3))
    parser.add_argument("--width", type=int, default=2)
    parser.add_argument("--max-history", type=int, default=4)
    parser.add_argument(
        "--headline-only",
        action="store_true",
        help="run terminal defect-weighted fixed-horizon rows only",
    )
    parser.add_argument(
        "--skip-surrogates",
        action="store_true",
        help="skip the terminal whole-child-triple permutation controls",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.width < 1 or args.max_history < 1:
        raise ValueError("width and history length must be positive")
    if any(horizon < 1 for horizon in args.horizons):
        raise ValueError("refinement horizons must be positive")

    run_digest = hashlib.sha256()
    all_rows: dict[tuple[int, int, int, str, str], Metric] = {}
    for level in args.levels:
        minimum_current = level - 1 - max(args.horizons)
        if not args.headline_only:
            minimum_current = min(
                minimum_current, args.width + args.max_history + 2
            )
        minimum_level = max(2, minimum_current)
        hierarchy, features, provenance = build_hierarchy(level, minimum_level)
        terminal = features[level - 1]
        terminal_defect = sum(as_python_ints(terminal.defect))
        print(
            f"PASS k={level}: {provenance}; exact genealogy through depth "
            f"{minimum_level}; terminal fibers={len(terminal.defect):,}; "
            f"defect mass={terminal_defect}"
        )
        run_digest.update(provenance.encode())

        print("  TERMINAL FIXED-HORIZON, S=R_2, defect weights")
        for horizon in args.horizons:
            future_depth = level - 1
            current_depth = future_depth - horizon
            if current_depth <= args.width + args.max_history:
                raise ValueError(
                    f"k={level}, r={horizon} has insufficient disjoint history"
                )
            histories: dict[int, dict[str, Metric]] = {}
            for history_length in range(1, args.max_history + 1):
                rows = analyze_cut(
                    level,
                    current_depth,
                    horizon,
                    history_length,
                    args.width,
                    "recent",
                    hierarchy,
                    features,
                )
                histories[history_length] = rows
                for target_name, result in rows.items():
                    all_rows[(level, horizon, history_length, "recent", target_name)] = result
                    run_digest.update(bytes.fromhex(result.table_digest))
            for history_length in (1, args.max_history):
                for target_name in ("location", "policy", "severity"):
                    print_metric(
                        f"    r={horizon} L={history_length} {target_name:8s}",
                        histories[history_length][target_name],
                    )
            for target_name in ("location", "policy", "severity"):
                increments = [histories[1][target_name].cmi_bits]
                increments.extend(
                    histories[length][target_name].cmi_bits
                    - histories[length - 1][target_name].cmi_bits
                    for length in range(2, args.max_history + 1)
                )
                if min(increments) < -2e-10:
                    raise AssertionError("nested-history CMI decreased")
                print(
                    f"    r={horizon} {target_name:8s} short-block CMI gains "
                    + ",".join(f"{value:.4g}" for value in increments)
                    + " bits"
                )

        # The central comparison: a fixed four-trit description versus the
        # complete parent address, followed by a genuinely out-of-block Brier
        # check.  The oracle is expected to stay large even when fixed-memory
        # gain disappears; it is whole-triple heterogeneity, not compression.
        terminal_current = level - 2
        fixed_terminal = analyze_cut(
            level,
            terminal_current,
            1,
            args.max_history,
            args.width,
            "transport",
            hierarchy,
            features,
        )
        oracles = terminal_parent_oracles(level, args.width, features)
        holdouts = terminal_blocked_holdouts(
            level, args.width, args.max_history, features
        )
        print("  FIXED MEMORY vs PARENT-ID ORACLE vs BLOCKED HOLDOUT, terminal r=1")
        for target_name in ("location", "policy", "severity"):
            fixed = fixed_terminal[target_name]
            oracle = oracles[target_name]
            holdout = holdouts[target_name]
            fraction = (
                fixed.cmi_bits / oracle.cmi_bits if oracle.cmi_bits > 0 else 0.0
            )
            print(
                f"    {target_name:8s} I_L={fixed.cmi_bits:.9g} bits; "
                f"I_parent={oracle.cmi_bits:.9g}; captured={fraction:.4%}; "
                f"heldout_Brier=[{holdout.gain.lower:.9g},"
                f"{holdout.gain.upper:.9g}], coverage={holdout.coverage:.6f}"
            )
            run_digest.update(bytes.fromhex(fixed.table_digest))
            run_digest.update(bytes.fromhex(oracle.table_digest))

        if not args.headline_only:
            # State sensitivity at the most literal terminal one-step cut.
            print("  BOUNDED-STATE SENSITIVITY, terminal r=1, L=max")
            current_depth = level - 2
            for variant in ("recent", "transport", "carry", "current"):
                rows = analyze_cut(
                    level,
                    terminal_current,
                    1,
                    args.max_history,
                    args.width,
                    variant,
                    hierarchy,
                    features,
                )
                for target_name in ("location", "policy", "severity"):
                    print_metric(
                        f"    S={variant:7s} {target_name:8s}", rows[target_name]
                    )
                    run_digest.update(bytes.fromhex(rows[target_name].table_digest))

            print("  WEIGHT CONTROLS, terminal r=1, L=max, S=R_2")
            for weight_kind in ("uniform", "mass", "defect"):
                rows = analyze_cut(
                    level,
                    current_depth,
                    1,
                    args.max_history,
                    args.width,
                    "recent",
                    hierarchy,
                    features,
                    weight_kind=weight_kind,
                )
                location = rows["location"]
                if weight_kind == "uniform" and not location.exact_independence:
                    raise AssertionError(
                        "uniform complete-tree future location was not independent"
                    )
                for target_name in ("location", "policy", "severity"):
                    print_metric(
                        f"    W={weight_kind:7s} {target_name:8s}", rows[target_name]
                    )

            # Canonical r=1 cut profile.  f=9 is the first depth at which a
            # two-trit window plus four older trits is disjoint from the root.
            print("  CUT PROFILE, r=1, L=max, S=R_2, defect weights")
            first_future = args.width + args.max_history + 3
            for future_depth in range(first_future, level):
                rows = analyze_cut(
                    level,
                    future_depth - 1,
                    1,
                    args.max_history,
                    args.width,
                    "recent",
                    hierarchy,
                    features,
                )
                print(
                    f"    future_depth={future_depth:2d} "
                    f"terminal_offset={level-1-future_depth:2d} "
                    f"I_loc={rows['location'].cmi_bits:.9g} "
                    f"I_policy={rows['policy'].cmi_bits:.9g} "
                    f"I_severity={rows['severity'].cmi_bits:.9g} bits"
                )

            if not args.skip_surrogates:
                print("  WHOLE-TRIPLE SURROGATES, terminal r=1, L=max")
                for preserve in (0, 1):
                    controls = surrogate_metrics(
                        level,
                        args.width,
                        args.max_history,
                        preserve,
                        features,
                        hierarchy,
                    )
                    for target_name in ("location", "policy", "severity"):
                        values = [row.cmi_bits for row in controls[target_name]]
                        print(
                            f"    preserve=S+H{preserve} {target_name:8s} "
                            f"CMI range=[{min(values):.9g},{max(values):.9g}] bits"
                        )

        del hierarchy, features

    print(f"PASS: canonical exact-table run digest {run_digest.hexdigest()}")
    print(
        "VERDICT SCOPE: all partitions, weights, marginal-preserving controls, "
        "and Brier enclosures above are exact finite computations; CMI uses "
        "floating logarithms.  Inspect fixed terminal offsets separately from "
        "fixed shallow cuts, and do not treat parent-ID/or singleton lookup "
        "gain as evidence for an infinite predictive state."
    )


if __name__ == "__main__":
    main()
