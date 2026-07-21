#!/usr/bin/env python3
"""Exact terminal minimum-defect audit for selected KL certificates.

For a level-k certificate, group the terminal triples as

    x_i(r) = C[r + i 3^(k-2)],  i = 0,1,2,
    P_r = x_0(r)+x_1(r)+x_2(r),
    m_r = min_i x_i(r),
    d_r = P_r-3m_r.

Under parent-mass weighting, the minimum defect ``u=1/3-min_i(x_i/P)`` has

    delta = E[u]   = sum_r d_r / (3T),
    E[u^2]         = (1/(9T)) sum_r d_r^2/P_r,
    T              = sum_r P_r.

The mean is an exact rational after cancellation.  For the second moment,
write ``d_r^2 = q_r P_r+s_r``.  Exact uint64-limb multiplication certifies
every quotient and gives the narrow rational enclosure

    sum q_r/(9T) <= E[u^2]
                    <= (sum q_r + #{r:s_r != 0})/(9T).

The terminal Pearson interval is imported from the independently generated,
SHA-pinned all-depth cache and fully recomputed with Python big integers at
k=12.  Its quotient/remainder convention is checked at every requested level.

Finally, summing the nonlinear KL operator gives

    Sigma = lambda^-2 - 1 + (w_2+w_8) sum_r m_r/T.

The certificate weights give an exact rational lower bound for Sigma.  Exact
integer power comparisons with

    log_2(3) < 125743/79335

give rational upper weights and hence an exact rational upper bound.  Floating
point is used to seed quotient/weight searches, to render already certified
rational quantities, and to sum bounded radix limbs whose integer totals are
proved below ``2^53``.  Every accepted quotient and weight endpoint is checked
with integer arithmetic.

This is a finite audit of the selected k=12,...,19 records, not an all-level
anti-concentration or rate theorem.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import resource
import sys
import time

import numpy as np

import multiscale_genealogy as genealogy


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = HERE / "analysis_cache" / "terminal_defect_statistics_exact.csv"
PEARSON_CACHE = HERE / "analysis_cache" / "chi_square_intervals_exact.csv"
PEARSON_CACHE_SHA256 = (
    "907c847e69cc6b0f6ab81d57d12f4ed2c411af8b4610149a51295232fe730f32"
)
EXPECTED_LEVELS = tuple(range(12, 20))
EXPECTED_MANIFEST_SHA256 = {
    12: "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f",
    13: "32f22a8bfc6e7962443ce0da0fd28bdb5d2a56748e0ea832a9135a45391fc7b7",
    14: "08ac51b3f259798b9bf979388ec5f7f590c26025cc323ee331867d20d616285f",
    15: "fdf28dbd79aa50334e4f643e51232bebb46d32e6e18d40acd144101613c87ae1",
    16: "5e4aa8081659c0d33ce0b50a6c3a211d62c508fcccc602dd2b33fa07dede170e",
    17: "56cf23c9ea2e61006535a3a65f952136c671d8f770df37dbc647d0133c462183",
    18: "4c064a165c680f4eab05b58b1cd49ba27de37fa15c3b093ea70bda711b406a6f",
    19: "a37716cc508410ec6043ff153c2f2b2527b25b53220fa9827d79d3145f0641fb",
}
EXPECTED_TOTAL_MASS = {
    12: 1_373_960_412_522_506_741,
    13: 4_475_321_486_922_343_160,
    14: 14_596_152_850_956_151_164,
    15: 47_049_100_452_382_107_460,
    16: 150_018_628_595_844_245_849,
    17: 479_475_287_827_487_078_427,
    18: 1_523_556_169_197_024_107_847,
    19: 4_845_180_013_388_557_558_821,
}

LOWER_ALPHA_NUMERATOR = 50_508
LOWER_ALPHA_DENOMINATOR = 31_867
UPPER_ALPHA_NUMERATOR = 125_743
UPPER_ALPHA_DENOMINATOR = 79_335

FLOAT_EXACT_INT = 2**53 - 1
RADIX = 2**20
UINT32_MASK = np.uint64(2**32 - 1)
UINT64_ONE = np.uint64(1)
MAX_QUOTIENT_CORRECTIONS = 16

FINITE_DELTA_CONSTANT = Fraction(21, 100)
FINITE_SECOND_MOMENT_CONSTANT = Fraction(1533, 1000)
FINITE_PEARSON_CONSTANT = Fraction(483, 1000)


def exact_nonnegative_sum(values: np.ndarray, chunk_size: int) -> int:
    """Sum nonnegative int64/uint64 values with exact binary64 radix limbs."""

    if len(values) == 0:
        return 0
    if values.dtype not in (np.dtype("int64"), np.dtype("uint64")):
        raise TypeError(f"expected int64 or uint64, got {values.dtype}")
    if values.dtype == np.dtype("int64") and int(values.min()) < 0:
        raise ValueError("exact_nonnegative_sum received a negative value")

    max_high_limb = max(1, int(values.max()) // RADIX)
    safe_chunk = min(
        chunk_size,
        FLOAT_EXACT_INT // max_high_limb,
        FLOAT_EXACT_INT // (RADIX - 1),
    )
    if safe_chunk <= 0:
        raise OverflowError("no binary64-exact radix chunk is available")

    total = 0
    for start in range(0, len(values), safe_chunk):
        block = values[start : start + safe_chunk]
        high = block // RADIX
        low = block - high * RADIX
        high_sum = float(np.sum(high, dtype=np.float64))
        low_sum = float(np.sum(low, dtype=np.float64))
        if not high_sum.is_integer() or not low_sum.is_integer():
            raise AssertionError("binary64 radix sum lost integrality")
        total += int(high_sum) * RADIX + int(low_sum)
    return total


def multiply_uint64_to_uint128(
    left: np.ndarray, right: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Return high and low uint64 limbs of exact pairwise products."""

    left = left.astype(np.uint64, copy=False)
    right = right.astype(np.uint64, copy=False)
    left_low = left & UINT32_MASK
    left_high = left >> np.uint64(32)
    right_low = right & UINT32_MASK
    right_high = right >> np.uint64(32)

    low_product = left_low * right_low
    cross_left = left_low * right_high
    cross_right = left_high * right_low
    high = left_high * right_high

    low = low_product + (cross_left << np.uint64(32))
    high += (cross_left >> np.uint64(32)) + (
        low < low_product
    ).astype(np.uint64)
    previous_low = low.copy()
    low += cross_right << np.uint64(32)
    high += (cross_right >> np.uint64(32)) + (
        low < previous_low
    ).astype(np.uint64)
    return high, low


def uint128_le(
    left_high: np.ndarray,
    left_low: np.ndarray,
    right_high: np.ndarray,
    right_low: np.ndarray,
) -> np.ndarray:
    return (left_high < right_high) | (
        (left_high == right_high) & (left_low <= right_low)
    )


def floor_square_over_denominator(
    values: np.ndarray, denominators: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Certify ``floor(values^2/denominators)`` using uint64 limbs.

    Binary64 supplies only the initial quotient.  Exact 128-bit comparisons
    correct and then certify it, so no correctness burden rests on the seed.
    The selected records satisfy ``0 <= values < denominators < 2^53``.
    """

    values = values.astype(np.uint64, copy=False)
    denominators = denominators.astype(np.uint64, copy=False)
    if len(values) != len(denominators):
        raise ValueError("numerator bases and denominators have different lengths")
    if len(values) == 0:
        return values.copy(), np.empty(0, dtype=bool)
    if int(denominators.min()) <= 0:
        raise ValueError("denominators must be positive")
    if int(denominators.max()) > FLOAT_EXACT_INT:
        raise OverflowError("terminal parent exceeds the exact binary64 seed range")
    if np.any(values >= denominators):
        raise AssertionError("minimum defect must satisfy 0 <= d < P")

    quotient = np.floor(
        values.astype(np.float64)
        * values.astype(np.float64)
        / denominators.astype(np.float64)
    ).astype(np.uint64)
    square_high, square_low = multiply_uint64_to_uint128(values, values)

    for _ in range(MAX_QUOTIENT_CORRECTIONS):
        product_high, product_low = multiply_uint64_to_uint128(
            quotient, denominators
        )
        too_high = ~uint128_le(
            product_high, product_low, square_high, square_low
        )
        if not np.any(too_high):
            break
        quotient[too_high] -= UINT64_ONE
    else:
        raise AssertionError("initial quotient needs too many downward corrections")

    for _ in range(MAX_QUOTIENT_CORRECTIONS):
        successor = quotient + UINT64_ONE
        product_high, product_low = multiply_uint64_to_uint128(
            successor, denominators
        )
        too_low = uint128_le(product_high, product_low, square_high, square_low)
        if not np.any(too_low):
            break
        quotient[too_low] += UINT64_ONE
    else:
        raise AssertionError("initial quotient needs too many upward corrections")

    product_high, product_low = multiply_uint64_to_uint128(
        quotient, denominators
    )
    if not np.all(
        uint128_le(product_high, product_low, square_high, square_low)
    ):
        raise AssertionError("certified quotient product exceeds the square")
    successor_high, successor_low = multiply_uint64_to_uint128(
        quotient + UINT64_ONE, denominators
    )
    if np.any(
        uint128_le(successor_high, successor_low, square_high, square_low)
    ):
        raise AssertionError("certified quotient is not maximal")

    zero_remainder = (product_high == square_high) & (
        product_low == square_low
    )
    return quotient, zero_remainder


def verify_limb_self_tests() -> None:
    rng = np.random.default_rng(20_260_721)
    full_left = (
        rng.integers(0, 2**32, size=4096, dtype=np.uint64) << np.uint64(32)
    ) | rng.integers(0, 2**32, size=4096, dtype=np.uint64)
    full_right = (
        rng.integers(0, 2**32, size=4096, dtype=np.uint64) << np.uint64(32)
    ) | rng.integers(0, 2**32, size=4096, dtype=np.uint64)
    full_high, full_low = multiply_uint64_to_uint128(full_left, full_right)
    for index in rng.choice(len(full_left), size=512, replace=False):
        product = int(full_left[index]) * int(full_right[index])
        if int(full_high[index]) != product >> 64:
            raise AssertionError("full-width uint128 high-limb self-test failed")
        if int(full_low[index]) != product & (2**64 - 1):
            raise AssertionError("full-width uint128 low-limb self-test failed")

    for bits in (16, 32, 52):
        left = rng.integers(0, 2**bits, size=4096, dtype=np.uint64)
        right = rng.integers(1, 2**bits, size=4096, dtype=np.uint64)
        high, low = multiply_uint64_to_uint128(left, right)
        values = np.minimum(left, right - UINT64_ONE)
        quotient, zero_remainder = floor_square_over_denominator(values, right)
        for index in rng.choice(len(left), size=256, replace=False):
            product = int(left[index]) * int(right[index])
            if int(high[index]) != product >> 64:
                raise AssertionError("uint128 high-limb self-test failed")
            if int(low[index]) != product & (2**64 - 1):
                raise AssertionError("uint128 low-limb self-test failed")
            expected_quotient, remainder = divmod(
                int(values[index]) ** 2, int(right[index])
            )
            if int(quotient[index]) != expected_quotient:
                raise AssertionError("exact quotient self-test failed")
            if bool(zero_remainder[index]) != (remainder == 0):
                raise AssertionError("exact remainder self-test failed")
    print("PASS: uint64-limb products and square quotients")


def load_terminal_pearson_rows() -> dict[int, dict[str, str]]:
    digest = hashlib.sha256(PEARSON_CACHE.read_bytes()).hexdigest()
    if digest != PEARSON_CACHE_SHA256:
        raise AssertionError(
            f"Pearson cache SHA-256 mismatch: expected {PEARSON_CACHE_SHA256}, "
            f"got {digest}"
        )
    with PEARSON_CACHE.open(newline="") as handle:
        terminal_rows = {
            int(row["k"]): row
            for row in csv.DictReader(handle)
            if int(row["terminal_offset"]) == 0
        }
    if set(terminal_rows) != set(EXPECTED_LEVELS):
        raise AssertionError("Pearson cache has an incomplete terminal tower")
    return terminal_rows


def crosscheck_k12_pearson(
    values: np.ndarray, cached_row: dict[str, str]
) -> None:
    """Independently reconstruct the complete k=12 terminal interval."""

    parent_count = len(values) // 3
    lower = 0
    upper = 0
    nonzero_remainders = 0
    for parent in range(parent_count):
        children = (
            int(values[parent]),
            int(values[parent_count + parent]),
            int(values[2 * parent_count + parent]),
        )
        total = sum(children)
        numerator = sum((3 * child - total) ** 2 for child in children)
        quotient, remainder = divmod(numerator, total)
        lower += quotient
        upper += quotient + bool(remainder)
        nonzero_remainders += bool(remainder)
    expected = (
        int(cached_row["chi_lower_num"]),
        int(cached_row["chi_upper_num"]),
        int(cached_row["nonzero_remainder_count"]),
    )
    if (lower, upper, nonzero_remainders) != expected:
        raise AssertionError("k=12 Pearson bigint/cache cross-check failed")
    print("PASS: k=12 terminal Pearson cache matches Python big integers")


def validate_pearson_row(
    row: dict[str, str],
    *,
    k: int,
    total_mass: int,
    parent_count: int,
    source: str,
    digest: str,
) -> tuple[Fraction, Fraction]:
    if int(row["parent_depth"]) != k - 1:
        raise AssertionError(f"k={k}: cached Pearson depth changed")
    if int(row["parent_node_count"]) != parent_count:
        raise AssertionError(f"k={k}: cached Pearson parent count changed")
    if int(row["total_mass"]) != total_mass:
        raise AssertionError(f"k={k}: cached Pearson total mass changed")
    if row["source"] != source or row["source_sha256"] != digest:
        raise AssertionError(f"k={k}: cached Pearson provenance changed")
    if row["source_sha256_verified"] != "True":
        raise AssertionError(f"k={k}: cached Pearson source was not SHA verified")
    lower_numerator = int(row["chi_lower_num"])
    upper_numerator = int(row["chi_upper_num"])
    common_denominator = int(row["chi_common_den"])
    remainder_count = int(row["nonzero_remainder_count"])
    if common_denominator != 3 * total_mass:
        raise AssertionError(f"k={k}: cached Pearson denominator changed")
    if upper_numerator - lower_numerator != remainder_count:
        raise AssertionError(f"k={k}: cached Pearson interval convention changed")
    if not 0 <= remainder_count <= parent_count:
        raise AssertionError(f"k={k}: invalid cached Pearson remainder count")
    return (
        Fraction(lower_numerator, common_denominator),
        Fraction(upper_numerator, common_denominator),
    )


def validate_certificate_lower_weights(manifest: dict[str, object]) -> None:
    numerator = int(manifest["P"])
    denominator = int(manifest["Q"])
    if (numerator, denominator) != (
        LOWER_ALPHA_NUMERATOR,
        LOWER_ALPHA_DENOMINATOR,
    ):
        raise AssertionError("certificate alpha lower approximant changed")
    if not 2**numerator < 3**denominator:
        raise AssertionError("certificate P/Q is not below log_2(3)")

    lambda_numerator = int(manifest["A"])
    lambda_denominator = int(manifest["SC_L"])
    weight_denominator = int(manifest["SC_W"])
    weight_two = int(manifest["B2"])
    weight_eight = int(manifest["B8"])
    negative_exponent = 2 * denominator - numerator
    positive_exponent = numerator - denominator
    if not (
        weight_two**denominator * lambda_numerator**negative_exponent
        <= weight_denominator**denominator
        * lambda_denominator**negative_exponent
    ):
        raise AssertionError("certificate B2 is not a valid lower weight")
    if not (
        weight_eight**denominator * lambda_denominator**positive_exponent
        <= lambda_numerator**positive_exponent
        * weight_denominator**denominator
    ):
        raise AssertionError("certificate B8 is not a valid lower weight")


def least_upper_weights(manifest: dict[str, object]) -> tuple[int, int]:
    """Return grid upper bounds using alpha < 125743/79335."""

    if not 2**UPPER_ALPHA_NUMERATOR > 3**UPPER_ALPHA_DENOMINATOR:
        raise AssertionError("upper rational is not above log_2(3)")
    lambda_numerator = int(manifest["A"])
    lambda_denominator = int(manifest["SC_L"])
    scale = int(manifest["SC_W"])
    negative_exponent = 2 * UPPER_ALPHA_DENOMINATOR - UPPER_ALPHA_NUMERATOR
    positive_exponent = UPPER_ALPHA_NUMERATOR - UPPER_ALPHA_DENOMINATOR
    lambda_float = lambda_numerator / lambda_denominator

    common_scale_power = scale**UPPER_ALPHA_DENOMINATOR

    def upper_two_ok(candidate: int) -> bool:
        return (
            candidate**UPPER_ALPHA_DENOMINATOR
            * lambda_numerator**negative_exponent
            >= common_scale_power * lambda_denominator**negative_exponent
        )

    def upper_eight_ok(candidate: int) -> bool:
        return (
            candidate**UPPER_ALPHA_DENOMINATOR
            * lambda_denominator**positive_exponent
            >= common_scale_power * lambda_numerator**positive_exponent
        )

    upper_two = math.ceil(
        lambda_float
        ** (UPPER_ALPHA_NUMERATOR / UPPER_ALPHA_DENOMINATOR - 2)
        * scale
    )
    upper_eight = math.ceil(
        lambda_float
        ** (UPPER_ALPHA_NUMERATOR / UPPER_ALPHA_DENOMINATOR - 1)
        * scale
    )
    for candidate_name, candidate, predicate in (
        ("B2 upper", upper_two, upper_two_ok),
        ("B8 upper", upper_eight, upper_eight_ok),
    ):
        corrections = 0
        while not predicate(candidate):
            candidate += 1
            corrections += 1
            if corrections > 16:
                raise AssertionError(f"{candidate_name} seed was unexpectedly low")
        while candidate > 0 and predicate(candidate - 1):
            candidate -= 1
            corrections += 1
            if corrections > 16:
                raise AssertionError(f"{candidate_name} seed was unexpectedly high")
        if candidate_name == "B2 upper":
            upper_two = candidate
        else:
            upper_eight = candidate
    return upper_two, upper_eight


def fraction_fields(prefix: str, value: Fraction) -> dict[str, object]:
    return {
        f"{prefix}_num": value.numerator,
        f"{prefix}_den": value.denominator,
        f"{prefix}_decimal": f"{float(value):.17g}",
    }


def analyze_level(
    k: int,
    *,
    chunk_size: int,
    pearson_row: dict[str, str],
) -> tuple[dict[str, object], float]:
    started = time.perf_counter()
    values, source, digest, hash_verified, hash_kind = (
        genealogy.load_certificate(k, verify_sha=True)
    )
    if not hash_verified:
        raise AssertionError(f"k={k}: certificate source was not SHA verified")
    manifest_path = HERE / f"cert_k{k}.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest_digest = hashlib.sha256(manifest_bytes).hexdigest()
    if manifest_digest != EXPECTED_MANIFEST_SHA256[k]:
        raise AssertionError(
            f"k={k}: certificate manifest SHA-256 mismatch: expected "
            f"{EXPECTED_MANIFEST_SHA256[k]}, got {manifest_digest}"
        )
    manifest = json.loads(manifest_bytes)
    if int(manifest["k"]) != k:
        raise AssertionError(f"k={k}: certificate manifest level changed")
    validate_certificate_lower_weights(manifest)

    coordinate_count = len(values)
    parent_count = coordinate_count // 3
    if coordinate_count != 3 ** (k - 1) or parent_count != 3 ** (k - 2):
        raise AssertionError(f"k={k}: terminal dimensions changed")

    total_mass = 0
    minimum_sum = 0
    second_moment_quotient_sum = 0
    second_moment_remainders = 0
    for start in range(0, parent_count, chunk_size):
        stop = min(start + chunk_size, parent_count)
        child_zero = values[start:stop]
        child_one = values[parent_count + start : parent_count + stop]
        child_two = values[2 * parent_count + start : 2 * parent_count + stop]
        parents = child_zero + child_one + child_two
        minima = np.minimum(np.minimum(child_zero, child_one), child_two)
        defects = parents - 3 * minima
        if int(parents.max()) > FLOAT_EXACT_INT:
            raise OverflowError(f"k={k}: terminal parent exceeds 2^53-1")

        quotients, zero_remainders = floor_square_over_denominator(
            defects.astype(np.uint64, copy=False),
            parents.astype(np.uint64, copy=False),
        )
        total_mass += exact_nonnegative_sum(parents, chunk_size)
        minimum_sum += exact_nonnegative_sum(minima, chunk_size)
        second_moment_quotient_sum += exact_nonnegative_sum(
            quotients, chunk_size
        )
        second_moment_remainders += len(quotients) - int(
            np.count_nonzero(zero_remainders)
        )

    if total_mass != EXPECTED_TOTAL_MASS[k]:
        raise AssertionError(f"k={k}: exact total-mass regression changed")
    raw_defect_numerator = total_mass - 3 * minimum_sum
    if raw_defect_numerator <= 0:
        raise AssertionError(f"k={k}: terminal mean defect is not positive")
    delta = Fraction(raw_defect_numerator, 3 * total_mass)
    second_moment_lower = Fraction(
        second_moment_quotient_sum, 9 * total_mass
    )
    second_moment_upper = Fraction(
        second_moment_quotient_sum + second_moment_remainders,
        9 * total_mass,
    )
    concentration_lower = second_moment_lower / delta**2
    concentration_upper = second_moment_upper / delta**2

    pearson_lower, pearson_upper = validate_pearson_row(
        pearson_row,
        k=k,
        total_mass=total_mass,
        parent_count=parent_count,
        source=source,
        digest=digest,
    )
    if k == 12:
        crosscheck_k12_pearson(values, pearson_row)

    upper_weight_two, upper_weight_eight = least_upper_weights(manifest)
    lambda_numerator = int(manifest["A"])
    lambda_denominator = int(manifest["SC_L"])
    weight_denominator = int(manifest["SC_W"])
    minimum_fraction = Fraction(minimum_sum, total_mass)
    transport_weight = Fraction(lambda_denominator**2, lambda_numerator**2)
    sigma_lower = (
        transport_weight
        - 1
        + Fraction(int(manifest["B2"]) + int(manifest["B8"]), weight_denominator)
        * minimum_fraction
    )
    sigma_upper = (
        transport_weight
        - 1
        + Fraction(upper_weight_two + upper_weight_eight, weight_denominator)
        * minimum_fraction
    )
    if not 0 <= sigma_lower <= sigma_upper:
        raise AssertionError(f"k={k}: invalid aggregate-slack enclosure")

    passes_delta = delta < FINITE_DELTA_CONSTANT / k
    passes_second_moment = (
        second_moment_upper < FINITE_SECOND_MOMENT_CONSTANT * delta**2
    )
    passes_pearson = pearson_upper < FINITE_PEARSON_CONSTANT / k**2
    if not (passes_delta and passes_second_moment and passes_pearson):
        raise AssertionError(f"k={k}: a finite terminal calibration failed")

    lambda_value = Fraction(lambda_numerator, lambda_denominator)
    k_lambda_gap = k * (2 - lambda_value)
    elapsed = time.perf_counter() - started
    row = {
        "k": k,
        **fraction_fields("lambda", lambda_value),
        **fraction_fields("k_lambda_gap", k_lambda_gap),
        "coordinate_count": coordinate_count,
        "terminal_parent_count": parent_count,
        "total_mass": total_mass,
        "terminal_minimum_sum": minimum_sum,
        "raw_defect_numerator": raw_defect_numerator,
        **fraction_fields("delta", delta),
        **fraction_fields("k_delta", k * delta),
        "second_moment_quotient_sum": second_moment_quotient_sum,
        "second_moment_nonzero_remainders": second_moment_remainders,
        **fraction_fields("second_moment_lower", second_moment_lower),
        **fraction_fields("second_moment_upper", second_moment_upper),
        **fraction_fields("concentration_ratio_lower", concentration_lower),
        **fraction_fields("concentration_ratio_upper", concentration_upper),
        **fraction_fields("pearson_lower", pearson_lower),
        **fraction_fields("pearson_upper", pearson_upper),
        **fraction_fields("k_squared_pearson_upper", k**2 * pearson_upper),
        "pearson_cache": PEARSON_CACHE.name,
        "pearson_cache_sha256": PEARSON_CACHE_SHA256,
        "certificate_manifest": manifest_path.name,
        "certificate_manifest_sha256": manifest_digest,
        "certificate_manifest_sha256_verified": True,
        "lower_alpha_num": LOWER_ALPHA_NUMERATOR,
        "lower_alpha_den": LOWER_ALPHA_DENOMINATOR,
        "lower_weight_two_num": int(manifest["B2"]),
        "lower_weight_eight_num": int(manifest["B8"]),
        "lower_weight_den": weight_denominator,
        "upper_alpha_num": UPPER_ALPHA_NUMERATOR,
        "upper_alpha_den": UPPER_ALPHA_DENOMINATOR,
        "upper_weight_two_num": upper_weight_two,
        "upper_weight_eight_num": upper_weight_eight,
        "upper_weight_den": weight_denominator,
        **fraction_fields("sigma_lower", sigma_lower),
        **fraction_fields("sigma_upper", sigma_upper),
        "passes_delta_lt_0_21_over_k": passes_delta,
        "passes_second_moment_lt_1_533_delta_squared": passes_second_moment,
        "passes_pearson_lt_0_483_over_k_squared": passes_pearson,
        "scope": "finite_selected_k12_k19_not_all_level",
        "source": source,
        "source_sha256": digest,
        "source_sha256_verified": hash_verified,
        "source_sha256_kind": hash_kind,
    }
    return row, elapsed


def write_rows(path: Path, rows: list[dict[str, object]]) -> None:
    if not rows:
        raise ValueError(f"refusing to write empty table {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {path} ({len(rows)} rows)")


def print_table(rows: list[dict[str, object]]) -> None:
    print()
    print(
        "  k     lambda  k(2-lam)       delta   k*delta"
        "       E[u^2]        K        chi   k^2*chi    1e7 Sigma"
    )
    for row in rows:
        second_lower = Fraction(
            int(row["second_moment_lower_num"]),
            int(row["second_moment_lower_den"]),
        )
        second_upper = Fraction(
            int(row["second_moment_upper_num"]),
            int(row["second_moment_upper_den"]),
        )
        concentration_lower = Fraction(
            int(row["concentration_ratio_lower_num"]),
            int(row["concentration_ratio_lower_den"]),
        )
        concentration_upper = Fraction(
            int(row["concentration_ratio_upper_num"]),
            int(row["concentration_ratio_upper_den"]),
        )
        pearson_lower = Fraction(
            int(row["pearson_lower_num"]), int(row["pearson_lower_den"])
        )
        pearson_upper = Fraction(
            int(row["pearson_upper_num"]), int(row["pearson_upper_den"])
        )
        sigma_lower = Fraction(
            int(row["sigma_lower_num"]), int(row["sigma_lower_den"])
        )
        sigma_upper = Fraction(
            int(row["sigma_upper_num"]), int(row["sigma_upper_den"])
        )
        print(
            f"{int(row['k']):3d}"
            f" {float(row['lambda_decimal']):10.7f}"
            f" {float(row['k_lambda_gap_decimal']):9.4f}"
            f" {float(row['delta_decimal']):11.7f}"
            f" {float(row['k_delta_decimal']):9.6f}"
            f" {float((second_lower + second_upper) / 2):12.6g}"
            f" {float((concentration_lower + concentration_upper) / 2):8.5f}"
            f" {float((pearson_lower + pearson_upper) / 2):10.6g}"
            f" {float(row['k_squared_pearson_upper_decimal']):9.6f}"
            f" [{1e7 * float(sigma_lower):.5f},{1e7 * float(sigma_upper):.5f}]"
        )


def maximum_resident_megabytes() -> float:
    maximum = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if sys.platform == "darwin":
        return maximum / 1024**2
    return maximum / 1024


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--levels", nargs="+", type=int, default=list(EXPECTED_LEVELS)
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--chunk-size", type=int, default=500_000)
    args = parser.parse_args()
    levels = tuple(args.levels)
    if args.chunk_size <= 0:
        parser.error("require a positive chunk size")
    if (
        not levels
        or tuple(sorted(set(levels))) != levels
        or any(level not in EXPECTED_LEVELS for level in levels)
    ):
        parser.error("levels must be an increasing subset of 12 through 19")
    if levels != EXPECTED_LEVELS and args.output.resolve() == DEFAULT_OUTPUT.resolve():
        parser.error("subset runs require a nondefault --output")

    started = time.perf_counter()
    verify_limb_self_tests()
    pearson_rows = load_terminal_pearson_rows()
    rows = []
    for k in levels:
        row, level_seconds = analyze_level(
            k,
            chunk_size=args.chunk_size,
            pearson_row=pearson_rows[k],
        )
        rows.append(row)
        print(
            f"PASS: k={k}, SHA verified, exact terminal statistics "
            f"({level_seconds:.6f}s)"
        )
    write_rows(args.output, rows)
    print_table(rows)
    print()
    print(
        "PASS: finite selected records satisfy delta < 0.21/k, "
        "E[u^2] < 1.533 delta^2, and chi < 0.483/k^2"
    )
    print(
        f"PASS: elapsed={time.perf_counter()-started:.3f}s, "
        f"max_rss={maximum_resident_megabytes():.1f} MiB"
    )


if __name__ == "__main__":
    main()
