#!/usr/bin/env python3
"""Exact finite audit of iterated minimum growth on selected KL records.

For a positive level-k vector ``x^(0)`` in the standard state order, define

    x^(j+1)_r = min_d x^(j)_(r+d 3^(k-j-2)),
    T_j       = sum_r x^(j)_r,
    epsilon_j = 1-3 T_(j+1)/T_j.

This checker proves, with Python integers, the post-hoc finite comparison

    epsilon_(j+1) >= epsilon_j + (3/2) epsilon_j^2

at every available stage of every selected exact certificate k=12,...,19.
The large NPY sidecars are reduced by the bundled C memory-mapped helper;
all cross-products are checked here with arbitrary-precision integers.  Source
manifests and sidecars are SHA-pinned.  This is finite selected-record evidence,
not an all-level theorem and not a statement about arbitrary feasible vectors.

The checker also verifies a small exact k=3 counterexample showing why that
scope matters.  At lambda=1001/1000 a positive integer vector is strictly
feasible for rationally tightened branch weights, but its coarse-minimum
excess is smaller than its fine excess.

An optional ``--float-k20`` run reports the same statistic on the uncertified
floating candidate in a separate, explicitly non-exact block.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
NATIVE_SOURCE = HERE / "iterated_minimum_totals.c"
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
EXPECTED_SIDECAR_SHA256 = {
    15: "fa65959e13cb445e50c92a447a924658b45aae943873e38d774a0b79aa85cda4",
    16: "180c4856ee6cffdf08a2feedea15a17bab9f0d8bf2702808b4ae2512a41d300b",
    17: "72da89e5733d56855d7514107b690c9127ca243ac65f6ad2873c9eeff0a770d2",
    18: "e3d998ff0e34ae16ec7f2a53be4f48bcedc3b106f5b7316f3b558e97c34522ef",
    19: "052c7e75907c99ec4c05dca550adcf23e4dad264175d3f559f4b5a9da5b4d517",
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

COUNTEREXAMPLE_LAMBDA = Fraction(1001, 1000)
COUNTEREXAMPLE = (487, 1916, 458, 1178, 485, 777, 1920, 1175, 1603)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_levels(specification: str) -> tuple[int, ...]:
    levels: set[int] = set()
    for piece in specification.split(","):
        piece = piece.strip()
        if not piece:
            continue
        if "-" in piece:
            first_text, last_text = piece.split("-", 1)
            first, last = int(first_text), int(last_text)
            levels.update(range(first, last + 1))
        else:
            levels.add(int(piece))
    result = tuple(sorted(levels))
    if not result or any(level not in EXPECTED_LEVELS for level in result):
        raise ValueError("exact levels must be a nonempty subset of 12,...,19")
    return result


def compile_native_helper(destination: Path) -> None:
    command = (
        "cc",
        "-O3",
        "-std=c11",
        "-Wall",
        "-Wextra",
        str(NATIVE_SOURCE),
        "-o",
        str(destination),
    )
    subprocess.run(command, check=True)


def python_totals(values: list[int]) -> list[tuple[int, int]]:
    totals: list[tuple[int, int]] = []
    while True:
        if not values or any(value <= 0 for value in values):
            raise AssertionError("certificate vector must be strictly positive")
        totals.append((len(values), sum(values)))
        if len(values) == 1:
            return totals
        if len(values) % 3 != 0:
            raise AssertionError("profile length is not divisible by three")
        third = len(values) // 3
        values = [
            min(values[index], values[index + third], values[index + 2 * third])
            for index in range(third)
        ]


def native_totals(helper: Path, mode: str, source: Path) -> list[tuple[int, int | Decimal]]:
    completed = subprocess.run(
        (str(helper), mode, str(source)),
        check=True,
        capture_output=True,
        text=True,
    )
    totals: list[tuple[int, int | Decimal]] = []
    for expected_depth, line in enumerate(completed.stdout.splitlines()):
        depth_text, length_text, total_text = line.split()
        if int(depth_text) != expected_depth:
            raise AssertionError("native helper returned depths out of order")
        total: int | Decimal
        total = int(total_text) if mode == "integer" else Decimal(total_text)
        totals.append((int(length_text), total))
    if not totals:
        raise AssertionError("native helper returned no totals")
    return totals


def verify_manifest(level: int) -> dict[str, object]:
    manifest_path = HERE / f"cert_k{level}.json"
    actual_hash = sha256(manifest_path)
    if actual_hash != EXPECTED_MANIFEST_SHA256[level]:
        raise AssertionError(
            f"k={level} manifest hash mismatch: {actual_hash}"
        )
    manifest = json.loads(manifest_path.read_text())
    if int(manifest["k"]) != level:
        raise AssertionError("manifest level mismatch")
    return manifest


def exact_totals(level: int, helper: Path) -> list[tuple[int, int]]:
    manifest = verify_manifest(level)
    if level <= 14:
        raw_values = manifest.get("C")
        if not isinstance(raw_values, list):
            raise AssertionError("portable manifest does not contain its vector")
        totals = python_totals([int(value) for value in raw_values])
    else:
        sidecar_name = manifest.get("C_file")
        if not isinstance(sidecar_name, str):
            raise AssertionError("sidecar manifest has no C_file")
        sidecar = HERE / sidecar_name
        if not sidecar.is_file():
            raise FileNotFoundError(
                f"k={level} sidecar is unavailable in this checkout: {sidecar}"
            )
        actual_hash = sha256(sidecar)
        if actual_hash != EXPECTED_SIDECAR_SHA256[level]:
            raise AssertionError(f"k={level} sidecar hash mismatch: {actual_hash}")
        if manifest.get("C_sha256") != actual_hash:
            raise AssertionError("manifest-to-sidecar provenance mismatch")
        native = native_totals(helper, "integer", sidecar)
        if any(not isinstance(total, int) for _, total in native):
            raise AssertionError("integer helper returned a noninteger total")
        totals = [(length, int(total)) for length, total in native]

    expected_lengths = [3 ** (level - 1 - depth) for depth in range(level)]
    if [length for length, _ in totals] != expected_lengths:
        raise AssertionError(f"k={level} minimum-profile lengths are wrong")
    if totals[0][1] != EXPECTED_TOTAL_MASS[level]:
        raise AssertionError(f"k={level} total mass does not match the pinned value")
    return totals


def verify_quadratic_growth(
    level: int, totals: list[tuple[int, int]]
) -> tuple[Fraction, int, Fraction, Fraction]:
    epsilons: list[Fraction] = []
    for (_, total), (_, coarse_total) in zip(totals, totals[1:], strict=False):
        excess = total - 3 * coarse_total
        if not 0 < excess < total:
            raise AssertionError(f"k={level} has a degenerate terminal excess")
        epsilons.append(Fraction(excess, total))

    ratios: list[Fraction] = []
    for stage, (epsilon, next_epsilon) in enumerate(
        zip(epsilons, epsilons[1:], strict=False)
    ):
        ratio = (next_epsilon - epsilon) / (epsilon * epsilon)
        ratios.append(ratio)

        # Direct integer cross-product form.  If T'=coarse total,
        # E=T-3T', and E'=T'-3T'', then this is exactly
        # epsilon'-epsilon >= (3/2)epsilon^2.
        total = totals[stage][1]
        coarse_total = totals[stage + 1][1]
        next_coarse_total = totals[stage + 2][1]
        excess = total - 3 * coarse_total
        next_excess = coarse_total - 3 * next_coarse_total
        margin = (
            2 * total * total * next_excess
            - 2 * coarse_total * total * excess
            - 3 * coarse_total * excess * excess
        )
        if margin < 0 or ratio < Fraction(3, 2):
            raise AssertionError(f"k={level}, stage={stage} violates the finite fit")

    minimum = min(ratios)
    return minimum, ratios.index(minimum), epsilons[0], epsilons[1]


def build_level_three_rows() -> list[tuple[int, int, tuple[int, int, int] | None]]:
    modulus = 27
    coarse_modulus = 9
    states = tuple(range(2, modulus, 3))
    index = {state: position for position, state in enumerate(states)}
    rows: list[tuple[int, int, tuple[int, int, int] | None]] = []
    for state in states:
        transport = index[(4 * state) % modulus]
        branch = state % 9
        if branch == 2:
            target = ((4 * state - 2) // 3) % coarse_modulus
        elif branch == 8:
            target = ((2 * state - 1) // 3) % coarse_modulus
        else:
            if branch != 5:
                raise AssertionError("unexpected residue class")
            rows.append((transport, branch, None))
            continue
        fiber = tuple(
            index[(target + digit * coarse_modulus) % modulus]
            for digit in range(3)
        )
        rows.append((transport, branch, fiber))
    return rows


def verify_feasibility_counterexample() -> None:
    # Since 2<3<4, alpha=log_2(3) lies strictly between one and two.
    # For lambda>1 this proves
    # lambda^(alpha-2)>lambda^-1 and lambda^(alpha-1)>1.
    if not 2 < 3 < 4 or not COUNTEREXAMPLE_LAMBDA > 1:
        raise AssertionError("elementary exponent comparison failed")

    tau = COUNTEREXAMPLE_LAMBDA ** -2
    tightened_weights = {2: COUNTEREXAMPLE_LAMBDA ** -1, 8: Fraction(1)}
    margins: list[Fraction] = []
    for row, (transport, branch, fiber) in enumerate(build_level_three_rows()):
        image = tau * COUNTEREXAMPLE[transport]
        if branch in (2, 8):
            if fiber is None:
                raise AssertionError("branch row has no target fiber")
            image += tightened_weights[branch] * min(
                COUNTEREXAMPLE[source] for source in fiber
            )
        margin = image - COUNTEREXAMPLE[row]
        if margin <= 0:
            raise AssertionError("counterexample is not strictly tightened-feasible")
        margins.append(margin)
    if min(margins) != Fraction(166_084, 1_002_001):
        raise AssertionError("counterexample minimum margin changed")

    total = sum(COUNTEREXAMPLE)
    third = len(COUNTEREXAMPLE) // 3
    minima = tuple(
        min(
            COUNTEREXAMPLE[index],
            COUNTEREXAMPLE[index + third],
            COUNTEREXAMPLE[index + 2 * third],
        )
        for index in range(third)
    )
    epsilon = Fraction(total - 3 * sum(minima), total)
    coarse_epsilon = Fraction(sum(minima) - 3 * min(minima), sum(minima))
    if minima != (487, 485, 458):
        raise AssertionError("counterexample fiber orientation changed")
    if epsilon != Fraction(173, 303) or coarse_epsilon != Fraction(28, 715):
        raise AssertionError("counterexample excesses changed")
    if not coarse_epsilon < epsilon:
        raise AssertionError("counterexample does not reverse excess monotonicity")

    print(
        "PASS: exact k=3 tightened-feasibility counterexample; "
        f"min margin={min(margins)}, epsilon={epsilon}, "
        f"coarse epsilon={coarse_epsilon}"
    )
    print(
        "SCOPE: positivity and KL feasibility alone do not imply even "
        "epsilon(coarse minimum)>=epsilon"
    )


def report_float_k20(helper: Path, path: Path) -> None:
    if not path.is_file():
        raise FileNotFoundError(f"floating k=20 candidate is unavailable: {path}")
    totals = native_totals(helper, "float", path)
    with localcontext() as context:
        context.prec = 40
        decimal_totals = [Decimal(total) for _, total in totals]
        epsilons = [
            Decimal(1) - Decimal(3) * coarse / total
            for total, coarse in zip(decimal_totals, decimal_totals[1:], strict=False)
        ]
        ratios = [
            (next_epsilon - epsilon) / (epsilon * epsilon)
            for epsilon, next_epsilon in zip(epsilons, epsilons[1:], strict=False)
        ]
        minimum = min(ratios)
        stage = ratios.index(minimum)
        print()
        print("NON-EXACT ORIENTATION: uncertified floating k=20 candidate")
        print(
            f"  first epsilon={epsilons[0]:.12g}, "
            f"minimum quadratic ratio={minimum:.12g} at stage {stage}"
        )
        print("  This block is not part of either exact PASS above.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--levels",
        default="12-19",
        help="comma/range subset of exact levels 12,...,19 (default: 12-19)",
    )
    parser.add_argument(
        "--float-k20",
        action="store_true",
        help="also report the separate non-exact k=20 floating orientation",
    )
    parser.add_argument(
        "--float-k20-path",
        type=Path,
        default=HERE / "eigvec_k20.npy",
        help="path used by --float-k20",
    )
    arguments = parser.parse_args()
    levels = parse_levels(arguments.levels)

    verify_feasibility_counterexample()
    with tempfile.TemporaryDirectory(prefix="kl_iterated_minimum_") as directory:
        helper = Path(directory) / "iterated_minimum_totals"
        compile_native_helper(helper)
        print()
        print("EXACT SELECTED-CERTIFICATE AUDIT")
        print(" k  first epsilon  first coarse epsilon  min ratio  stage")
        for level in levels:
            totals = exact_totals(level, helper)
            minimum, stage, epsilon, coarse_epsilon = verify_quadratic_growth(
                level, totals
            )
            print(
                f"{level:2d}  {float(epsilon):.10f}     "
                f"{float(coarse_epsilon):.10f}        "
                f"{float(minimum):.9f}  {stage:2d}"
            )
        print(
            "PASS: every exact adjacent minimum profile satisfies "
            "epsilon_(j+1)>=epsilon_j+(3/2)epsilon_j^2"
        )
        level_list = ",".join(str(level) for level in levels)
        print(
            "SCOPE: post-hoc finite statement on the requested selected "
            f"certificate levels {level_list} only"
        )

        if arguments.float_k20:
            report_float_k20(helper, arguments.float_k20_path)


if __name__ == "__main__":
    main()
