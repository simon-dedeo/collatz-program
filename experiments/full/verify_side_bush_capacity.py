#!/usr/bin/env python3
"""Exact finite checks for the side-bush capacity construction.

The all-orbit disjointness lemma is a mathematical statement and is being
sent to Lean.  This script supplies bounded regression gates and uses only
integer/Fraction arithmetic for the KL lower-load comparison.  Its orbit
search is finite evidence, not evidence that every tested trajectory pattern
persists on a hypothetical divergent orbit.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CERTIFICATE = ROOT / "experiments" / "kl" / "cert_k12.json"
CERTIFICATE_SHA256 = (
    "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f"
)
CHAMPION_SEARCH_LIMIT = 200_000
BRUTE_CUTOFF = 1_000_000
SMALL_SEED_LIMIT = 128
SMALL_CUTOFF = 512
MAX_TRACE_STEPS = 10_000


def syracuse(n: int) -> int:
    assert n > 0
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1 << 20):
            digest.update(block)
    return digest.hexdigest()


def orbit_to_one(seed: int) -> list[int]:
    """Return the finite Syracuse path through its first occurrence of one."""

    path: list[int] = []
    seen: set[int] = set()
    n = seed
    for _ in range(MAX_TRACE_STEPS):
        if n in seen:
            raise AssertionError(f"seed {seed} repeated {n} before reaching one")
        seen.add(n)
        path.append(n)
        if n == 1:
            return path
        n = syracuse(n)
    raise AssertionError(f"seed {seed} exceeded the finite trace budget")


def stopping_time_champion(limit: int) -> tuple[int, int]:
    """Find the largest total stopping time among ``1 <= seed <= limit``."""

    stopping: dict[int, int] = {1: 0}
    best_steps = 0
    best_seed = 1
    for seed in range(2, limit + 1):
        trail: list[int] = []
        positions: dict[int, int] = {}
        n = seed
        while n not in stopping:
            if n in positions:
                raise AssertionError(
                    f"bounded champion search found a non-unit cycle at {n}"
                )
            positions[n] = len(trail)
            trail.append(n)
            n = syracuse(n)
        total = len(trail) + stopping[n]
        for index, value in enumerate(trail):
            stopping[value] = total - index
        if total > best_steps:
            best_steps = total
            best_seed = seed
    return best_seed, best_steps


def side_targets(path: list[int]) -> dict[int, tuple[int, int]]:
    """Map ``b_j=2(3n_j+1)`` to ``(j,n_j)`` for nonterminal odd nodes."""

    targets: dict[int, tuple[int, int]] = {}
    for index, n in enumerate(path[:-1]):
        if n % 2 == 0:
            continue
        a = 3 * n + 1
        b = 2 * a
        assert a == 2 * path[index + 1]
        assert b % 3 == 2
        assert syracuse(syracuse(b)) == path[index + 1]
        assert b not in targets
        targets[b] = (index, n)
    return targets


def target_hits_before_one(start: int, targets: set[int]) -> list[int]:
    hits: list[int] = []
    n = start
    seen: set[int] = set()
    for _ in range(MAX_TRACE_STEPS):
        if n in seen:
            if n in (1, 2):
                return hits
            raise AssertionError(f"trace from {start} repeated unexpected value {n}")
        seen.add(n)
        if n in targets:
            hits.append(n)
        if n == 1:
            return hits
        n = syracuse(n)
    raise AssertionError(f"trace from {start} exceeded the finite trace budget")


def assert_target_family_disjoint(
    path: list[int], targets: dict[int, tuple[int, int]], cutoff: int
) -> None:
    """Boundedly check that no traced point meets two side targets."""

    target_set = set(targets)
    path_set = set(path)
    for b, (_, n) in targets.items():
        a = 3 * n + 1
        assert a not in path_set
        hits = target_hits_before_one(b, target_set)
        assert hits == [b], (b, hits)

    for start in range(1, cutoff + 1):
        hits = target_hits_before_one(start, target_set)
        if len(hits) > 1:
            raise AssertionError(
                f"bounded side-bush collision from {start}: {hits}"
            )


def predecessor_partition(
    targets: dict[int, tuple[int, int]], cutoff: int
) -> dict[int, int]:
    """Count predecessors of each disjoint target among ``[1,cutoff]``."""

    target_set = set(targets)
    counts = {target: 0 for target in targets}
    # A memoized first-target label is safe after the target-family gate above.
    label: dict[int, int | None] = {1: None}
    label.update({target: target for target in targets})

    for start in range(1, cutoff + 1):
        trail: list[int] = []
        positions: set[int] = set()
        n = start
        for _ in range(MAX_TRACE_STEPS):
            if n in label:
                outcome = label[n]
                break
            if n in positions:
                raise AssertionError(
                    f"bounded predecessor census repeated unexpected value {n}"
                )
            positions.add(n)
            trail.append(n)
            n = syracuse(n)
        else:
            raise AssertionError(
                f"bounded predecessor census from {start} exceeded trace budget"
            )
        for value in trail:
            label[value] = outcome
        if outcome is not None:
            assert outcome in target_set
            counts[outcome] += 1
    return counts


def load_k12() -> tuple[dict[str, object], list[int]]:
    actual_sha = sha256(CERTIFICATE)
    if actual_sha != CERTIFICATE_SHA256:
        raise AssertionError(
            f"k=12 manifest SHA changed: expected {CERTIFICATE_SHA256}, "
            f"got {actual_sha}"
        )
    manifest = json.loads(CERTIFICATE.read_text())
    if manifest["k"] != 12:
        raise AssertionError("portable certificate is no longer level 12")
    vector = [int(value) for value in manifest["C"]]
    if len(vector) != 3**11 or min(vector) <= 0:
        raise AssertionError("portable certificate vector shape/positivity changed")
    return manifest, vector


def state_index(target: int, level: int) -> int:
    modulus = 3**level
    residue = target % modulus
    if residue % 3 != 2:
        raise AssertionError(f"target {target} is not in the KL class 2 mod 3")
    index = (residue - 2) // 3
    assert 0 <= index < 3 ** (level - 1)
    return index


def dyadic_depth(cutoff: int, target: int) -> int:
    """Largest ``y>=0`` such that ``target*2^y <= cutoff``."""

    if target > cutoff:
        raise ValueError("dyadic depth requires target <= cutoff")
    return (cutoff // target).bit_length() - 1


def exact_kl_lower_load(
    manifest: dict[str, object],
    vector: list[int],
    counts: dict[int, int],
    cutoff: int,
) -> tuple[Fraction, list[tuple[Fraction, int, int, int]]]:
    """Evaluate the rational form (3.4) and check it target by target."""

    level = int(manifest["k"])
    lam = Fraction(int(manifest["A"]), int(manifest["SC_L"]))
    total_mass = sum(vector)
    rows: list[tuple[Fraction, int, int, int]] = []
    lower_total = Fraction(0)
    for target, actual_count in counts.items():
        if target > cutoff:
            continue
        coordinate = vector[state_index(target, level)]
        depth = dyadic_depth(cutoff, target)
        lower = Fraction(coordinate, 4 * total_mass) * lam**depth
        if lower > actual_count:
            raise AssertionError(
                f"KL rational lower load failed for target {target}: "
                f"{lower} > {actual_count}"
            )
        lower_total += lower
        rows.append((lower, actual_count, target, coordinate))
    if lower_total > sum(counts.values()):
        raise AssertionError("summed lower load exceeds the disjoint-bush census")
    if sum(counts.values()) > cutoff:
        raise AssertionError("disjoint predecessor bushes exceed the ambient interval")
    return lower_total, rows


def main() -> None:
    # A bounded structural regression on many complete, simple paths to one.
    for seed in range(1, SMALL_SEED_LIMIT + 1):
        path = orbit_to_one(seed)
        targets = side_targets(path)
        assert_target_family_disjoint(path, targets, SMALL_CUTOFF)
    print(
        "PASS: side-target identities and bounded first-entry disjointness "
        f"for seeds <= {SMALL_SEED_LIMIT}, starts <= {SMALL_CUTOFF}"
    )

    champion, steps = stopping_time_champion(CHAMPION_SEARCH_LIMIT)
    path = orbit_to_one(champion)
    if steps != len(path) - 1:
        raise AssertionError("champion stopping-time cache disagrees with direct trace")
    targets = side_targets(path)
    assert_target_family_disjoint(path, targets, BRUTE_CUTOFF)
    active_targets = {
        target: data for target, data in targets.items() if target <= BRUTE_CUTOFF
    }
    counts = predecessor_partition(active_targets, BRUTE_CUTOFF)

    manifest, vector = load_k12()
    lower_total, rows = exact_kl_lower_load(
        manifest, vector, counts, BRUTE_CUTOFF
    )
    total_mass = sum(vector)
    coordinates = [row[3] for row in rows]
    occupied = sum(counts.values())

    print(
        "PASS: SHA-pinned k=12 rational KL lower loads lie below every "
        "brute-force side-bush count"
    )
    print(
        f"champion <= {CHAMPION_SEARCH_LIMIT}: seed={champion}, "
        f"steps={steps}, max={max(path)}, odd attachments={len(targets)}"
    )
    print(
        f"cutoff={BRUTE_CUTOFF}, active targets={len(active_targets)}, "
        f"actual disjoint union={occupied} ({occupied / BRUTE_CUTOFF:.6f})"
    )
    print(
        "certified rational lower load="
        f"{float(lower_total):.12g} "
        f"({float(lower_total / BRUTE_CUTOFF):.12g} of the interval)"
    )
    print(
        "normalized k=12 side-state weight min/mean/max="
        f"{min(coordinates) / total_mass:.12g}/"
        f"{sum(coordinates) / len(coordinates) / total_mass:.12g}/"
        f"{max(coordinates) / total_mass:.12g}; "
        f"uniform={1 / len(vector):.12g}"
    )
    largest = sorted(rows, key=lambda row: row[3], reverse=True)[:5]
    print("largest normalized side-state weights:")
    for _, actual, target, coordinate in largest:
        print(
            f"  target={target:>8} count={actual:>7} "
            f"mu={coordinate / total_mass:.12g}"
        )
    print(
        "SCOPE: exact finite diagnostic only; it does not prove the "
        "all-orbit disjointness lemma or an endpoint capacity theorem"
    )


if __name__ == "__main__":
    main()
