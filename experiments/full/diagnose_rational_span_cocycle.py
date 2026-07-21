#!/usr/bin/env python3
"""Exact bounded diagnostics for the base-3/2 span cocycle.

The bottom-word evaluation is irrational in general.  We therefore use exact
rational prefixes together with a rigorous tail interval.  Exhaustive checks
below concern finite prefixes and the stated finite scan only; the all-level
identities printed by the script are proved in
``docs/notes/rational-span-cocycle.md``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


DEPTH = 96
RECURRENCE_SCAN = 20_000
SLOPE_SCAN = 20_000
PREIMAGE_ROOT_SCAN = 1_000
PREIMAGE_DEPTH = 12


def bottom_successor(n: int) -> int:
    """The least-digit child U(n)=ceil(3n/2) of the base-3/2 tree."""

    assert n >= 0
    return (3 * n + (n & 1)) // 2


def syracuse(n: int) -> int:
    assert n > 0
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def bottom_prefix_numerator(n: int, depth: int) -> int:
    """Return N with F_depth(n)=N/3**depth, using exact integers."""

    assert n >= 0 and depth >= 0
    if depth == 0:
        return 0
    numerator = 0
    power_two = 1
    power_three = 3 ** (depth - 1)
    for index in range(depth):
        digit = n & 1
        numerator += digit * power_two * power_three
        n = bottom_successor(n)
        power_two *= 2
        if index + 1 < depth:
            power_three //= 3
    return numerator


@dataclass(frozen=True)
class Interval:
    low: Fraction
    high: Fraction

    def midpoint(self) -> Fraction:
        return (self.low + self.high) / 2


def f_interval(n: int, depth: int = DEPTH) -> Interval:
    """Rigorous interval for the bottom-word value F(n)."""

    denominator = 3**depth
    numerator = bottom_prefix_numerator(n, depth)
    # Every omitted bottom digit is 0 or 1, so the entire tail is at most
    # sum_{i>depth} 2^(i-1)/3^i = (2/3)^depth.
    tail_numerator = 2**depth
    return Interval(
        Fraction(numerator, denominator),
        Fraction(numerator + tail_numerator, denominator),
    )


def sigma_interval(n: int, depth: int = DEPTH) -> Interval:
    """Rigorous interval for sigma(n)=1+F(n+1)-F(n)."""

    denominator = 3**depth
    left = bottom_prefix_numerator(n, depth)
    right = bottom_prefix_numerator(n + 1, depth)
    center = denominator + right - left
    tail_numerator = 2**depth
    return Interval(
        Fraction(center - tail_numerator, denominator),
        Fraction(center + tail_numerator, denominator),
    )


def defect_interval(m: int, depth: int = DEPTH) -> Interval:
    """Rigorous interval for d(m)=2F(m)-F(2m)."""

    denominator = 3**depth
    center = (
        2 * bottom_prefix_numerator(m, depth)
        - bottom_prefix_numerator(2 * m, depth)
    )
    tail_numerator = 2**depth
    # If F=F_depth+e with 0<=e<=tail, then 2e_m-e_2m is in
    # [-tail,2tail].
    return Interval(
        Fraction(center - tail_numerator, denominator),
        Fraction(center + 2 * tail_numerator, denominator),
    )


def josephus_constant_interval(depth: int = DEPTH) -> Interval:
    """Rigorous interval for K(3)=lim (2/3)^k ceil_(3/2)^k(1)."""

    value = 1
    for _ in range(depth):
        value = (3 * value + 1) // 2
    lower = Fraction((2**depth) * value, 3**depth)
    # Each future ceiling error is at most 1/2, giving a remaining
    # normalized tail of at most (2/3)^depth.
    return Interval(lower, lower + Fraction(2**depth, 3**depth))


def fmt(value: Fraction, digits: int = 12) -> str:
    return f"{float(value):.{digits}g}"


def fmt_interval(interval: Interval) -> str:
    return f"[{fmt(interval.low)}, {fmt(interval.high)}]"


def assert_disjoint_below(left: Interval, right: Interval) -> None:
    assert left.high < right.low, (left, right)


def verify_prefix_recurrences() -> None:
    """Exhaust the exact depth-L/depth-(L-1) identities."""

    depth = DEPTH
    denominator_previous = 3 ** (depth - 1)
    denominator = 3 * denominator_previous

    for n in range(RECURRENCE_SCAN + 1):
        digit = n & 1
        child = bottom_successor(n)
        current = bottom_prefix_numerator(n, depth)
        previous_child = bottom_prefix_numerator(child, depth - 1)
        assert current == digit * denominator_previous + 2 * previous_child

        sigma_current = (
            denominator
            + bottom_prefix_numerator(n + 1, depth)
            - bottom_prefix_numerator(n, depth)
        )
        if n % 2:
            target = syracuse(n)
            sigma_target_previous = (
                denominator_previous
                + bottom_prefix_numerator(target + 1, depth - 1)
                - bottom_prefix_numerator(target, depth - 1)
            )
            assert sigma_current == 2 * sigma_target_previous
        else:
            r = n // 2
            first = 3 * r
            sigma_first_previous = (
                denominator_previous
                + bottom_prefix_numerator(first + 1, depth - 1)
                - bottom_prefix_numerator(first, depth - 1)
            )
            sigma_second_previous = (
                denominator_previous
                + bottom_prefix_numerator(first + 2, depth - 1)
                - bottom_prefix_numerator(first + 1, depth - 1)
            )
            assert sigma_current == 2 * (
                sigma_first_previous + sigma_second_previous
            )

    # The subadditivity-defect renormalization is another exact prefix
    # identity when one digit is peeled from each term.
    for r in range(1, RECURRENCE_SCAN // 2 + 1):
        current = (
            2 * bottom_prefix_numerator(2 * r, depth)
            - bottom_prefix_numerator(4 * r, depth)
        )
        previous = (
            2 * bottom_prefix_numerator(3 * r, depth - 1)
            - bottom_prefix_numerator(6 * r, depth - 1)
        )
        assert current == 2 * previous

    print(
        "exact prefix recurrences: PASS "
        f"(0<=n<={RECURRENCE_SCAN}, depth={DEPTH})"
    )


def certify_counterexamples() -> None:
    """Certify small failures of natural monotonicity claims."""

    # sigma itself can go either direction even on an even Syracuse step.
    sigma_1 = sigma_interval(1)
    sigma_2 = sigma_interval(2)
    sigma_3 = sigma_interval(3)
    sigma_6 = sigma_interval(6)
    sigma_12 = sigma_interval(12)
    assert_disjoint_below(sigma_1, sigma_2)  # 2 -> 1 decreases
    assert_disjoint_below(sigma_12, sigma_6)  # 12 -> 6 increases

    # sigma(n)/n also goes both ways on even steps.
    assert_disjoint_below(
        Interval(sigma_2.low / 2, sigma_2.high / 2), sigma_1
    )
    assert_disjoint_below(
        Interval(sigma_3.low / 3, sigma_3.high / 3),
        Interval(sigma_6.low / 6, sigma_6.high / 6),
    )

    # The even slope of the H-conjugated Syracuse map can contract or expand.
    sigma_14 = sigma_interval(14)
    sigma_28 = sigma_interval(28)
    sigma_63 = sigma_interval(63)
    sigma_126 = sigma_interval(126)
    assert_disjoint_below(sigma_28, sigma_14)  # slope at cell 28 > 1
    assert_disjoint_below(sigma_63, sigma_126)  # slope at cell 126 < 1

    print("certified monotonicity counterexamples:")
    print(
        "  sigma under even T: 2->1 decreases, 12->6 increases; "
        f"sigma(1)={fmt_interval(sigma_1)}, "
        f"sigma(2)={fmt_interval(sigma_2)}, "
        f"sigma(6)={fmt_interval(sigma_6)}, "
        f"sigma(12)={fmt_interval(sigma_12)}"
    )
    print(
        "  even conjugate slopes: sigma(14)/sigma(28)>1 and "
        "sigma(63)/sigma(126)<1"
    )


def scan_even_slopes() -> None:
    """Report rigorous enclosures for finite-scan slope extrema."""

    sigmas = [sigma_interval(n) for n in range(2 * SLOPE_SCAN + 1)]
    josephus = josephus_constant_interval()
    candidates: list[tuple[Fraction, int]] = []
    expanding = 0
    contracting = 0
    unresolved = 0
    for m in range(1, SLOPE_SCAN + 1):
        source = sigmas[2 * m]
        target = sigmas[m]
        ratio_midpoint = target.midpoint() / source.midpoint()
        candidates.append((ratio_midpoint, m))
        if target.low > source.high:
            expanding += 1
        elif target.high < source.low:
            contracting += 1
        else:
            unresolved += 1

        # Finite confirmations of the all-level stable-gap bounds proved in
        # the note: sigma(m)<=K(3), sigma(2m)>=(2/3)K(3), and hence the even
        # inverse-capacity ratio sigma(2m)/sigma(m)>=2/3.
        assert target.high < josephus.low
        assert source.low > Fraction(2, 3) * josephus.high
        assert 3 * source.low > 2 * target.high

    minimum_m = min(candidates)[1]
    maximum_m = max(candidates)[1]

    def ratio_bounds(m: int) -> Interval:
        source = sigmas[2 * m]
        target = sigmas[m]
        assert source.low > 0
        return Interval(target.low / source.high, target.high / source.low)

    minimum_bounds = ratio_bounds(minimum_m)
    maximum_bounds = ratio_bounds(maximum_m)
    assert all(
        minimum_bounds.high < ratio_bounds(m).low
        for m in range(1, SLOPE_SCAN + 1)
        if m != minimum_m
    )
    assert all(
        ratio_bounds(m).high < maximum_bounds.low
        for m in range(1, SLOPE_SCAN + 1)
        if m != maximum_m
    )

    print(
        f"even-slope exact interval scan (1<=m<={SLOPE_SCAN}, "
        f"depth={DEPTH}): contracting={contracting}, "
        f"expanding={expanding}, unresolved={unresolved}"
    )
    print(
        f"  smallest midpoint at m={minimum_m}: "
        f"{fmt_interval(ratio_bounds(minimum_m))}"
    )
    print(
        f"  largest midpoint at m={maximum_m}: "
        f"{fmt_interval(ratio_bounds(maximum_m))}"
    )
    print(
        "  stable-gap inequalities also certified throughout the scan: "
        "sigma(m)<K(3), sigma(2m)>(2/3)K(3), "
        "sigma(2m)/sigma(m)>2/3"
    )


def predecessors(m: int) -> tuple[int, ...]:
    """All positive normalized-Syracuse predecessors of m."""

    result = [2 * m]
    if m % 3 == 2:
        result.append((2 * m - 1) // 3)
    return tuple(result)


def scan_preimage_capacity() -> None:
    """Exact finite scan of sigma-capacity on full preimage levels."""

    sigma_cache: dict[int, Interval] = {}
    capacity_cache: dict[tuple[int, int], Interval] = {}

    def sigma_cached(n: int) -> Interval:
        if n not in sigma_cache:
            sigma_cache[n] = sigma_interval(n)
        return sigma_cache[n]

    def capacity(m: int, depth: int) -> Interval:
        key = (m, depth)
        if key in capacity_cache:
            return capacity_cache[key]
        if depth == 0:
            answer = sigma_cached(m)
        else:
            children = [capacity(p, depth - 1) for p in predecessors(m)]
            answer = Interval(
                sum((child.low for child in children), Fraction(0)),
                sum((child.high for child in children), Fraction(0)),
            )
        capacity_cache[key] = answer
        return answer

    print(
        "exact-depth predecessor sigma-capacity scan "
        f"(1<=root<={PREIMAGE_ROOT_SCAN}, root not 0 mod 3):"
    )
    for depth in range(1, PREIMAGE_DEPTH + 1):
        candidates: list[tuple[Fraction, int, Interval]] = []
        for root in range(1, PREIMAGE_ROOT_SCAN + 1):
            if root % 3 == 0:
                continue
            root_weight = sigma_cached(root)
            level_weight = capacity(root, depth)
            ratio = Interval(
                level_weight.low / root_weight.high,
                level_weight.high / root_weight.low,
            )
            candidates.append((ratio.midpoint(), root, ratio))
        _, root, ratio = min(candidates)
        assert all(
            ratio.high < rival.low
            for _, rival_root, rival in candidates
            if rival_root != root
        )
        print(
            f"  depth={depth:2d}: smallest enclosed ratio at root={root:4d}, "
            f"Cap(T^-{depth}{{root}})/sigma(root)={fmt_interval(ratio)}"
        )


def report_explicit_degeneracy() -> None:
    """Show two exact families that destroy uniform coercivity."""

    print("explicit small-span family n=2^k-1:")
    josephus = josephus_constant_interval()
    for k in (4, 8, 12, 16):
        n = 2**k - 1
        interval = sigma_interval(n)
        theorem_bound = josephus.high * Fraction(2, 3) ** k
        assert interval.high < theorem_bound
        print(
            f"  k={k:2d}, n={n:6d}, sigma(n)={fmt_interval(interval)}, "
            f"proved upper bound K(3)(2/3)^k<={fmt(theorem_bound)}"
        )

    print("subadditivity-defect degeneration m=7*2^k:")
    for k in (4, 8, 12, 16):
        m = 7 * 2**k
        interval = defect_interval(m)
        theorem_bound = 2 * Fraction(2, 3) ** k
        assert interval.high < theorem_bound
        print(
            f"  k={k:2d}, m={m:7d}, d(m)={fmt_interval(interval)}, "
            f"proved upper bound 2(2/3)^k={fmt(theorem_bound)}"
        )


def main() -> None:
    verify_prefix_recurrences()
    certify_counterexamples()
    scan_even_slopes()
    scan_preimage_capacity()
    report_explicit_degeneracy()
    print("all rational-span diagnostics: PASS")


if __name__ == "__main__":
    main()
