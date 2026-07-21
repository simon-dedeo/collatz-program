#!/usr/bin/env python3
"""Exact finite core of the annealed-floor obstruction to two fitted envelopes.

Let ``A_lambda^(k)`` be the linear KL operator obtained by replacing each
three-fiber minimum by its average.  Aggregating one ternary digit intertwines
these operators exactly:

    P A_lambda^(k) = A_lambda^(k-1) P.

For normalized critical KL eigenvectors with ``1 < lambda <= 2``, or feasible
vectors in that range whose aggregate normalized slack vanishes, any
localization estimate that forces the terminal fiber defect to zero also
forces ``lambda -> 2``.  The positive difference
``A_lambda c-c`` then has total mass ``s(lambda)-1 -> 0``.  The intertwining
identity implies that every fixed marginal converges to the unique normalized
right Perron vector of the corresponding annealed operator at lambda=2.
Consequently, any proposed uniform fixed-depth envelope must lie above this
``annealed floor``.

This standard-library verifier checks the finite algebra behind that argument:

* the finite quotient/carry reduction behind all-level projection
  intertwining, plus the full symbolic sparse matrices through k=8;
* the exact lambda=2 annealed Perron vectors at levels 2 and 3;
* the first entropy floor is strictly above ``(1/5)(3/4)^1`` using rational
  logarithm bounds; and
* the second L1 martingale floor is strictly above
  ``(1/2)(9/10)^2`` by an exact rational margin.

Thus both geometric fits remain valid finite diagnostics, but neither can be
the stated all-level critical-family theorem.  This does not refute relative
L1 compactness, a polynomial entropy envelope, or any looser bound above the
annealed floor.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction


TRANSPORT = "transport"
BRANCH_2 = "branch_2"
BRANCH_8 = "branch_8"
ANNEALED_COEFFICIENTS = {
    TRANSPORT: Fraction(1, 4),
    BRANCH_2: Fraction(1, 4),
    BRANCH_8: Fraction(1, 2),
}
LEVEL_2_PERRON = tuple(Fraction(value, 21) for value in (8, 2, 11))
LEVEL_3_NUMERATORS = (9632, 4316, 5240, 6392, 2408, 17246, 17264, 1598, 23285)
LEVEL_3_PERRON = tuple(Fraction(value, 87381) for value in LEVEL_3_NUMERATORS)


def build_rows(k: int) -> list[list[tuple[int, str]]]:
    """Build the sparse annealed row pattern with symbolic coefficient labels."""

    if k < 2:
        raise ValueError("the KL state system starts at level two")
    modulus = 3**k
    coarse_modulus = 3 ** (k - 1)
    states = tuple(range(2, modulus, 3))
    index = {state: i for i, state in enumerate(states)}
    rows: list[list[tuple[int, str]]] = []
    for state in states:
        row = [(index[(4 * state) % modulus], TRANSPORT)]
        branch = state % 9
        if branch == 2:
            coarse = ((4 * state - 2) // 3) % coarse_modulus
            label = BRANCH_2
        elif branch == 8:
            coarse = ((2 * state - 1) // 3) % coarse_modulus
            label = BRANCH_8
        else:
            if branch != 5:
                raise AssertionError("unexpected KL residue class")
            rows.append(row)
            continue
        row.extend(
            (index[coarse + digit * coarse_modulus], label)
            for digit in range(3)
        )
        rows.append(row)
    return rows


def apply_annealed(
    rows: list[list[tuple[int, str]]],
    vector: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    if len(rows) != len(vector):
        raise ValueError("annealed matrix and vector dimensions differ")
    return tuple(
        sum(ANNEALED_COEFFICIENTS[label] * vector[source] for source, label in row)
        for row in rows
    )


def project(vector: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """Aggregate the three highest-digit blocks exactly."""

    if len(vector) % 3:
        raise ValueError("a ternary state vector must have three equal blocks")
    block = len(vector) // 3
    return tuple(
        vector[i] + vector[i + block] + vector[i + 2 * block]
        for i in range(block)
    )


def verify_symbolic_intertwining(first_k: int = 3, last_k: int = 8) -> None:
    """Compare every sparse coefficient of ``P A_k`` and ``A_(k-1) P``."""

    for k in range(first_k, last_k + 1):
        fine_rows = build_rows(k)
        coarse_rows = build_rows(k - 1)
        coarse_size = len(coarse_rows)
        for output in range(coarse_size):
            left: defaultdict[tuple[int, str], int] = defaultdict(int)
            for lift in range(3):
                for source, label in fine_rows[output + lift * coarse_size]:
                    left[(source, label)] += 1

            right: defaultdict[tuple[int, str], int] = defaultdict(int)
            for coarse_source, label in coarse_rows[output]:
                for lift in range(3):
                    right[(coarse_source + lift * coarse_size, label)] += 1
            if left != right:
                raise AssertionError(
                    f"projection intertwining failed at k={k}, output={output}"
                )
    print(
        "PASS: symbolic-weight annealed projection intertwining for "
        f"k={first_k},...,{last_k}"
    )


def verify_generic_carry_reduction() -> None:
    """Check every local carry case in the all-level intertwining proof.

    Aggregating a fine output row sums its three lift digits ``e``.  For the
    transport source, multiplication by four sends the source lift to
    ``carry+4e = carry+e (mod 3)``, hence permutes all three lifts.  A type-2
    branch uses the same multiplier four, while a type-8 branch uses two;
    both permute the intermediate lift digit, and the branch's own lift digit
    supplies the second independent coordinate.  The mod-9 branch label is
    unchanged because every fine output lift is a multiple of nine for k>=3.
    These are all quotient/carry cases left after the displayed index formulas
    are reduced modulo the coarse power of three.
    """

    digits = tuple(range(3))
    for branch_residue in (2, 5, 8):
        for lift in digits:
            if (branch_residue + 9 * lift) % 9 != branch_residue:
                raise AssertionError("fine lift changed its mod-9 branch label")

    for carry in range(4):
        transport_lifts = sorted((carry + 4 * lift) % 3 for lift in digits)
        if transport_lifts != list(digits):
            raise AssertionError("transport lift map is not a permutation")

    expected_branch_lifts = sorted(
        (middle, high) for middle in digits for high in digits
    )
    for multiplier in (4, 2):
        for carry in digits:
            actual = sorted(
                ((carry + multiplier * output_lift) % 3, branch_lift)
                for output_lift in digits
                for branch_lift in digits
            )
            if actual != expected_branch_lifts:
                raise AssertionError("branch lift-pair map is not bijective")
    print("PASS: generic quotient/carry reduction for every level k>=3")


def verify_irreducible_transport(k: int) -> None:
    """Check that the transport edges alone form one full state cycle."""

    rows = build_rows(k)
    seen: set[int] = set()
    state = 0
    while state not in seen:
        seen.add(state)
        transport = [source for source, label in rows[state] if label == TRANSPORT]
        if len(transport) != 1:
            raise AssertionError("every row must have one transport edge")
        state = transport[0]
    if state != 0 or len(seen) != len(rows):
        raise AssertionError(f"level-{k} transport is not one full cycle")


def martingale_increment(
    children: tuple[Fraction, ...],
) -> Fraction:
    parents = project(children)
    parent_count = len(parents)
    return sum(
        abs(3 * children[parent + digit * parent_count] - parents[parent])
        for digit in range(3)
        for parent in range(parent_count)
    ) / 3


def log_lower_bound_one_term(x: Fraction) -> Fraction:
    """Rigorous lower bound from the atanh series for ``log(x)``.

    With ``z=(x-1)/(x+1)``,

        log(x) = 2 sum_(n>=0) z^(2n+1)/(2n+1).

    For positive z, the first term is a strict lower bound.  For negative z,
    the omitted absolute tail is at most
    ``2 |z|^3 / (3(1-|z|^2))``.
    """

    if x <= 0:
        raise ValueError("logarithms require positive arguments")
    z = (x - 1) / (x + 1)
    bound = 2 * z
    if z < 0:
        magnitude = -z
        bound -= 2 * magnitude**3 / (3 * (1 - magnitude**2))
    return bound


def verify_perron_floors() -> None:
    rows_2 = build_rows(2)
    rows_3 = build_rows(3)
    for k in (2, 3):
        verify_irreducible_transport(k)
        column_sums = [Fraction(0) for _ in build_rows(k)]
        for row in build_rows(k):
            for source, label in row:
                column_sums[source] += ANNEALED_COEFFICIENTS[label]
        if any(total != 1 for total in column_sums):
            raise AssertionError(f"level-{k} annealed matrix is not stochastic")

    if sum(LEVEL_2_PERRON) != 1 or apply_annealed(rows_2, LEVEL_2_PERRON) != LEVEL_2_PERRON:
        raise AssertionError("level-2 annealed Perron vector failed")
    if sum(LEVEL_3_PERRON) != 1 or apply_annealed(rows_3, LEVEL_3_PERRON) != LEVEL_3_PERRON:
        raise AssertionError("level-3 annealed Perron vector failed")
    if project(LEVEL_3_PERRON) != LEVEL_2_PERRON:
        raise AssertionError("annealed Perron marginals are inconsistent")

    entropy_lower = sum(
        probability * log_lower_bound_one_term(3 * probability)
        for probability in LEVEL_2_PERRON
    )
    entropy_fit = Fraction(1, 5) * Fraction(3, 4)
    if entropy_lower <= entropy_fit:
        raise AssertionError("rational entropy bound does not clear fitted envelope")

    delta_2 = martingale_increment(LEVEL_3_PERRON)
    delta_fit = Fraction(1, 2) * Fraction(9, 10) ** 2
    if delta_2 <= delta_fit:
        raise AssertionError("annealed L1 floor does not clear fitted envelope")

    print(
        "PASS: exact annealed Perron marginals at levels 2 and 3; "
        "level-2 law=(8,2,11)/21"
    )
    print(
        "PASS: entropy floor > "
        f"{entropy_lower} > {entropy_fit}, margin > "
        f"{entropy_lower - entropy_fit}"
    )
    print(
        "PASS: L1 floor="
        f"{delta_2} > {delta_fit}, exact margin={delta_2 - delta_fit}"
    )
    print(
        "CONCLUSION: the two fitted geometric envelopes cannot extend to "
        "an all-level critical or vanishing-slack family in 1<lambda<=2"
    )


def main() -> None:
    verify_generic_carry_reduction()
    verify_symbolic_intertwining()
    verify_perron_floors()


if __name__ == "__main__":
    main()
