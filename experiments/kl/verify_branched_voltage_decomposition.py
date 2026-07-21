#!/usr/bin/env python3
"""Exact sparse audit of the annealed KL three-sheet decomposition.

For level ``k`` the KL coordinates are the residues ``m == 2 (mod 3)``
modulo ``3**k``.  The annealed operator is a formal weighted sum

    A_k = tau * T_k + w_2 * B_{2,k} + w_8 * B_{8,k},

where ``T_k`` is transport and each ``B`` includes the literal factor ``1/3``
from averaging a ternary branch fiber.  This checker keeps the three edge
types separate.  Thus proving an intertwining identity for all three proves it
for arbitrary weights; no floating value of lambda is used.

With ``n=3**(k-2)``, the coarse projection is

    (P_k x)[u] = (x[u] + x[u+n] + x[u+2*n]) / 3.

The audit exhausts every row/fiber through the requested level and checks:

* ``P_k E_k = E_{k-1} P_k`` for each edge type E;
* the branch maps annihilate ``ker(P_k)``;
* transport is a coordinate permutation preserving ``ker(P_k)``;
* transport blocks over a coarse edge are 3-by-3 permutation matrices;
* branch blocks over a *fixed coarse branch edge* are rank-one sheet resets
  (one full row of exact entries ``1/3``), not the base-edge weight ``1/3``
  times permutation matrices required by an ordinary weighted voltage lift.
  Their transposes are rank-one resets as well, so reversing row/column
  orientation does not repair the ordinary-cover axiom.

All arithmetic is integer or ``fractions.Fraction``.  The script does not
claim that a published definition of a factored/branched lift applies; it
only establishes the exact incidence structure that such a definition would
have to encode.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable


EDGE_TYPES = ("transport", "type_two", "type_eight")


@dataclass(frozen=True)
class LevelMaps:
    level: int
    states: tuple[int, ...]
    transport: tuple[int, ...]
    type_two: tuple[tuple[int, ...], ...]
    type_eight: tuple[tuple[int, ...], ...]

    @property
    def count(self) -> int:
        return len(self.states)


def build_level_maps(level: int) -> LevelMaps:
    """Build the literal KL row-to-dependency incidence maps."""

    if level < 2:
        raise ValueError("the audited KL incidence maps start at level 2")
    modulus = 3**level
    coarse_modulus = 3 ** (level - 1)
    states = tuple(range(2, modulus, 3))
    positions = {state: index for index, state in enumerate(states)}

    transport: list[int] = []
    type_two: list[tuple[int, ...]] = []
    type_eight: list[tuple[int, ...]] = []
    for state in states:
        transport.append(positions[(4 * state) % modulus])
        if state % 9 == 2:
            target = ((4 * state - 2) // 3) % coarse_modulus
            type_two.append(
                tuple(
                    positions[target + digit * coarse_modulus]
                    for digit in range(3)
                )
            )
        else:
            type_two.append(())
        if state % 9 == 8:
            target = ((2 * state - 1) // 3) % coarse_modulus
            type_eight.append(
                tuple(
                    positions[target + digit * coarse_modulus]
                    for digit in range(3)
                )
            )
        else:
            type_eight.append(())

    result = LevelMaps(
        level=level,
        states=states,
        transport=tuple(transport),
        type_two=tuple(type_two),
        type_eight=tuple(type_eight),
    )
    expected_count = 3 ** (level - 1)
    if result.count != expected_count:
        raise AssertionError(
            f"level {level}: got {result.count} states, expected {expected_count}"
        )
    return result


def row_entries(
    maps: LevelMaps, edge_type: str, row: int
) -> tuple[tuple[int, Fraction], ...]:
    """Return one formal edge-type row, including branch factors 1/3."""

    if edge_type == "transport":
        return ((maps.transport[row], Fraction(1)),)
    if edge_type == "type_two":
        return tuple((column, Fraction(1, 3)) for column in maps.type_two[row])
    if edge_type == "type_eight":
        return tuple(
            (column, Fraction(1, 3)) for column in maps.type_eight[row]
        )
    raise ValueError(f"unknown edge type {edge_type!r}")


def add_coefficient(
    coefficients: dict[int, Fraction], column: int, value: Fraction
) -> None:
    coefficients[column] = coefficients.get(column, Fraction(0)) + value
    if coefficients[column] == 0:
        del coefficients[column]


def projected_fine_row(
    fine: LevelMaps, edge_type: str, coarse_row: int
) -> dict[int, Fraction]:
    """Sparse row of ``P_k E_k`` in fine input coordinates."""

    coarse_count = fine.count // 3
    result: dict[int, Fraction] = {}
    for sheet in range(3):
        fine_row = coarse_row + sheet * coarse_count
        for column, coefficient in row_entries(fine, edge_type, fine_row):
            add_coefficient(result, column, Fraction(1, 3) * coefficient)
    return result


def coarse_row_after_projection(
    coarse: LevelMaps, edge_type: str, coarse_row: int
) -> dict[int, Fraction]:
    """Sparse row of ``E_{k-1} P_k`` in fine input coordinates."""

    fine_count = 3 * coarse.count
    if fine_count <= 0:
        raise AssertionError("invalid fine state count")
    result: dict[int, Fraction] = {}
    for coarse_column, coefficient in row_entries(coarse, edge_type, coarse_row):
        for sheet in range(3):
            fine_column = coarse_column + sheet * coarse.count
            add_coefficient(result, fine_column, coefficient * Fraction(1, 3))
    return result


def verify_quotient_intertwining(fine: LevelMaps, coarse: LevelMaps) -> None:
    """Exhaustively check ``P E_k = E_{k-1} P`` componentwise."""

    if fine.level != coarse.level + 1 or fine.count != 3 * coarse.count:
        raise AssertionError("incompatible adjacent levels")
    for edge_type in EDGE_TYPES:
        for row in range(coarse.count):
            left = projected_fine_row(fine, edge_type, row)
            right = coarse_row_after_projection(coarse, edge_type, row)
            if left != right:
                raise AssertionError(
                    f"level {fine.level}, {edge_type}, coarse row {row}: "
                    f"P E != E P\nleft={left}\nright={right}"
                )


def column_signatures(
    maps: LevelMaps, edge_type: str
) -> tuple[tuple[tuple[int, Fraction], ...], ...]:
    """Return exact sparse columns of one edge-type matrix."""

    columns: list[list[tuple[int, Fraction]]] = [
        [] for _ in range(maps.count)
    ]
    for row in range(maps.count):
        for column, coefficient in row_entries(maps, edge_type, row):
            columns[column].append((row, coefficient))
    return tuple(tuple(entries) for entries in columns)


def verify_branch_annihilates_detail(maps: LevelMaps) -> None:
    """Check both branch maps vanish on the canonical basis of ker(P)."""

    coarse_count = maps.count // 3
    for edge_type in ("type_two", "type_eight"):
        columns = column_signatures(maps, edge_type)
        for coarse_column in range(coarse_count):
            signatures = tuple(
                columns[coarse_column + sheet * coarse_count]
                for sheet in range(3)
            )
            if not signatures[0] == signatures[1] == signatures[2]:
                raise AssertionError(
                    f"level {maps.level}, {edge_type}, input fiber "
                    f"{coarse_column}: branch columns differ: {signatures}"
                )


def inverse_permutation(permutation: tuple[int, ...]) -> tuple[int, ...]:
    inverse = [-1] * len(permutation)
    for row, column in enumerate(permutation):
        if not 0 <= column < len(permutation):
            raise AssertionError(f"permutation target {column} is out of range")
        if inverse[column] != -1:
            raise AssertionError(
                f"columns {inverse[column]} and {row} both map to {column}"
            )
        inverse[column] = row
    if any(row == -1 for row in inverse):
        raise AssertionError("transport misses a coordinate")
    return tuple(inverse)


def verify_transport_detail_permutation(maps: LevelMaps) -> None:
    """Check transport is a coordinate permutation preserving fine fibers."""

    inverse = inverse_permutation(maps.transport)
    coarse_count = maps.count // 3
    for coarse_column in range(coarse_count):
        preimage_rows = tuple(
            inverse[coarse_column + sheet * coarse_count]
            for sheet in range(3)
        )
        coarse_rows = {row % coarse_count for row in preimage_rows}
        output_sheets = {row // coarse_count for row in preimage_rows}
        if len(coarse_rows) != 1 or output_sheets != {0, 1, 2}:
            raise AssertionError(
                f"level {maps.level}, input fiber {coarse_column}: transport "
                f"preimages {preimage_rows} do not form one output fiber"
            )


def incidence_block(
    fine: LevelMaps,
    edge_type: str,
    coarse_row: int,
    coarse_column: int,
) -> tuple[tuple[Fraction, Fraction, Fraction], ...]:
    """Return the literal weighted block over one coarse row/column pair."""

    coarse_count = fine.count // 3
    rows: list[tuple[Fraction, Fraction, Fraction]] = []
    for output_sheet in range(3):
        fine_row = coarse_row + output_sheet * coarse_count
        dependencies = {
            column: coefficient
            for column, coefficient in row_entries(fine, edge_type, fine_row)
        }
        rows.append(
            tuple(
                dependencies.get(
                    coarse_column + input_sheet * coarse_count,
                    Fraction(0),
                )
                for input_sheet in range(3)
            )
        )
    return tuple(rows)


def is_weighted_permutation_block(
    block: tuple[tuple[Fraction, ...], ...], edge_weight: Fraction
) -> bool:
    """Test the fixed-base-edge axiom for a regular weighted lift."""

    return (
        all(
            sorted(row) == [Fraction(0), Fraction(0), edge_weight]
            for row in block
        )
        and all(
            sorted(block[row][column] for row in range(3))
            == [Fraction(0), Fraction(0), edge_weight]
            for column in range(3)
        )
    )


def is_row_reset_block(
    block: tuple[tuple[Fraction, ...], ...], edge_weight: Fraction
) -> bool:
    row_sums = sorted(sum(row) for row in block)
    column_sums = [sum(block[row][column] for row in range(3)) for column in range(3)]
    return (
        row_sums == [Fraction(0), Fraction(0), 3 * edge_weight]
        and column_sums == [edge_weight, edge_weight, edge_weight]
        and all(entry in (Fraction(0), edge_weight) for row in block for entry in row)
    )


def transpose_block(
    block: tuple[tuple[Fraction, ...], ...]
) -> tuple[tuple[Fraction, Fraction, Fraction], ...]:
    return tuple(tuple(block[row][column] for row in range(3)) for column in range(3))


@dataclass(frozen=True)
class BlockAudit:
    transport_blocks: int
    branch_blocks: int
    first_branch_witness: tuple[
        str, int, int, tuple[tuple[Fraction, Fraction, Fraction], ...]
    ]


def verify_voltage_and_reset_blocks(
    fine: LevelMaps, coarse: LevelMaps
) -> BlockAudit:
    """Separate voltage-permutation transport from rank-one branch resets."""

    transport_blocks = 0
    for coarse_row in range(coarse.count):
        coarse_column = coarse.transport[coarse_row]
        block = incidence_block(
            fine, "transport", coarse_row, coarse_column
        )
        if not is_weighted_permutation_block(block, Fraction(1)):
            raise AssertionError(
                f"level {fine.level}, transport edge "
                f"{coarse_row}->{coarse_column}: block is not a permutation: {block}"
            )
        transport_blocks += 1

    branch_blocks = 0
    first_witness: tuple[
        str, int, int, tuple[tuple[Fraction, Fraction, Fraction], ...]
    ] | None = None
    for edge_type in ("type_two", "type_eight"):
        for coarse_row in range(coarse.count):
            coarse_dependencies = tuple(
                column
                for column, _ in row_entries(coarse, edge_type, coarse_row)
            )
            for coarse_column in coarse_dependencies:
                block = incidence_block(
                    fine, edge_type, coarse_row, coarse_column
                )
                edge_weight = Fraction(1, 3)
                if not is_row_reset_block(block, edge_weight):
                    raise AssertionError(
                        f"level {fine.level}, {edge_type} edge "
                        f"{coarse_row}->{coarse_column}: expected one full reset "
                        f"row, got {block}"
                    )
                if is_weighted_permutation_block(block, edge_weight):
                    raise AssertionError("a rank-one reset was a permutation block")
                transposed = transpose_block(block)
                if is_weighted_permutation_block(transposed, edge_weight):
                    raise AssertionError(
                        "transposing a branch reset unexpectedly made it a permutation"
                    )
                if first_witness is None:
                    first_witness = (
                        edge_type,
                        coarse_row,
                        coarse_column,
                        block,
                    )
                branch_blocks += 1

    if first_witness is None:
        raise AssertionError("no branch block was audited")
    return BlockAudit(
        transport_blocks=transport_blocks,
        branch_blocks=branch_blocks,
        first_branch_witness=first_witness,
    )


def format_fraction(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else str(value)


def format_block(block: Iterable[Iterable[Fraction]]) -> str:
    return "[" + "; ".join(
        " ".join(format_fraction(entry) for entry in row) for row in block
    ) + "]"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-level",
        type=int,
        default=10,
        help="largest fine level to audit (default: 10)",
    )
    args = parser.parse_args()
    if args.max_level < 3:
        parser.error("--max-level must be at least 3")
    return args


def main() -> None:
    args = parse_args()
    totals = defaultdict(int)
    for level in range(3, args.max_level + 1):
        fine = build_level_maps(level)
        coarse = build_level_maps(level - 1)
        verify_quotient_intertwining(fine, coarse)
        verify_branch_annihilates_detail(fine)
        verify_transport_detail_permutation(fine)
        blocks = verify_voltage_and_reset_blocks(fine, coarse)
        totals["fine_rows"] += fine.count
        totals["coarse_rows"] += coarse.count
        totals["transport_blocks"] += blocks.transport_blocks
        totals["branch_blocks"] += blocks.branch_blocks
        edge_type, row, column, witness = blocks.first_branch_witness
        print(
            f"k={level:2d} fine={fine.count:7d} coarse={coarse.count:7d}  "
            f"PASS quotient/detail; transport_blocks={blocks.transport_blocks}; "
            f"reset_blocks={blocks.branch_blocks}; first_reset="
            f"{edge_type}:{row}->{column} {format_block(witness)}"
        )

    print()
    print(
        "EXACT PASS: componentwise P_k E_k = E_(k-1) P_k; both branch "
        "averages annihilate ker(P_k); transport is a coordinate permutation "
        "preserving ker(P_k)."
    )
    print(
        "COVER SCOPE: transport blocks are ordinary 3-sheet permutation "
        "blocks.  Every fixed coarse branch-edge block is a rank-one sheet "
        "reset (one full row of exact 1/3 entries), not the base-edge weight "
        "1/3 times a permutation; it remains non-permutation after transpose. "
        "The full annealed refinement is therefore not an ordinary weighted "
        "voltage lift in either row/column orientation."
    )
    print(
        f"AUDITED levels 3..{args.max_level}: fine_rows={totals['fine_rows']}, "
        f"coarse_rows={totals['coarse_rows']}, "
        f"transport_blocks={totals['transport_blocks']}, "
        f"branch_reset_blocks={totals['branch_blocks']}"
    )


if __name__ == "__main__":
    main()
