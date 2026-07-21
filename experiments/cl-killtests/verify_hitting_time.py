#!/usr/bin/env python3
"""Exact finite check of the backward-orbit hitting-time formula.

The general proof is recorded in docs/FOR_CLEAN_LEAN.md.  This script is an
independent bounded check: for every 1 <= J <= max_j it enumerates t from zero
until 2*4^t == -1 (mod 3^J), then compares the first hit with
(3^(J-1)-1)/2.  Python integers are exact.
"""

from __future__ import annotations

import argparse


def first_hit(j: int) -> int:
    modulus = 3**j
    residue = 2 % modulus
    target = modulus - 1
    for t in range((3 ** (j - 1) - 1) // 2 + 1):
        if residue == target:
            return t
        residue = (4 * residue) % modulus
    raise AssertionError(f"no hit found through the predicted time for J={j}")


def verify(max_j: int) -> None:
    if max_j < 1:
        raise ValueError("max_j must be positive")

    for j in range(1, max_j + 1):
        predicted = (3 ** (j - 1) - 1) // 2
        observed = first_hit(j)
        assert observed == predicted, (j, observed, predicted)

        modulus = 3**j
        assert (2 * pow(4, predicted, modulus) + 1) % modulus == 0

        in_depth_window = predicted < j
        assert in_depth_window == (j <= 2)

        print(
            f"J={j:2d} modulus={modulus:7d} "
            f"first_hit={observed:6d} in_E_J={in_depth_window}"
        )

    print(f"PASS: exact first-hit formula verified for J=1..{max_j}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=12)
    args = parser.parse_args()
    verify(args.max_j)


if __name__ == "__main__":
    main()
