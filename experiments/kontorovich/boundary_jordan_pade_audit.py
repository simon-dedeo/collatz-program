#!/usr/bin/env python3
"""Exact audit for the degree-17 Padé remainder in the rank-two ruler.

This is deliberately not a numerical transcendence test.  It checks the
integer identities and finite regressions used by the elementary
precision-versus-height proof documented in
``docs/notes/boundary-jordan-mahler.md``.

The universal proof is algebraic; ``--emit`` records a bounded regression as
an independently replayable audit artifact.  ``--verify`` checks both the
artifact hash and every recorded row using Python integers only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mp
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFAULT_ARTIFACT = HERE / "boundary_jordan_pade_audit.json"

# The k=4096 regression intentionally records exact integers with more than
# 4,300 decimal digits.  This disables only Python's string-conversion guard;
# arithmetic remains exact.
sys.set_int_max_str_digits(0)


def place_sum(n: int) -> int:
    total = 0
    for t in range(1, n + 1):
        power = 1
        while t % (17 * power) == 0:
            power *= 17
        total += power
    return total


def dyadic_u_exponent(j: int, k: int) -> int:
    return (79 + 8 * j) * 17**k + 1024 * k * 17 ** max(k - 1, 0)


def triadic_u_exponent(j: int, k: int) -> int:
    return (59 + 6 * j) * 17**k + 768 * k * 17 ** max(k - 1, 0)


def height_exponent(j: int, k: int) -> int:
    # Independent closed form for sum_(i<k) f_ji, obtained from the two
    # geometric sums.  Keeping this separate from height_exponent_closed
    # catches the 16-fold product-height indexing error without an O(k^2)
    # regression.
    power = 17**k
    numerator = 768 * k * power + (187 + 102 * j) * (power - 1)
    assert numerator % 272 == 0
    fsum = numerator // 272
    return triadic_u_exponent(j, k) + 16 * fsum


def height_exponent_closed(j: int, k: int) -> int:
    numerator = (
        204 * j * 17**k
        + 1536 * k * 17**k
        + 1190 * 17**k
        - 102 * j
        - 187
    )
    assert numerator % 17 == 0
    return numerator // 17


def surplus(j: int, k: int) -> int:
    """D with 17*e_k = 2*G_k + D."""
    return 17 * dyadic_u_exponent(j, k) - 2 * height_exponent(j, k)


def surplus_closed(j: int, k: int) -> int:
    numerator = (
        1904 * j * 17**k
        + 14336 * k * 17**k
        + 20451 * 17**k
        + 204 * j
        + 374
    )
    assert numerator % 17 == 0
    return numerator // 17


def check_row(args: tuple[int, int]) -> dict[str, int]:
    j, k = args
    e = dyadic_u_exponent(j, k)
    f = triadic_u_exponent(j, k)
    g = height_exponent(j, k)
    d = surplus(j, k)
    assert g == height_exponent_closed(j, k)
    assert d == surplus_closed(j, k)
    assert 17 * e == 2 * g + d
    assert d >= 17**k
    return {"j": j, "k": k, "e": e, "f": f, "G": g, "D": d}


def canonical_payload(doc: dict) -> bytes:
    body = {k: v for k, v in doc.items() if k != "sha256_payload"}
    return json.dumps(body, sort_keys=True, separators=(",", ":")).encode()


def build(max_k: int, workers: int) -> dict:
    tasks = [(j, k) for j in range(1, 9) for k in range(max_k + 1)]
    with mp.Pool(processes=workers) as pool:
        rows = pool.map(check_row, tasks, chunksize=max(1, len(tasks) // (8 * workers)))

    # The Padé cancellation is coefficientwise and universal.  The direct
    # finite check catches indexing errors in placeSum at the first block.
    cancellation = []
    for n in range(1, 35):
        left = place_sum(n)
        right = place_sum(n - 1) + 1
        cancellation.append(
            {"n": n, "left_C_exponent": left, "right_C_exponent": right}
        )
    assert all(r["left_C_exponent"] == r["right_C_exponent"] for r in cancellation[:16])
    assert cancellation[16] == {
        "n": 17,
        "left_C_exponent": 33,
        "right_C_exponent": 17,
    }

    # Exact real-contraction gates.  No floating logarithms occur.
    assert 2**64 < 3**48
    for j in range(1, 9):
        assert 2 ** (15 + 8 * j) < 3 ** (11 + 6 * j)

    extrema = []
    for j in range(1, 9):
        jr = [r for r in rows if r["j"] == j]
        extrema.append(
            {
                "j": j,
                "min_surplus_ratio_numerator": min(r["D"] for r in jr),
                "at_k": min(jr, key=lambda r: r["D"])["k"],
                "last": jr[-1],
            }
        )

    doc = {
        "format": "boundary-jordan-pade-v1",
        "claim_scope": (
            "Exact coefficient cancellation through Z^16, the first Z^17 coefficient, "
            "closed exponent identities, contraction inequalities, and bounded integer "
            "regressions. The all-k irrationality argument is mathematical/Lean work, "
            "not certified merely by the bounded regression."
        ),
        "pade_remainder": "E(C,Z)=(1-C*Z)*H(C,Z)-1",
        "first_nonzero_term": "C^17*(C^16-1)*Z^17",
        "specialized_u_exponents": {
            "e_jk": "(79+8*j)*17^k + 1024*k*17^(k-1), with the k=0 shear term zero",
            "f_jk": "(59+6*j)*17^k + 768*k*17^(k-1), with the k=0 shear term zero",
        },
        "height_bound_exponent": "G_jk=f_jk+16*sum_(0<=i<k) f_ji",
        "precision_identity": "17*e_jk=2*G_jk+D_jk",
        "surplus_closed": (
            "17*D_jk=1904*j*17^k+14336*k*17^k+20451*17^k+204*j+374"
        ),
        "elementary_comparison": (
            "2^(17e)=4^G*2^D > 3^G*2^D; D>=17^k absorbs every fixed "
            "rational-height constant and the factor 17^k."
        ),
        "regression": {
            "j_min": 1,
            "j_max": 8,
            "k_min": 0,
            "k_max": max_k,
            "workers": workers,
            "rows_checked": len(rows),
            "extrema": extrema,
        },
        "cancellation_rows": cancellation,
        "negative_control": {
            "description": "At n=17 the two C exponents must differ; equality would erase the remainder.",
            "passed": cancellation[16]["left_C_exponent"] != cancellation[16]["right_C_exponent"],
        },
    }
    doc["sha256_payload"] = hashlib.sha256(canonical_payload(doc)).hexdigest()
    return doc


def verify(path: Path, workers: int) -> None:
    doc = json.loads(path.read_text())
    expected = hashlib.sha256(canonical_payload(doc)).hexdigest()
    assert doc["sha256_payload"] == expected
    assert doc["format"] == "boundary-jordan-pade-v1"
    reg = doc["regression"]
    rebuilt = build(int(reg["k_max"]), workers)
    # Runtime worker count is intentionally not hash-significant for meaning.
    rebuilt["regression"]["workers"] = reg["workers"]
    rebuilt["sha256_payload"] = hashlib.sha256(canonical_payload(rebuilt)).hexdigest()
    assert rebuilt == doc
    print(
        f"verified {path}: {reg['rows_checked']} exact exponent rows; "
        f"sha256={expected}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--emit", action="store_true")
    mode.add_argument("--verify", action="store_true")
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--max-k", type=int, default=4096)
    parser.add_argument("--workers", type=int, default=max(1, mp.cpu_count()))
    args = parser.parse_args()
    if args.emit:
        doc = build(args.max_k, args.workers)
        args.artifact.write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n")
        print(
            f"wrote {args.artifact}: {doc['regression']['rows_checked']} rows; "
            f"sha256={doc['sha256_payload']}"
        )
    else:
        verify(args.artifact, args.workers)


if __name__ == "__main__":
    main()
