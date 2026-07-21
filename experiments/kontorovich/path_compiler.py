#!/usr/bin/env python3
"""Exact compiler and verifier for Kontorovich--Sinai valuation words.

For the accelerated odd Collatz map

    T(x) = (3*x + 1) / 2^v2(3*x+1),

a word ``k = (k_0, ..., k_(N-1))`` of positive valuations has affine data

    2^S T^N(x) = 3^N x + A,
    S = sum(k),
    A = sum_j 3^(N-1-j) 2^(sum_(i<j) k_i).

For each admissible residue epsilon in {1,5} modulo 6 there is one canonical
least positive seed modulo 6*2^S realizing the word exactly.  Certificates
store the redundant affine data, but verification recomputes everything and
replays every accelerated step with Python's arbitrary-precision integers.

This file is deliberately dependency-free.  It is search infrastructure, not
evidence for or against Collatz by itself.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


PATH_SCHEMA = "collatz-k-path-v1"
CYCLE_SCHEMA = "collatz-accelerated-cycle-v1"
MAP_NAME = "accelerated_odd_3x_plus_1"


def v2(n: int) -> int:
    """Return the 2-adic valuation of a nonzero integer."""
    if n == 0:
        raise ValueError("v2(0) is not finite")
    n = abs(n)
    return (n & -n).bit_length() - 1


def accelerated_step(n: int) -> tuple[int, int]:
    """One accelerated step on a positive odd integer, returning (image, k)."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("accelerated_step requires a positive odd integer")
    a = 3 * n + 1
    k = v2(a)
    return a >> k, k


@dataclass(frozen=True)
class AffineBlock:
    """The exact numerator data for a finite accelerated path."""

    steps: int
    halvings: int
    constant: int

    @staticmethod
    def identity() -> "AffineBlock":
        return AffineBlock(0, 0, 0)

    @staticmethod
    def letter(k: int) -> "AffineBlock":
        if not isinstance(k, int) or isinstance(k, bool) or k <= 0:
            raise ValueError("every valuation k must be a positive integer")
        return AffineBlock(1, k, 1)

    def then(self, other: "AffineBlock") -> "AffineBlock":
        """Concatenate path blocks: execute ``self`` and then ``other``."""
        # A_(uv) = 3^|v| A_u + 2^S_u A_v.
        return AffineBlock(
            self.steps + other.steps,
            self.halvings + other.halvings,
            pow(3, other.steps) * self.constant
            + (1 << self.halvings) * other.constant,
        )

    @property
    def three_power(self) -> int:
        return pow(3, self.steps)

    @property
    def two_power(self) -> int:
        return 1 << self.halvings

    @property
    def cycle_denominator(self) -> int:
        return self.two_power - self.three_power


def affine_block(word: Iterable[int]) -> AffineBlock:
    block = AffineBlock.identity()
    for k in word:
        block = block.then(AffineBlock.letter(k))
    if block.steps == 0:
        raise ValueError("valuation word must be nonempty")
    return block


@dataclass(frozen=True)
class CompiledPath:
    schema: str
    map: str
    word: tuple[int, ...]
    residue_mod_6: int
    seed: int
    seed_modulus: int
    endpoint: int
    endpoint_stride: int
    affine_constant: int
    total_halvings: int
    accelerated_steps: int

    def json_dict(self) -> dict[str, object]:
        out = asdict(self)
        # JSON consumers in languages without unbounded integers must not
        # silently round certificate fields.
        for key in (
            "seed",
            "seed_modulus",
            "endpoint",
            "endpoint_stride",
            "affine_constant",
        ):
            out[key] = str(out[key])
        out["word"] = list(self.word)
        return out


def _validate_residue(residue_mod_6: int) -> None:
    if residue_mod_6 not in (1, 5):
        raise ValueError("residue_mod_6 must be 1 or 5")


def compile_block(
    block: AffineBlock, residue_mod_6: int, word: Sequence[int] = ()
) -> CompiledPath:
    """Compile affine data to its least positive seed in a class modulo 6.

    Exactness of the final valuation fixes x modulo 2^(S+1):

        3^N x + A == 2^S (mod 2^(S+1)).

    CRT with x == residue_mod_6 (mod 3) gives a unique class modulo
    3*2^(S+1) = 6*2^S.
    """
    _validate_residue(residue_mod_6)
    if block.steps <= 0 or block.halvings < block.steps:
        raise ValueError("invalid affine block")
    modulus_two = 1 << (block.halvings + 1)
    rhs = (1 << block.halvings) - block.constant
    residue_two = (
        rhs * pow(block.three_power, -1, modulus_two)
    ) % modulus_two
    lift = (
        (residue_mod_6 - residue_two) * pow(modulus_two, -1, 3)
    ) % 3
    seed = residue_two + modulus_two * lift
    modulus = 3 * modulus_two
    if seed <= 0 or seed >= modulus:
        raise AssertionError("CRT did not return the canonical positive seed")
    numerator = block.three_power * seed + block.constant
    if numerator % block.two_power:
        raise AssertionError("compiled affine numerator is not integral")
    endpoint = numerator // block.two_power
    compiled = CompiledPath(
        schema=PATH_SCHEMA,
        map=MAP_NAME,
        word=tuple(word),
        residue_mod_6=residue_mod_6,
        seed=seed,
        seed_modulus=modulus,
        endpoint=endpoint,
        endpoint_stride=6 * block.three_power,
        affine_constant=block.constant,
        total_halvings=block.halvings,
        accelerated_steps=block.steps,
    )
    if word:
        replay_endpoint = replay_word(seed, word)
        if replay_endpoint != endpoint:
            raise AssertionError("compiled path failed exact replay")
    return compiled


def compile_path(word: Sequence[int], residue_mod_6: int) -> CompiledPath:
    clean_word = tuple(word)
    return compile_block(affine_block(clean_word), residue_mod_6, clean_word)


def replay_word(seed: int, word: Sequence[int]) -> int:
    """Replay and require exact equality with every claimed valuation."""
    n = seed
    if n <= 0 or n % 2 == 0 or n % 3 == 0:
        raise ValueError("seed must be positive and coprime to 6")
    for index, claimed_k in enumerate(word):
        n, actual_k = accelerated_step(n)
        if actual_k != claimed_k:
            raise ValueError(
                f"valuation mismatch at step {index}: "
                f"claimed {claimed_k}, got {actual_k}"
            )
    return n


def rational_periodic_seed(word: Sequence[int]) -> Fraction:
    """The unique rational seed with the valuation word repeated forever."""
    block = affine_block(word)
    return Fraction(block.constant, block.cycle_denominator)


@dataclass(frozen=True)
class CycleCertificate:
    schema: str
    map: str
    word: tuple[int, ...]
    seed: int
    orbit: tuple[int, ...]
    affine_constant: int
    total_halvings: int
    accelerated_steps: int
    ordinary_steps: int

    def json_dict(self) -> dict[str, object]:
        out = asdict(self)
        for key in ("seed", "affine_constant"):
            out[key] = str(out[key])
        out["word"] = list(self.word)
        out["orbit"] = [str(n) for n in self.orbit]
        return out


def cycle_certificate(word: Sequence[int]) -> CycleCertificate | None:
    """Return an exact positive accelerated-cycle certificate, if any."""
    clean_word = tuple(word)
    block = affine_block(clean_word)
    denominator = block.cycle_denominator
    if denominator <= 0 or block.constant % denominator:
        return None
    seed = block.constant // denominator
    if seed <= 0 or seed % 2 == 0 or seed % 3 == 0:
        return None
    orbit: list[int] = []
    n = seed
    try:
        for k in clean_word:
            orbit.append(n)
            n, actual_k = accelerated_step(n)
            if actual_k != k:
                return None
    except ValueError:
        return None
    if n != seed:
        return None
    return CycleCertificate(
        schema=CYCLE_SCHEMA,
        map=MAP_NAME,
        word=clean_word,
        seed=seed,
        orbit=tuple(orbit),
        affine_constant=block.constant,
        total_halvings=block.halvings,
        accelerated_steps=block.steps,
        # The unaccelerated map performs one 3x+1 step and k halvings.
        ordinary_steps=block.halvings + block.steps,
    )


def _int_field(data: dict[str, object], key: str) -> int:
    value = data[key]
    if isinstance(value, bool):
        raise ValueError(f"{key} is not an integer")
    return int(value)


def verify_path_certificate(data: dict[str, object]) -> CompiledPath:
    if data.get("schema") != PATH_SCHEMA or data.get("map") != MAP_NAME:
        raise ValueError("unsupported path certificate schema or map")
    word = tuple(int(k) for k in data["word"])
    compiled = compile_path(word, _int_field(data, "residue_mod_6"))
    expected = compiled.json_dict()
    for key, value in expected.items():
        if key == "word":
            actual = [int(k) for k in data[key]]
        elif isinstance(value, str):
            actual = str(data[key])
        else:
            actual = data[key]
        if actual != value:
            raise ValueError(f"certificate mismatch in {key}: {actual} != {value}")
    return compiled


def verify_cycle_certificate(data: dict[str, object]) -> CycleCertificate:
    if data.get("schema") != CYCLE_SCHEMA or data.get("map") != MAP_NAME:
        raise ValueError("unsupported cycle certificate schema or map")
    word = tuple(int(k) for k in data["word"])
    cert = cycle_certificate(word)
    if cert is None:
        raise ValueError("word does not encode a positive accelerated cycle")
    expected = cert.json_dict()
    for key, value in expected.items():
        if key in ("word", "orbit"):
            actual = [int(x) for x in data[key]]
            wanted = [int(x) for x in value]
        elif isinstance(value, str):
            actual, wanted = str(data[key]), value
        else:
            actual, wanted = data[key], value
        if actual != wanted:
            raise ValueError(f"certificate mismatch in {key}: {actual} != {wanted}")
    return cert


def verify_certificate_file(path: Path) -> str:
    data = json.loads(path.read_text())
    schema = data.get("schema")
    if schema == PATH_SCHEMA:
        cert = verify_path_certificate(data)
        return (
            f"verified path: N={cert.accelerated_steps}, "
            f"S={cert.total_halvings}, seed={cert.seed}, endpoint={cert.endpoint}"
        )
    if schema == CYCLE_SCHEMA:
        cert = verify_cycle_certificate(data)
        kind = "trivial" if cert.seed == 1 else "NONTRIVIAL"
        return (
            f"verified {kind} cycle: N={cert.accelerated_steps}, "
            f"S={cert.total_halvings}, seed={cert.seed}"
        )
    raise ValueError(f"unsupported schema: {schema!r}")


def selftest() -> None:
    # The example in Kontorovich's thread.
    example = compile_path((1, 1, 2, 2), 1)
    assert example.seed == 199
    assert replay_word(199, (1, 1, 2, 2)) == example.endpoint

    # Exhaustively compare the compiler with literal path membership on one
    # complete period for all small words.
    from itertools import product

    for length in range(1, 5):
        for word in product(range(1, 5), repeat=length):
            for residue in (1, 5):
                cert = compile_path(word, residue)
                hits = []
                for seed in range(residue, cert.seed_modulus + 1, 6):
                    try:
                        replay_word(seed, word)
                    except ValueError:
                        continue
                    hits.append(seed)
                assert hits == [cert.seed], (word, residue, hits, cert.seed)
                assert replay_word(cert.seed + cert.seed_modulus, word) == (
                    cert.endpoint + cert.endpoint_stride
                )

    # Concatenation algebra and the known signed periodic points.
    u, v = (1, 3, 2), (4, 1)
    assert affine_block(u).then(affine_block(v)) == affine_block(u + v)
    assert rational_periodic_seed((2,)) == 1
    assert rational_periodic_seed((1, 2)) == -5
    assert rational_periodic_seed((1, 1, 1, 2, 1, 1, 4)) == -17

    trivial = cycle_certificate((2,))
    assert trivial is not None and trivial.seed == 1
    verify_cycle_certificate(trivial.json_dict())
    verify_path_certificate(example.json_dict())


def _parse_word(text: str) -> tuple[int, ...]:
    try:
        word = tuple(int(piece) for piece in text.split(",") if piece.strip())
    except ValueError as exc:
        raise argparse.ArgumentTypeError("word must be comma-separated integers") from exc
    if not word or any(k <= 0 for k in word):
        raise argparse.ArgumentTypeError("word must contain positive integers")
    return word


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    p_compile = sub.add_parser("compile", help="compile an exact finite k-word")
    p_compile.add_argument("word", type=_parse_word)
    p_compile.add_argument("--class", dest="residue", type=int, choices=(1, 5), default=1)

    p_cycle = sub.add_parser("cycle", help="test a k-word for exact positive closure")
    p_cycle.add_argument("word", type=_parse_word)

    p_verify = sub.add_parser("verify", help="verify a JSON path/cycle certificate")
    p_verify.add_argument("certificate", type=Path)

    sub.add_parser("selftest", help="run exhaustive small regression tests")
    args = parser.parse_args()

    if args.command == "compile":
        print(json.dumps(compile_path(args.word, args.residue).json_dict(), indent=2))
    elif args.command == "cycle":
        cert = cycle_certificate(args.word)
        if cert is None:
            raise SystemExit("not a positive accelerated cycle")
        print(json.dumps(cert.json_dict(), indent=2))
    elif args.command == "verify":
        print(verify_certificate_file(args.certificate))
    else:
        selftest()
        print("path_compiler selftest: PASS")


if __name__ == "__main__":
    main()
