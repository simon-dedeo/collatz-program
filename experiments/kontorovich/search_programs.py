#!/usr/bin/env python3
"""Exact bounded searches for cycles and low-description Collatz programs.

Two independent finite searches are provided:

* ``compositions`` exhausts every accelerated valuation word whose total
  number of halvings S is at most a stated bound (cyclic rotations included).
* ``morphisms`` exhausts binary uniform substitutions of stated width,
  positive codings of the two symbols, and all substitution depths whose
  expanded word stays below a stated length.  It tests exact cycle closure and
  whether the canonical ordinary seed stabilizes across nested prefixes.

All arithmetic is integer arithmetic.  A nontrivial cycle is emitted with the
``collatz-accelerated-cycle-v1`` certificate schema and can be independently
replayed by path_compiler.py.  A negative search is only a bounded exclusion
of the explicitly reported ansatz class.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from math import comb
from pathlib import Path

from path_compiler import (
    AffineBlock,
    accelerated_step,
    compile_block,
    cycle_certificate,
    replay_word,
)


def compositions(total: int, length: int):
    """Generate all ordered compositions of total into length positive parts."""
    if length == 1:
        yield (total,)
        return
    for cuts in itertools.combinations(range(1, total), length - 1):
        points = (0,) + cuts + (total,)
        yield tuple(points[i + 1] - points[i] for i in range(length))


def search_compositions(max_total_halvings: int) -> dict[str, object]:
    if max_total_halvings < 1:
        raise ValueError("max_total_halvings must be positive")
    tested = 0
    positive_shape_words = 0
    exact_cycles = []
    expected = 0
    for total in range(1, max_total_halvings + 1):
        for length in range(1, total + 1):
            if (1 << total) <= pow(3, length):
                continue
            expected += comb(total - 1, length - 1)
            for word in compositions(total, length):
                tested += 1
                cert = cycle_certificate(word)
                if cert is not None:
                    exact_cycles.append(cert.json_dict())
            positive_shape_words += comb(total - 1, length - 1)
    assert tested == expected == positive_shape_words
    nontrivial = [c for c in exact_cycles if int(c["seed"]) != 1]
    return {
        "search": "all_ordered_positive_compositions",
        "max_total_halvings": max_total_halvings,
        "words_tested": tested,
        "positive_multiplier_shapes_only": True,
        "exact_cycle_words": len(exact_cycles),
        "nontrivial_cycle_words": len(nontrivial),
        "cycles": exact_cycles,
    }


def uniform_morphisms(width: int):
    """All binary width-uniform morphisms prolongable on symbol 0."""
    tails = itertools.product((0, 1), repeat=width - 1)
    images_zero = [(0,) + tail for tail in tails]
    images_one = list(itertools.product((0, 1), repeat=width))
    for image_zero in images_zero:
        for image_one in images_one:
            yield (image_zero, image_one)


def expand(image: tuple[tuple[int, ...], tuple[int, ...]], depth: int) -> tuple[int, ...]:
    word = (0,)
    for _ in range(depth):
        word = tuple(bit for symbol in word for bit in image[symbol])
    return word


def encoded_block(symbol_word: tuple[int, ...], coding: tuple[int, int]) -> AffineBlock:
    block = AffineBlock.identity()
    for symbol in symbol_word:
        block = block.then(AffineBlock.letter(coding[symbol]))
    return block


def block_substitute(
    blocks: tuple[AffineBlock, AffineBlock],
    image: tuple[tuple[int, ...], tuple[int, ...]],
) -> tuple[AffineBlock, AffineBlock]:
    out = []
    for symbol in (0, 1):
        block = AffineBlock.identity()
        for child in image[symbol]:
            block = block.then(blocks[child])
        out.append(block)
    return out[0], out[1]


def bounded_fate(seed: int, max_steps: int = 10000) -> dict[str, object]:
    """Exact continuation audit, with an explicit unresolved step bound."""
    n = seed
    peak = n
    seen: dict[int, int] = {}
    for step in range(max_steps + 1):
        if n == 1:
            return {
                "status": "reaches_one",
                "accelerated_steps": step,
                "peak": str(peak),
            }
        if n in seen:
            return {
                "status": "cycle",
                "preperiod": seen[n],
                "period": step - seen[n],
                "cycle_seed": str(n),
                "peak": str(peak),
            }
        if step == max_steps:
            break
        seen[n] = step
        n, _ = accelerated_step(n)
        peak = max(peak, n)
    return {
        "status": "unresolved_within_bound",
        "max_accelerated_steps": max_steps,
        "last_value": str(n),
        "peak": str(peak),
    }


def search_morphisms(
    max_uniform_width: int,
    max_k: int,
    max_word_length: int,
    max_seed_word_length: int,
) -> dict[str, object]:
    if (
        max_uniform_width < 2
        or max_k < 1
        or max_word_length < 2
        or not 1 <= max_seed_word_length <= max_word_length
    ):
        raise ValueError("invalid morphism search bounds")
    morphism_count = 0
    instance_count = 0
    positive_multiplier_count = 0
    exact_cycle_count = 0
    nontrivial_cycles: list[dict[str, object]] = []
    stabilization_events = 0
    longest_stabilization: dict[str, object] | None = None
    nontrivial_stabilization_events = 0
    longest_nontrivial_stabilization: dict[str, object] | None = None
    one_avoiding_stabilization_events = 0
    longest_one_avoiding_stabilization: dict[str, object] | None = None

    for width in range(2, max_uniform_width + 1):
        depth_limit = 0
        size = 1
        while size * width <= max_word_length:
            size *= width
            depth_limit += 1
        for image in uniform_morphisms(width):
            morphism_count += 1
            for coding in itertools.product(range(1, max_k + 1), repeat=2):
                blocks = (
                    AffineBlock.letter(coding[0]),
                    AffineBlock.letter(coding[1]),
                )
                previous_seed = {1: None, 5: None}
                stable_extensions = {1: 0, 5: 0}
                for depth in range(1, depth_limit + 1):
                    blocks = block_substitute(blocks, image)
                    block = blocks[0]
                    assert block.steps == width**depth
                    instance_count += 1
                    if block.cycle_denominator > 0:
                        positive_multiplier_count += 1
                        denominator = block.cycle_denominator
                        if block.constant % denominator == 0:
                            # Expand only on a divisibility hit, then require
                            # literal valuation replay before recording it.
                            symbols = expand(image, depth)
                            word = tuple(coding[s] for s in symbols)
                            cert = cycle_certificate(word)
                            if cert is None:
                                raise AssertionError("compressed divisibility hit failed replay")
                            exact_cycle_count += 1
                            if cert.seed != 1:
                                nontrivial_cycles.append(cert.json_dict())

                    # Canonical-seed synthesis requires a modular inverse at
                    # the full bit precision S+1.  Keep that independent
                    # exact gate at an explicit (usually smaller) bound while
                    # cycle divisibility continues through max_word_length.
                    if block.steps > max_seed_word_length:
                        continue
                    for residue in (1, 5):
                        compiled = compile_block(block, residue)
                        if compiled.seed == previous_seed[residue]:
                            stable_extensions[residue] += 1
                            stabilization_events += 1
                            symbols = expand(image, depth)
                            word = tuple(coding[s] for s in symbols)
                            if replay_word(compiled.seed, word) != compiled.endpoint:
                                raise AssertionError("stabilized prefix failed exact replay")
                            n = compiled.seed
                            first_one_step = 0 if n == 1 else None
                            for step_index, k in enumerate(word, start=1):
                                n, actual_k = accelerated_step(n)
                                if actual_k != k:
                                    raise AssertionError("stabilized trace valuation mismatch")
                                if n == 1 and first_one_step is None:
                                    first_one_step = step_index
                            event = {
                                "uniform_width": width,
                                "image_0": "".join(map(str, image[0])),
                                "image_1": "".join(map(str, image[1])),
                                "coding": list(coding),
                                "residue_mod_6": residue,
                                "depth": depth,
                                "word_length": block.steps,
                                "stable_extensions": stable_extensions[residue],
                                "seed": str(compiled.seed),
                                "first_one_step": first_one_step,
                            }
                            if first_one_step is None:
                                one_avoiding_stabilization_events += 1
                                if (
                                    longest_one_avoiding_stabilization is None
                                    or event["word_length"]
                                    > longest_one_avoiding_stabilization["word_length"]
                                ):
                                    longest_one_avoiding_stabilization = event
                            if compiled.seed != 1:
                                nontrivial_stabilization_events += 1
                                if (
                                    longest_nontrivial_stabilization is None
                                    or event["stable_extensions"]
                                    > longest_nontrivial_stabilization["stable_extensions"]
                                    or (
                                        event["stable_extensions"]
                                        == longest_nontrivial_stabilization["stable_extensions"]
                                        and event["word_length"]
                                        > longest_nontrivial_stabilization["word_length"]
                                    )
                                ):
                                    longest_nontrivial_stabilization = event
                            if (
                                longest_stabilization is None
                                or event["stable_extensions"]
                                > longest_stabilization["stable_extensions"]
                                or (
                                    event["stable_extensions"]
                                    == longest_stabilization["stable_extensions"]
                                    and event["word_length"]
                                    > longest_stabilization["word_length"]
                                )
                            ):
                                longest_stabilization = event
                        else:
                            stable_extensions[residue] = 0
                        previous_seed[residue] = compiled.seed

    if longest_one_avoiding_stabilization is not None:
        longest_one_avoiding_stabilization = dict(longest_one_avoiding_stabilization)
        longest_one_avoiding_stabilization["continuation"] = bounded_fate(
            int(longest_one_avoiding_stabilization["seed"])
        )
    return {
        "search": "binary_uniform_prolongable_morphisms",
        "max_uniform_width": max_uniform_width,
        "max_coding_value": max_k,
        "max_expanded_word_length": max_word_length,
        "max_seed_stabilization_word_length": max_seed_word_length,
        "morphisms_tested": morphism_count,
        "coding_pairs_per_morphism": max_k * max_k,
        "depth_instances_tested": instance_count,
        "positive_multiplier_instances": positive_multiplier_count,
        "exact_cycle_instances": exact_cycle_count,
        "nontrivial_cycle_instances": len(nontrivial_cycles),
        "nontrivial_cycles": nontrivial_cycles,
        "seed_stabilization_events": stabilization_events,
        "nontrivial_seed_stabilization_events": nontrivial_stabilization_events,
        "one_avoiding_seed_stabilization_events": one_avoiding_stabilization_events,
        "longest_seed_stabilization": longest_stabilization,
        "longest_nontrivial_seed_stabilization": longest_nontrivial_stabilization,
        "longest_one_avoiding_seed_stabilization": longest_one_avoiding_stabilization,
    }


def selftest() -> None:
    assert list(compositions(5, 3)) == [
        (1, 1, 3),
        (1, 2, 2),
        (1, 3, 1),
        (2, 1, 2),
        (2, 2, 1),
        (3, 1, 1),
    ]
    assert len(list(uniform_morphisms(2))) == 8
    image = ((0, 1), (1, 0))
    coding = (1, 3)
    blocks = (AffineBlock.letter(1), AffineBlock.letter(3))
    for depth in range(1, 6):
        blocks = block_substitute(blocks, image)
        symbols = expand(image, depth)
        assert blocks[0] == encoded_block(symbols, coding)
    small = search_compositions(8)
    assert small["nontrivial_cycle_words"] == 0
    morphic = search_morphisms(2, 2, 16, 16)
    assert morphic["nontrivial_cycle_instances"] == 0


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-total-halvings", type=int, default=22)
    parser.add_argument("--max-uniform-width", type=int, default=4)
    parser.add_argument("--max-k", type=int, default=4)
    parser.add_argument("--max-word-length", type=int, default=16384)
    parser.add_argument("--max-seed-word-length", type=int, default=512)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        print("search_programs selftest: PASS")
        return

    result = {
        "schema": "collatz-program-search-v1",
        "arithmetic": "exact_python_integers",
        "composition_search": search_compositions(args.max_total_halvings),
        "morphic_search": search_morphisms(
            args.max_uniform_width,
            args.max_k,
            args.max_word_length,
            args.max_seed_word_length,
        ),
    }
    source = Path(__file__).read_bytes() + Path(__file__).with_name("path_compiler.py").read_bytes()
    result["source_sha256"] = hashlib.sha256(source).hexdigest()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
