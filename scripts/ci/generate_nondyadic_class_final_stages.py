#!/usr/bin/env python3
"""Generate checkpointable stages for the non-dyadic class final assembly."""

from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = ROOT / "Goldbach" / "Cert" / "MajorArcModules"
MODULE_PREFIX = "Goldbach.Cert.MajorArcModules."
STEM = (
    "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFive"
    "NonDyadicClassFinal"
)
GROUP_STEM = (
    "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFive"
    "NonDyadicClassGroup"
)
BRIDGE_MODULE = (
    MODULE_PREFIX
    + "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFive"
    "DyadicBridge"
)
NAMESPACE = "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage"
GROUP_COUNT = 287
DEFAULT_STAGE_SIZE = 8
DEFAULT_TAIL_START = 184
DEFAULT_TAIL_STAGE_SIZE = 1
DEFAULT_ACCUMULATION_RESET_START = 273
DEFAULT_DISJOINT_CHUNK_SIZE = 10


def module_name(stem: str) -> str:
    return MODULE_PREFIX + stem


def common_header(imports: list[str], comment: str) -> list[str]:
    lines = [*(f"import {name}" for name in imports), ""]
    lines.extend(
        [
            "set_option maxHeartbeats 0",
            "set_option maxRecDepth 100000",
            "set_option linter.constructorNameAsVariable false",
            "",
            f"namespace {NAMESPACE}",
            "",
            "open Goldbach",
            "open Goldbach.BankParams",
            "open Goldbach.Windows",
            "",
            comment,
            "",
        ]
    )
    return lines


def common_footer() -> list[str]:
    return [f"end {NAMESPACE}", ""]


def group_name(index: int) -> str:
    return f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup{index:03d}"


def upto_name(index: int) -> str:
    return f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairsUpTo{index:03d}"


def total_name(index: int) -> str:
    return f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotalUpTo{index:03d}"


def tail_upto_name(index: int) -> str:
    return f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo{index:03d}"


def tail_total_name(index: int) -> str:
    return f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailTotalUpTo{index:03d}"


def emit_group_step(index: int) -> list[str]:
    group = group_name(index)
    upto = upto_name(index)
    total = total_name(index)
    actual = "surrogatePeriodicMainActiveOrderedPairSummandRat X0"
    if index == 0:
        return [
            f"def {upto} : Finset (ℕ × ℕ) :=",
            f"  {group}Pairs",
            "",
            f"def {total} : ℚ :=",
            f"  {group}Total",
            "",
            f"theorem {upto}_actual_sum :",
            f"    (∑ p ∈ {upto}, {actual} p) = {total} := by",
            f"  simpa [{upto}, {total}] using {group[0].lower() + group[1:]}_actual_sum",
            "",
        ]

    previous_upto = upto_name(index - 1)
    previous_total = total_name(index - 1)
    disjoint = f"{previous_upto}_disjoint_{group}Pairs"
    return [
        f"def {upto} : Finset (ℕ × ℕ) :=",
        f"  {previous_upto} ∪ {group}Pairs",
        "",
        f"def {total} : ℚ :=",
        f"  {previous_total} + {group}Total",
        "",
        f"theorem {disjoint} :",
        f"    Disjoint {previous_upto} {group}Pairs := by",
        "  native_decide",
        "",
        f"theorem {upto}_actual_sum :",
        f"    (∑ p ∈ {upto}, {actual} p) = {total} := by",
        f"  rw [{upto}, Finset.sum_union {disjoint}]",
        f"  rw [{previous_upto}_actual_sum, {group[0].lower() + group[1:]}_actual_sum]",
        "  rfl",
        "",
    ]


def emit_tail_group_step(index: int, reset_start: int) -> list[str]:
    group = group_name(index)
    upto = tail_upto_name(index)
    total = tail_total_name(index)
    actual = "surrogatePeriodicMainActiveOrderedPairSummandRat X0"
    group_actual = group[0].lower() + group[1:] + "_actual_sum"
    if index == reset_start:
        return [
            f"def {upto} : Finset (ℕ × ℕ) :=",
            f"  {group}Pairs",
            "",
            f"def {total} : ℚ :=",
            f"  {group}Total",
            "",
            f"theorem {upto}_actual_sum :",
            f"    (∑ p ∈ {upto}, {actual} p) = {total} := by",
            f"  simpa [{upto}, {total}] using {group_actual}",
            "",
        ]

    previous_upto = tail_upto_name(index - 1)
    previous_total = tail_total_name(index - 1)
    disjoint = f"{previous_upto}_disjoint_{group}Pairs"
    return [
        f"def {upto} : Finset (ℕ × ℕ) :=",
        f"  {previous_upto} ∪ {group}Pairs",
        "",
        f"def {total} : ℚ :=",
        f"  {previous_total} + {group}Total",
        "",
        f"theorem {disjoint} :",
        f"    Disjoint {previous_upto} {group}Pairs := by",
        "  native_decide",
        "",
        f"theorem {upto}_actual_sum :",
        f"    (∑ p ∈ {upto}, {actual} p) = {total} := by",
        f"  rw [{upto}, Finset.sum_union {disjoint}]",
        f"  rw [{previous_upto}_actual_sum, {group_actual}]",
        "  rfl",
        "",
    ]


def stage_stem(index: int) -> str:
    return f"{STEM}Stage{index:03d}"


def render_stage(
    stage_index: int,
    start: int,
    end: int,
    accumulation_reset_start: int,
) -> str:
    if stage_index == 0:
        imports = [BRIDGE_MODULE]
    else:
        imports = [module_name(stage_stem(stage_index - 1))]
    imports.extend(
        module_name(f"{GROUP_STEM}{index:03d}") for index in range(start, end)
    )
    if start >= accumulation_reset_start:
        comment = (
            f"/- Checkpointed tail assembly stage for class groups "
            f"{start:03d}..{end - 1:03d}. -/"
        )
    else:
        comment = (
            f"/- Checkpointed final assembly stage for class groups "
            f"{start:03d}..{end - 1:03d}. -/"
        )
    lines = common_header(imports, comment)
    for index in range(start, end):
        if index >= accumulation_reset_start:
            lines.extend(emit_tail_group_step(index, accumulation_reset_start))
        else:
            lines.extend(emit_group_step(index))
    lines.extend(common_footer())
    return "\n".join(lines)


def pairwise_chunk_stem(index: int) -> str:
    return f"{STEM}PrefixTailPairwiseChunk{index:03d}"


def aggregate_chunk_stem(index: int) -> str:
    return f"{STEM}PrefixTailAggregateChunk{index:03d}"


def group_tail_disjoint_name(group_index: int, tail_end: int) -> str:
    return f"{group_name(group_index)}Pairs_disjoint_{tail_upto_name(tail_end)}"


def prefix_tail_disjoint_name(prefix_end: int, tail_end: int) -> str:
    return f"{upto_name(prefix_end)}_disjoint_{tail_upto_name(tail_end)}"


def render_pairwise_chunk(
    chunk_index: int,
    start: int,
    end: int,
    last_stage: int,
    tail_end: int,
) -> str:
    lines = common_header(
        [module_name(stage_stem(last_stage))],
        (
            f"/- Pairwise prefix/tail disjointness for class groups "
            f"{start:03d}..{end - 1:03d}. -/"
        ),
    )
    tail = tail_upto_name(tail_end)
    for index in range(start, end):
        group_pairs = f"{group_name(index)}Pairs"
        theorem_name = group_tail_disjoint_name(index, tail_end)
        lines.extend(
            [
                f"theorem {theorem_name} :",
                f"    Disjoint {group_pairs} {tail} := by",
                "  native_decide",
                "",
            ]
        )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_aggregate_chunk(
    chunk_index: int,
    start: int,
    end: int,
    tail_end: int,
) -> str:
    imports = [module_name(pairwise_chunk_stem(chunk_index))]
    if chunk_index > 0:
        imports.append(module_name(aggregate_chunk_stem(chunk_index - 1)))
    lines = common_header(
        imports,
        (
            f"/- Structural prefix/tail disjointness assembly through class group "
            f"{end - 1:03d}. -/"
        ),
    )
    tail = tail_upto_name(tail_end)
    for index in range(start, end):
        theorem_name = prefix_tail_disjoint_name(index, tail_end)
        group_theorem = group_tail_disjoint_name(index, tail_end)
        if index == 0:
            lines.extend(
                [
                    f"theorem {theorem_name} :",
                    f"    Disjoint {upto_name(index)} {tail} := by",
                    f"  simpa [{upto_name(index)}] using {group_theorem}",
                    "",
                ]
            )
            continue
        previous_theorem = prefix_tail_disjoint_name(index - 1, tail_end)
        lines.extend(
            [
                f"theorem {theorem_name} :",
                f"    Disjoint {upto_name(index)} {tail} := by",
                f"  rw [{upto_name(index)}, Finset.disjoint_union_left]",
                f"  exact ⟨{previous_theorem}, {group_theorem}⟩",
                "",
            ]
        )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_summary(
    accumulation_reset_start: int,
    last_aggregate_chunk: int,
) -> str:
    prefix_end = accumulation_reset_start - 1
    tail_end = GROUP_COUNT - 1
    prefix_pairs = upto_name(prefix_end)
    prefix_total = total_name(prefix_end)
    tail_pairs = tail_upto_name(tail_end)
    tail_total = tail_total_name(tail_end)
    full_pairs = upto_name(tail_end)
    full_total = total_name(tail_end)
    disjoint = prefix_tail_disjoint_name(prefix_end, tail_end)
    lines = common_header(
        [module_name(aggregate_chunk_stem(last_aggregate_chunk))],
        "/- Recombine the checkpointed prefix and tail assemblies. -/",
    )
    lines.extend(
        [
            f"def {full_pairs} : Finset (ℕ × ℕ) :=",
            f"  {prefix_pairs} ∪ {tail_pairs}",
            "",
            f"def {full_total} : ℚ :=",
            f"  {prefix_total} + {tail_total}",
            "",
            f"theorem {full_pairs}_actual_sum :",
            f"    (∑ p ∈ {full_pairs}, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = {full_total} := by",
            f"  rw [{full_pairs}, Finset.sum_union {disjoint}]",
            f"  rw [{prefix_pairs}_actual_sum, {tail_pairs}_actual_sum]",
            "  rfl",
            "",
            "def PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs : Finset (ℕ × ℕ) :=",
            f"  {full_pairs}",
            "",
            "def PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal : ℚ :=",
            f"  {full_total}",
            "",
            "theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_actual_sum :",
            "    (∑ p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal := by",
            f"  simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs, PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal] using {full_pairs}_actual_sum",
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_coverage() -> str:
    lines = common_header(
        [module_name(f"{STEM}Summary")],
        "/- Isolate the finite target-set equality from the actual-sum assembly. -/",
    )
    lines.extend(
        [
            "theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_eq_target :",
            "    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs = PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic := by",
            "  native_decide",
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_final() -> str:
    lines = common_header(
        [module_name(f"{STEM}Coverage")],
        "/- Public wrapper retaining the original final theorem surface. -/",
    )
    lines.extend(
        [
            "theorem periodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_actual_sum :",
            "    (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal := by",
            "  rw [← PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_eq_target]",
            "  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_actual_sum]",
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def stage_ranges(
    stage_size: int,
    tail_start: int | None,
    tail_stage_size: int,
    accumulation_reset_start: int,
) -> list[tuple[int, int]]:
    if stage_size <= 0:
        raise ValueError("stage size must be positive")
    if tail_stage_size <= 0:
        raise ValueError("tail stage size must be positive")
    if tail_start is not None and not 0 <= tail_start <= GROUP_COUNT:
        raise ValueError(f"tail start must be between 0 and {GROUP_COUNT}")
    if not 1 <= accumulation_reset_start < GROUP_COUNT:
        raise ValueError(
            f"accumulation reset start must be between 1 and {GROUP_COUNT - 1}"
        )

    ranges: list[tuple[int, int]] = []
    start = 0
    while start < GROUP_COUNT:
        size = (
            tail_stage_size
            if tail_start is not None and start >= tail_start
            else stage_size
        )
        end = min(GROUP_COUNT, start + size)
        if tail_start is not None and start < tail_start < end:
            end = tail_start
        if start < accumulation_reset_start < end:
            end = accumulation_reset_start
        ranges.append((start, end))
        start = end
    return ranges


def expected_files(
    stage_size: int,
    tail_start: int | None,
    tail_stage_size: int,
    accumulation_reset_start: int,
    disjoint_chunk_size: int,
) -> dict[Path, str]:
    rendered: dict[Path, str] = {}
    if disjoint_chunk_size <= 0:
        raise ValueError("disjoint chunk size must be positive")
    ranges = stage_ranges(
        stage_size,
        tail_start,
        tail_stage_size,
        accumulation_reset_start,
    )
    for stage_index, (start, end) in enumerate(ranges):
        rendered[OUT_DIR / f"{stage_stem(stage_index)}.lean"] = render_stage(
            stage_index,
            start,
            end,
            accumulation_reset_start,
        )
    last_stage = len(ranges) - 1
    prefix_ranges = list(
        range(0, accumulation_reset_start, disjoint_chunk_size)
    )
    for chunk_index, start in enumerate(prefix_ranges):
        end = min(accumulation_reset_start, start + disjoint_chunk_size)
        rendered[OUT_DIR / f"{pairwise_chunk_stem(chunk_index)}.lean"] = (
            render_pairwise_chunk(
                chunk_index,
                start,
                end,
                last_stage,
                GROUP_COUNT - 1,
            )
        )
        rendered[OUT_DIR / f"{aggregate_chunk_stem(chunk_index)}.lean"] = (
            render_aggregate_chunk(
                chunk_index,
                start,
                end,
                GROUP_COUNT - 1,
            )
        )
    last_aggregate_chunk = len(prefix_ranges) - 1
    rendered[OUT_DIR / f"{STEM}Summary.lean"] = render_summary(
        accumulation_reset_start,
        last_aggregate_chunk,
    )
    rendered[OUT_DIR / f"{STEM}Coverage.lean"] = render_coverage()
    rendered[OUT_DIR / f"{STEM}.lean"] = render_final()
    return rendered


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage-size", type=int, default=DEFAULT_STAGE_SIZE)
    parser.add_argument(
        "--tail-start",
        type=int,
        default=DEFAULT_TAIL_START,
        help="First group emitted with the smaller tail stage size.",
    )
    parser.add_argument(
        "--tail-stage-size",
        type=int,
        default=DEFAULT_TAIL_STAGE_SIZE,
        help="Groups per checkpoint after --tail-start.",
    )
    parser.add_argument(
        "--accumulation-reset-start",
        type=int,
        default=DEFAULT_ACCUMULATION_RESET_START,
        help=(
            "Restart the final Finset accumulation at this group, then prove "
            "prefix/tail disjointness in checkpointable chunks."
        ),
    )
    parser.add_argument(
        "--disjoint-chunk-size",
        type=int,
        default=DEFAULT_DISJOINT_CHUNK_SIZE,
        help="Prefix groups per pairwise/structural disjointness module.",
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    rendered = expected_files(
        args.stage_size,
        args.tail_start,
        args.tail_stage_size,
        args.accumulation_reset_start,
        args.disjoint_chunk_size,
    )
    mismatches: list[str] = []
    for path, content in rendered.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                mismatches.append(str(path.relative_to(ROOT)))
        else:
            path.write_text(content)

    if mismatches:
        raise SystemExit("generated files differ: " + ", ".join(mismatches))
    action = "verified" if args.check else "wrote"
    print(
        f"{action} {len(rendered)} files with "
        f"stage_size={args.stage_size}, tail_start={args.tail_start}, "
        f"tail_stage_size={args.tail_stage_size}, "
        f"accumulation_reset_start={args.accumulation_reset_start}, "
        f"disjoint_chunk_size={args.disjoint_chunk_size}"
    )


if __name__ == "__main__":
    main()
