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


def stage_stem(index: int) -> str:
    return f"{STEM}Stage{index:03d}"


def render_stage(stage_index: int, start: int, end: int) -> str:
    if stage_index == 0:
        imports = [BRIDGE_MODULE]
    else:
        imports = [module_name(stage_stem(stage_index - 1))]
    imports.extend(
        module_name(f"{GROUP_STEM}{index:03d}") for index in range(start, end)
    )
    lines = common_header(
        imports,
        f"/- Checkpointed final assembly stage for class groups {start:03d}..{end - 1:03d}. -/",
    )
    for index in range(start, end):
        lines.extend(emit_group_step(index))
    lines.extend(common_footer())
    return "\n".join(lines)


def render_summary(last_stage: int) -> str:
    lines = common_header(
        [module_name(stage_stem(last_stage))],
        "/- Shallow aliases for the completed non-dyadic class assembly. -/",
    )
    lines.extend(
        [
            "def PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs : Finset (ℕ × ℕ) :=",
            "  PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairsUpTo286",
            "",
            "def PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal : ℚ :=",
            "  PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotalUpTo286",
            "",
            "theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_actual_sum :",
            "    (∑ p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal := by",
            "  simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs, PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal] using PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairsUpTo286_actual_sum",
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
) -> list[tuple[int, int]]:
    if stage_size <= 0:
        raise ValueError("stage size must be positive")
    if tail_stage_size <= 0:
        raise ValueError("tail stage size must be positive")
    if tail_start is not None and not 0 <= tail_start <= GROUP_COUNT:
        raise ValueError(f"tail start must be between 0 and {GROUP_COUNT}")

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
        ranges.append((start, end))
        start = end
    return ranges


def expected_files(
    stage_size: int,
    tail_start: int | None,
    tail_stage_size: int,
) -> dict[Path, str]:
    rendered: dict[Path, str] = {}
    ranges = stage_ranges(stage_size, tail_start, tail_stage_size)
    for stage_index, (start, end) in enumerate(ranges):
        rendered[OUT_DIR / f"{stage_stem(stage_index)}.lean"] = render_stage(
            stage_index, start, end
        )
    rendered[OUT_DIR / f"{STEM}Summary.lean"] = render_summary(len(ranges) - 1)
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
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    rendered = expected_files(
        args.stage_size,
        args.tail_start,
        args.tail_stage_size,
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
        f"tail_stage_size={args.tail_stage_size}"
    )


if __name__ == "__main__":
    main()
