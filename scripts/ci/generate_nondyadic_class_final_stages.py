#!/usr/bin/env python3
"""Generate checkpointable stages for the non-dyadic class final assembly."""

from __future__ import annotations

import argparse
import re
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
CLASS_STEM = (
    "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFive"
    "NonDyadicClass"
)
BRIDGE_MODULE = (
    MODULE_PREFIX
    + "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFive"
    "DyadicBridge"
)
NAMESPACE = "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage"
GROUP_COUNT = 287
CLASS_COUNT = 7158
CLASSES_PER_GROUP = 25
DEFAULT_STAGE_SIZE = 8
DEFAULT_TAIL_START = 184
DEFAULT_TAIL_STAGE_SIZE = 1
DEFAULT_ACCUMULATION_RESET_START = 273
DEFAULT_DISJOINT_CHUNK_SIZE = 10
DEFAULT_LATE_TAIL_START = 284
DEFAULT_LATE_TAIL_DISJOINT_CHUNK_SIZE = 3
OLD_TAIL_MIN_UPPER = 1391
LATE_TAIL_MIN_LOWER = 1393
LATE_GROUP_MIN_BOUNDS = {
    284: (1393, 1493),
    285: (1495, 1610),
    286: (1613, 1661),
}


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


def late_tail_upto_name(index: int) -> str:
    return (
        "PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo"
        f"{index:03d}"
    )


def late_tail_total_name(index: int) -> str:
    return (
        "PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailTotalUpTo"
        f"{index:03d}"
    )


def min_coordinate(p: str = "p") -> str:
    return f"Nat.min {p}.1 {p}.2"


def group_min_bounds_name(index: int) -> str:
    return f"{group_name(index)}Pairs_min_coordinate_bounds"


def group_min_upper_name(index: int) -> str:
    return f"{group_name(index)}Pairs_min_coordinate_le_{OLD_TAIL_MIN_UPPER}"


def class_name(index: int) -> str:
    return f"PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass{index}"


def class_min_bounds_name(index: int) -> str:
    return f"{class_name(index)}Pairs_min_coordinate_bounds"


def class_min_upper_name(index: int) -> str:
    return f"{class_name(index)}Pairs_min_coordinate_le_{OLD_TAIL_MIN_UPPER}"


def tail_min_upper_name(index: int) -> str:
    return f"{tail_upto_name(index)}_min_coordinate_le_{OLD_TAIL_MIN_UPPER}"


def late_tail_min_lower_name(index: int) -> str:
    return f"{late_tail_upto_name(index)}_min_coordinate_ge_{LATE_TAIL_MIN_LOWER}"


def late_tail_min_upper_name(index: int, upper: int) -> str:
    return f"{late_tail_upto_name(index)}_min_coordinate_le_{upper}"


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


def emit_late_tail_group_step(index: int, reset_start: int) -> list[str]:
    group = group_name(index)
    upto = late_tail_upto_name(index)
    total = late_tail_total_name(index)
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

    previous_upto = late_tail_upto_name(index - 1)
    previous_total = late_tail_total_name(index - 1)
    disjoint = f"{previous_upto}_disjoint_{group}Pairs"
    lower, upper = LATE_GROUP_MIN_BOUNDS[index]
    previous_upper = LATE_GROUP_MIN_BOUNDS[index - 1][1]
    lines = [
        f"def {upto} : Finset (ℕ × ℕ) :=",
        f"  {previous_upto} ∪ {group}Pairs",
        "",
        f"def {total} : ℚ :=",
        f"  {previous_total} + {group}Total",
        "",
        f"theorem {disjoint} :",
        f"    Disjoint {previous_upto} {group}Pairs := by",
        "  refine Finset.disjoint_left.mpr ?_",
        "  intro p hp_previous hp_group",
        (
            f"  have hprevious := {late_tail_min_upper_name(index - 1, previous_upper)} "
            "hp_previous"
        ),
        f"  have hgroup := {group_min_bounds_name(index)} hp_group",
        "  omega",
        "",
        f"theorem {upto}_actual_sum :",
        f"    (∑ p ∈ {upto}, {actual} p) = {total} := by",
        f"  rw [{upto}, Finset.sum_union {disjoint}]",
        f"  rw [{previous_upto}_actual_sum, {group_actual}]",
        "  rfl",
        "",
    ]
    lines.extend(
        [
            f"theorem {late_tail_min_lower_name(index)} {{p : ℕ × ℕ}}",
            f"    (hp : p ∈ {upto}) : {LATE_TAIL_MIN_LOWER} ≤ {min_coordinate()} := by",
            f"  rw [{upto}, Finset.mem_union] at hp",
            "  rcases hp with hp | hp",
            f"  · exact {late_tail_min_lower_name(index - 1)} hp",
            f"  · exact ({group_min_bounds_name(index)} hp).1",
            "",
            f"theorem {late_tail_min_upper_name(index, upper)} {{p : ℕ × ℕ}}",
            f"    (hp : p ∈ {upto}) : {min_coordinate()} ≤ {upper} := by",
            f"  rw [{upto}, Finset.mem_union] at hp",
            "  rcases hp with hp | hp",
            f"  · exact {late_tail_min_upper_name(index - 1, previous_upper)} hp",
            f"  · exact ({group_min_bounds_name(index)} hp).2",
            "",
        ]
    )
    return lines


def stage_stem(index: int) -> str:
    return f"{STEM}Stage{index:03d}"


def render_stage(
    stage_index: int,
    start: int,
    end: int,
    accumulation_reset_start: int,
    late_tail_start: int,
) -> str:
    if stage_index == 0:
        imports = [BRIDGE_MODULE]
    else:
        imports = [module_name(stage_stem(stage_index - 1))]
    if start == 285 and end == 286:
        imports.extend(
            [module_name(late_bound_stem(284)), module_name(late_bound_stem(285))]
        )
    elif start == 286 and end == 287:
        imports.append(module_name(late_bound_stem(286)))
    else:
        imports.extend(
            module_name(f"{GROUP_STEM}{index:03d}") for index in range(start, end)
        )
    if start >= late_tail_start:
        if start == late_tail_start:
            comment = (
                "/- Reset the late tail so the final tail merge can be checked "
                "in small pairwise pieces. -/"
            )
        else:
            comment = (
                f"/- Checkpointed late-tail assembly stage for class groups "
                f"{start:03d}..{end - 1:03d}. -/"
            )
    elif start >= accumulation_reset_start:
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
        if index >= late_tail_start:
            lines.extend(emit_late_tail_group_step(index, late_tail_start))
        elif index >= accumulation_reset_start:
            lines.extend(emit_tail_group_step(index, accumulation_reset_start))
        else:
            lines.extend(emit_group_step(index))
    lines.extend(common_footer())
    return "\n".join(lines)


def pairwise_chunk_stem(index: int) -> str:
    return f"{STEM}PrefixTailPairwiseChunk{index:03d}"


def aggregate_chunk_stem(index: int) -> str:
    return f"{STEM}PrefixTailAggregateChunk{index:03d}"


def late_stage_stem(index: int) -> str:
    return f"{STEM}TailLateStage{index:03d}"


def late_bound_stem(index: int) -> str:
    return f"{STEM}LateBound{index:03d}"


def range_leaf_stem(index: int) -> str:
    return f"{STEM}RangeLeaf{index:04d}"


def range_group_stem(index: int) -> str:
    return f"{STEM}RangeGroup{index:03d}"


def group_class_indices(group_index: int) -> range:
    start = group_index * CLASSES_PER_GROUP
    return range(start, min(start + CLASSES_PER_GROUP, CLASS_COUNT))


def class_pair_count(index: int) -> int:
    path = OUT_DIR / f"{CLASS_STEM}{index}.lean"
    text = path.read_text()
    name = re.escape(f"{class_name(index)}Pairs")
    match = re.search(
        rf"def {name} : Finset \(ℕ × ℕ\) :=\s*\[(.*?)\]\.toFinset",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise ValueError(f"could not parse pair list in {path.relative_to(ROOT)}")
    count = len(re.findall(r"\(\d+,\s*\d+\)", match.group(1)))
    if count == 0:
        raise ValueError(f"empty pair list in {path.relative_to(ROOT)}")
    return count


def render_range_leaf(class_index: int, group_index: int) -> str:
    pairs = f"{class_name(class_index)}Pairs"
    if group_index < 284:
        predicate = f"{min_coordinate()} ≤ {OLD_TAIL_MIN_UPPER}"
        theorem_name = class_min_upper_name(class_index)
    else:
        lower, upper = LATE_GROUP_MIN_BOUNDS[group_index]
        predicate = f"{lower} ≤ {min_coordinate()} ∧ {min_coordinate()} ≤ {upper}"
        theorem_name = class_min_bounds_name(class_index)
    alternatives = " | ".join("rfl" for _ in range(class_pair_count(class_index)))
    lines = common_header(
        [module_name(f"{CLASS_STEM}{class_index}")],
        f"/- Constant-size coordinate certificate for non-dyadic class {class_index}. -/",
    )
    lines.extend(
        [
            f"theorem {theorem_name} {{p : ℕ × ℕ}}",
            f"    (hp : p ∈ {pairs}) : {predicate} := by",
            f"  simp [{pairs}] at hp",
            f"  rcases hp with {alternatives} <;> norm_num",
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_range_group(group_index: int) -> str:
    class_indices = list(group_class_indices(group_index))
    imports = [module_name(f"{GROUP_STEM}{group_index:03d}")]
    imports.extend(module_name(range_leaf_stem(index)) for index in class_indices)
    if group_index < 284:
        predicate = f"{min_coordinate()} ≤ {OLD_TAIL_MIN_UPPER}"
        group_theorem = group_min_upper_name(group_index)
        leaf_theorem = class_min_upper_name
    else:
        lower, upper = LATE_GROUP_MIN_BOUNDS[group_index]
        predicate = f"{lower} ≤ {min_coordinate()} ∧ {min_coordinate()} ≤ {upper}"
        group_theorem = group_min_bounds_name(group_index)
        leaf_theorem = class_min_bounds_name
    lines = common_header(
        imports,
        f"/- Structural coordinate-range assembly for non-dyadic group {group_index:03d}. -/",
    )
    for offset, class_index in enumerate(class_indices):
        upto = (
            f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup{group_index:03d}"
            f"PairsUpTo{offset:03d}"
        )
        upto_theorem = f"{upto}_coordinate_bound"
        if offset == 0:
            lines.extend(
                [
                    f"theorem {upto_theorem} {{p : ℕ × ℕ}}",
                    f"    (hp : p ∈ {upto}) : {predicate} := by",
                    f"  exact {leaf_theorem(class_index)} (by simpa [{upto}] using hp)",
                    "",
                ]
            )
        else:
            previous = (
                f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup{group_index:03d}"
                f"PairsUpTo{offset - 1:03d}_coordinate_bound"
            )
            lines.extend(
                [
                    f"theorem {upto_theorem} {{p : ℕ × ℕ}}",
                    f"    (hp : p ∈ {upto}) : {predicate} := by",
                    f"  rw [{upto}, Finset.mem_union] at hp",
                    "  rcases hp with hp | hp",
                    f"  · exact {previous} hp",
                    f"  · exact {leaf_theorem(class_index)} hp",
                    "",
                ]
            )
    final_upto = (
        f"PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup{group_index:03d}"
        f"PairsUpTo{len(class_indices) - 1:03d}"
    )
    group_pairs = f"{group_name(group_index)}Pairs"
    lines.extend(
        [
            f"theorem {group_theorem} {{p : ℕ × ℕ}}",
            f"    (hp : p ∈ {group_pairs}) : {predicate} := by",
            (
                f"  exact {final_upto}_coordinate_bound "
                f"(by simpa [{group_pairs}] using hp)"
            ),
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def tail_merge_pairwise_chunk_stem(index: int) -> str:
    return f"{STEM}TailMergePairwiseChunk{index:03d}"


def tail_merge_aggregate_stem() -> str:
    return f"{STEM}TailMergeAggregate"


def render_late_bound(index: int, stage_123_index: int) -> str:
    lower, upper = LATE_GROUP_MIN_BOUNDS[index]
    if index == 284:
        imports = [
            module_name(stage_stem(stage_123_index)),
            module_name(range_group_stem(index)),
        ]
    else:
        imports = [module_name(range_group_stem(index))]
    lines = common_header(
        imports,
        f"/- Late-tail coordinate interface for group {index:03d}. -/",
    )
    if index == 284:
        lines.extend(
            [
                f"theorem {late_tail_min_lower_name(index)} {{p : ℕ × ℕ}}",
                f"    (hp : p ∈ {late_tail_upto_name(index)}) : {LATE_TAIL_MIN_LOWER} ≤ {min_coordinate()} := by",
                f"  exact ({group_min_bounds_name(index)} (by simpa [{late_tail_upto_name(index)}] using hp)).1",
                "",
                f"theorem {late_tail_min_upper_name(index, upper)} {{p : ℕ × ℕ}}",
                f"    (hp : p ∈ {late_tail_upto_name(index)}) : {min_coordinate()} ≤ {upper} := by",
                f"  exact ({group_min_bounds_name(index)} (by simpa [{late_tail_upto_name(index)}] using hp)).2",
                "",
            ]
        )
    lines.extend(common_footer())
    return "\n".join(lines)


def group_tail_disjoint_name(group_index: int, tail_end: int) -> str:
    return f"{group_name(group_index)}Pairs_disjoint_{tail_upto_name(tail_end)}"


def prefix_tail_disjoint_name(prefix_end: int, tail_end: int) -> str:
    return f"{upto_name(prefix_end)}_disjoint_{tail_upto_name(tail_end)}"


def group_late_tail_disjoint_name(group_index: int, late_tail_end: int) -> str:
    return (
        f"{group_name(group_index)}Pairs_disjoint_"
        f"{late_tail_upto_name(late_tail_end)}"
    )


def tail_late_tail_disjoint_name(tail_end: int, late_tail_end: int) -> str:
    return (
        f"{tail_upto_name(tail_end)}_disjoint_"
        f"{late_tail_upto_name(late_tail_end)}"
    )


def render_tail_merge_pairwise_chunk(
    chunk_index: int,
    start: int,
    end: int,
    early_tail_stage_index: int,
    late_tail_end: int,
) -> str:
    imports = [module_name(stage_stem(early_tail_stage_index))]
    imports.extend(module_name(range_group_stem(index)) for index in range(start, end))
    lines = common_header(
        imports,
        (
            f"/- Import constant-size coordinate certificates for tail groups "
            f"{start:03d}..{end - 1:03d}. -/"
        ),
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_tail_merge_aggregate(
    chunk_count: int,
    tail_start: int,
    tail_end: int,
    late_tail_end: int,
    late_stage_index: int,
) -> str:
    imports = [
        module_name(tail_merge_pairwise_chunk_stem(index))
        for index in range(chunk_count)
    ]
    imports.append(module_name(late_stage_stem(late_stage_index)))
    lines = common_header(
        imports,
        (
            f"/- Structural disjointness assembly for tail groups "
            f"{tail_start:03d}..{tail_end:03d} against the late tail. -/"
        ),
    )
    for index in range(tail_start, tail_end + 1):
        theorem_name = tail_min_upper_name(index)
        group_theorem = group_min_upper_name(index)
        if index == tail_start:
            lines.extend(
                [
                    f"theorem {theorem_name} {{p : ℕ × ℕ}}",
                    f"    (hp : p ∈ {tail_upto_name(index)}) : {min_coordinate()} ≤ {OLD_TAIL_MIN_UPPER} := by",
                    f"  exact {group_theorem} (by simpa [{tail_upto_name(index)}] using hp)",
                    "",
                ]
            )
            continue
        previous_theorem = tail_min_upper_name(index - 1)
        lines.extend(
            [
                f"theorem {theorem_name} {{p : ℕ × ℕ}}",
                f"    (hp : p ∈ {tail_upto_name(index)}) : {min_coordinate()} ≤ {OLD_TAIL_MIN_UPPER} := by",
                f"  rw [{tail_upto_name(index)}, Finset.mem_union] at hp",
                "  rcases hp with hp | hp",
                f"  · exact {previous_theorem} hp",
                f"  · exact {group_theorem} hp",
                "",
            ]
        )
    late_tail = late_tail_upto_name(late_tail_end)
    disjoint = tail_late_tail_disjoint_name(tail_end, late_tail_end)
    lines.extend(
        [
            f"theorem {disjoint} :",
            f"    Disjoint {tail_upto_name(tail_end)} {late_tail} := by",
            "  refine Finset.disjoint_left.mpr ?_",
            "  intro p hp_tail hp_late",
            f"  have htail := {tail_min_upper_name(tail_end)} hp_tail",
            f"  have hlate := {late_tail_min_lower_name(late_tail_end)} hp_late",
            "  omega",
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


def render_tail_merge_stage(
    stage_index: int,
    tail_end: int,
    late_tail_end: int,
) -> str:
    tail_pairs = tail_upto_name(late_tail_end)
    tail_total = tail_total_name(late_tail_end)
    early_pairs = tail_upto_name(tail_end)
    early_total = tail_total_name(tail_end)
    late_pairs = late_tail_upto_name(late_tail_end)
    late_total = late_tail_total_name(late_tail_end)
    disjoint = tail_late_tail_disjoint_name(tail_end, late_tail_end)
    lines = common_header(
        [module_name(tail_merge_aggregate_stem())],
        "/- Recombine the two independently checked tail segments. -/",
    )
    lines.extend(
        [
            f"def {tail_pairs} : Finset (ℕ × ℕ) :=",
            f"  {early_pairs} ∪ {late_pairs}",
            "",
            f"def {tail_total} : ℚ :=",
            f"  {early_total} + {late_total}",
            "",
            f"theorem {tail_pairs}_actual_sum :",
            f"    (∑ p ∈ {tail_pairs}, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = {tail_total} := by",
            f"  rw [{tail_pairs}, Finset.sum_union {disjoint}]",
            f"  rw [{early_pairs}_actual_sum, {late_pairs}_actual_sum]",
            "  rfl",
            "",
        ]
    )
    lines.extend(common_footer())
    return "\n".join(lines)


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
    late_tail_start: int,
    late_tail_disjoint_chunk_size: int,
) -> dict[Path, str]:
    rendered: dict[Path, str] = {}
    if disjoint_chunk_size <= 0:
        raise ValueError("disjoint chunk size must be positive")
    if late_tail_disjoint_chunk_size <= 0:
        raise ValueError("late-tail disjoint chunk size must be positive")
    if not accumulation_reset_start < late_tail_start < GROUP_COUNT:
        raise ValueError(
            "late-tail start must be after the accumulation reset and before "
            f"{GROUP_COUNT}"
        )
    ranges = stage_ranges(
        stage_size,
        tail_start,
        tail_stage_size,
        accumulation_reset_start,
    )
    for stage_index, (start, end) in enumerate(ranges):
        output_stem = (
            late_stage_stem(stage_index)
            if end == GROUP_COUNT
            else stage_stem(stage_index)
        )
        rendered[OUT_DIR / f"{output_stem}.lean"] = render_stage(
            stage_index,
            start,
            end,
            accumulation_reset_start,
            late_tail_start,
        )
    last_stage = len(ranges) - 1
    late_reset_stage = next(
        stage_index
        for stage_index, (start, _end) in enumerate(ranges)
        if start == late_tail_start
    )
    early_tail_stage = late_reset_stage - 1
    for group_index in range(accumulation_reset_start, GROUP_COUNT):
        for class_index in group_class_indices(group_index):
            rendered[OUT_DIR / f"{range_leaf_stem(class_index)}.lean"] = (
                render_range_leaf(class_index, group_index)
            )
        rendered[OUT_DIR / f"{range_group_stem(group_index)}.lean"] = (
            render_range_group(group_index)
        )
    for index in range(late_tail_start, GROUP_COUNT):
        rendered[OUT_DIR / f"{late_bound_stem(index)}.lean"] = render_late_bound(
            index, late_reset_stage
        )
    early_tail_end = late_tail_start - 1
    late_tail_end = GROUP_COUNT - 1
    late_pairwise_starts = list(
        range(
            accumulation_reset_start,
            late_tail_start,
            late_tail_disjoint_chunk_size,
        )
    )
    for chunk_index, start in enumerate(late_pairwise_starts):
        end = min(late_tail_start, start + late_tail_disjoint_chunk_size)
        rendered[
            OUT_DIR / f"{tail_merge_pairwise_chunk_stem(chunk_index)}.lean"
        ] = render_tail_merge_pairwise_chunk(
            chunk_index,
            start,
            end,
            early_tail_stage,
            late_tail_end,
        )
    rendered[OUT_DIR / f"{tail_merge_aggregate_stem()}.lean"] = (
        render_tail_merge_aggregate(
            len(late_pairwise_starts),
            accumulation_reset_start,
            early_tail_end,
            late_tail_end,
            last_stage,
        )
    )
    rendered[OUT_DIR / f"{stage_stem(last_stage)}.lean"] = (
        render_tail_merge_stage(last_stage, early_tail_end, late_tail_end)
    )
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
    parser.add_argument(
        "--late-tail-start",
        type=int,
        default=DEFAULT_LATE_TAIL_START,
        help="Restart the tail again before the final oversized accumulation.",
    )
    parser.add_argument(
        "--late-tail-disjoint-chunk-size",
        type=int,
        default=DEFAULT_LATE_TAIL_DISJOINT_CHUNK_SIZE,
        help="Early-tail groups per pairwise late-tail module.",
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    rendered = expected_files(
        args.stage_size,
        args.tail_start,
        args.tail_stage_size,
        args.accumulation_reset_start,
        args.disjoint_chunk_size,
        args.late_tail_start,
        args.late_tail_disjoint_chunk_size,
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
        f"disjoint_chunk_size={args.disjoint_chunk_size}, "
        f"late_tail_start={args.late_tail_start}, "
        f"late_tail_disjoint_chunk_size={args.late_tail_disjoint_chunk_size}"
    )


if __name__ == "__main__":
    main()
