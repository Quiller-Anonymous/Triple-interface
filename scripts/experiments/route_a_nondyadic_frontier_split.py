#!/usr/bin/env python3
"""Proactively split hard Route A non-dyadic class groups.

The direct Route A CI build compiles ignored generated source restored from a
checked-in tarball.  If an unsplit non-dyadic class is too large, the hosted
runner can spend hours on it and then time out.  This helper scans a bounded
class-group frontier, selects rows that dominate large unsplit class wrappers,
reruns the existing group generator with those rows split, and optionally
refreshes the q0cert source archive.

Default mode is report-only.  Pass --apply to regenerate sources.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import os
import re
import subprocess
import sys
import tarfile
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(".")
MODULE_DIR = Path("Goldbach/Cert/MajorArcModules")
CLASS_PREFIX = (
    "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFive"
    "NonDyadicClass"
)
SPLIT_MARKER = "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicSplit"
GROUP_BUILDER = Path("scripts/experiments/build_periodic_main_nondyadic_group.py")
ARCHIVE_MANIFEST = Path(".github/route_a_smoke/q0cert_extra_missing_sources.txt")
ARCHIVE_TARBALL = Path(".github/route_a_smoke/q0cert_extra_missing_sources.tar.gz")
ARCHIVE_SHA256 = Path(".github/route_a_smoke/q0cert_extra_missing_sources.tar.gz.sha256")
DEFAULT_TARGET = "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert"


@dataclass(frozen=True)
class LargeClass:
    idx: int
    size: int
    left_rows: tuple[int, ...]


@dataclass(frozen=True)
class GroupPlan:
    group: int
    classes: tuple[LargeClass, ...]
    rows: tuple[int, ...]
    row_counts: tuple[tuple[int, int], ...]
    total_bytes: int


def class_path(idx: int) -> Path:
    return MODULE_DIR / f"{CLASS_PREFIX}{idx}.lean"


def class_group_range(group: int) -> range:
    return range(group * 25, min(group * 25 + 25, 7158))


def extract_left_rows(text: str) -> tuple[int, ...]:
    pairs = re.findall(r"periodicMainPair_(\d+)_(\d+)_X1000000", text)
    return tuple(sorted({int(left) for left, _right in pairs}))


def scan_group(group: int, threshold_bytes: int, include_split: bool) -> GroupPlan | None:
    large: list[LargeClass] = []
    row_counts: collections.Counter[int] = collections.Counter()
    for idx in class_group_range(group):
        path = class_path(idx)
        if not path.exists():
            continue
        text = path.read_text(errors="ignore")
        if not include_split and SPLIT_MARKER in text:
            continue
        size = path.stat().st_size
        if size < threshold_bytes:
            continue
        left_rows = extract_left_rows(text)
        large.append(LargeClass(idx=idx, size=size, left_rows=left_rows))
        for row in left_rows:
            row_counts[row] += 1
    if not large:
        return None
    rows = tuple(row for row, _count in row_counts.most_common())
    return GroupPlan(
        group=group,
        classes=tuple(large),
        rows=rows,
        row_counts=tuple(row_counts.most_common()),
        total_bytes=sum(item.size for item in large),
    )


def choose_rows(plan: GroupPlan, max_rows: int, min_row_count: int) -> tuple[int, ...]:
    rows = [
        row
        for row, count in plan.row_counts
        if count >= min_row_count
    ]
    if max_rows > 0:
        rows = rows[:max_rows]
    return tuple(rows)


def run_group_builder(
    group: int,
    rows: tuple[int, ...],
    *,
    row_part_size: int,
    split_min_right_divisors: int,
    verbose_child: bool,
) -> None:
    cmd = [
        "python3",
        str(GROUP_BUILDER),
        str(group),
        "--split-left-rows",
        *[str(row) for row in rows],
        "--split-min-right-divisors",
        str(split_min_right_divisors),
        "--row-part-size",
        str(row_part_size),
        "--skip-build",
    ]
    print(f"[split] group={group:03d} rows={list(rows)}", flush=True)
    started = time.monotonic()
    if verbose_child:
        subprocess.run(cmd, check=True)
    else:
        proc = subprocess.run(
            cmd,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if proc.returncode != 0:
            print(f"[split-failed] group={group:03d} exit={proc.returncode}", flush=True)
            print("\n".join(proc.stdout.splitlines()[-120:]), file=sys.stderr)
            raise SystemExit(proc.returncode)
    elapsed = time.monotonic() - started
    print(f"[split-ok] group={group:03d} elapsed_s={elapsed:.1f}", flush=True)


def import_archive_audit_helpers():
    sys.path.insert(0, str((ROOT / "scripts/ci").resolve()))
    import route_a_source_archive_audit as audit  # type: ignore

    return audit


def refresh_source_archive(target: str, progress_every: int) -> None:
    audit = import_archive_audit_helpers()
    root = ROOT.resolve()
    order, _missing, _imports_by_module = audit.local_closure_fast(
        root,
        target,
        progress_every=progress_every,
    )
    tracked = audit.git_tracked_files(root)
    entries = sorted(
        audit.module_source_relpath(root, module)
        for module in order
        if audit.module_source_relpath(root, module) not in tracked
    )

    ARCHIVE_MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    ARCHIVE_MANIFEST.write_text("\n".join(entries) + ("\n" if entries else ""))

    tmp_tarball = ARCHIVE_TARBALL.with_suffix(ARCHIVE_TARBALL.suffix + ".tmp")
    if tmp_tarball.exists():
        tmp_tarball.unlink()
    with tarfile.open(tmp_tarball, "w:gz") as archive:
        for relpath in entries:
            archive.add(root / relpath, arcname=relpath)
    os.replace(tmp_tarball, ARCHIVE_TARBALL)

    digest = hashlib.sha256(ARCHIVE_TARBALL.read_bytes()).hexdigest()
    ARCHIVE_SHA256.write_text(f"{digest}  {ARCHIVE_TARBALL.name}\n")
    print(
        "[archive] "
        f"entries={len(entries)} manifest={ARCHIVE_MANIFEST} "
        f"tarball={ARCHIVE_TARBALL} sha256={digest}",
        flush=True,
    )


def print_plan(plan: GroupPlan, chosen_rows: tuple[int, ...]) -> None:
    max_class = max(plan.classes, key=lambda item: item.size)
    row_text = ",".join(str(row) for row in chosen_rows) if chosen_rows else "-"
    counts_text = ",".join(f"{row}:{count}" for row, count in plan.row_counts[:5])
    print(
        f"[plan] group={plan.group:03d} large={len(plan.classes)} "
        f"bytes={plan.total_bytes} rows={row_text} top_counts={counts_text} "
        f"max=Class{max_class.idx}:{max_class.size}:rows{list(max_class.left_rows)}",
        flush=True,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start-group", type=int, required=True)
    parser.add_argument("--end-group", type=int, required=True)
    parser.add_argument("--threshold-bytes", type=int, default=30_000)
    parser.add_argument("--max-rows-per-group", type=int, default=2)
    parser.add_argument("--min-row-count", type=int, default=1)
    parser.add_argument("--row-part-size", type=int, default=4)
    parser.add_argument("--split-min-right-divisors", type=int, default=16)
    parser.add_argument("--include-already-split", action="store_true")
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--verbose-child", action="store_true")
    parser.add_argument("--skip-archive-refresh", action="store_true")
    parser.add_argument("--target", default=DEFAULT_TARGET)
    parser.add_argument("--archive-progress-every", type=int, default=50_000)
    args = parser.parse_args()

    if args.end_group < args.start_group:
        raise SystemExit("--end-group must be >= --start-group")

    plans: list[tuple[GroupPlan, tuple[int, ...]]] = []
    for group in range(args.start_group, args.end_group + 1):
        plan = scan_group(
            group,
            args.threshold_bytes,
            include_split=args.include_already_split,
        )
        if plan is None:
            continue
        chosen_rows = choose_rows(
            plan,
            max_rows=args.max_rows_per_group,
            min_row_count=args.min_row_count,
        )
        if not chosen_rows:
            continue
        plans.append((plan, chosen_rows))
        print_plan(plan, chosen_rows)

    print(
        f"[summary] groups={len(plans)} apply={str(args.apply).lower()} "
        f"threshold_bytes={args.threshold_bytes}",
        flush=True,
    )

    if not args.apply:
        return 0

    for plan, rows in plans:
        run_group_builder(
            plan.group,
            rows,
            row_part_size=args.row_part_size,
            split_min_right_divisors=args.split_min_right_divisors,
            verbose_child=args.verbose_child,
        )

    if not args.skip_archive_refresh:
        refresh_source_archive(args.target, progress_every=args.archive_progress_every)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
