#!/usr/bin/env python3
"""Build one non-dyadic periodic-main class group in a controlled workflow.

The raw group target can stall on uncached hard class files. This script makes
the dependency shape explicit:

1. Regenerate the class wrappers for the group.
2. Emit any missing hard split modules imported by those wrappers.
3. Build split modules one at a time.
4. Build class wrappers in small batches.
5. Build the group wrapper.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path


MODULE_DIR = Path("Goldbach/Cert/MajorArcModules")
DATA_PATH = Path(
    ".cache/periodic_main_exact_records_full/"
    "periodic_main_ordered_nonzero_without_row_five_nondyadic_unordered_pairs.json"
)
GENERATOR = Path("scripts/experiments/exp_q0_exact_trunc_paircorr_boundary_audit.py")
CLASS_FILE_PREFIX = "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass"
CLASS_LABEL_PREFIX = "NonzeroWithoutRowFiveNonDyadicClass"
SPLIT_FILE_PREFIX = "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicSplit"
SPLIT_LABEL_PREFIX = "NonzeroWithoutRowFiveNonDyadicSplit"
MODULE_PREFIX = (
    "Goldbach.Cert.MajorArcModules."
    "Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadic"
)


class BuildTimedOut(RuntimeError):
    pass


def run(cmd: list[str], log: Path | None = None, timeout: int = 0) -> None:
    started = time.monotonic()
    if log is None:
        print("[run]", " ".join(cmd), flush=True)
        subprocess.run(cmd, check=True)
    else:
        log.parent.mkdir(parents=True, exist_ok=True)
        print("[build]", cmd[-1], "log=", log, flush=True)
        with log.open("w") as fh:
            proc = subprocess.Popen(
                cmd,
                stdout=fh,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            try:
                proc.wait(timeout=timeout if timeout > 0 else None)
            except subprocess.TimeoutExpired as exc:
                print(f"[timeout] {timeout}s log={log}", flush=True)
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                    proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                raise BuildTimedOut(str(log)) from exc
        if proc.returncode != 0:
            print(f"[fail] exit={proc.returncode} log={log}", flush=True)
            try:
                tail = log.read_text().splitlines()[-80:]
                print("\n".join(tail), file=sys.stderr)
            except OSError:
                pass
            raise SystemExit(proc.returncode)
    elapsed = time.monotonic() - started
    print(f"[ok] {elapsed:.1f}s", flush=True)


def module_olean(stem: str) -> Path:
    return Path(".lake/build/lib/lean/Goldbach/Cert/MajorArcModules") / f"{stem}.olean"


def module_source(stem: str) -> Path:
    return MODULE_DIR / f"{stem}.lean"


def module_is_fresh(stem: str) -> bool:
    """Return true only when the cached olean is not older than the source."""
    olean = module_olean(stem)
    source = module_source(stem)
    if not olean.exists() or not source.exists():
        return False
    return olean.stat().st_mtime >= source.stat().st_mtime


def target(stem: str) -> str:
    return f"+Goldbach.Cert.MajorArcModules.{stem}:olean"


def group_stem(group: int) -> str:
    return f"{CLASS_FILE_PREFIX}Group{group:03d}"


def class_stem(cls: int) -> str:
    return f"{CLASS_FILE_PREFIX}{cls}"


def split_stem(split: int) -> str:
    return f"{SPLIT_FILE_PREFIX}{split}"


def parse_group_classes(group: int) -> list[int]:
    path = MODULE_DIR / f"{group_stem(group)}.lean"
    text = path.read_text()
    classes = sorted(
        {
            int(m.group(1))
            for m in re.finditer(
                rf"{re.escape(CLASS_FILE_PREFIX)}(\d+)", text
            )
        }
    )
    if not classes:
        raise SystemExit(f"no classes found in {path}")
    return classes


def emit_class(cls: int, split_left_rows: list[int], split_min_right_divisors: int) -> None:
    start = cls * 2
    cmd = [
        "python3",
        str(GENERATOR),
        "--X",
        "1000000",
        "--emit-periodic-main-unordered-pair-lean-files",
        str(DATA_PATH),
        str(MODULE_DIR),
        CLASS_FILE_PREFIX,
        CLASS_LABEL_PREFIX,
        "--periodic-main-class-start",
        str(start),
        "--periodic-main-class-count",
        "2",
        "--periodic-main-class-file-chunk-size",
        "2",
        "--periodic-main-unordered-use-symmetry",
        "--periodic-main-unordered-split-left-rows",
        *[str(row) for row in split_left_rows],
        "--periodic-main-unordered-split-min-right-divisors",
        str(split_min_right_divisors),
        "--periodic-main-unordered-split-file-prefix",
        SPLIT_FILE_PREFIX,
        "--periodic-main-unordered-split-out-dir",
        str(MODULE_DIR),
    ]
    run(cmd)


def class_split_imports(cls: int) -> set[int]:
    path = MODULE_DIR / f"{class_stem(cls)}.lean"
    text = path.read_text()
    return {
        int(m.group(1))
        for m in re.finditer(r"NonzeroWithoutRowFiveNonDyadicSplit(\d+)", text)
    }


def split_import_stems(stem: str) -> list[str]:
    path = MODULE_DIR / f"{stem}.lean"
    if not path.exists():
        return []
    imports: list[str] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line.startswith("import "):
            continue
        imported = line.split()[-1].rsplit(".", 1)[-1]
        if imported.startswith(SPLIT_FILE_PREFIX) and (MODULE_DIR / f"{imported}.lean").exists():
            imports.append(imported)
    return imports


def load_source_to_class() -> dict[int, int]:
    data = json.loads(DATA_PATH.read_text())
    source_to_class: dict[int, int] = {}
    for class_idx, entry in enumerate(data["classes"]):
        for rec in entry["records"]:
            source_to_class[int(rec["source_index"])] = class_idx
    return source_to_class


def emit_split(
    split: int,
    source_to_class: dict[int, int],
    row_part_size: int,
    split_left_rows: list[int],
    split_min_right_divisors: int,
) -> None:
    try:
        class_idx = source_to_class[split]
    except KeyError as exc:
        raise SystemExit(f"no unordered class index found for split source_index={split}") from exc
    cmd = [
        "python3",
        str(GENERATOR),
        "--X",
        "1000000",
        "--emit-periodic-main-unordered-hard-split-lean-files",
        str(DATA_PATH),
        str(MODULE_DIR),
        SPLIT_FILE_PREFIX,
        SPLIT_LABEL_PREFIX,
        "--periodic-main-class-start",
        str(class_idx),
        "--periodic-main-class-count",
        "1",
        "--periodic-main-unordered-use-symmetry",
        "--periodic-main-unordered-split-left-rows",
        *[str(row) for row in split_left_rows],
        "--periodic-main-unordered-split-min-right-divisors",
        str(split_min_right_divisors),
        "--periodic-main-split-row-part-size",
        str(row_part_size),
        "--periodic-main-split-inline-row-parts",
    ]
    run(cmd)


def build_one(stem: str, log_dir: Path, timeout: int = 0) -> None:
    if module_is_fresh(stem):
        print(f"[skip-built] {stem}", flush=True)
        return
    run(["lake", "--quiet", "build", target(stem)], log=log_dir / f"{stem}.out", timeout=timeout)


def build_split_tree(
    stem: str,
    log_dir: Path,
    *,
    root_timeout: int,
    dependency_timeout: int,
    seen: set[str] | None = None,
) -> None:
    seen = seen or set()
    if stem in seen:
        return
    seen.add(stem)
    for dep in split_import_stems(stem):
        build_split_tree(
            dep,
            log_dir,
            root_timeout=dependency_timeout,
            dependency_timeout=dependency_timeout,
            seen=seen,
        )
    build_one(stem, log_dir, timeout=root_timeout)


def build_batch(stems: list[str], log_dir: Path, name: str) -> None:
    missing = [s for s in stems if not module_is_fresh(s)]
    if not missing:
        print(f"[skip-built] {name}", flush=True)
        return
    cmd = ["lake", "--quiet", "build"] + [target(s) for s in missing]
    run(cmd, log=log_dir / f"{name}.out")


def chunked(xs: list[int], n: int) -> list[list[int]]:
    return [xs[i : i + n] for i in range(0, len(xs), n)]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("group", type=int, help="Class group number, e.g. 43 for Group043.")
    ap.add_argument("--row-part-size", type=int, default=4)
    ap.add_argument("--fallback-row-part-size", type=int, default=2)
    ap.add_argument("--second-fallback-row-part-size", type=int, default=1)
    ap.add_argument("--split-timeout-seconds", type=int, default=0)
    ap.add_argument("--fallback-split-timeout-seconds", type=int, default=900)
    ap.add_argument("--second-fallback-split-timeout-seconds", type=int, default=1200)
    ap.add_argument("--split-dependency-timeout-seconds", type=int, default=900)
    ap.add_argument("--class-batch-size", type=int, default=2)
    ap.add_argument("--split-left-rows", nargs="*", type=int, default=[10])
    ap.add_argument("--split-min-right-divisors", type=int, default=16)
    ap.add_argument("--log-dir", type=Path, default=Path("/private/tmp/goldbach_periodic_group_build"))
    ap.add_argument("--skip-emit", action="store_true")
    ap.add_argument("--skip-built-class-emit", action="store_true")
    ap.add_argument("--skip-build", action="store_true")
    args = ap.parse_args()

    classes = parse_group_classes(args.group)
    print(
        f"[group] {args.group:03d} classes={classes[0]}..{classes[-1]} count={len(classes)}",
        flush=True,
    )

    if not args.skip_emit:
        for cls in classes:
            if args.skip_built_class_emit and module_olean(class_stem(cls)).exists():
                print(f"[skip-class-emit-built] {cls}", flush=True)
                continue
            emit_class(cls, args.split_left_rows, args.split_min_right_divisors)

    split_ids = sorted({s for cls in classes for s in class_split_imports(cls)})
    source_to_class = load_source_to_class()
    print(f"[splits] count={len(split_ids)} ids={split_ids}", flush=True)

    if not args.skip_emit:
        for split in split_ids:
            if module_olean(split_stem(split)).exists():
                print(f"[skip-split-emit-built] {split}", flush=True)
                continue
            emit_split(
                split,
                source_to_class,
                args.row_part_size,
                args.split_left_rows,
                args.split_min_right_divisors,
            )

    if args.skip_build:
        return

    for split in split_ids:
        try:
            build_split_tree(
                split_stem(split),
                args.log_dir,
                root_timeout=args.split_timeout_seconds,
                dependency_timeout=args.split_dependency_timeout_seconds,
            )
        except BuildTimedOut:
            fallbacks = [
                (args.fallback_row_part_size, args.fallback_split_timeout_seconds),
                (args.second_fallback_row_part_size, args.second_fallback_split_timeout_seconds),
            ]
            last_timeout: BuildTimedOut | None = None
            for row_part_size, timeout in fallbacks:
                if row_part_size <= 0:
                    continue
                print(
                    f"[retry-split] {split} row-part-size={row_part_size} timeout={timeout}s",
                    flush=True,
                )
                emit_split(
                    split,
                    source_to_class,
                    row_part_size,
                    args.split_left_rows,
                    args.split_min_right_divisors,
                )
                try:
                    build_split_tree(
                        split_stem(split),
                        args.log_dir,
                        root_timeout=timeout,
                        dependency_timeout=args.split_dependency_timeout_seconds,
                    )
                    last_timeout = None
                    break
                except BuildTimedOut as exc:
                    last_timeout = exc
            if last_timeout is not None:
                raise last_timeout

    for batch in chunked(classes, args.class_batch_size):
        stems = [class_stem(cls) for cls in batch]
        name = f"classes_{batch[0]}_{batch[-1]}"
        build_batch(stems, args.log_dir, name)

    build_one(group_stem(args.group), args.log_dir)
    print(f"[done] group {args.group:03d}", flush=True)


if __name__ == "__main__":
    main()
