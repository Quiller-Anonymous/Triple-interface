#!/usr/bin/env python3
"""Build the Route A LCM reverse-target bridge with low fan-out.

The final LCM reverse-target module imports hundreds of generated modules. A
plain `lake build` can launch many large Lean workers at once, which is bad on
memory-constrained local runs. This driver builds the generated dependency
layers in an explicit order, one module target at a time by default, and skips
modules whose cached olean is newer than their source and direct local imports.
"""

from __future__ import annotations

import argparse
import re
import signal
import subprocess
import sys
import time
from pathlib import Path


MODULE_DIR = Path("Goldbach/Cert/MajorArcModules")
OLEAN_DIR = Path(".lake/build/lib/lean/Goldbach/Cert/MajorArcModules")
MODULE_PREFIX = "Goldbach.Cert.MajorArcModules."

Q0 = "Q0MinorZeroModeNormalizedAverageX0PeriodicMain"


class BuildTimedOut(RuntimeError):
    pass


def module_source(stem: str) -> Path:
    return MODULE_DIR / f"{stem}.lean"


def module_olean(stem: str) -> Path:
    return OLEAN_DIR / f"{stem}.olean"


def target(stem: str) -> str:
    return f"+{MODULE_PREFIX}{stem}:olean"


def import_stems(stem: str) -> list[str]:
    path = module_source(stem)
    if not path.exists():
        return []
    imports: list[str] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line.startswith("import "):
            continue
        imported = line.split()[-1]
        if not imported.startswith(MODULE_PREFIX):
            continue
        imported_stem = imported.removeprefix(MODULE_PREFIX)
        if module_source(imported_stem).exists():
            imports.append(imported_stem)
    return imports


def module_is_fresh(stem: str) -> bool:
    """Return true when the olean is newer than source and direct local imports."""
    olean = module_olean(stem)
    source = module_source(stem)
    if not olean.exists() or not source.exists():
        return False
    olean_mtime = olean.stat().st_mtime
    if olean_mtime < source.stat().st_mtime:
        return False
    for dep in import_stems(stem):
        dep_olean = module_olean(dep)
        if not dep_olean.exists():
            return False
        if olean_mtime < dep_olean.stat().st_mtime:
            return False
    return True


def natural_key(stem: str) -> tuple[object, ...]:
    parts = re.split(r"(\d+)", stem)
    return tuple(int(p) if p.isdigit() else p for p in parts)


def stems_matching(pattern: str) -> list[str]:
    return sorted((p.stem for p in MODULE_DIR.glob(pattern)), key=natural_key)


def lcm_base_stems() -> list[str]:
    stems: list[str] = []
    stems.extend(stems_matching(f"{Q0}LCMWeight*.lean"))
    stems.extend(stems_matching(f"{Q0}LCMFiberAbs*.lean"))
    stems.extend(stems_matching(f"{Q0}LCMWrapperAbs*.lean"))
    stems.extend(stems_matching(f"{Q0}LCMGroup[0-9][0-9][0-9].lean"))
    stems.extend(stems_matching(f"{Q0}LCMSuperGroup*.lean"))
    stems.append(f"{Q0}LCMFinal")
    return unique_existing(stems)


def target_stems() -> list[str]:
    chunk_re = re.compile(rf"^{re.escape(Q0)}LCMTargetChunk(\d+)(?:Sub(\d+))?$")
    chunk_stems = [
        p.stem
        for p in MODULE_DIR.glob(f"{Q0}LCMTargetChunk*.lean")
        if chunk_re.match(p.stem)
    ]

    def chunk_key(stem: str) -> tuple[int, int, int]:
        m = chunk_re.match(stem)
        if m is None:
            return (10**9, 10**9, 10**9)
        chunk = int(m.group(1))
        sub = m.group(2)
        # Build subchunks before the parent chunk.
        return (chunk, 0 if sub is not None else 1, int(sub or 0))

    stems = sorted(chunk_stems, key=chunk_key)
    stems.extend(stems_matching(f"{Q0}LCMTargetGroup[0-9][0-9][0-9].lean"))
    stems.append(f"{Q0}LCMTargetSubset")
    stems.append(f"{Q0}LCMTarget")
    return unique_existing(stems)


def nonzero_subset_stems() -> list[str]:
    return stems_matching(f"{Q0}CoverageNonzeroChunkSubsetGroup*.lean")


def reverse_stems() -> list[str]:
    stems: list[str] = []
    stems.extend(stems_matching(f"{Q0}LCMReverseTargetGroupAbs*.lean"))
    stems.extend(stems_matching(f"{Q0}LCMReverseTargetGroup[0-9][0-9][0-9].lean"))
    stems.append(f"{Q0}LCMReverseTarget")
    return unique_existing(stems)


def core_stems() -> list[str]:
    return unique_existing(
        [
            f"{Q0}NonzeroRowFiveSurface",
            f"{Q0}NonzeroWithoutRowFiveDyadicBridge",
            f"{Q0}LCM",
        ]
    )


def unique_existing(stems: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for stem in stems:
        if stem in seen:
            continue
        seen.add(stem)
        if module_source(stem).exists():
            out.append(stem)
    return out


def selected_stems(phases: list[str]) -> list[str]:
    order: list[str] = []
    for phase in phases:
        if phase == "core":
            order.extend(core_stems())
        elif phase == "lcm-base":
            order.extend(lcm_base_stems())
        elif phase == "nonzero-subset":
            order.extend(nonzero_subset_stems())
        elif phase == "target":
            order.extend(target_stems())
        elif phase == "reverse":
            order.extend(reverse_stems())
        elif phase == "all":
            order.extend(core_stems())
            order.extend(lcm_base_stems())
            order.extend(nonzero_subset_stems())
            order.extend(target_stems())
            order.extend(reverse_stems())
        else:
            raise SystemExit(f"unknown phase: {phase}")
    return unique_existing(order)


def run_build(stem: str, log_dir: Path, timeout: int) -> None:
    started = time.monotonic()
    log_dir.mkdir(parents=True, exist_ok=True)
    log = log_dir / f"{stem}.out"
    cmd = ["lake", "--quiet", "build", target(stem)]
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
            try:
                os_kill_process_group(proc.pid, signal.SIGTERM)
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os_kill_process_group(proc.pid, signal.SIGKILL)
                proc.wait()
            raise BuildTimedOut(stem) from exc
    elapsed = time.monotonic() - started
    if proc.returncode != 0:
        print(f"[fail] {stem} exit={proc.returncode} log={log}", flush=True)
        try:
            print("\n".join(log.read_text().splitlines()[-80:]), file=sys.stderr)
        except OSError:
            pass
        raise SystemExit(proc.returncode)
    print(f"[ok] {stem} {elapsed:.1f}s", flush=True)


def os_kill_process_group(pid: int, sig: signal.Signals) -> None:
    import os

    os.killpg(pid, sig)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--phase",
        nargs="+",
        default=["all"],
        choices=["all", "core", "lcm-base", "nonzero-subset", "target", "reverse"],
    )
    ap.add_argument("--log-dir", type=Path, default=Path("/private/tmp/goldbach_lcm_reverse_build"))
    ap.add_argument("--start-index", type=int, default=0)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--timeout-seconds", type=int, default=0)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    stems = selected_stems(args.phase)
    if args.start_index:
        stems = stems[args.start_index :]
    if args.limit > 0:
        stems = stems[: args.limit]

    pending = [stem for stem in stems if args.force or not module_is_fresh(stem)]
    print(
        f"[plan] phases={','.join(args.phase)} selected={len(stems)} pending={len(pending)}",
        flush=True,
    )
    if args.dry_run:
        for stem in pending:
            print(stem)
        return

    for idx, stem in enumerate(pending, start=1):
        print(f"[build] {idx}/{len(pending)} {stem}", flush=True)
        run_build(stem, args.log_dir, args.timeout_seconds)

    print("[done]", flush=True)


if __name__ == "__main__":
    main()
