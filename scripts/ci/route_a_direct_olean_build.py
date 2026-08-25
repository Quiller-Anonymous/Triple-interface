#!/usr/bin/env python3
"""Build a Lean module closure directly to .olean/.ilean artifacts.

This is a CI escape hatch for very large generated certificate targets where
Lake's module build also emits native C/IR artifacts.  It assumes it is run
under `lake env`, so LEAN_PATH already points at Mathlib and project artifacts.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import heapq
import json
import os
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path


_ACTIVE_PROCESSES: dict[int, tuple[str, subprocess.Popen]] = {}
_ACTIVE_PROCESS_LOCK = threading.Lock()
SOURCE_HASH_STAMP_SUFFIX = ".route_a_source.sha256"


def module_to_source(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def module_to_artifact(root: Path, module: str, suffix: str) -> Path:
    return root / ".lake" / "build" / "lib" / "lean" / (
        module.replace(".", "/") + suffix
    )


def module_artifact_is_fresh(root: Path, module: str) -> bool:
    source = module_to_source(root, module)
    olean = module_to_artifact(root, module, ".olean")
    if not olean.exists():
        return False
    if not source.exists():
        return True
    return olean.stat().st_mtime >= source.stat().st_mtime


def module_source_hash(root: Path, module: str) -> str | None:
    source = module_to_source(root, module)
    if not source.exists():
        return None
    digest = hashlib.sha256()
    with source.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def module_force_stamp_matches(root: Path, module: str) -> bool:
    """Whether a force-listed module has already been rebuilt for this source content."""
    if not module_artifact_is_fresh(root, module):
        return False
    source_hash = module_source_hash(root, module)
    if source_hash is None:
        return True
    stamp = module_to_artifact(root, module, SOURCE_HASH_STAMP_SUFFIX)
    if not stamp.exists():
        return False
    return stamp.read_text(errors="ignore").strip() == source_hash


def write_module_force_stamp(root: Path, module: str) -> None:
    source_hash = module_source_hash(root, module)
    if source_hash is None:
        return
    stamp = module_to_artifact(root, module, SOURCE_HASH_STAMP_SUFFIX)
    stamp.parent.mkdir(parents=True, exist_ok=True)
    stamp.write_text(source_hash + "\n")


def strip_lean_comments(text: str) -> str:
    """Remove Lean line and nested block comments before scanning imports."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            if i < len(text):
                out.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            # Preserve line boundaries so diagnostics still correspond roughly.
            out.append("\n")
        i += 1
    return "".join(out)


def parse_imports(source: Path) -> list[str]:
    imports: list[str] = []
    text = strip_lean_comments(source.read_text(errors="ignore"))
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line.startswith("import "):
            continue
        imported = line.split(None, 1)[1].strip()
        if imported:
            imports.append(imported)
    return imports


def local_closure(root: Path, target: str) -> tuple[list[str], list[str], dict[str, list[str]]]:
    order: list[str] = []
    missing: list[str] = []
    imports_by_module: dict[str, list[str]] = {}
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(module: str) -> None:
        current = state.get(module, 0)
        if current == 2:
            return
        if current == 1:
            cycle_start = stack.index(module)
            cycle = stack[cycle_start:] + [module]
            raise RuntimeError("import cycle detected:\n  " + "\n  ".join(cycle))
        state[module] = 1
        stack.append(module)
        source = module_to_source(root, module)
        if not source.exists():
            missing.append(module)
            stack.pop()
            state[module] = 2
            return
        imports = parse_imports(source)
        imports_by_module[module] = imports
        for imported in imports:
            visit(imported)
        stack.pop()
        state[module] = 2
        order.append(module)

    visit(target)
    return order, missing, imports_by_module


def terminate_process(module: str, process: subprocess.Popen, reason: str) -> None:
    """Terminate one Lean process group, escalating if needed."""
    if process.poll() is not None:
        return
    print(f"[terminate] {module}: {reason}", flush=True)
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except Exception:
        process.terminate()
    try:
        process.wait(timeout=10.0)
        return
    except subprocess.TimeoutExpired:
        pass
    if process.poll() is not None:
        return
    print(f"[kill] {module}: did not terminate after SIGTERM", flush=True)
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except Exception:
        process.kill()
    try:
        process.wait(timeout=10.0)
    except subprocess.TimeoutExpired:
        pass


def terminate_active_processes(reason: str) -> None:
    with _ACTIVE_PROCESS_LOCK:
        active = list(_ACTIVE_PROCESSES.values())
    for module, process in active:
        terminate_process(module, process, reason)


def run_lean(root: Path, module: str, timeout_seconds: float | None) -> int:
    if timeout_seconds is not None and timeout_seconds <= 0:
        print(f"[timeout] {module}", flush=True)
        return 124
    source = module_to_source(root, module)
    olean = module_to_artifact(root, module, ".olean")
    ilean = module_to_artifact(root, module, ".ilean")
    olean.parent.mkdir(parents=True, exist_ok=True)

    cmd = [
        "lean",
        "--root=.",
        "-o",
        str(olean),
        "-i",
        str(ilean),
        str(source),
    ]
    process: subprocess.Popen | None = None
    try:
        process = subprocess.Popen(cmd, cwd=root, start_new_session=True)
        with _ACTIVE_PROCESS_LOCK:
            _ACTIVE_PROCESSES[process.pid] = (module, process)
        return process.wait(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        print(f"[timeout] {module}", flush=True)
        if process is not None:
            terminate_process(module, process, "module timeout")
        return 124
    finally:
        if process is not None:
            with _ACTIVE_PROCESS_LOCK:
                _ACTIVE_PROCESSES.pop(process.pid, None)


def build_closure(
    root: Path,
    order: list[str],
    imports_by_module: dict[str, list[str]],
    *,
    force: bool,
    force_modules: set[str],
    workers: int,
    progress_every: int,
    deadline: float,
    module_timeout_seconds: float | None,
) -> tuple[int, int, str | None, int]:
    """Compile the local module DAG, running independent modules in parallel."""
    total = len(order)
    order_index = {module: index for index, module in enumerate(order, start=1)}
    local_modules = set(order)

    reverse_deps_all: dict[str, list[str]] = {module: [] for module in order}
    for module in order:
        for imported in imports_by_module.get(module, []):
            if imported in local_modules:
                reverse_deps_all.setdefault(imported, []).append(module)

    stale_roots: set[str] = set()
    force_roots_pending: set[str] = set()
    if not force:
        stale_roots = {
            module for module in order
            if not module_artifact_is_fresh(root, module)
        }
        force_roots_pending = {
            module for module in force_modules
            if module in local_modules and not module_force_stamp_matches(root, module)
        }

    dirty_modules: set[str] = set()
    dirty_stack = list(stale_roots | force_roots_pending)
    while dirty_stack:
        module = dirty_stack.pop()
        if module in dirty_modules:
            continue
        dirty_modules.add(module)
        dirty_stack.extend(reverse_deps_all.get(module, []))

    missing_forced = sorted(module for module in force_modules if module not in local_modules)
    if missing_forced:
        print(
            "[force] ignored modules outside target closure: "
            + ", ".join(missing_forced[:20]),
            flush=True,
        )

    completed: set[str] = set()
    skipped = 0

    for module in order:
        if module_artifact_is_fresh(root, module) and not force and module not in dirty_modules:
            completed.add(module)
            skipped += 1

    reverse_deps: dict[str, list[str]] = {module: [] for module in order}
    remaining_deps: dict[str, int] = {}
    for module in order:
        if module in completed:
            continue
        count = 0
        for imported in imports_by_module.get(module, []):
            if imported not in local_modules:
                continue
            reverse_deps.setdefault(imported, []).append(module)
            if imported not in completed:
                count += 1
        remaining_deps[module] = count

    ready: list[tuple[int, str]] = [
        (order_index[module], module)
        for module, count in remaining_deps.items()
        if count == 0
    ]
    heapq.heapify(ready)

    built = 0
    failed_module: str | None = None
    exit_code = 0
    started = time.monotonic()
    worker_count = max(workers, 1)
    progress_step = max(progress_every, 1)

    print(
        f"[scheduler] workers={worker_count} initial_skipped={skipped} "
        f"initial_ready={len(ready)} pending={len(remaining_deps)} "
        f"dirty={len(dirty_modules)} stale_roots={len(stale_roots)} "
        f"force_pending={len(force_roots_pending)} force_satisfied="
        f"{len(force_modules & local_modules) - len(force_roots_pending)}",
        flush=True,
    )

    executor = concurrent.futures.ThreadPoolExecutor(max_workers=worker_count)
    submitted: dict[concurrent.futures.Future[int], str] = {}
    try:
        while ready or submitted:
            remaining_time = deadline - time.monotonic()
            if remaining_time <= 0:
                print("[timeout] build budget exhausted before next module", flush=True)
                exit_code = 124
                break

            while ready and len(submitted) < worker_count and remaining_time > 0:
                index, module = heapq.heappop(ready)
                if module_artifact_is_fresh(root, module) and not force and module not in dirty_modules:
                    completed.add(module)
                    skipped += 1
                    for dependent in reverse_deps.get(module, []):
                        if dependent not in remaining_deps:
                            continue
                        remaining_deps[dependent] -= 1
                        if remaining_deps[dependent] == 0:
                            heapq.heappush(ready, (order_index[dependent], dependent))
                    continue
                print(f"[build] {index}/{total} {module}", flush=True)
                timeout_seconds = remaining_time
                if module_timeout_seconds is not None:
                    timeout_seconds = min(timeout_seconds, module_timeout_seconds)
                submitted[executor.submit(run_lean, root, module, timeout_seconds)] = module
                remaining_time = deadline - time.monotonic()

            if not submitted:
                continue

            wait_timeout = max(0.1, min(5.0, deadline - time.monotonic()))
            done, _ = concurrent.futures.wait(
                submitted,
                timeout=wait_timeout,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            if not done:
                continue

            for future in done:
                module = submitted.pop(future)
                code = future.result()
                if code != 0:
                    failed_module = module
                    exit_code = code
                    print(f"[failed] code={code} module={module}", flush=True)
                    break

                built += 1
                completed.add(module)
                write_module_force_stamp(root, module)
                for dependent in reverse_deps.get(module, []):
                    if dependent not in remaining_deps:
                        continue
                    remaining_deps[dependent] -= 1
                    if remaining_deps[dependent] == 0:
                        heapq.heappush(ready, (order_index[dependent], dependent))

                if built % progress_step == 0:
                    elapsed = time.monotonic() - started
                    print(
                        f"[progress] built={built} skipped={skipped} "
                        f"running={len(submitted)} ready={len(ready)} elapsed_s={elapsed:.1f}",
                        flush=True,
                    )

            if exit_code != 0:
                break
    finally:
        if exit_code != 0:
            terminate_active_processes("build exiting after failure/timeout")
        executor.shutdown(wait=True, cancel_futures=True)

    if exit_code == 0 and ready:
        exit_code = 124

    return built, skipped, failed_module, exit_code


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True)
    parser.add_argument("--root", default=".")
    parser.add_argument("--timeout-minutes", type=float, default=240.0)
    parser.add_argument("--progress-every", type=int, default=25)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--force-module",
        action="append",
        default=[],
        help="Rebuild this local module and every local dependent in the target closure.",
    )
    parser.add_argument(
        "--force-module-list",
        action="append",
        default=[],
        help="File containing local module names to rebuild, one per line.",
    )
    parser.add_argument(
        "--module-timeout-minutes",
        type=float,
        default=150.0,
        help="Maximum time to spend on one Lean module before checkpointing.",
    )
    parser.add_argument(
        "--status-file",
        default="route-a-direct-build-status.json",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    started = time.monotonic()
    deadline = started + args.timeout_minutes * 60.0
    module_timeout_seconds = None
    if args.module_timeout_minutes > 0:
        module_timeout_seconds = args.module_timeout_minutes * 60.0

    force_modules = set(args.force_module or [])
    for raw_path in args.force_module_list or []:
        path = Path(raw_path)
        if not path.is_absolute():
            path = root / path
        if not path.exists():
            print(f"[force] module list not found: {path}", flush=True)
            continue
        for raw_line in path.read_text().splitlines():
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            force_modules.add(line)

    order, missing, imports_by_module = local_closure(root, args.target)
    local_missing = [m for m in missing if module_to_source(root, m).exists()]
    project_missing = [
        m for m in missing
        if m.startswith("Goldbach.") and not module_to_source(root, m).exists()
    ]
    external_missing = [
        m for m in missing
        if not module_to_source(root, m).exists() and not m.startswith("Goldbach.")
    ]
    if local_missing:
        print("[error] local imports reported missing unexpectedly:", flush=True)
        for module in local_missing[:50]:
            print(f"  {module}", flush=True)
        return 2
    if project_missing:
        print("[error] missing project source imports:", flush=True)
        for module in project_missing[:50]:
            print(f"  {module_to_source(root, module).relative_to(root)}", flush=True)
        return 2

    print(f"[closure] local_modules={len(order)} external_imports={len(external_missing)}")
    print(f"[target] {args.target}", flush=True)

    built = 0
    skipped = 0
    failed_module: str | None = None
    exit_code = 0

    try:
        built, skipped, failed_module, exit_code = build_closure(
            root,
            order,
            imports_by_module,
            force=args.force,
            force_modules=force_modules,
            workers=args.workers,
            progress_every=args.progress_every,
            deadline=deadline,
            module_timeout_seconds=module_timeout_seconds,
        )
    finally:
        elapsed = time.monotonic() - started
        status = {
            "target": args.target,
            "local_modules": len(order),
            "external_imports": len(external_missing),
            "built": built,
            "skipped": skipped,
            "workers": max(args.workers, 1),
            "module_timeout_minutes": args.module_timeout_minutes,
            "failed_module": failed_module,
            "exit_code": exit_code,
            "elapsed_seconds": elapsed,
        }
        Path(args.status_file).write_text(json.dumps(status, indent=2) + "\n")
        print("[status] " + json.dumps(status, sort_keys=True), flush=True)

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
