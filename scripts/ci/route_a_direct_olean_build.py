#!/usr/bin/env python3
"""Build a Lean module closure directly to .olean/.ilean artifacts.

This is a CI escape hatch for very large generated certificate targets where
Lake's module build also emits native C/IR artifacts.  It assumes it is run
under `lake env`, so LEAN_PATH already points at Mathlib and project artifacts.
"""

from __future__ import annotations

import argparse
import concurrent.futures
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


def module_to_source(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def module_to_artifact(root: Path, module: str, suffix: str) -> Path:
    return root / ".lake" / "build" / "lib" / "lean" / (
        module.replace(".", "/") + suffix
    )


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
    workers: int,
    progress_every: int,
    deadline: float,
) -> tuple[int, int, str | None, int]:
    """Compile the local module DAG, running independent modules in parallel."""
    total = len(order)
    order_index = {module: index for index, module in enumerate(order, start=1)}
    local_modules = set(order)
    completed: set[str] = set()
    skipped = 0

    for module in order:
        if module_to_artifact(root, module, ".olean").exists() and not force:
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
        f"initial_ready={len(ready)} pending={len(remaining_deps)}",
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
                if module_to_artifact(root, module, ".olean").exists() and not force:
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
                submitted[executor.submit(run_lean, root, module, remaining_time)] = module
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
        "--status-file",
        default="route-a-direct-build-status.json",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    started = time.monotonic()
    deadline = started + args.timeout_minutes * 60.0

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
            workers=args.workers,
            progress_every=args.progress_every,
            deadline=deadline,
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
            "failed_module": failed_module,
            "exit_code": exit_code,
            "elapsed_seconds": elapsed,
        }
        Path(args.status_file).write_text(json.dumps(status, indent=2) + "\n")
        print("[status] " + json.dumps(status, sort_keys=True), flush=True)

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
