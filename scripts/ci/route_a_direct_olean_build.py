#!/usr/bin/env python3
"""Build a Lean module closure directly to .olean/.ilean artifacts.

This is a CI escape hatch for very large generated certificate targets where
Lake's module build also emits native C/IR artifacts.  It assumes it is run
under `lake env`, so LEAN_PATH already points at Mathlib and project artifacts.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path


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


def local_closure(root: Path, target: str) -> tuple[list[str], list[str]]:
    order: list[str] = []
    missing: list[str] = []
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
        for imported in parse_imports(source):
            visit(imported)
        stack.pop()
        state[module] = 2
        order.append(module)

    visit(target)
    return order, missing


def run_lean(root: Path, module: str, timeout_seconds: float | None) -> int:
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
    try:
        completed = subprocess.run(cmd, cwd=root, timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        print(f"[timeout] {module}", flush=True)
        return 124
    return completed.returncode


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True)
    parser.add_argument("--root", default=".")
    parser.add_argument("--timeout-minutes", type=float, default=240.0)
    parser.add_argument("--progress-every", type=int, default=25)
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--status-file",
        default="route-a-direct-build-status.json",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    started = time.monotonic()
    deadline = started + args.timeout_minutes * 60.0

    order, missing = local_closure(root, args.target)
    local_missing = [m for m in missing if module_to_source(root, m).exists()]
    external_missing = [m for m in missing if not module_to_source(root, m).exists()]
    if local_missing:
        print("[error] local imports reported missing unexpectedly:", flush=True)
        for module in local_missing[:50]:
            print(f"  {module}", flush=True)
        return 2

    print(f"[closure] local_modules={len(order)} external_imports={len(external_missing)}")
    print(f"[target] {args.target}", flush=True)

    built = 0
    skipped = 0
    failed_module: str | None = None
    exit_code = 0

    try:
        for index, module in enumerate(order, start=1):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                print("[timeout] build budget exhausted before next module", flush=True)
                exit_code = 124
                break

            olean = module_to_artifact(root, module, ".olean")
            if olean.exists() and not args.force:
                skipped += 1
                if skipped % max(args.progress_every, 1) == 0:
                    print(
                        f"[skip] {index}/{len(order)} skipped={skipped} built={built} {module}",
                        flush=True,
                    )
                continue

            print(f"[build] {index}/{len(order)} {module}", flush=True)
            code = run_lean(root, module, remaining)
            if code != 0:
                failed_module = module
                exit_code = code
                print(f"[failed] code={code} module={module}", flush=True)
                break
            built += 1
            if built % max(args.progress_every, 1) == 0:
                elapsed = time.monotonic() - started
                print(
                    f"[progress] built={built} skipped={skipped} elapsed_s={elapsed:.1f}",
                    flush=True,
                )
    finally:
        elapsed = time.monotonic() - started
        status = {
            "target": args.target,
            "local_modules": len(order),
            "external_imports": len(external_missing),
            "built": built,
            "skipped": skipped,
            "failed_module": failed_module,
            "exit_code": exit_code,
            "elapsed_seconds": elapsed,
        }
        Path(args.status_file).write_text(json.dumps(status, indent=2) + "\n")
        print("[status] " + json.dumps(status, sort_keys=True), flush=True)

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
