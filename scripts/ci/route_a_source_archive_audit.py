#!/usr/bin/env python3
"""Audit generated-source archive coverage for a Route A Lean target.

The Route A CI workflow restores many ignored generated `.lean` sources from
checked-in tarballs.  A target can therefore pass locally but fail in GitHub if
one ignored transitive import was not included in the source archive.  This
script catches that before the expensive compile starts.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tarfile
from pathlib import Path

from route_a_direct_olean_build import module_to_source


def read_lines(paths: list[Path]) -> set[str]:
    entries: set[str] = set()
    for path in paths:
        if not path.exists():
            continue
        for line in path.read_text(errors="ignore").splitlines():
            stripped = line.strip()
            if stripped:
                entries.add(stripped)
    return entries


def read_archive_names(paths: list[Path]) -> set[str]:
    names: set[str] = set()
    for path in paths:
        if not path.exists():
            continue
        with tarfile.open(path, "r:gz") as archive:
            names.update(name for name in archive.getnames() if name)
    return names


def git_tracked_files(root: Path) -> set[str]:
    proc = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
    )
    return {item.decode() for item in proc.stdout.split(b"\0") if item}


def _consume_block_comment_markers(line: str, depth: int) -> int:
    i = 0
    while i < len(line):
        if line.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and line.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        i += 1
    return depth


def parse_header_imports(source: Path) -> list[str]:
    """Parse top-level Lean imports without scanning generated proof bodies."""
    imports: list[str] = []
    block_depth = 0
    with source.open("r", errors="ignore") as handle:
        for raw_line in handle:
            line = raw_line.strip()
            if block_depth > 0:
                block_depth = _consume_block_comment_markers(line, block_depth)
                continue
            if not line or line.startswith("--"):
                continue
            if line.startswith("/-"):
                block_depth = _consume_block_comment_markers(line, block_depth)
                continue
            if line.startswith("import "):
                imported = line.split(None, 1)[1].split("--", 1)[0].strip()
                if imported:
                    imports.append(imported)
                continue
            # Lean imports must be in the file header.  Once code starts, stop.
            break
    return imports


def local_closure_fast(
    root: Path,
    target: str,
    *,
    progress_every: int,
) -> tuple[list[str], list[str], dict[str, list[str]]]:
    order: list[str] = []
    missing: list[str] = []
    imports_by_module: dict[str, list[str]] = {}
    state: dict[str, int] = {}
    stack: list[str] = []
    parsed = 0

    def visit(module: str) -> None:
        nonlocal parsed
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
        imports = parse_header_imports(source)
        parsed += 1
        if progress_every > 0 and parsed % progress_every == 0:
            print(
                f"[source-archive-audit:scan] parsed={parsed} "
                f"module={module}",
                flush=True,
            )
        imports_by_module[module] = imports
        for imported in imports:
            visit(imported)
        stack.pop()
        state[module] = 2
        order.append(module)

    visit(target)
    return order, missing, imports_by_module


def module_source_relpath(root: Path, module: str) -> str:
    return module_to_source(root, module).relative_to(root).as_posix()


def is_project_module(module: str, prefixes: list[str]) -> bool:
    return any(module == prefix.rstrip(".") or module.startswith(prefix) for prefix in prefixes)


def sample(items: list[str], limit: int) -> list[str]:
    return items[:limit]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path("."))
    ap.add_argument("--target", required=True, help="Lean module name, not a file path.")
    ap.add_argument("--manifest", nargs="*", type=Path, default=[])
    ap.add_argument("--archive", nargs="*", type=Path, default=[])
    ap.add_argument("--project-prefix", nargs="*", default=["Goldbach."])
    ap.add_argument("--json-output", type=Path, default=Path("route-a-source-archive-audit.json"))
    ap.add_argument("--sample-limit", type=int, default=20)
    ap.add_argument("--progress-every", type=int, default=5000)
    args = ap.parse_args()

    root = args.root.resolve()
    manifests = [path if path.is_absolute() else root / path for path in args.manifest]
    archives = [path if path.is_absolute() else root / path for path in args.archive]

    order, missing, _imports_by_module = local_closure_fast(
        root,
        args.target,
        progress_every=args.progress_every,
    )
    tracked = git_tracked_files(root)
    manifest_entries = read_lines(manifests)
    archive_entries = read_archive_names(archives)

    project_missing = sorted(
        module for module in missing if is_project_module(module, args.project_prefix)
    )
    external_imports = sorted(
        module for module in missing if not is_project_module(module, args.project_prefix)
    )

    local_source_paths = sorted(module_source_relpath(root, module) for module in order)
    untracked_required_sources = sorted(
        path for path in local_source_paths if path not in tracked
    )
    untracked_missing_manifest = sorted(
        path for path in untracked_required_sources if path not in manifest_entries
    )
    untracked_missing_archive = sorted(
        path for path in untracked_required_sources if path not in archive_entries
    )
    manifest_missing_on_disk = sorted(
        path for path in manifest_entries if not (root / path).exists()
    )
    manifest_missing_archive = sorted(
        path for path in manifest_entries if path not in archive_entries
    )

    diagnostics = {
        "missing_project_sources": project_missing,
        "required_untracked_missing_manifest": untracked_missing_manifest,
        "required_untracked_missing_archive": untracked_missing_archive,
        "manifest_entries_missing_on_disk": manifest_missing_on_disk,
        "manifest_entries_missing_archive": manifest_missing_archive,
    }
    failures = {
        "missing_project_sources": project_missing,
        "required_untracked_missing_archive": untracked_missing_archive,
    }
    ok = all(len(items) == 0 for items in failures.values())

    report = {
        "ok": ok,
        "target": args.target,
        "local_modules": len(order),
        "external_imports": len(external_imports),
        "tracked_sources": len(tracked),
        "manifest_entries": len(manifest_entries),
        "archive_entries": len(archive_entries),
        "required_untracked_sources": len(untracked_required_sources),
        "missing_project_sources": len(project_missing),
        "required_untracked_missing_manifest": len(untracked_missing_manifest),
        "required_untracked_missing_archive": len(untracked_missing_archive),
        "manifest_entries_missing_on_disk": len(manifest_missing_on_disk),
        "manifest_entries_missing_archive": len(manifest_missing_archive),
        "samples": {
            key: sample(value, args.sample_limit)
            for key, value in diagnostics.items()
        },
    }

    args.json_output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    print(
        "[source-archive-audit] "
        f"target={args.target} "
        f"local_modules={len(order)} "
        f"external_imports={len(external_imports)} "
        f"required_untracked_sources={len(untracked_required_sources)} "
        f"manifest_entries={len(manifest_entries)} "
        f"archive_entries={len(archive_entries)} "
        f"ok={str(ok).lower()}",
        flush=True,
    )
    if not ok:
        for key, values in failures.items():
            if not values:
                continue
            print(f"[source-archive-audit:{key}] count={len(values)}", flush=True)
            for value in sample(values, args.sample_limit):
                print(value, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
