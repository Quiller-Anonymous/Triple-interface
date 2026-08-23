#!/usr/bin/env python3
"""Split an already-generated Route A dyadic `Common` module into chunks.

`split_route_a_dyadic_base_module.py` now emits common fact chunks directly for
fresh monolithic inputs. This helper handles modules that were already split
before that extra layer existed, for example:

  ...DyadicBase467Pair11552310Common.lean

It rewrites that module into a thin importer and moves its declarations into:

  ...DyadicBase467Pair11552310CommonPart000.lean
  ...DyadicBase467Pair11552310CommonPart001.lean
  ...
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


NAMESPACE = "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage"
MODULE_PREFIX = "Goldbach.Cert.MajorArcModules"
DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+([A-Za-z0-9_']+)\b"
)
DEFAULT_CHUNK_SIZE = 64


@dataclass(frozen=True)
class Decl:
    name: str
    text: str


def module_header(imports: list[str], comment: str | None = None) -> str:
    lines: list[str] = []
    for module in imports:
        lines.append(f"import {module}")
    lines.extend(
        [
            "",
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
        ]
    )
    if comment:
        lines.extend([comment, ""])
    return "\n".join(lines)


def module_footer() -> str:
    return f"\nend {NAMESPACE}\n"


def parse_imports(lines: list[str]) -> list[str]:
    imports: list[str] = []
    for line in lines:
        if line.startswith("import "):
            imports.append(line.removeprefix("import ").strip())
    if not imports:
        raise SystemExit("common module has no imports")
    return imports


def parse_decls(path: Path) -> list[Decl]:
    lines = path.read_text().splitlines(keepends=True)
    decl_starts: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            decl_starts.append((idx, match.group(1)))
    if not decl_starts:
        return []

    footer_idx = None
    for idx in range(len(lines) - 1, -1, -1):
        if lines[idx].startswith(f"end {NAMESPACE}"):
            footer_idx = idx
            break
    if footer_idx is None:
        raise SystemExit(f"{path}: missing namespace footer")

    decls: list[Decl] = []
    for pos, (start, name) in enumerate(decl_starts):
        end = decl_starts[pos + 1][0] if pos + 1 < len(decl_starts) else footer_idx
        decls.append(Decl(name=name, text="".join(lines[start:end]).rstrip() + "\n"))
    return decls


def chunks(values: list[Decl], size: int) -> list[list[Decl]]:
    return [values[idx : idx + size] for idx in range(0, len(values), size)]


def module_name_for(path: Path) -> str:
    return f"{MODULE_PREFIX}.{path.stem}"


def write_module(path: Path, imports: list[str], body: str, comment: str | None) -> None:
    path.write_text(module_header(imports, comment) + body.rstrip() + module_footer())


def split_common(path: Path, chunk_size: int) -> list[Path]:
    if not path.name.endswith("Common.lean"):
        raise SystemExit(f"{path}: expected a Common.lean file")

    lines = path.read_text().splitlines()
    imports = parse_imports(lines)
    decls = parse_decls(path)
    if not decls:
        return []

    written: list[Path] = []
    common_imports: list[str] = []
    for idx, chunk_decls in enumerate(chunks(decls, chunk_size)):
        part_path = path.with_name(f"{path.stem}Part{idx:03d}.lean")
        write_module(
            part_path,
            imports,
            "\n".join(decl.text for decl in chunk_decls),
            f"/- Common fact chunk {idx} for {path.stem}. -/",
        )
        written.append(part_path)
        common_imports.append(module_name_for(part_path))

    write_module(
        path,
        common_imports,
        "",
        f"/- Common fact imports for {path.stem}. -/",
    )
    written.append(path)
    return written


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("modules", nargs="+", type=Path)
    parser.add_argument("--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE)
    args = parser.parse_args()

    for module in args.modules:
        for path in split_common(module, args.chunk_size):
            print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
