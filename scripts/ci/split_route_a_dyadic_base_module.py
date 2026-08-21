#!/usr/bin/env python3
"""Split one generated Route A dyadic base Lean module into small modules.

The generated dyadic base files can become too large for CI as one `.olean`.
This script factors a file such as

  Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveDyadicBase077.lean

into the same shape used for Base042:

  Base077Pair195390Common
  Base077Pair195390Row001Term001
  Base077Pair195390Row001
  Base077Pair195390
  Base077

It is intentionally conservative: it only recognizes the declaration naming
scheme emitted by the existing Route A generator.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


NAMESPACE = "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage"
MODULE_PREFIX = "Goldbach.Cert.MajorArcModules"
BASE_IMPORT = (
    "Goldbach.Cert.MajorArcModules."
    "Q0MinorZeroModeNormalizedAverageX0PeriodicMain"
)
PAIR_RE = re.compile(r"^(periodicMainPair_(\d+)_(\d+)_X(\d+))_")
DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+([A-Za-z0-9_']+)\b"
)
STEM_RE = re.compile(
    r"^(Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveDyadicBase)(\d{3})$"
)


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


def parse_decls(path: Path) -> list[Decl]:
    lines = path.read_text().splitlines(keepends=True)
    decl_starts: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            decl_starts.append((idx, match.group(1)))
    if not decl_starts:
        raise SystemExit(f"{path}: no top-level declarations found")

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
        text = "".join(lines[start:end]).rstrip() + "\n"
        decls.append(Decl(name=name, text=text))
    return decls


def theorem_rhs(decl: Decl) -> str:
    marker = " := by"
    if marker not in decl.text:
        raise SystemExit(f"{decl.name}: declaration is not a theorem proof")
    theorem_part = decl.text.split(marker, 1)[0]
    if " = " not in theorem_part:
        raise SystemExit(f"{decl.name}: theorem does not expose an equality")
    return theorem_part.rsplit(" = ", 1)[1].strip()


def list_to_finset(values: list[int]) -> str:
    return "([" + ", ".join(str(value) for value in values) + "] : List ℕ).toFinset"


def rcases_pattern(count: int) -> str:
    if count <= 0:
        raise ValueError("empty rcases pattern")
    return " | ".join("rfl" for _ in range(count))


def row_term_expr(*, q: int, q2: int, g: int, h_expr: str, h_set: str) -> str:
    return f"""(∑ h ∈ {h_set},
      ramanujanGcdClassCoeffRat {q} {g} * ramanujanGcdClassCoeffRat {q2} {h_expr}
        * ((((H + 1) / centeredRamanujanPairBlockPeriod {q} {q2}) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h_expr}
                - ramanujanGcdClassWindowAverageRat X0 {q2} {h_expr}
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} {g}
                - ramanujanGcdClassWindowAverageRat X0 {q} {g}
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} {h_expr}
                + ramanujanGcdClassWindowAverageRat X0 {q} {g}
                    * ramanujanGcdClassWindowAverageRat X0 {q2} {h_expr}
                    * evenRamanujanBlockCountRat {q} {q2}))
    )"""


def nested_pair_expr(*, q: int, q2: int) -> str:
    return f"""(∑ g ∈ Nat.divisors {q}, ∑ h ∈ Nat.divisors {q2},
        ramanujanGcdClassCoeffRat {q} g * ramanujanGcdClassCoeffRat {q2} h
          * ((((H + 1) / centeredRamanujanPairBlockPeriod {q} {q2}) : ℕ)
              • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} g h
                  - ramanujanGcdClassWindowAverageRat X0 {q2} h
                      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} g
                  - ramanujanGcdClassWindowAverageRat X0 {q} g
                      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} h
                  + ramanujanGcdClassWindowAverageRat X0 {q} g
                      * ramanujanGcdClassWindowAverageRat X0 {q2} h
                      * evenRamanujanBlockCountRat {q} {q2}))
      )"""


def row_value_decl(prefix: str, g: int, h_values: list[int], values_by_h: dict[int, str]) -> str:
    lines = [f"def {prefix}_rowValue_{g} : ℕ → ℚ"]
    for h in h_values:
        lines.append(f"| {h} => {values_by_h[h]}")
    lines.append("| _ => 0")
    return "\n".join(lines) + "\n"


def row_theorem_decl(prefix: str, q: int, q2: int, g: int, h_values: list[int], row_value: str) -> str:
    right_set = list_to_finset(h_values)
    body = [
        f"theorem {prefix}_row_{g} :",
        f"    {row_term_expr(q=q, q2=q2, g=g, h_expr='h', h_set=f'Nat.divisors {q2}')} = {row_value} := by",
        f"  rw [{prefix}_divRight]",
        "  have hsum :",
        f"      {row_term_expr(q=q, q2=q2, g=g, h_expr='h', h_set=right_set)} = (∑ h ∈ {right_set}, {prefix}_rowValue_{g} h) := by",
        "    apply Finset.sum_congr rfl",
        "    intro h hh",
        "    simp at hh",
        f"    rcases hh with {rcases_pattern(len(h_values))}",
    ]
    for h in h_values:
        body.append(f"    · simpa [{prefix}_rowValue_{g}] using {prefix}_term_{g}_{h}")
    body.extend(["  rw [hsum]", "  native_decide"])
    return "\n".join(body) + "\n"


def pair_row_value_decl(prefix: str, row_values: dict[int, str]) -> str:
    lines = [f"def {prefix}_rowValue : ℕ → ℚ"]
    for g in sorted(row_values):
        lines.append(f"| {g} => {row_values[g]}")
    lines.append("| _ => 0")
    return "\n".join(lines) + "\n"


def centered_theorem_decl(prefix: str, q: int, q2: int, row_values: dict[int, str], centered_value: str) -> str:
    g_values = sorted(row_values)
    body = [
        f"theorem {prefix}_centeredTerm :",
        f"    centeredRamanujanPairPeriodicMainTermRat X0 {q} {q2} = {centered_value} := by",
        "  unfold centeredRamanujanPairPeriodicMainTermRat",
        "  have hsum :",
        f"      {nested_pair_expr(q=q, q2=q2)} = (∑ g ∈ Nat.divisors {q}, {prefix}_rowValue g) := by",
        "    apply Finset.sum_congr rfl",
        "    intro g hg",
        f"    rw [{prefix}_divLeft] at hg",
        "    simp at hg",
        f"    rcases hg with {rcases_pattern(len(g_values))}",
    ]
    for g in g_values:
        body.append(f"    · simpa [{prefix}_rowValue] using {prefix}_row_{g}")
    body.extend([f"  rw [hsum, {prefix}_divLeft]", "  native_decide"])
    return "\n".join(body) + "\n"


def write_module(out_dir: Path, stem: str, suffix: str, imports: list[str], body: str, comment: str | None = None) -> Path:
    path = out_dir / f"{stem}{suffix}.lean"
    path.write_text(module_header(imports, comment) + body.rstrip() + module_footer())
    return path


def split_module(path: Path, out_dir: Path) -> list[Path]:
    stem = path.stem
    stem_match = STEM_RE.match(stem)
    if not stem_match:
        raise SystemExit(f"{path}: unexpected dyadic base module stem")
    base_index = stem_match.group(2)
    decls = parse_decls(path)
    decl_by_name = {decl.name: decl for decl in decls}

    pair_order: list[tuple[str, int, int, int]] = []
    seen_pairs: set[str] = set()
    for decl in decls:
        match = PAIR_RE.match(decl.name)
        if not match:
            continue
        prefix, q_raw, q2_raw, x_raw = match.groups()
        if prefix in seen_pairs:
            continue
        seen_pairs.add(prefix)
        pair_order.append((prefix, int(q_raw), int(q2_raw), int(x_raw)))
    if not pair_order:
        raise SystemExit(f"{path}: no periodicMainPair declarations found")

    written: list[Path] = []
    pair_suffixes: list[str] = []
    for prefix, q, q2, x in pair_order:
        pair_suffix = f"Pair{q}{q2}"
        pair_suffixes.append(pair_suffix)
        common_suffix = f"{pair_suffix}Common"
        common_import = f"{MODULE_PREFIX}.{stem}{common_suffix}"

        term_names: dict[int, list[int]] = {}
        row_names: list[int] = []
        common_decls: list[Decl] = []
        pair_decls: list[Decl] = []
        for decl in decls:
            if not decl.name.startswith(prefix + "_"):
                continue
            tail = decl.name.removeprefix(prefix + "_")
            term_match = re.fullmatch(r"term_(\d+)_(\d+)", tail)
            row_match = re.fullmatch(r"row_(\d+)", tail)
            row_value_match = re.fullmatch(r"rowValue_(\d+)", tail)
            if term_match:
                g = int(term_match.group(1))
                h = int(term_match.group(2))
                term_names.setdefault(g, []).append(h)
            elif row_match:
                row_names.append(int(row_match.group(1)))
            elif row_value_match:
                pass
            elif tail in {"rowValue", "centeredTerm", "orderedSummand"}:
                pair_decls.append(decl)
            else:
                common_decls.append(decl)

        written.append(
            write_module(
                out_dir,
                stem,
                common_suffix,
                [BASE_IMPORT],
                "\n".join(decl.text for decl in common_decls),
                f"/- Common facts for {prefix}. -/",
            )
        )

        row_names = sorted(set(row_names))
        row_values: dict[int, str] = {}
        for g in row_names:
            h_values = sorted(set(term_names.get(g, [])))
            if not h_values:
                raise SystemExit(f"{path}: row {g} for {prefix} has no terms")
            term_imports: list[str] = []
            term_values: dict[int, str] = {}
            for h in h_values:
                term_suffix = f"{pair_suffix}Row{g:03d}Term{h:03d}"
                term_name = f"{prefix}_term_{g}_{h}"
                term_decl = decl_by_name.get(term_name)
                if term_decl is None:
                    raise SystemExit(f"{path}: missing {term_name}")
                term_values[h] = theorem_rhs(term_decl)
                written.append(
                    write_module(
                        out_dir,
                        stem,
                        term_suffix,
                        [common_import],
                        term_decl.text,
                        f"/- Term ({g},{h}) for {prefix}. -/",
                    )
                )
                term_imports.append(f"{MODULE_PREFIX}.{stem}{term_suffix}")

            row_body_parts: list[str] = []
            row_decl = decl_by_name.get(f"{prefix}_row_{g}")
            if row_decl is None:
                raise SystemExit(f"{path}: missing row declaration for {prefix}, row {g}")
            row_values[g] = theorem_rhs(row_decl)
            row_body_parts.extend(
                [
                    row_value_decl(prefix, g, h_values, term_values),
                    row_theorem_decl(prefix, q, q2, g, h_values, row_values[g]),
                ]
            )
            row_suffix = f"{pair_suffix}Row{g:03d}"
            written.append(
                write_module(
                    out_dir,
                    stem,
                    row_suffix,
                    term_imports,
                    "\n".join(row_body_parts),
                    f"/- Row {g} wrapper for {prefix}. -/",
                )
            )

        pair_imports = [
            f"{MODULE_PREFIX}.{stem}{pair_suffix}Row{g:03d}" for g in row_names
        ]
        pair_body: list[str] = []
        centered_decl = decl_by_name.get(f"{prefix}_centeredTerm")
        ordered_decl = decl_by_name.get(f"{prefix}_orderedSummand")
        if centered_decl is None or ordered_decl is None:
            raise SystemExit(f"{path}: missing pair wrapper declarations for {prefix}")
        pair_body.append(pair_row_value_decl(prefix, row_values))
        pair_body.append(centered_theorem_decl(prefix, q, q2, row_values, theorem_rhs(centered_decl)))
        pair_body.append(ordered_decl.text)
        written.append(
            write_module(
                out_dir,
                stem,
                pair_suffix,
                pair_imports,
                "\n".join(pair_body),
                f"/- Wrapper for row-split proof of {prefix}. -/",
            )
        )

    record_decls = [decl for decl in decls if decl.name.startswith("PeriodicMainRecords")]
    if not record_decls:
        raise SystemExit(f"{path}: no PeriodicMainRecords declarations found")
    wrapper_imports = [f"{MODULE_PREFIX}.{stem}{suffix}" for suffix in pair_suffixes]
    wrapper_body = "\n".join(decl.text for decl in record_decls)
    path.write_text(
        module_header(
            wrapper_imports,
            f"/- Wrapper for dyadic base-pair proofs for base index {int(base_index)}. -/",
        )
        + wrapper_body.rstrip()
        + module_footer()
    )
    written.append(path)
    return written


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("module", type=Path)
    parser.add_argument("--out-dir", type=Path, default=None)
    args = parser.parse_args()
    path = args.module
    out_dir = args.out_dir or path.parent
    written = split_module(path, out_dir)
    for written_path in written:
        print(written_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
