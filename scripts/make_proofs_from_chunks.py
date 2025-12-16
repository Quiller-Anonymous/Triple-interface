#!/usr/bin/env python3
import re, sys, pathlib
from typing import List, Tuple

USAGE = f"""\
Usage:
  python3 {sys.argv[0]} <chunks_dir> <out_dir>

Where:
  <chunks_dir>   = Goldbach/FiniteBase/Chunks
  <out_dir>      = Goldbach/FiniteBase/ProofChunks
"""

# Regex to capture rows of the shape: (N, (p, q))
ROW_RE = re.compile(r"\(\s*(\d+)\s*,\s*\(\s*(\d+)\s*,\s*(\d+)\s*\)\s*\)")

HEADER = """\
/-
  Auto-generated from chunk rows.
  For each even N in this chunk we emit:

    theorem rep_<N> : Goldbach.Base.GoldbachRep N
      := ⟨p, q, by decide, by decide, by decide⟩

  Notes:
  - We rely on computation (`by decide`) to verify primality and p+q = N.
  - Keep these files small-ish and parallelizable.
-/

import Mathlib
import Goldbach.Base.FiniteBaseDefs

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
-- set_option diagnostics true

open Goldbach.Base

namespace Goldbach.FiniteBase.Proofs
"""

FOOTER = """
end Goldbach.FiniteBase.Proofs
"""

def extract_rows(text: str) -> List[Tuple[int,int,int]]:
    # Find all triples (N, p, q)
    triples = []
    for m in ROW_RE.finditer(text):
        N = int(m.group(1))
        p = int(m.group(2))
        q = int(m.group(3))
        if N >= 4 and N % 2 == 0:
            triples.append((N,p,q))
    # Deduplicate just in case and sort by N
    triples = sorted(set(triples), key=lambda t: t[0])
    return triples

def write_proof_file(out_dir: pathlib.Path, chunk_path: pathlib.Path, rows: List[Tuple[int,int,int]]):
    # Derive a stable module-ish suffix from the chunk filename
    base = chunk_path.stem  # e.g. "Generated_000004_100000_Part_01A"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"Rep_{base}.lean"

    with out_path.open("w") as f:
        f.write(HEADER)
        for (N, p, q) in rows:
            f.write(f"""
/-- Auto-generated: Goldbach representation for N = {N} as {p} + {q}. -/
theorem rep_{N:06d} : GoldbachRep {N} := by
  exact ⟨{p}, {q}, by decide, by decide, by decide⟩
""")
        f.write(FOOTER)
    print(f"[write] {out_path}")

def main():
    if len(sys.argv) < 3:
        print(USAGE, file=sys.stderr)
        sys.exit(2)

    chunks_dir = pathlib.Path(sys.argv[1])
    out_dir    = pathlib.Path(sys.argv[2])

    if not chunks_dir.is_dir():
        print(f"Chunks dir not found: {chunks_dir}", file=sys.stderr)
        sys.exit(1)

    chunk_files = sorted(chunks_dir.glob("Generated_000004_100000_Part_*.lean"))
    if not chunk_files:
        print(f"No chunk files found in {chunks_dir}", file=sys.stderr)
        sys.exit(1)

    for cf in chunk_files:
        text = cf.read_text()
        rows = extract_rows(text)
        if not rows:
            print(f"[warn] No rows parsed in {cf.name} (skipping)")
            continue
        write_proof_file(out_dir, cf, rows)

    # Optionally write an "All.lean" that imports everything we just created
    all_file = out_dir / "All.lean"
    with all_file.open("w") as f:
        f.write("-- Auto-generated imports of all proof chunks\n")
        for cf in chunk_files:
            base = cf.stem
            f.write(f"import Goldbach.FiniteBase.ProofChunks.Rep_{base}\n")
    print(f"[write] {all_file}")

if __name__ == "__main__":
    main()
