#!/usr/bin/env python3
import re, sys, pathlib

src = pathlib.Path(sys.argv[1])
dst = pathlib.Path(sys.argv[2])

rows = []
for line in src.read_text().splitlines():
    m = re.search(r'm\s*:=\s*m\.insert\s*(\d+)\s*\(\s*(\d+)\s*,\s*(\d+)\s*\)', line)
    if m:
        N, p, q = m.group(1), m.group(2), m.group(3)
        rows.append(f"  ({N}, ({p}, {q})),")
# Write minimal chunk with array+fold
dst.write_text(f"""import Std
open Std
namespace Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_02
set_option maxHeartbeats 200000000
set_option maxRecDepth   200000
def rows : Array (Nat × (Nat × Nat)) := #[
{chr(10).join(rows)}
]
@[inline] private def build (xs : Array (Nat × (Nat × Nat)))
    : HashMap Nat (Nat × Nat) :=
  xs.foldl (init := {{}}) (fun m (k, v) => m.insert k v)
def table01 : HashMap Nat (Nat × Nat) := build rows
end Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_01
""")
print(f"wrote {dst}")
