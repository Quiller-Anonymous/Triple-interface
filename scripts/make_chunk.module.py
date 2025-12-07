# save as scripts/make_chunk.module.py and run:
#   python3 scripts/make_chunk.module.py \
#     Goldbach/Base/data/chunk_100002_200000.csv \
#     Goldbach/FiniteBase/Generated_100002_200000.lean

# scripts/make_this_chunk.py
from pathlib import Path
import sys, runpy



sys.argv = [sys.argv[0], str(CSV), str(OUT)]
# Only set sys.argv and recursively invoke if not already running with arguments
if len(sys.argv) < 3:
    sys.argv = [sys.argv[0], str(CSV), str(OUT)]
    runpy.run_path("scripts/make_chunk.module.py", run_name="__main__")
    sys.exit(0)

csv_path = pathlib.Path(sys.argv[1])
out_path = pathlib.Path(sys.argv[2])

lo, hi = csv_path.stem.replace("chunk_", "").split("_")
ns = f"Goldbach.FiniteBase.Generated_{lo}_{hi}"

rows = []
with csv_path.open() as f:
    for N,p,q in csv.reader(f):
        N = N.strip(); p = p.strip(); q = q.strip()
        if not N or N.startswith("#"): continue
        rows.append((N,p,q))

code = []
code.append(f"/- AUTO-GENERATED from {csv_path} -/")
code.append("import Std.Data.HashMap\n")
code.append(f"namespace {ns}\n")
code.append("open Std\n")
code.append("/-- Raw rows for this chunk, as (N, p, q). -/")
code.append("def rows : List (Nat × Nat × Nat) :=\n  [")
for (N,p,q) in rows:
    code.append(f"    ({N}, {p}, {q}),")
if rows:
    code[-1] = code[-1].rstrip(",")  # drop trailing comma
code.append("  ]\n")
code.append("/-- Hash map from N ↦ (p,q) for this chunk. -/")
code.append("def table : Std.HashMap Nat (Nat × Nat) := Id.run do")
code.append("  let mut m : Std.HashMap Nat (Nat × Nat) := {}")
code.append("  for (n,p,q) in rows do")
code.append("    m := m.insert n (p,q)")
code.append("  return m\n")
code.append("/-- Convenience: does this chunk contain a certificate for N? -/")
code.append("@[inline] def has (N : Nat) : Bool := (table.get? N).isSome\n")
code.append("/-- Optional quick check that p+q = N for all rows (computational). -/")
code.append("def selfCheckSumOk : Bool := rows.all (fun (n,p,q) => n == p + q)\n")
code.append("end " + ns + "\n")

out_path.parent.mkdir(parents=True, exist_ok=True)
out_path.write_text("\n".join(code))
print(f"Wrote {out_path}")
