#!/usr/bin/env python3
import json, sys, pathlib

# ---------- helpers ----------
def is_int_like(x):
    try:
        int(x)
        return True
    except:
        return False

def pick_key(d, candidates):
    # return first present key (case-insensitive)
    lower = {k.lower(): k for k in d.keys()}
    for c in candidates:
        if c.lower() in lower:
            return lower[c.lower()]
    return None

def normalize_rows(obj):
    """
    Yield (N, p, q) as ints from a few common JSON layouts:
    - [{ "N": 10, "p": 3, "q": 7 }, ...]
    - [{ "n": 10, "P": 3, "Q": 7 }, ...]
    - { "10": {"p": 3, "q": 7}, "12": [5,7], ... }
    - [[10,3,7], [12,5,7], ...]
    """
    if isinstance(obj, list):
        if not obj:
            return
        # list of dicts?
        if isinstance(obj[0], dict):
            for r in obj:
                Nk = pick_key(r, ["N","n","num","even","sum"])
                pk = pick_key(r, ["p","P"])
                qk = pick_key(r, ["q","Q"])
                if Nk is None or pk is None or qk is None:
                    # skip rows we can't parse
                    continue
                N = int(r[Nk]); p = int(r[pk]); q = int(r[qk])
                yield (N, p, q)
        # list of lists like [N,p,q]
        elif isinstance(obj[0], (list, tuple)) and len(obj[0]) >= 3:
            for r in obj:
                N, p, q = r[0], r[1], r[2]
                yield (int(N), int(p), int(q))
        else:
            # unknown list shape
            return
    elif isinstance(obj, dict):
        # dict keyed by N
        for k, v in obj.items():
            if not is_int_like(k):
                continue
            N = int(k)
            if isinstance(v, dict):
                pk = pick_key(v, ["p","P"])
                qk = pick_key(v, ["q","Q"])
                if pk is None or qk is None:
                    continue
                p = int(v[pk]); q = int(v[qk])
                yield (N, p, q)
            elif isinstance(v, (list, tuple)) and len(v) >= 2:
                p = int(v[0]); q = int(v[1])
                yield (N, p, q)
            else:
                continue
    else:
        return

def emit_row(N, p, q):
    nm = f"row_{N:06d}"
    return f"""
theorem {nm} : Goldbach.Base.GoldbachRep {N} := by
  have hp : Nat.Prime {p} := by decide
  have hq : Nat.Prime {q} := by decide
  have hs : {p} + {q} = {N} := by decide
  exact ⟨{p}, {q}, hp, hq, hs⟩
""".rstrip()

def emit_chunk_range(lo, hi, evens):
    # A smaller range dispatcher; we’ll stitch several of these together if needed
    arms = "\n".join([f"| {N}, _, _, _ => row_{N:06d}"
                      for N in evens if lo <= N <= hi and N % 2 == 0])
    return f"""
theorem rep_in_{lo:06d}_{hi:06d} :
  ∀ {{N : Nat}}, Even N → {lo} ≤ N → N ≤ {hi} → Goldbach.Base.GoldbachRep N
{arms if arms.strip() else "| _, _, _, _ => False.elim (by cases rfl)"} -- placeholder if empty
""".strip()

def emit_top_range(chunks):
    # chunks = [(lo,hi), ...]
    # we dispatch to the right chunk by bounds
    lines = []
    for (lo, hi) in chunks:
        lines.append(f"  have h_{lo}_{hi} : N ≤ {hi} ∨ {hi} < N := le_or_gt N {hi}")
        lines.append(f"  cases h_{lo}_{hi} with")
        lines.append(f"  | inl hNle => exact rep_in_{lo:06d}_{hi:06d} hEven (by exact hLo) hNle")
        lines.append(f"  | inr hNgt =>")
        lines.append(f"    have hLo' : {hi+2} ≤ N := by exact Nat.succ_le_of_lt (Nat.succ_lt_of_lt hNgt)")
    # The above is illustrative; top splitter is optional if you keep a single chunk.

    return "\n".join(lines)

# ---------- main ----------
def main():
    if len(sys.argv) != 3:
        print("usage: python3 scripts/make_generated_proofs.py witness.json Goldbach/FiniteBase/Generated_real_Proofs.lean")
        sys.exit(1)
    src = pathlib.Path(sys.argv[1])
    out = pathlib.Path(sys.argv[2])

    obj = json.loads(src.read_text())
    triples = list(normalize_rows(obj))
    if not triples:
        print("Could not parse any (N,p,q) triples from JSON. Please show me a snippet of the JSON.")
        sys.exit(2)

    # keep only even N in [4..100000]
    triples = [(N,p,q) for (N,p,q) in triples if (N % 2 == 0 and 4 <= N <= 100000)]
    triples.sort()

    header = """import Mathlib
import Goldbach.Base.FiniteBaseDefs

namespace Goldbach.FiniteBase.Generated_000004_100000
"""
    body = []
    for (N,p,q) in triples:
        body.append(emit_row(N,p,q))

    # One dispatcher for the whole range 4..100000 (about 50k arms).
    # If this feels heavy on your machine, we can split into, say, five sub-ranges.
    evens = [N for (N,_,_) in triples]
    arms = "\n".join([f"| {N}, _, _, _ => row_{N:06d}" for N in evens])

    rep_all = f"""
/-- For 4 ≤ N ≤ 100000 (even), pick the right row. -/
theorem rep_in_range :
  ∀ {{N : Nat}}, Even N → 4 ≤ N → N ≤ 100000 → Goldbach.Base.GoldbachRep N
{arms}
""".strip()

    footer = "\nend Goldbach.FiniteBase.Generated_000004_100000\n"
    out.write_text(header + "\n\n".join(body) + "\n\n" + rep_all + "\n" + footer)

if __name__ == "__main__":
    main()
