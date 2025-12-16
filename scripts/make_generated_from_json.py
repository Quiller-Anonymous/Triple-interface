#!/usr/bin/env python3
# scripts/make_generated_from_json.py
import json, sys, pathlib

# Usage:
#   python3 scripts/make_generated_from_json.py \
#     Tools/data/witness_1e6.json \
#     Goldbach/FiniteBase/Generated_000004_100000.lean \
#     100000

def norm_int(x):
    if isinstance(x, bool):  # avoid True/False mis-parsing
        raise ValueError("bool where int expected")
    if isinstance(x, (int,)):
        return x
    if isinstance(x, str) and x.strip().isdigit():
        return int(x)
    return int(x)

def iter_rows(obj):
    """
    Yields triples (N, p, q). Handles these shapes:

    1) [{ "N": 10, "p": 3, "q": 7 }, ...]
    2) [{ "n": 10, "p1": 3, "p2": 7 }, ...]
    3) { "10": [3,7], "12": [5,7], ... }
    4) { "10": {"p":3, "q":7}, ... }
    5) [[10,3,7], [12,5,7], ...]
    """
    # Helper to try dict row with unknown key names
    def dict_to_tuple(d):
        if not isinstance(d, dict): 
            return None
        keys = {k.lower(): k for k in d.keys()}
        # candidates for field names
        Nkey  = next((keys[k] for k in ("n","N","num","even","x") if k in keys), None)
        pkey  = next((keys[k] for k in ("p","p1","prime1","a","left") if k in keys), None)
        qkey  = next((keys[k] for k in ("q","p2","prime2","b","right") if k in keys), None)
        if Nkey and pkey and qkey:
            return (norm_int(d[Nkey]), norm_int(d[pkey]), norm_int(d[qkey]))
        # also accept {"p":..,"q":..} with N implied by sum (rare)
        if pkey and qkey and not Nkey:
            p, q = norm_int(d[pkey]), norm_int(d[qkey])
            return (p+q, p, q)
        return None

    # Case: top-level list
    if isinstance(obj, list):
        for row in obj:
            # list of lists/tuples?
            if isinstance(row, (list, tuple)) and len(row) >= 3:
                N, p, q = map(norm_int, row[:3])
                yield (N, p, q)
                continue
            # list of dicts?
            triple = dict_to_tuple(row)
            if triple is not None:
                yield triple
                continue
        return

    # Case: top-level dict
    if isinstance(obj, dict):
        for k, v in obj.items():
            try:
                N = norm_int(k)
            except Exception:
                # maybe k is not N, try dict-of-dicts with N inside
                triple = dict_to_tuple(v)
                if triple is not None:
                    yield triple
                continue

            # values: [p,q] or {"p":..., "q":...}
            if isinstance(v, (list, tuple)) and len(v) >= 2:
                p, q = map(norm_int, v[:2])
                yield (N, p, q)
            elif isinstance(v, dict):
                triple = dict_to_tuple(v)
                if triple is not None:
                    # prefer explicit N (k) over inferred N from p+q
                    _, p, q = triple
                    yield (N, p, q)
            else:
                continue
        return

    raise ValueError("Unsupported JSON structure at top level")

def main():
    if len(sys.argv) != 4:
        print("usage: make_generated_from_json.py <in.json> <out.lean> <limit_N>", file=sys.stderr)
        sys.exit(2)

    src = pathlib.Path(sys.argv[1])
    dst = pathlib.Path(sys.argv[2])
    limit = int(sys.argv[3])

    data = json.loads(src.read_text())
    rows = []
    seen = set()
    bad = 0
    for (N, p, q) in iter_rows(data):
        # basic sanity: even N >= 4, p+q=N
        try:
            if N % 2 == 0 and N >= 4 and p + q == N:
                if 4 <= N <= limit and (N,p,q) not in seen:
                    rows.append((int(N), int(p), int(q)))
                    seen.add((N,p,q))
            else:
                bad += 1
        except Exception:
            bad += 1

    rows.sort()
    ns = f"Goldbach.FiniteBase.Generated_000004_{limit}"

    dst.parent.mkdir(parents=True, exist_ok=True)
    with dst.open("w") as f:
        f.write("import Std\n")
        f.write(f"namespace {ns}\n")
        f.write("open Std\n\n")
        f.write("def table : Std.HashMap Nat (Nat × Nat) := Id.run do\n")
        f.write("  let mut m : Std.HashMap Nat (Nat × Nat) := {}\n")
        lastN = None
        for (N,p,q) in rows:
            # If multiple pairs for the same N exist, the last insert wins (ok).
            f.write(f"  m := m.insert {N} ({p}, {q})\n")
            lastN = N
        f.write("  return m\n")
        f.write(f"end {ns}\n")

    print(f"Wrote {dst} with {len(rows)} rows ≤ {limit} (skipped {bad} invalid rows)")

if __name__ == "__main__":
    main()
