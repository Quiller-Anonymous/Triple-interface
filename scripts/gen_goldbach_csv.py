# scripts/gen_goldbach_csv.py
# Generate a CSV with rows: N,p,q for even N in [LO, HI], with p and q primes, p+q=N.

from math import isqrt
import csv
from pathlib import Path

# --- EDIT THESE THREE LINES ---
LO = 100_002
HI = 200_000
OUTPUT_CSV = Path("Goldbach/Base/data/chunk_100002_200000.csv")
# ------------------------------

def sieve_primes(nmax: int):
    """Return a boolean list is_prime[0..nmax]."""
    is_prime = [False, False] + [True]*(nmax-1)
    for p in range(2, isqrt(nmax)+1):
        if is_prime[p]:
            step = p
            start = p*p
            is_prime[start:nmax+1:step] = [False]*(((nmax - start)//step) + 1)
    return is_prime

def find_goldbach_pair(N: int, is_prime):
    """Return one (p, q) with p+q=N and both prime, or None if not found."""
    # Only even N are processed; for safety, guard odd N
    if N % 2 == 1 or N < 4:
        return None
    for p in range(2, (N // 2) + 1):
        if is_prime[p]:
            q = N - p
            if q >= 2 and is_prime[q]:
                return (p, q)
    return None

def main():
    # Make sure LO/Hl are sane
    lo = LO if LO % 2 == 0 else LO + 1  # start at even
    hi = HI
    if lo < 4:
        lo = 4

    # Precompute primes up to HI
    print(f"[gen_goldbach_csv] Sieving primes up to {hi}…")
    is_prime = sieve_primes(hi)

    OUTPUT_CSV.parent.mkdir(parents=True, exist_ok=True)
    rows = []
    total = 0
    missing = []

    print(f"[gen_goldbach_csv] Generating Goldbach pairs for even N in [{lo}, {hi}]…")
    for N in range(lo, hi + 1, 2):
        total += 1
        pq = find_goldbach_pair(N, is_prime)
        if pq is None:
            missing.append(N)
        else:
            p, q = pq
            # sanity: assert p+q == N
            if p + q != N:
                raise RuntimeError(f"Internal error: p+q != N for N={N}, p={p}, q={q}")
            rows.append((N, p, q))
        if total % 2000 == 0:
            print(f"  processed {total} evens; latest N={N}")

    # Write CSV
    with OUTPUT_CSV.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["N", "p", "q"])
        w.writerows(rows)

    print(f"[gen_goldbach_csv] Wrote {len(rows)} rows to {OUTPUT_CSV}")
    if missing:
        print(f"[gen_goldbach_csv] WARNING: no pair found for {len(missing)} N’s (unexpected below a few billion).")
        print(f"  First few missing: {missing[:10]}")

if __name__ == "__main__":
    main()
