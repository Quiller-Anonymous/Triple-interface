# scripts/make_this_chunk.py
from pathlib import Path
import subprocess, sys

# --- EDIT THESE TWO LINES to the chunk you are generating ---
LOW, HIGH = 100002, 200000
# ------------------------------------------------------------

ROOT = Path(__file__).resolve().parents[1]  # repo root (adjust if your structure differs)

GEN  = ROOT / "scripts" / "make_chunk.module.py"
CSV  = ROOT / "Goldbach" / "Base" / "data" / f"chunk_{LOW}_{HIGH}.csv"
OUT  = ROOT / "Goldbach" / "FiniteBase" / f"Generated_{LOW}_{HIGH}.lean"

def main() -> None:
    # sanity checks help avoid silent mistakes
    if not GEN.exists():
        raise SystemExit(f"Generator not found: {GEN}")
    if not CSV.exists():
        raise SystemExit(f"CSV not found: {CSV} (populate it first!)")
    OUT.parent.mkdir(parents=True, exist_ok=True)

    # Call the real generator with proper CLI args.
    # Using sys.executable guarantees the same Python you’re running in VS Code.
    subprocess.run([sys.executable, str(GEN), str(CSV), str(OUT)], check=True)

if __name__ == "__main__":
    main()
