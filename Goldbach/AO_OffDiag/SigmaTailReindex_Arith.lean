import Mathlib.Data.Nat.Basic
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_OffDiag
namespace SigmaTailReindex_Arith

open TailBlock

/-
  Arithmetic lemmas for the reindexing step in `SigmaTailReindex.lean`.

  Main goal: from `Q0 < q` and a factorization `q = d * r` with `d ≠ 0`,
  deduce `Q0 / d < r`.

  This is the standard fact that dividing by `d` is order-preserving in the right way
  for natural numbers.
-/

/-- If `Q0 < d * r` and `d ≠ 0`, then `Q0 / d < r`. -/
lemma div_lt_of_lt_mul {Q0 d r : ℕ} (hd : d ≠ 0) (h : Q0 < d * r) :
    Q0 / d < r := by
  -- Use `Nat.div_lt_iff_lt_mul` (requires `0 < d`).
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  -- `Nat.div_lt_iff_lt_mul` is the natural-number API lemma for this.
  -- It states: `a / b < c ↔ a < b * c` when `0 < b`.
  exact (Nat.div_lt_iff_lt_mul hd').2 (by rwa [mul_comm] at h)

/-- If `q = d * r` and `Q0 < q` with `d ≠ 0`, then `Q0 / d < r`. -/
lemma div_lt_of_lt_of_eq_mul {Q0 q d r : ℕ} (hd : d ≠ 0) (hq : q = d * r) (hQ : Q0 < q) :
    Q0 / d < r := by
  -- reduce to the previous lemma
  refine div_lt_of_lt_mul (Q0 := Q0) (d := d) (r := r) hd ?_
  simpa [hq] using hQ

/-
A specialization matching the gcd-splitting situation:
  d = gcd q N, r = q / d and q = d * r.
-/

/-- In the gcd-split `d = gcd q N`, `r = q / d`, `Q0 < q` implies `Q0 / d < r`. -/
lemma div_gcd_lt_quot {Q0 q N : ℕ} (hq0 : q ≠ 0) (hQ : Q0 < q) :
    Q0 / (Nat.gcd q N) < (q / Nat.gcd q N) := by
  -- Apply `div_lt_of_lt_mul` with `d = gcd q N` and `r = q / gcd q N`.
  -- First show `gcd q N ≠ 0` (since q ≠ 0).
  have hd : Nat.gcd q N ≠ 0 := by
    exact Nat.gcd_ne_zero_left hq0
  -- Now use `Q0 < (gcd q N) * (q / gcd q N)` which equals `q`.
  have hmul : Q0 < (Nat.gcd q N) * (q / Nat.gcd q N) := by
    -- `Nat.mul_div_cancel'` gives `gcd q N * (q / gcd q N) = q`.
    have : (Nat.gcd q N) * (q / Nat.gcd q N) = q := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q N)
    simpa [this] using hQ
  exact div_lt_of_lt_mul (Q0 := Q0) (d := Nat.gcd q N) (r := q / Nat.gcd q N) hd hmul

end SigmaTailReindex_Arith
end Goldbach.AO_OffDiag
