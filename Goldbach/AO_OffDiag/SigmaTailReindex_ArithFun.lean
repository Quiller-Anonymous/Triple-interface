import Mathlib.Data.Nat.Basic

namespace Goldbach.AO_OffDiag
namespace SigmaTailReindex_ArithFun

/-!
Arithmetic lemmas for the reindexing step, parameterized by a truncation height `Q`.

Main goal: from `Q < q` and a factorization `q = d * r` with `d ≠ 0`,
deduce `Q / d < r`.
-/

/-- If `Q < d * r` and `d ≠ 0`, then `Q / d < r`. -/
lemma div_lt_of_lt_mul {Q d r : ℕ} (hd : d ≠ 0) (h : Q < d * r) :
    Q / d < r := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have h' : Q < r * d := by
    simpa [Nat.mul_comm] using h
  exact (Nat.div_lt_iff_lt_mul hd').2 h'

/-- If `q = d * r` and `Q < q` with `d ≠ 0`, then `Q / d < r`. -/
lemma div_lt_of_lt_of_eq_mul {Q q d r : ℕ} (hd : d ≠ 0) (hq : q = d * r) (hQ : Q < q) :
    Q / d < r := by
  refine div_lt_of_lt_mul (Q := Q) (d := d) (r := r) hd ?_
  simpa [hq] using hQ

/-- In the gcd-split `d = gcd q N`, `r = q / d`, `Q < q` implies `Q / d < r`. -/
lemma div_gcd_lt_quot {Q q N : ℕ} (hq0 : q ≠ 0) (hQ : Q < q) :
    Q / (Nat.gcd q N) < (q / Nat.gcd q N) := by
  have hd : Nat.gcd q N ≠ 0 := by
    exact Nat.gcd_ne_zero_left hq0
  have hmul : Q < (Nat.gcd q N) * (q / Nat.gcd q N) := by
    have : (Nat.gcd q N) * (q / Nat.gcd q N) = q := by
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q N)
    simpa [this] using hQ
  exact div_lt_of_lt_mul (Q := Q) (d := Nat.gcd q N) (r := q / Nat.gcd q N) hd hmul

end SigmaTailReindex_ArithFun
end Goldbach.AO_OffDiag
