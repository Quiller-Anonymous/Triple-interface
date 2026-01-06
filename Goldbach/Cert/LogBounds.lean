import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Goldbach.BankParams

/-!
Numeric log bounds on the canonical cutoff `X0`.

These are “conventional math” facts (numerical inequalities about `Real.log`) that we keep as
explicit axioms for now. They can later be discharged either by:
- a small analytic proof using monotonicity of `Real.log` and a certified inequality for `Real.exp`,
  or
- an external numeric certificate checked against the real-analytic library.
-/

namespace Goldbach.Cert

open Real
open scoped BigOperators Nat

/-- A conservative upper bound on `log X0` for `X0 = 10^6`. -/
private lemma cubic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have hsum :
      (∑ i ∈ Finset.range 4, x ^ i / (i ! : ℝ)) ≤ Real.exp x :=
    Real.sum_le_exp_of_nonneg hx 4
  have hsum_eq :
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 = (∑ i ∈ Finset.range 4, x ^ i / (i ! : ℝ)) := by
    -- Unroll `range 4` and evaluate factorials `0! = 1`, `1! = 1`, `2! = 2`, `3! = 6`.
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      _root_.pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_succ,
      Nat.cast_succ, Nat.cast_one]
    ring_nf
  -- rewrite the sum as the cubic Taylor polynomial, then apply the standard `sum_le_exp` bound
  have : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    simpa [hsum_eq] using hsum
  exact this

private lemma log_two_le_seven_tenths : Real.log (2 : ℝ) ≤ (7 / 10 : ℝ) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hx0 : (0 : ℝ) ≤ (7 / 10 : ℝ) := by norm_num
  have h2_le_poly : (2 : ℝ) ≤ 1 + (7 / 10 : ℝ) + (7 / 10 : ℝ) ^ 2 / 2 + (7 / 10 : ℝ) ^ 3 / 6 := by
    norm_num
  have hpoly_le_exp :
      1 + (7 / 10 : ℝ) + (7 / 10 : ℝ) ^ 2 / 2 + (7 / 10 : ℝ) ^ 3 / 6 ≤ Real.exp (7 / 10 : ℝ) :=
    cubic_le_exp_of_nonneg hx0
  have h2_le_exp : (2 : ℝ) ≤ Real.exp (7 / 10 : ℝ) := le_trans h2_le_poly hpoly_le_exp
  exact (Real.log_le_iff_le_exp h2pos).2 h2_le_exp

theorem log_X0_le : Real.log (Goldbach.BankParams.X0 : ℝ) ≤ 14 := by
  -- `X0 = 10^6 ≤ 2^20`, so `log X0 ≤ log (2^20) = 20 * log 2`.
  have hX0_le : (Goldbach.BankParams.X0 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) := by
    -- `10^6 = 1_000_000 ≤ 1_048_576 = 2^20`.
    norm_num [Goldbach.BankParams.X0]

  have hlog_le : Real.log (Goldbach.BankParams.X0 : ℝ) ≤ Real.log ((2 : ℝ) ^ (20 : ℕ)) := by
    have hpos : 0 < (Goldbach.BankParams.X0 : ℝ) := by
      norm_num [Goldbach.BankParams.X0]
    exact Real.log_le_log hpos hX0_le

  have hlog_pow : Real.log ((2 : ℝ) ^ (20 : ℕ)) = (20 : ℝ) * Real.log (2 : ℝ) := by
    simpa using (Real.log_pow (2 : ℝ) 20)

  calc
    Real.log (Goldbach.BankParams.X0 : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (20 : ℕ)) := hlog_le
    _   = (20 : ℝ) * Real.log (2 : ℝ) := by simpa [mul_comm] using hlog_pow
    _   ≤ (20 : ℝ) * (7 / 10 : ℝ) := by gcongr; exact log_two_le_seven_tenths
    _   = 14 := by norm_num

end Goldbach.Cert
