/-
  Twin/CLSFromL2.lean
  -------------------
  From the windowed L² bound
      L2 ≤ ε^2 · SS^2 · ((H+1)/9)
  derive the linear CLS bound
      A  ≤ ε · SS · ((H+1)/3).

  rc2-safe:
   • No sqrt-division rewrites (never introduce √N/√9).
   • Use `Real.sqrt_le_iff` with an explicitly squared RHS `R^2`.
   • Finish in the exact goal order: ε * SS * (↑H+1) / 3.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Twin.GoalAPI
import Twin.CLSL2
import Twin.AnalyticCore
import Twin.LedgerExtra
import Twin.Compat

open Real
open Twin

namespace Twin
namespace CLSFromL2

/-- Convert the windowed L² bound (`CLSL2.Bound`) into the linear CLS bound
    expected by `AnalyticCore.CLSBound`. -/
theorem toCLS
  (P : GoalAPI.Params) (e : ℕ → ℝ)
  (hL2 : CLSL2.Bound P e) :
  AnalyticCore.CLSBound P e := by
  classical
  refine ⟨?_⟩
  intro X hX0

  -- Shorthands
  let H  : ℕ := P.H
  let SS : ℝ := truncSingularSeries P.S
  let ε  : ℝ := P.eps
  let N  : ℝ := (↑H : ℝ) + 1
  let A  : ℝ := Ledger.windowSum X H (fun n => |e n|)
  let L2 : ℝ := Ledger.windowSum X H (fun n => e n ^ 2)

  -- Nonnegativity
  have hN_nonneg  : 0 ≤ N := by
    have : (0 : ℝ) ≤ (↑H : ℝ) := by exact_mod_cast Nat.zero_le H
    exact add_nonneg this (by norm_num)
  have hα_nonneg  : 0 ≤ N / 9 := div_nonneg hN_nonneg (by norm_num : (0 : ℝ) ≤ 9)
  have hε_nonneg  : 0 ≤ ε := le_of_lt P.eps_pos
  have hSS_nonneg : 0 ≤ SS := Twin.Compat.truncSS_nonneg_of_ge3 P.S P.S_ge_three

  -- Windowed Cauchy–Schwarz (from LedgerExtra)
  have hCS : A ≤ Real.sqrt N * Real.sqrt L2 :=
    Twin.LedgerExtra.window_l1_le_sqrt_span_mul_window_l2 (X := X) (H := H) (e := e)

  -- Normalize L² hypothesis to `L2 ≤ ε^2 * SS^2 * (N/9)`
  have hL2X' : L2 ≤ ε ^ 2 * SS ^ 2 * (N / 9) := by
    have := hL2.bound X hX0
    simpa [N, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this

  -- Define R := ε·SS·√(N/9) and compute R^2 explicitly (no √N/√9 expansions)
  set R : ℝ := ε * SS * Real.sqrt (N / 9) with hR
  have hR_nonneg : 0 ≤ R :=
    mul_nonneg (mul_nonneg hε_nonneg hSS_nonneg) (Real.sqrt_nonneg _)

  have hR_sq : R ^ 2 = ε ^ 2 * SS ^ 2 * (N / 9) := by
    unfold R
    calc
      (ε * SS * Real.sqrt (N / 9)) ^ 2
          = (ε * SS) ^ 2 * (Real.sqrt (N / 9)) ^ 2 := by
              simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
      _   = (ε ^ 2 * SS ^ 2) * (N / 9) := by
              rw [pow_two, pow_two, Real.mul_self_sqrt hα_nonneg]
              ring
      _   = ε ^ 2 * SS ^ 2 * (N / 9) := by
              simp [mul_comm, mul_left_comm]

  -- From L² bound to a bound on √L2
  have hx : L2 ≤ R ^ 2 := by simpa [hR_sq] using hL2X'
  have h_sqrtL2 : Real.sqrt L2 ≤ R :=
    (Real.sqrt_le_iff).mpr ⟨hR_nonneg, hx⟩

  -- Chain CS with √L2 bound: A ≤ √N * R
  have hA_step : A ≤ Real.sqrt N * R :=
    le_trans hCS (mul_le_mul_of_nonneg_left h_sqrtL2 (Real.sqrt_nonneg _))

  -- Reassociate to ε·SS·(√N·√(N/9)) (never introduce √N/√9)
  have hA_prod : A ≤ ε * SS * (Real.sqrt N * Real.sqrt (N / 9)) := by
    have eqR :
      Real.sqrt N * R = ε * SS * (Real.sqrt N * Real.sqrt (N / 9)) := by
      unfold R; simp [mul_comm, mul_left_comm, mul_assoc]
    simpa [eqR] using hA_step

  -- Apply the span identity: √N · √(N/9) = N/3
  have span : Real.sqrt N * Real.sqrt (N / 9) = N / 3 := by
    change Real.sqrt ((↑H : ℝ) + 1) * Real.sqrt (((↑H : ℝ) + 1) / 9)
            = ((↑H : ℝ) + 1) / 3
    simpa using Twin.LedgerExtra.sqrt_span_mul_sqrt_span_div9 H

  -- Now in exact goal order: ε * SS * (↑H+1) / 3
  have hA_le_div : A ≤ (ε * SS * N) / 3 := by
    -- ε*SS*(N/3) = (ε*SS*N)/3
    have : ε * SS * (N / 3) = (ε * SS * N) / 3 := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    -- use hA_prod + span to get ε*SS*(N/3), then rewrite to (ε*SS*N)/3
    have hA_le' : A ≤ ε * SS * (N / 3) := by rw [← span]; exact hA_prod
    simpa [this] using hA_le'

  -- Present exactly as: ε * SS * (↑H+1) / 3
  have : (Ledger.windowSum X P.H (fun n => |e n|))
          ≤ P.eps * truncSingularSeries P.S * ((↑P.H : ℝ) + 1) / 3 := by
    -- replace N by ((↑H : ℝ) + 1)
    simpa [N, mul_comm, mul_left_comm, mul_assoc] using hA_le_div

  exact this

end CLSFromL2
end Twin
