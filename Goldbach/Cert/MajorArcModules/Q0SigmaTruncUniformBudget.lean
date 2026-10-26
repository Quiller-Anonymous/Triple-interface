import Goldbach.Cert.MajorArcModules.Q0SigmaTruncRawEnergy
import Goldbach.Cert.MajorArcModules.EvenWindowReindex
import Goldbach.Cert.MajorArcModules.NormalizedRealWindowEnergy
import Goldbach.BankParams

/-! Uniform truncation energy with any real normalizer greater than 1.32. -/
namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncUniformBudget
open scoped BigOperators
open Goldbach.BankParams Goldbach.Windows Goldbach.AO_OffDiag.TailBlock
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncRawEnergy
open Goldbach.Cert.MajorArcModules.EvenWindowReindex
open Goldbach.Cert.MajorArcModules.NormalizedRealWindowEnergy

theorem raw_reference_energy_evenIn_le {X : ℕ} (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, (sigma_trunc_Q0 N - 2) ^ 2) ≤
      5001 * (varianceRat : ℝ) + (twoTermL1BoundRat : ℝ) := by
  have hX1 : 1 ≤ X := le_trans (by norm_num [X0]) hX
  rw [sum_evenIn_eq_Ioc hX1, half_window_eq_Ioc_add hX1]
  apply raw_reference_energy_Ioc_le_5001
  have hcard := evenIn_card_le (H := H) hX1
  simpa only [H] using hcard

/-- The normalized energy bound holds for every canonical window, not just at `X0`. -/
theorem normalized_truncation_energy_lt_1795
    {X : ℕ} (hX : X0 ≤ X) (c : ℝ) (hc : (33 : ℝ) / 25 < c) :
    (∑ N ∈ EvenIn X H, ‖((sigma_trunc_Q0 N / c : ℝ) : ℂ) -
      ((EvenIn X H).card : ℂ)⁻¹ *
        ∑ j ∈ EvenIn X H, ((sigma_trunc_Q0 j / c : ℝ) : ℂ)‖ ^ 2) < 1795 := by
  let U : ℝ := 5001 * (varianceRat : ℝ) + (twoTermL1BoundRat : ℝ)
  have hc0 : 0 < c := by linarith
  have hc2 : ((33 : ℝ) / 25) ^ 2 ≤ c ^ 2 := by nlinarith
  have hraw := raw_reference_energy_evenIn_le hX
  have hU : 0 ≤ U :=
    le_trans (Finset.sum_nonneg fun N hN => sq_nonneg _) hraw
  have hcenter : (∑ N ∈ EvenIn X H, ‖((sigma_trunc_Q0 N / c : ℝ) : ℂ) -
      ((EvenIn X H).card : ℂ)⁻¹ *
        ∑ j ∈ EvenIn X H, ((sigma_trunc_Q0 j / c : ℝ) : ℂ)‖ ^ 2) ≤
      (∑ N ∈ EvenIn X H, (sigma_trunc_Q0 N - 2) ^ 2) / c ^ 2 := by
    exact centered_normalized_energy_le_reference (EvenIn X H) sigma_trunc_Q0 c 2
  have hbudget : U / ((33 : ℝ) / 25) ^ 2 < 1795 := by
    dsimp [U]
    have h := (Rat.cast_lt (K := ℝ)).2 twoTerm_normalized_budget_lt_1795
    push_cast at h
    exact h
  calc
    (∑ N ∈ EvenIn X H, ‖((sigma_trunc_Q0 N / c : ℝ) : ℂ) -
      ((EvenIn X H).card : ℂ)⁻¹ *
        ∑ j ∈ EvenIn X H, ((sigma_trunc_Q0 j / c : ℝ) : ℂ)‖ ^ 2)
        ≤ (∑ N ∈ EvenIn X H, (sigma_trunc_Q0 N - 2) ^ 2) / c ^ 2 := hcenter
    _ ≤ U / c ^ 2 := div_le_div_of_nonneg_right hraw (sq_nonneg c)
    _ ≤ U / ((33 : ℝ) / 25) ^ 2 :=
      div_le_div_of_nonneg_left hU (by norm_num) hc2
    _ < 1795 := hbudget

end Goldbach.Cert.MajorArcModules.Q0SigmaTruncUniformBudget
