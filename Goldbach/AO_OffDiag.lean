import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.WeightMass

namespace Goldbach
namespace AO_OffDiag

/-
Assumed API already in this file or nearby:
  * sigma              : ℕ → ℝ
  * sigma_trunc_Q0     : ℕ → ℝ          -- the truncation at your fixed Q0
  * E_off              : ℕ → ℕ → ℝ      -- the AO off-diagonal model
  * weight_mass        : ℕ → ℝ
  and (by definition) E_off X N = (sigma N - sigma_trunc_Q0 N) * weight_mass X
If the last identity is not yet definitional, keep the lemma `E_off_def` below.
-/

/-- If not definitional in your file, keep this helper; otherwise you can delete it. -/
lemma E_off_def
    (E_off : ℕ → ℕ → ℝ)
    (sigma sigma_trunc_Q0 : ℕ → ℝ)
    (weight_mass : ℕ → ℝ)
    (hdef : ∀ X N, E_off X N = (sigma N - sigma_trunc_Q0 N) * weight_mass X) :
    ∀ X N, E_off X N = (sigma N - sigma_trunc_Q0 N) * weight_mass X := hdef

/-- Main off-diagonal bound on the canonical window:
    use (1) the tail bound from `TailBlock` and (2) `|weight_mass X| ≤ 1`. -/
theorem E_off_bound_of_sigma_tail
    {X0 H X N Q0 : ℕ}
    (E_off : ℕ → ℕ → ℝ)
    (sigma sigma_trunc_Q0 : ℕ → ℝ)
    (weight_mass : ℕ → ℝ)
    (hdef : ∀ X N, E_off X N = (sigma N - sigma_trunc_Q0 N) * weight_mass X)
    (hX  : X0 ≤ X) (hN : Goldbach.Windows.EvenIn X H N)
    -- tail input (from TailBlock):  |sigma - sigma_trunc| ≤ 3e-4
    (I   : Goldbach.AO_OffDiag.TailBlock.SigmaTailInputs Q0)
    -- bump normalization on the window: |weight_mass X| ≤ 1
    (hmass_nonneg : 0 ≤ weight_mass X)
    (hmass_le_one : weight_mass X ≤ 1) :
    |E_off X N| ≤ (3e-4 : ℝ) := by
  -- unfold the model
  have hE : E_off X N = (sigma N - sigma_trunc_Q0 N) * weight_mass X :=
    hdef X N
  -- tail size
  have htail : |sigma N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) :=
    Goldbach.AO_OffDiag.TailBlock.tail_bound_Q0 (I:=I) (X0:=X0) (H:=H) (X:=X) (N:=N) hX hN
  -- mass bound: |weight_mass X| ≤ 1
  have hmass : |weight_mass X| ≤ 1 :=
    Goldbach.AO_OffDiag.weight_mass_abs_on_window (weight_mass:=weight_mass) (X0:=X0) (H:=H)
      hX hN hmass_nonneg hmass_le_one
  -- combine
  calc
    |E_off X N|
        = |(sigma N - sigma_trunc_Q0 N) * weight_mass X| := by simpa [hE]
    _   ≤ |sigma N - sigma_trunc_Q0 N| * |weight_mass X| := by
            simpa [abs_mul] using (le_of_eq (by rfl : |(sigma N - sigma_trunc_Q0 N) * weight_mass X|
                                                           = |sigma N - sigma_trunc_Q0 N| * |weight_mass X|))
    _   ≤ (3e-4 : ℝ) * |weight_mass X| := by
            exact mul_le_mul_of_nonneg_right htail (abs_nonneg _)
    _   ≤ (3e-4 : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hmass (by norm_num : 0 ≤ (3e-4 : ℝ))
    _   = (3e-4 : ℝ) := by ring

end AO_OffDiag
end Goldbach
