import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.AO_WeightMass
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.EntryPoint


namespace Goldbach
namespace AO_OffDiag

set_option maxRecDepth 10000

/-!
Inputs required here:
• `tail_bound_on_window` (axiom, to be discharged by the off-diagonal analysis): the Ramanujan truncation gap on the canonical window.
• An instance `[WeightMassOnWindow]` giving `|weight_mass| ≤ 1` for `X ≥ X0`.
-/

/-
Assumed API already in this file or nearby:
  * sigma              : ℕ → ℝ
  * sigma_trunc_Q0     : ℕ → ℝ          -- the truncation at your fixed Q0
  * E_off              : ℕ → ℕ → ℝ      -- the AO off-diagonal model
  * weight_mass        : ℕ → ℝ
  and (by definition) E_off X N = (sigma N - sigma_trunc_Q0 N) * weight_mass X
If the last identity is not yet definitional, keep the lemma `E_off_def` below.
-/

noncomputable def E_off (X N : ℕ) : ℝ :=
  (Goldbach.AO_OffDiag.sigmaHonest N - TailBlock.sigma_trunc_Q0 N) *
    Goldbach.AO_WeightMass.weight_mass X

theorem E_off_bound {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |E_off X N| ≤ (3e-4 : ℝ) := by

  have htail :
      |Goldbach.AO_OffDiag.sigmaHonest N - TailBlock.sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) :=
    -- this is the lemma proved (axiomatically for now) in EntryPoint.lean
    Goldbach.AO_OffDiag.tail_bound_on_window (X := X) (N := N) hX hN
  -- |weight_mass| ≤ 1 on the canonical window
  have hmass : |Goldbach.AO_WeightMass.weight_mass X| ≤ (1 : ℝ) :=
    (inferInstance : WeightMassOnWindow).weight_mass_abs_le_one_on_window (X:=X) hX
  -- combine the two bounds
  calc
    |E_off X N|
        = |(Goldbach.AO_OffDiag.sigmaHonest N - TailBlock.sigma_trunc_Q0 N)
            * Goldbach.AO_WeightMass.weight_mass X| := by
            simp [E_off]
    _   = |Goldbach.AO_OffDiag.sigmaHonest N - TailBlock.sigma_trunc_Q0 N|
            * |Goldbach.AO_WeightMass.weight_mass X| := by
            simp [abs_mul]
    _   ≤ (3e-4 : ℝ) * |Goldbach.AO_WeightMass.weight_mass X| := by
            exact mul_le_mul_of_nonneg_right htail (abs_nonneg _)
    _   ≤ (3e-4 : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hmass (by norm_num : 0 ≤ (3e-4 : ℝ))
    _   = (3e-4 : ℝ) := by ring


end AO_OffDiag
end Goldbach
