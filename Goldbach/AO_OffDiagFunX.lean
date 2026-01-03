import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.AO_Core
import Goldbach.AO_OffDiag.TailBlockFunX
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_OffDiagFunX

set_option maxRecDepth 10000

open Real
open Goldbach.Windows
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.TailBlockFunX

/-!
Off-diagonal AO error term bound for an `X`-dependent tail-block witness.

This is the analogue of `Goldbach/AO_OffDiagFun.lean`, but for `TailBlockFunX.Model`.
-/

/-- Off-diagonal AO error term (X-dependent sigma witness). -/
noncomputable def E_off (M : TailBlockFunX.Model) (X N : ℕ) : ℝ :=
  (M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N) * AO_Core.weight_mass X

theorem E_off_bound
    (M : TailBlockFunX.Model)
    (eps : ℝ)
    (eps_nonneg : 0 ≤ eps)
    (hbudget :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F_ub : ℝ) ≤ eps)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |E_off M X N| ≤ eps := by
  have hmass : |Goldbach.AO_Core.weight_mass X| ≤ (1 : ℝ) :=
    (inferInstance : WeightMassOnWindow).weight_mass_abs_le_one_on_window (X := X) hX
  have htail :
      |M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N| ≤ eps :=
    Goldbach.AO_OffDiag.TailBlockFunX.tail_bound_on_window (M := M) (eps := eps)
      (hbudget := by
        intro X hX
        exact hbudget (X := X) hX)
      hX hN
  calc
    |E_off M X N|
        = |(M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N)
            * Goldbach.AO_Core.weight_mass X| := by
            simp [E_off]
    _   = |M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N|
            * |Goldbach.AO_Core.weight_mass X| := by
            simp
    _   ≤ eps * |Goldbach.AO_Core.weight_mass X| := by
            exact mul_le_mul_of_nonneg_right htail (abs_nonneg _)
    _   ≤ eps * 1 := by
            exact mul_le_mul_of_nonneg_left hmass eps_nonneg
    _   = eps := by ring

end AO_OffDiagFunX
end Goldbach

