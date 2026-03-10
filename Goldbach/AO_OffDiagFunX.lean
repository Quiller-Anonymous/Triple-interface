import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.AO_OffDiag.TailBlockFunX
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.AO_WeightMass
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
  (M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N) *
    Goldbach.AO_WeightMass.weight_mass X

/--
Relative off-diagonal bound before the canonical `|weight_mass X| ≤ 1` flattening step.

This captures the honest normalization shape of the off-diagonal channel: the sigma-tail budget is
multiplied by the AO weight mass.
-/
theorem E_off_bound_relative
    (M : TailBlockFunX.Model)
    (eps : ℝ)
    (hbudget :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Windows.EvenIn X BankParams.H →
        (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F N) ≤ eps)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |E_off M X N| ≤ eps * |Goldbach.AO_WeightMass.weight_mass X| := by
  have htail :
      |M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N| ≤ eps :=
    Goldbach.AO_OffDiag.TailBlockFunX.tail_bound_on_window (M := M) (eps := eps)
      (hbudget := by
        intro X N hX hN
        exact hbudget (X := X) (N := N) hX hN)
      hX hN
  calc
    |E_off M X N|
        = |M.sigma X N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N|
            * |Goldbach.AO_WeightMass.weight_mass X| := by
            simp [E_off]
    _   ≤ eps * |Goldbach.AO_WeightMass.weight_mass X| := by
            exact mul_le_mul_of_nonneg_right htail (abs_nonneg _)

theorem E_off_bound
    (M : TailBlockFunX.Model)
    (eps : ℝ)
    (eps_nonneg : 0 ≤ eps)
    (hbudget :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Windows.EvenIn X BankParams.H →
        (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F N) ≤ eps)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |E_off M X N| ≤ eps := by
  have hmass : |Goldbach.AO_WeightMass.weight_mass X| ≤ (1 : ℝ) :=
    (inferInstance : WeightMassOnWindow).weight_mass_abs_le_one_on_window (X := X) hX
  have hrel :
      |E_off M X N| ≤ eps * |Goldbach.AO_WeightMass.weight_mass X| :=
    E_off_bound_relative (M := M) (eps := eps)
      (hbudget := by
        intro X N hX hN
        exact hbudget (X := X) (N := N) hX hN)
      hX hN
  calc
    |E_off M X N|
        ≤ eps * |Goldbach.AO_WeightMass.weight_mass X| := hrel
    _   ≤ eps * 1 := by
            exact mul_le_mul_of_nonneg_left hmass eps_nonneg
    _   = eps := by ring

end AO_OffDiagFunX
end Goldbach
