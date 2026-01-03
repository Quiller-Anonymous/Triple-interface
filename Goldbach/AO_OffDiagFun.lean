import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.AO_Core
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_OffDiagFun

set_option maxRecDepth 10000

open scoped BigOperators
open Real
open Goldbach.Windows
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.TailBlockFun

/-!
Parallel `Q(X)` refactor for the off-diagonal AO error term.

This is the analogue of `Goldbach/AO_OffDiag.lean`, but it uses the variable-truncation
tail-block interface (`TailBlockFun.Model`), i.e. truncation height `Q : ℕ → ℕ`.

Nothing here is analytic: we only combine
* the tail bound `|sigma - trunc| ≤ eps` on the window, and
* `|weight_mass| ≤ 1`,
to produce a bound on the off-diagonal error term `E_off`.
-/

/-- Off-diagonal AO error term at variable truncation height `Q(X)`. -/
noncomputable def E_off (M : Goldbach.AO_OffDiag.TailBlockFun.Model) (X N : ℕ) : ℝ :=
  (M.sigma N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N) * AO_Core.weight_mass X

/--
If the tail bound holds on the canonical window, then `E_off` is bounded by the same epsilon
on that window (since `|weight_mass| ≤ 1`).
-/
theorem E_off_bound_of_tail_bound
    (M : Goldbach.AO_OffDiag.TailBlockFun.Model)
    (eps : ℝ)
    (eps_nonneg : 0 ≤ eps)
    (htail :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Windows.EvenIn X BankParams.H →
        |M.sigma N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N| ≤ eps)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |E_off M X N| ≤ eps := by
  have hmass : |Goldbach.AO_Core.weight_mass X| ≤ (1 : ℝ) :=
    (inferInstance : WeightMassOnWindow).weight_mass_abs_le_one_on_window (X := X) hX
  have htail' :
      |M.sigma N - Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc (M.Q X) N| ≤ eps :=
    htail (X := X) (N := N) hX hN
  calc
    |E_off M X N|
        = |(M.sigma N - TailBlockFun.sigma_trunc (M.Q X) N)
            * Goldbach.AO_Core.weight_mass X| := by
            simp [E_off]
    _   = |M.sigma N - TailBlockFun.sigma_trunc (M.Q X) N|
            * |Goldbach.AO_Core.weight_mass X| := by
            simp
    _   ≤ eps * |Goldbach.AO_Core.weight_mass X| := by
            exact mul_le_mul_of_nonneg_right htail' (abs_nonneg _)
    _   ≤ eps * 1 := by
            exact mul_le_mul_of_nonneg_left hmass eps_nonneg
    _   = eps := by ring

/--
Convenience: produce the tail bound from the model's structural lemma + a budget assumption.
-/
theorem E_off_bound
    (M : Goldbach.AO_OffDiag.TailBlockFun.Model)
    (eps : ℝ)
    (eps_nonneg : 0 ≤ eps)
    (hbudget :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F_ub : ℝ) ≤ eps)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |E_off M X N| ≤ eps := by
  refine E_off_bound_of_tail_bound (M := M) (eps := eps) (eps_nonneg := eps_nonneg)
    (X := X) (N := N) ?_ hX hN
  intro X N hX hN
  exact Goldbach.AO_OffDiag.TailBlockFun.tail_bound_on_window (M := M) (eps := eps) (hbudget := by
    intro X hX
    exact hbudget (X := X) hX) hX hN

end AO_OffDiagFun
end Goldbach
