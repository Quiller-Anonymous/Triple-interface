import Mathlib
import Goldbach.AO_OffDiag.EntryPointTenorFunX
import Goldbach.AO_OffDiagFunX
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

/-!
Single “Tenor-style” hypothesis bundle for the off-diagonal tail at scale-dependent truncation `Q(X)`.

This is a packaging layer: it collects the (currently conventional/analytic) assumptions into one
structure and exposes the derived `E_off` bound used by the AO error budget.
-/

namespace TenorHypFunX

open TailBlockFunX
open EntryPointTenorFunX

structure OffDiagHyp where
  /-- Truncation height as a function of the scale. -/
  Q : ℕ → ℕ
  /-- Majorant factor in the σ-tail bound. -/
  F : ℕ → ℝ
  /-- Tail constant (analytic). -/
  K_tail : ℝ
  K_tail_nonneg : 0 ≤ K_tail
  /-- Target error budget for the off-diagonal channel. -/
  eps : ℝ
  eps_nonneg : 0 ≤ eps

  /-- On the canonical window, truncation height is positive. -/
  Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X

  /-- Uniform truncation bound on the canonical window (analytic; currently an axiom in the refactor). -/
  sigmaTail_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * F N

  /-- Numeric budget inequality on the window. -/
  budget_ok :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      (K_tail : ℝ) / (Q X : ℝ) * F N ≤ eps

/-- The induced `TailBlockFunX.Model` using the definitional `sigmaHonest`. -/
noncomputable def model (H : OffDiagHyp) : TailBlockFunX.Model :=
  EntryPointTenorFunX.offDiagModel
    (Q := H.Q)
    (Q_pos_on_window := H.Q_pos_on_window)
    (F := H.F)
    (K_tail := H.K_tail)
    (sigmaTail_bound_on_window := by
      intro X N hX hN
      exact H.sigmaTail_bound_on_window (X := X) (N := N) hX hN)
    (K_tail_nonneg := H.K_tail_nonneg)

/-- Tail bound on the canonical window, in the bundled hypothesis form. -/
theorem tail_bound_on_window
    (H : OffDiagHyp)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |(model H).sigma X N - TailBlockFun.sigma_trunc (H.Q X) N| ≤ H.eps := by
  -- use the tail-block consumer lemma
  exact TailBlockFunX.tail_bound_on_window
    (M := model H) (eps := H.eps)
    (hbudget := by
      intro X N hX hN
      simpa [model, EntryPointTenorFunX.offDiagModel] using
        H.budget_ok (X := X) (N := N) hX hN)
    hX hN

/-- Off-diagonal AO error term bound on the canonical window, in the bundled hypothesis form. -/
theorem E_off_bound_relative
    (H : OffDiagHyp)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |Goldbach.AO_OffDiagFunX.E_off (model H) X N|
    ≤ H.eps * |Goldbach.AO_WeightMass.weight_mass X| := by
  exact Goldbach.AO_OffDiagFunX.E_off_bound_relative
    (M := model H) (eps := H.eps)
    (hbudget := by
      intro X N hX hN
      simpa [model, EntryPointTenorFunX.offDiagModel] using
        H.budget_ok (X := X) (N := N) hX hN)
    hX hN

/-- Off-diagonal AO error term bound on the canonical window, in the bundled hypothesis form. -/
theorem E_off_bound
    (H : OffDiagHyp)
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |Goldbach.AO_OffDiagFunX.E_off (model H) X N| ≤ H.eps := by
  exact Goldbach.AO_OffDiagFunX.E_off_bound
    (M := model H) (eps := H.eps) (eps_nonneg := H.eps_nonneg)
    (hbudget := by
      intro X N hX hN
      simpa [model, EntryPointTenorFunX.offDiagModel] using
        H.budget_ok (X := X) (N := N) hX hN)
    hX hN

end TenorHypFunX

end AO_OffDiag
end Goldbach
