import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary

/-!
Live arithmetic frontier for the half-mass zero-mode side.

This file deliberately contains only the pairwise-error target surface that remains after the
centered-variance reduction in `Q0MinorHalfMassArithmeticBoundary`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassPairwiseError

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary

noncomputable section

/--
Generator-facing pairwise-error window expression for the half-mass-recentered zero-mode error
layer.
-/
noncomputable def halfMassErrorPairwiseWindowUpper (κ : ℝ) (X : ℕ) : ℝ :=
  halfMassRecenteredZeroModeErrorPairwiseEnergy κ X

/--
Any certified route-sized upper bound for the exact pairwise-error window expression upgrades to
the abstract pairwise-error target.
-/
theorem halfMassErrorPairwiseTarget_of_windowUpper
    {κ C2 C3 : ℝ}
    (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        halfMassErrorPairwiseWindowUpper κ X
          ≤
        2 * (((EvenIn X H).card : ℝ) *
          (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) :
    HalfMassErrorPairwiseTarget κ C2 C3 := by
  refine ⟨hC2, hC3, ?_⟩
  intro X hX
  change halfMassErrorPairwiseWindowUpper κ X
      ≤
    2 * (((EvenIn X H).card : ℝ) *
      (C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
  exact hUpper (X := X) hX

end
