import Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare

namespace Goldbach.ProjectedTrueModelScaleObstacle

open Goldbach

noncomputable section

/--
The naive model-scale closure route already fails at the first positivity gate: the natural
model-scale lower margin `σmin * weight_mass(X)` is below the canonical absolute error at `X0`.
-/
theorem not_model_scale_eps_lt_cModel_at_X0
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] :
    ¬ Goldbach.CanonParams.ε
        < Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.cModel Goldbach.Analytic.X0 := by
  have hc :
      Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.cModel Goldbach.Analytic.X0
        < Goldbach.CanonParams.ε :=
    Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.cModel_at_X0_lt_eps
  exact not_lt_of_ge hc.le

/--
So no canonical-window witness can use the raw normalized model together with the lower margin
`cModel(X) = σmin * weight_mass(X)` and the existing absolute error `ε`.
-/
theorem not_model_scale_eps_lt_cModel_on_window
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] :
    ¬ (∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
          Goldbach.CanonParams.ε
            < Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.cModel X) := by
  intro h
  exact not_model_scale_eps_lt_cModel_at_X0 (h le_rfl)

end

end Goldbach.ProjectedTrueModelScaleObstacle
