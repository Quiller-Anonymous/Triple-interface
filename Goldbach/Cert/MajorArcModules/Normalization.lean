import Goldbach.Cert.MajorArcAxiomsFunX

/-!
`MajorArcModules/Normalization` collects small, purely algebraic helpers about the major-arc
objects (`RΛ_smooth`, `RΛ_model`) and their log-scalings.

This is intended to support the “offline turnkey” work without changing the live pipeline.
-/

namespace Goldbach.Cert.MajorArcModules.Normalization

open Goldbach.Cert.MajorArcAxiomsFunX

noncomputable section

-- Convenience: in this project `weight_mass X = 1`, so the model is just `sigma N`.
lemma RΛ_model_eq_sigma (X N : ℕ) :
    RΛ_model X N = Goldbach.AO_SigmaModel.sigma N := by
  simp [RΛ_model, Goldbach.AO_WeightMass.weight_mass]

/-- Log-scaled version of the smoothed correlation (undoes the payload’s `(log N)^{-2}`). -/
noncomputable def RΛ_smooth_logScaled (X N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 2 * RΛ_smooth X N

/-- Log-scaled version of the model term (same scaling, for comparison). -/
noncomputable def RΛ_model_logScaled (X N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 2 * RΛ_model X N

lemma RΛ_logScaled_sub_eq (X N : ℕ) :
    RΛ_smooth_logScaled X N - RΛ_model_logScaled X N =
      (Real.log (N : ℝ)) ^ 2 * (RΛ_smooth X N - RΛ_model X N) := by
  simp [RΛ_smooth_logScaled, RΛ_model_logScaled]
  ring_nf

end

end Goldbach.Cert.MajorArcModules.Normalization
