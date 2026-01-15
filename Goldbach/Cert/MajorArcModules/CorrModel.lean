import Goldbach.Cert.MajorArcModules.MainTermQ0
import Goldbach.Cert.MajorArcModules.NumericFacts
import Goldbach.AO_SigmaModel

/-!
`MajorArcModules/CorrModel` defines the σ-side “model” term for the *unnormalized* complex
correlation integral `corr_integral`.

Recall:
- `RΛ_smooth` is the *normalized real* correlation functional; Step 11 shows
  `(RΛ_smooth : ℂ) = ((1/800) * (log N)^{-2}) * corr_integral`.
- `RΛ_model = sigma N` (since `weight_mass = 1`).

Therefore the corresponding model for `corr_integral` is:

`corrModel N := (log N)^2 * 800 * sigma N`,

which, using the definition of `AO_SigmaModel.sigma`, is exactly:

`(log N)^2 * mass_even * sigma_trunc_Q0 N`.

This module keeps that identity in a stable, reusable form for the certificate route.
-/

namespace Goldbach.Cert.MajorArcModules.CorrModel

open Complex
open Goldbach
open Goldbach.Cert.MajorArcModules.MainTermQ0

noncomputable section

/-- σ-side model term for the unnormalized complex correlation integral. -/
noncomputable def corrModel (N : ℕ) : ℂ :=
  ((Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N : ℝ)

lemma corrModel_eq_logSq_mul_massEven_mul_sigma_trunc (N : ℕ) :
    corrModel N
      =
    ((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
        * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) := by
  -- Unfold `AO_SigmaModel.sigma` and cancel the `800` factor.
  simp [corrModel, Goldbach.AO_SigmaModel.sigma, mul_assoc, mul_left_comm, mul_comm]

lemma corrModel_eq_logSq_mul_massEven_mul_qa_mainTerm_Q0C (N : ℕ) :
    corrModel N
      =
    ((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even : ℝ) * qa_mainTerm_Q0C N := by
  -- Rewrite `qa_mainTerm_Q0C` to the σ truncation, then compare both sides as casts of `ℝ`.
  have hqa : qa_mainTerm_Q0C N = ((Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ) :=
    qa_mainTerm_Q0C_eq_sigma_trunc_Q0 (N := N)
  -- `corrModel` is a real number viewed in `ℂ`.
  simp [corrModel_eq_logSq_mul_massEven_mul_sigma_trunc, hqa, mul_assoc, mul_left_comm, mul_comm]

end

end Goldbach.Cert.MajorArcModules.CorrModel

