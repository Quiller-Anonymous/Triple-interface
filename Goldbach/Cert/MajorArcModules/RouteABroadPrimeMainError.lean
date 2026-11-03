import Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector
import Goldbach.MainTerm
import Goldbach.SingularSeriesExtras

/-!
# Hardy--Littlewood main/error split for the broad Route A observable

This module fixes the exact decomposition that the direct projector route must estimate.  The
singular-series constant remains a parameter.  In production it should be instantiated by the
repository's genuine Ramanujan/Euler-product realization, not by the conservative
`C2_numeric` lower-bound surrogate.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeMainError

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector

noncomputable section

/-- Hardy--Littlewood main sequence for a supplied positive Euler-product constant. -/
noncomputable def hardyLittlewoodMainSequence
    (C : Goldbach.Singular.C2Const) : RealSequence :=
  fun N => Goldbach.MainTerm.M C N

/-- Exact residual between the complete normalized prime convolution and its main model. -/
noncomputable def hardyLittlewoodErrorSequence
    (C : Goldbach.Singular.C2Const) : RealSequence :=
  broadPrimeSequence - hardyLittlewoodMainSequence C

/-- The broad observable is definitionally the Hardy--Littlewood main plus its exact residual. -/
theorem broadPrimeSequence_eq_hardyLittlewoodMain_add_error
    (C : Goldbach.Singular.C2Const) :
    broadPrimeSequence
      = hardyLittlewoodMainSequence C + hardyLittlewoodErrorSequence C := by
  funext N
  simp [hardyLittlewoodErrorSequence]

/-- The Hardy--Littlewood main model is positive on every nontrivial even input. -/
theorem hardyLittlewoodMainSequence_pos
    {C : Goldbach.Singular.C2Const} {N : ℕ}
    (hTwo : 2 ≤ N) (hEven : Even N) :
    0 < hardyLittlewoodMainSequence C N := by
  have hsigmaFloor :
      (2 : ℝ) * C.C2 ≤ Goldbach.Singular.sigma C N :=
    Goldbach.Singular.sigma_floor_even hEven
  have hsigmaPos : 0 < Goldbach.Singular.sigma C N := by
    have : 0 < (2 : ℝ) * C.C2 := mul_pos (by norm_num) C.pos
    exact lt_of_lt_of_le this hsigmaFloor
  have hNPos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hTwo)
  have hNCast : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hTwo)
  have hlogPos : 0 < Real.log (N : ℝ) := Real.log_pos hNCast
  unfold hardyLittlewoodMainSequence Goldbach.MainTerm.M
  exact div_pos (mul_pos hsigmaPos hNPos) (sq_pos_of_pos hlogPos)

/-- Projection-certificate surface specialized to the exact Hardy--Littlewood residual. -/
abbrev HardyLittlewoodDyadicProjectionCertificate
    (C : Goldbach.Singular.C2Const)
    (X : ℕ) (P : RealSequence →ₗ[ℝ] RealSequence) :=
  BroadPrimeDyadicProjectionCertificate X P
    (hardyLittlewoodMainSequence C) (hardyLittlewoodErrorSequence C)

/--
Constructor reducing a dyadic Hardy--Littlewood certificate to its three quantitative bounds.

The decomposition field is discharged exactly.  Therefore all future analytic work is localized
in `main_lower`, `projected_error_le`, `complement_le`, and `budget`.
-/
def hardyLittlewoodProjectionCertificateOfBounds
    (C : Goldbach.Singular.C2Const)
    (X : ℕ) (P : RealSequence →ₗ[ℝ] RealSequence)
    (mainLower projectedErrorUpper complementUpper : ℝ)
    (main_lower :
      ∀ {N : ℕ}, N ∈ dyadicBlock X → Even N →
        mainLower ≤ (P (hardyLittlewoodMainSequence C)) N)
    (projected_error_le :
      dyadicL2Norm X (P (hardyLittlewoodErrorSequence C)) ≤ projectedErrorUpper)
    (complement_le :
      dyadicL2Norm X (projectorComplement P broadPrimeSequence) ≤ complementUpper)
    (budget : projectedErrorUpper + complementUpper < mainLower) :
    HardyLittlewoodDyadicProjectionCertificate C X P where
  decomposition := broadPrimeSequence_eq_hardyLittlewoodMain_add_error C
  mainLower := mainLower
  projectedErrorUpper := projectedErrorUpper
  complementUpper := complementUpper
  main_lower := main_lower
  projected_error_le := projected_error_le
  complement_le := complement_le
  budget := budget

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeMainError
