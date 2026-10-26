import Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
import Goldbach.MainTerm
import Goldbach.SingularSeriesExtras

/-!
# Production von Mangoldt circle program for corrected Route A

The standard major-arc estimates in the repository are naturally stated for von Mangoldt.  This
module therefore keeps the complete von Mangoldt weight through the exact circle split and removes
higher prime powers only at the final convolution.  The sparse contamination is not folded into a
pointwise exponential-sum error.

A certificate has three quantitative obligations:

* major-arc approximation for the complete von Mangoldt sum;
* minor-arc norm control for that same sum;
* an upper bound for the exact higher-prime-power contamination.

If their combined budget is below the Hardy--Littlewood main term, the prime-only convolution is
positive and hence gives an actual Goldbach representation.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtCircleProgram

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit

noncomputable section

/-- Real parameterization of the complete von Mangoldt circle integrand. -/
noncomputable def broadVonMangoldtIntervalIntegrand
    (N : ℕ) (alpha : ℝ) : ℂ :=
  finiteWeightIntervalIntegrand broadVonMangoldtWeight N alpha

lemma continuous_broadVonMangoldtIntervalIntegrand (N : ℕ) :
    Continuous (broadVonMangoldtIntervalIntegrand N) := by
  simpa [broadVonMangoldtIntervalIntegrand] using
    (continuous_finiteWeightIntervalIntegrand broadVonMangoldtWeight N)

lemma intervalIntegrable_broadVonMangoldtIntervalIntegrand (N : ℕ) :
    IntervalIntegrable (broadVonMangoldtIntervalIntegrand N) volume (0 : ℝ) (1 : ℝ) := by
  simpa [broadVonMangoldtIntervalIntegrand] using
    (intervalIntegrable_finiteWeightIntervalIntegrand broadVonMangoldtWeight N)

/-- Major-arc part of the complete von Mangoldt circle integral. -/
noncomputable def broadVonMangoldtMajorArcIntegral
    (N B : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightMajorArcIntegral broadVonMangoldtWeight N B Delta

/-- Minor-arc part of the complete von Mangoldt circle integral. -/
noncomputable def broadVonMangoldtMinorArcIntegral
    (N B : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightMinorArcIntegral broadVonMangoldtWeight N B Delta

theorem broadVonMangoldtPairConvolution_cast_eq_major_add_minor
    (N B : ℕ) (Delta : ℝ) :
    (broadVonMangoldtPairConvolution N : ℂ)
      = broadVonMangoldtMajorArcIntegral N B Delta
        + broadVonMangoldtMinorArcIntegral N B Delta := by
  simpa [broadVonMangoldtPairConvolution, broadVonMangoldtMajorArcIntegral,
    broadVonMangoldtMinorArcIntegral, finiteWeightPairConvolution] using
    (finiteWeightPairConvolution_cast_eq_major_add_minor
      broadVonMangoldtWeight N B Delta)

theorem broadVonMangoldtPairConvolution_eq_major_re_add_minor_re
    (N B : ℕ) (Delta : ℝ) :
    broadVonMangoldtPairConvolution N
      = (broadVonMangoldtMajorArcIntegral N B Delta).re
        + (broadVonMangoldtMinorArcIntegral N B Delta).re := by
  simpa [broadVonMangoldtPairConvolution, broadVonMangoldtMajorArcIntegral,
    broadVonMangoldtMinorArcIntegral, finiteWeightPairConvolution] using
    (finiteWeightPairConvolution_eq_major_re_add_minor_re
      broadVonMangoldtWeight N B Delta)

/-- Raw Hardy--Littlewood main term on the logarithmically weighted convolution scale. -/
noncomputable def broadVonMangoldtRawMain
    (C : Goldbach.Singular.C2Const) (N : ℕ) : ℝ :=
  Goldbach.Singular.sigma C N * (N : ℝ)

theorem broadVonMangoldtRawMain_pos
    {C : Goldbach.Singular.C2Const} {N : ℕ}
    (hTwo : 2 ≤ N) (hEven : Even N) :
    0 < broadVonMangoldtRawMain C N := by
  have hsigmaFloor :
      (2 : ℝ) * C.C2 ≤ Goldbach.Singular.sigma C N :=
    Goldbach.Singular.sigma_floor_even hEven
  have hsigmaPos : 0 < Goldbach.Singular.sigma C N := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) C.pos) hsigmaFloor
  have hNPos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hTwo)
  exact mul_pos hsigmaPos hNPos

/--
The corrected Route A certificate surface.  Every field is a quantitative estimate; there is no
bank-coverage or positive-window-mean assumption hidden in the interface.
-/
structure BroadVonMangoldtCircleCertificate
    (C : Goldbach.Singular.C2Const)
    (Xmin B : ℕ) (Delta : ℝ)
    (majorError minorError primePowerError : ℕ → ℝ) : Prop where
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(broadVonMangoldtMajorArcIntegral N B Delta).re
          - broadVonMangoldtRawMain C N| ≤ majorError N
  minor_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖broadVonMangoldtMinorArcIntegral N B Delta‖ ≤ minorError N
  primePower_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      broadPrimePowerContamination N ≤ primePowerError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N + primePowerError N
        < broadVonMangoldtRawMain C N

theorem broadPrimePairConvolution_pos_of_vonMangoldtCircleCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ}
    {majorError minorError primePowerError : ℕ → ℝ}
    (hcert : BroadVonMangoldtCircleCertificate C Xmin B Delta
      majorError minorError primePowerError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    0 < broadPrimePairConvolution N := by
  have hmajorAbs := hcert.major_approx hN hEven
  have hmajorLower :
      broadVonMangoldtRawMain C N - majorError N
        ≤ (broadVonMangoldtMajorArcIntegral N B Delta).re := by
    have := (abs_le.mp hmajorAbs).1
    linarith
  have hminorAbs :
      |(broadVonMangoldtMinorArcIntegral N B Delta).re| ≤ minorError N :=
    (Complex.abs_re_le_norm _).trans (hcert.minor_bound hN hEven)
  have hminorLower :
      -minorError N ≤ (broadVonMangoldtMinorArcIntegral N B Delta).re :=
    (abs_le.mp hminorAbs).1
  have hPower := hcert.primePower_bound hN hEven
  have hBudget := hcert.strict_budget hN hEven
  rw [broadPrimePairConvolution_eq_vonMangoldt_sub_contamination,
    broadVonMangoldtPairConvolution_eq_major_re_add_minor_re]
  linarith

theorem goldbachRep_of_vonMangoldtCircleCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ}
    {majorError minorError primePowerError : ℕ → ℝ}
    (hcert : BroadVonMangoldtCircleCertificate C Xmin B Delta
      majorError minorError primePowerError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N :=
  broadPrimePairConvolution_pos_iff_goldbachRep.mp
    (broadPrimePairConvolution_pos_of_vonMangoldtCircleCertificate hcert hN hEven)

/-- A checked broad von Mangoldt certificate plus the finite base closes Goldbach. -/
theorem goldbach_of_finiteBase_and_vonMangoldtCircleCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ}
    {majorError minorError primePowerError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BroadVonMangoldtCircleCertificate C Xmin B Delta
      majorError minorError primePowerError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_vonMangoldtCircleCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtCircleProgram
