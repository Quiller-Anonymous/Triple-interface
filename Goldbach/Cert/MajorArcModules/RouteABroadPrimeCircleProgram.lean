import Goldbach.Cert.MajorArcModules.RouteABroadPrimeCircle
import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
import Goldbach.MainTerm
import Goldbach.SingularSeriesExtras

/-!
# Major/minor circle program for the complete prime convolution

This is the theorem-facing boundary for the corrected Route A.  The major and minor arcs split the
circle variable in the exact complete-convolution identity.  In particular, this module never
restricts the prime coefficients to `BG_Bank.wX` and never infers exact-center positivity from a
positive window average.

The final certificate has only three analytic obligations:

* the real part of the broad major-arc integral approximates the raw Hardy--Littlewood main term;
* the norm of the broad minor-arc integral is bounded;
* the two bounds add to less than the main term.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeCircleProgram

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit

noncomputable section

/-- The broad prime circle integrand in the real parameterization of `AddCircle 1`. -/
noncomputable def broadPrimeIntervalIntegrand (N : ℕ) (alpha : ℝ) : ℂ :=
  finiteWeightIntervalIntegrand Goldbach.BG_Bank.Λ N alpha

lemma continuous_broadPrimeIntervalIntegrand (N : ℕ) :
    Continuous (broadPrimeIntervalIntegrand N) := by
  simpa [broadPrimeIntervalIntegrand] using
    (continuous_finiteWeightIntervalIntegrand Goldbach.BG_Bank.Λ N)

lemma intervalIntegrable_broadPrimeIntervalIntegrand (N : ℕ) :
    IntervalIntegrable (broadPrimeIntervalIntegrand N) volume (0 : ℝ) (1 : ℝ) := by
  simpa [broadPrimeIntervalIntegrand] using
    (intervalIntegrable_finiteWeightIntervalIntegrand Goldbach.BG_Bank.Λ N)

/-- Broad major-arc contribution for the textbook denominator and width parameters. -/
noncomputable def broadPrimeMajorArcIntegral
    (N B : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightMajorArcIntegral Goldbach.BG_Bank.Λ N B Delta

/-- Broad minor-arc contribution on the complementary part of the same exact integral. -/
noncomputable def broadPrimeMinorArcIntegral
    (N B : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightMinorArcIntegral Goldbach.BG_Bank.Λ N B Delta

/-- The complete prime convolution is exactly its broad major plus minor circle integral. -/
theorem broadPrimePairConvolution_cast_eq_major_add_minor
    (N B : ℕ) (Delta : ℝ) :
    (broadPrimePairConvolution N : ℂ)
      = broadPrimeMajorArcIntegral N B Delta + broadPrimeMinorArcIntegral N B Delta := by
  simpa [broadPrimePairConvolution, broadPrimeMajorArcIntegral,
    broadPrimeMinorArcIntegral, finiteWeightPairConvolution] using
    (finiteWeightPairConvolution_cast_eq_major_add_minor
      Goldbach.BG_Bank.Λ N B Delta)

/-- Real form of the exact major/minor decomposition. -/
theorem broadPrimePairConvolution_eq_major_re_add_minor_re
    (N B : ℕ) (Delta : ℝ) :
    broadPrimePairConvolution N
      = (broadPrimeMajorArcIntegral N B Delta).re
        + (broadPrimeMinorArcIntegral N B Delta).re := by
  simpa [broadPrimePairConvolution, broadPrimeMajorArcIntegral,
    broadPrimeMinorArcIntegral, finiteWeightPairConvolution] using
    (finiteWeightPairConvolution_eq_major_re_add_minor_re
      Goldbach.BG_Bank.Λ N B Delta)

/-- Raw, log-weighted Hardy--Littlewood main term appropriate to the circle identity. -/
noncomputable def broadPrimeRawMain
    (C : Goldbach.Singular.C2Const) (N : ℕ) : ℝ :=
  Goldbach.Singular.sigma C N * (N : ℝ)

theorem broadPrimeRawMain_pos
    {C : Goldbach.Singular.C2Const} {N : ℕ}
    (hTwo : 2 ≤ N) (hEven : Even N) :
    0 < broadPrimeRawMain C N := by
  have hsigmaFloor :
      (2 : ℝ) * C.C2 ≤ Goldbach.Singular.sigma C N :=
    Goldbach.Singular.sigma_floor_even hEven
  have hsigmaPos : 0 < Goldbach.Singular.sigma C N := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) C.pos) hsigmaFloor
  have hNPos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hTwo)
  exact mul_pos hsigmaPos hNPos

/-- Inspectable analytic obligations for the direct prime-only circle route. -/
structure BroadPrimeCircleCertificate
    (C : Goldbach.Singular.C2Const)
    (Xmin B : ℕ) (Delta : ℝ)
    (majorError minorError : ℕ → ℝ) : Prop where
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(broadPrimeMajorArcIntegral N B Delta).re - broadPrimeRawMain C N|
        ≤ majorError N
  minor_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖broadPrimeMinorArcIntegral N B Delta‖ ≤ minorError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N < broadPrimeRawMain C N

theorem broadPrimePairConvolution_pos_of_circleCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hcert : BroadPrimeCircleCertificate C Xmin B Delta majorError minorError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    0 < broadPrimePairConvolution N := by
  have hmajorAbs := hcert.major_approx hN hEven
  have hmajorLower :
      broadPrimeRawMain C N - majorError N
        ≤ (broadPrimeMajorArcIntegral N B Delta).re := by
    have := (abs_le.mp hmajorAbs).1
    linarith
  have hminorAbs :
      |(broadPrimeMinorArcIntegral N B Delta).re| ≤ minorError N :=
    (Complex.abs_re_le_norm _).trans (hcert.minor_bound hN hEven)
  have hminorLower :
      -minorError N ≤ (broadPrimeMinorArcIntegral N B Delta).re :=
    (abs_le.mp hminorAbs).1
  have hbudget := hcert.strict_budget hN hEven
  rw [broadPrimePairConvolution_eq_major_re_add_minor_re]
  linarith

theorem goldbachRep_of_circleCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hcert : BroadPrimeCircleCertificate C Xmin B Delta majorError minorError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N :=
  broadPrimePairConvolution_pos_iff_goldbachRep.mp
    (broadPrimePairConvolution_pos_of_circleCertificate hcert hN hEven)

/-- A checked circle certificate plus the existing finite base closes Goldbach. -/
theorem goldbach_of_finiteBase_and_circleCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BroadPrimeCircleCertificate C Xmin B Delta majorError minorError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_circleCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeCircleProgram
