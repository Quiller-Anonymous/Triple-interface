import Mathlib.MeasureTheory.Function.L2Space
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1CommonWindowTargets

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1CommonEnergyTargets

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1CommonWindowTargets
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers

noncomputable section

private lemma continuous_coe_UC_local : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_canonicalQ1TwoSidedShiftCommonPositiveOverlap_uncurry_local
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K p.2 p.1 := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveOverlap
  refine continuous_finset_sum _ ?_
  intro j hj
  refine continuous_finset_sum _ ?_
  intro k hk
  have h1 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e (2 * p.2 / (X : ℝ)) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ => 2 * Real.pi * (2 * p.2 / (X : ℝ)) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi * (2 * p.2 / (X : ℝ)) : ℝ) : ℂ) := by
      exact continuous_const.mul (Complex.continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h2 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        (p.1 * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) : ℝ) : ℂ) := by
      exact continuous_const.mul (Complex.continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h3 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        ((p.2 / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi
          * ((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * ((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))) : ℝ) : ℂ) := by
      exact continuous_const.mul (Complex.continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  simpa [mul_assoc] using h1.mul (h2.mul h3)

private lemma continuous_canonicalQ1TwoSidedShiftCommonNegativeOverlap_uncurry_local
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K p.2 p.1 := by
  unfold canonicalQ1TwoSidedShiftCommonNegativeOverlap
  refine continuous_finset_sum _ ?_
  intro j hj
  refine continuous_finset_sum _ ?_
  intro k hk
  have h1 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e (2 * p.2 / (X : ℝ)) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ => 2 * Real.pi * (2 * p.2 / (X : ℝ)) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi * (2 * p.2 / (X : ℝ)) : ℝ) : ℂ) := by
      exact continuous_const.mul (Complex.continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h2 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        (p.1 * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) : ℝ) : ℂ) := by
      exact continuous_const.mul (Complex.continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h3 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        (-((p.2 / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi
          * (-((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * (-((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))) : ℝ) : ℂ) := by
      exact continuous_const.mul (Complex.continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  simpa [mul_assoc] using h1.mul (h2.mul h3)

private lemma continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_uncurry_local
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC))
        * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K p.2 p.1 := by
  have hK : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC) := by
    dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      (((fourier (T := (1 : ℝ)) k).continuous).comp (continuous_coe_UC_local.comp continuous_fst))
  exact hK.mul (continuous_canonicalQ1TwoSidedShiftCommonPositiveOverlap_uncurry_local X overlap K)

private lemma continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_uncurry_local
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC))
        * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K p.2 p.1 := by
  have hK : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC) := by
    dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      (((fourier (T := (1 : ℝ)) k).continuous).comp (continuous_coe_UC_local.comp continuous_fst))
  exact hK.mul (continuous_canonicalQ1TwoSidedShiftCommonNegativeOverlap_uncurry_local X overlap K)

private lemma intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_local
    (X overlap K : ℕ) (β : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β)
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  let ψ : ℝ → ℝ × ℝ := fun u => (β, u)
  have hψ : Continuous ψ := continuous_const.prodMk continuous_id
  have hcont : Continuous fun u : ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β := by
    simpa [ψ] using
      (continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_uncurry_local X overlap K).comp
        hψ
  exact hcont.intervalIntegrable (μ := MeasureTheory.volume) _ _

private lemma intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_local
    (X overlap K : ℕ) (β : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β)
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  let ψ : ℝ → ℝ × ℝ := fun u => (β, u)
  have hψ : Continuous ψ := continuous_const.prodMk continuous_id
  have hcont : Continuous fun u : ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β := by
    simpa [ψ] using
      (continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_uncurry_local X overlap K).comp
        hψ
  exact hcont.intervalIntegrable (μ := MeasureTheory.volume) _ _

private lemma continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
    (X overlap K : ℕ) :
    Continuous fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β)
      (hf := by
        simpa [Function.uncurry] using
          continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_uncurry_local X overlap K)
      (0 : ℝ) (1 : ℝ))

private lemma continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
    (X overlap K : ℕ) :
    Continuous fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β)
      (hf := by
        simpa [Function.uncurry] using
          continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_uncurry_local X overlap K)
      (0 : ℝ) (1 : ℝ))

private lemma intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
    (X overlap K : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β) β)
      MeasureTheory.volume aβ bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β)
        MeasureTheory.volume aβ bβ :=
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
      X overlap K).intervalIntegrable _ _
  exact
    intervalIntegrable_indicator_of_intervalIntegrable
      (a := aβ) (b := bβ) (s := betaSmallSet)
      (f := fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β)
      measurableSet_betaSmallSet hInt

private lemma intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
    (X overlap K : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β) β)
      MeasureTheory.volume aβ bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β)
        MeasureTheory.volume aβ bβ :=
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
      X overlap K).intervalIntegrable _ _
  exact
    intervalIntegrable_indicator_of_intervalIntegrable
      (a := aβ) (b := bβ) (s := betaSmallSet)
      (f := fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β)
      measurableSet_betaSmallSet hInt

/--
The exact pre-absolute-value `β`-integrand for the `q = 1` common branch.

This is the object the next analytic attempt should treat quadratically, rather than taking norms
before integrating in `β`.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
    (X N M : ℕ) (β : ℝ) : ℂ :=
  betaSmallSet.indicator
    (fun β : ℝ =>
      Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
        X N M β) β

/--
The current `q = 1` common integral is exactly the `β`-integral of the pre-absolute-value
integrand above.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegral_eq_betaIntegral_preAbsolute
    (X N M : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M
      =
    ∫ β in aβ..bβ, canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_eq_positive_and_negative
    (X N M : ℕ) :
    (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β)
      =
    (fun β : ℝ =>
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β
        +
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β) := by
  funext β
  by_cases hβ : β ∈ betaSmallSet
  · simp [canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand, hβ,
      canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_eq_positive_and_negative]
  · simp [canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand, hβ]

/--
Positive `β`-preintegrand for the `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand
    (X N M : ℕ) (β : ℝ) : ℂ :=
  betaSmallSet.indicator
    (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β

/--
Negative `β`-preintegrand for the `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand
    (X N M : ℕ) (β : ℝ) : ℂ :=
  betaSmallSet.indicator
    (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β

/-- Local product form of the fixed-overlap positive one-dimensional `gExp` sums. -/
private noncomputable def canonicalQ1TwoSidedShiftCommonPositiveProductLocal
    (X overlap : ℕ) (u β : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
    *
  (∑ m ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m)

/--
Exact Fourier/product-factorized positive `β`-preintegrand.

This keeps the fixed overlap at `N`, the `N` versus `M` dependence in the Fourier difference, and
the `β`-oscillation in the one-variable finite exponential sum product.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrandFactored
    (X N M : ℕ) (β : ℝ) : ℂ :=
  betaSmallSet.indicator
    (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
              * ((((fourier (T := (1 : ℝ)) (-(N : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))
                - ((fourier (T := (1 : ℝ)) (-(M : ℤ)) ((u / (X : ℝ)) : UC) : ℂ)))
              *
                (canonicalQ1TwoSidedShiftCommonPositiveProductLocal X N u β))) β

theorem canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_eq_positive_add_negative
    (X N M : ℕ) :
    (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β)
      =
    (fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β
        +
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand X N M β) := by
  simpa [canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand,
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand] using
    canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_eq_positive_and_negative X N M

/--
Exact fixed-overlap Fourier/product factorization of the positive `β`-preintegrand.

For the positive q=1 common branch, the overlap width is frozen at `N`. The `N` versus `M`
dependence sits entirely in the Fourier factor, while the `β`-oscillation is carried by the two
one-variable finite exponential sums in the product.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteFourierProductReduction :
    Prop where
  eq :
    ∀ X N M β,
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β
        =
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrandFactored X N M β

theorem canonicalQ1TwoSidedShiftCommonPositiveProductLocal_eq_finiteGExpIco
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveProductLocal X overlap u β
      =
    finiteGExpIco overlap (u / (X : ℝ) + β)
      * finiteGExpIco overlap (u / (X : ℝ) - β) := by
  rfl

theorem intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    IntervalIntegrable
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β)
      MeasureTheory.volume aβ bβ := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_eq_positive_and_negative]
  have hpos :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β)
        MeasureTheory.volume aβ bβ := by
    have hraw :=
      (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
          X N N).sub
        (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
          X N M)
    have hEq :
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β)
          =
        (fun x : ℝ =>
          betaSmallSet.indicator
              (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N N β) x
            +
          -betaSmallSet.indicator
              (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N M β) x) := by
      funext β
      by_cases hβ : β ∈ betaSmallSet <;>
        simp [canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral, sub_eq_add_neg, hβ]
    rw [hEq]
    simpa [sub_eq_add_neg] using hraw
  have hneg :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β)
        MeasureTheory.volume aβ bβ := by
    have hraw :=
      (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
          X N N).sub
        (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
          X N M)
    have hEq :
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β)
          =
        (fun x : ℝ =>
          betaSmallSet.indicator
              (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N N β) x
            +
          -betaSmallSet.indicator
              (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N M β) x) := by
      funext β
      by_cases hβ : β ∈ betaSmallSet <;>
        simp [canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral, sub_eq_add_neg, hβ]
    rw [hEq]
    simpa [sub_eq_add_neg] using hraw
  exact hpos.add hneg

theorem intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    IntervalIntegrable
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β)
      MeasureTheory.volume aβ bβ := by
  have hraw :=
    (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
        X N N).sub
      (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
        X N M)
  have hEq :
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β)
        =
      (fun x : ℝ =>
        betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N N β) x
          +
        -betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N M β) x) := by
    funext β
    by_cases hβ : β ∈ betaSmallSet <;>
      simp [canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand,
        canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral, sub_eq_add_neg, hβ]
  rw [hEq]
  simpa [sub_eq_add_neg] using hraw

theorem intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    IntervalIntegrable
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand X N M β)
      MeasureTheory.volume aβ bβ := by
  have hraw :=
    (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
        X N N).sub
      (intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
        X N M)
  have hEq :
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand X N M β)
        =
      (fun x : ℝ =>
        betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N N β) x
          +
        -betaSmallSet.indicator
            (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N M β) x) := by
    funext β
    by_cases hβ : β ∈ betaSmallSet <;>
      simp [canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand,
        canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral, sub_eq_add_neg, hβ]
  rw [hEq]
  simpa [sub_eq_add_neg] using hraw

theorem aestronglyMeasurable_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β)
      ((MeasureTheory.volume).restrict (Set.Ioc aβ bβ)) := by
  exact
    IntervalIntegrable.aestronglyMeasurable
      (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M)

private lemma betaSmallSet_subset_Ioc_local : betaSmallSet ⊆ Set.Ioc aβ bβ := by
  intro β hβ
  have hβ' : -betaSmallRadius ≤ β ∧ β ≤ betaSmallRadius := by
    simpa [betaSmallSet, Set.mem_Icc] using hβ
  have hrad_lt_half : betaSmallRadius < ((2 : ℝ)⁻¹) := by
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hlt : (2 : ℝ) < (4 * Real.pi : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have : (1 : ℝ) / (4 * Real.pi) < (1 : ℝ) / (2 : ℝ) :=
      one_div_lt_one_div_of_lt h2 hlt
    simpa [betaSmallRadius, one_div] using this
  have hleft : aβ < β := by
    have : (-( (2 : ℝ)⁻¹) : ℝ) < -betaSmallRadius := by
      have := neg_lt_neg hrad_lt_half
      simpa [aβ] using this
    exact lt_of_lt_of_le this hβ'.1
  have hright : β < bβ := by
    have : betaSmallRadius < ((2 : ℝ)⁻¹) := hrad_lt_half
    exact lt_of_le_of_lt hβ'.2 (by simpa [bβ] using this)
  exact ⟨hleft, le_of_lt hright⟩

private lemma continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_local
    (X N M : ℕ) :
    Continuous fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral
  exact
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
      X N N).sub
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral_local
      X N M)

private lemma continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral_local
    (X N M : ℕ) :
    Continuous fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral
  exact
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
      X N N).sub
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral_local
      X N M)

private lemma norm_sq_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_le_two_mul_pos_neg
    (X N M : ℕ) (β : ℝ) :
    ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ^ 2
      ≤
    2 * ‖betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β‖ ^ 2
      + 2 * ‖betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β‖ ^ 2 := by
  have hEq :=
    congrFun
      (canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_eq_positive_and_negative X N M) β
  rw [hEq]
  let z1 :=
    betaSmallSet.indicator
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β
  let z2 :=
    betaSmallSet.indicator
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β
  have htri : ‖z1 + z2‖ ≤ ‖z1‖ + ‖z2‖ := norm_add_le _ _
  have hsq1 : ‖z1 + z2‖ ^ 2 ≤ (‖z1‖ + ‖z2‖) ^ 2 := by
    have hnonneg1 : 0 ≤ ‖z1 + z2‖ := norm_nonneg _
    have hnonneg2 : 0 ≤ ‖z1‖ + ‖z2‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg hnonneg1, abs_of_nonneg hnonneg2] using htri)
  have hsq2 : (‖z1‖ + ‖z2‖) ^ 2 ≤ 2 * ‖z1‖ ^ 2 + 2 * ‖z2‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z1‖ - ‖z2‖)]
  exact le_trans hsq1 hsq2

private lemma exists_bound_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ Set.Ioc aβ bβ,
        ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ≤ C := by
  let gpos := fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β
  let gneg := fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β
  obtain ⟨Cpos, hCpos⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_local X N M).continuousOn
  obtain ⟨Cneg, hCneg⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral_local X N M).continuousOn
  refine ⟨max Cpos 0 + max Cneg 0, by positivity, ?_⟩
  intro β hβIoc
  by_cases hβsmall : β ∈ betaSmallSet
  · have hβIcc : β ∈ Set.Icc aβ bβ := ⟨le_of_lt hβIoc.1, hβIoc.2⟩
    have hEq :=
      congrFun
        (canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_eq_positive_and_negative X N M) β
    calc
      ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖
          = ‖betaSmallSet.indicator
                (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β) β
              +
              betaSmallSet.indicator
                (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β‖ := by
                  simpa [hEq]
      _ = ‖gpos β + gneg β‖ := by simp [gpos, gneg, hβsmall]
      _ ≤ ‖gpos β‖ + ‖gneg β‖ := norm_add_le _ _
      _ ≤ (max Cpos 0) + (max Cneg 0) := by
            gcongr
            · exact le_trans (hCpos β hβIcc) (le_max_left _ _)
            · exact le_trans (hCneg β hβIcc) (le_max_left _ _)
  · have hnonneg : 0 ≤ max Cpos 0 + max Cneg 0 := by positivity
    simpa [canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand, hβsmall] using hnonneg

private lemma memLp_two_norm_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    MeasureTheory.MemLp
      (fun β : ℝ => ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖)
      2
      ((MeasureTheory.volume).restrict (Set.Ioc aβ bβ)) := by
  let μ0 : MeasureTheory.Measure ℝ := (MeasureTheory.volume).restrict (Set.Ioc aβ bβ)
  haveI : MeasureTheory.IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    have hfin : MeasureTheory.volume (Set.Ioc aβ bβ) < ⊤ := by
      simp
    simpa [μ0, MeasureTheory.Measure.restrict_apply, measurableSet_Ioc] using hfin
  obtain ⟨C, hCnonneg, hC⟩ :=
    exists_bound_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M
  have hAeImp :
      ∀ᵐ β ∂MeasureTheory.volume,
        β ∈ Set.Ioc aβ bβ →
          ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ≤ C := by
    exact Filter.Eventually.of_forall hC
  have hAe :
      ∀ᵐ β ∂μ0,
        ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Set.Ioc aβ bβ) measurableSet_Ioc).2
      hAeImp
  exact
    MeasureTheory.MemLp.of_bound
      (aestronglyMeasurable_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M).norm
      C <|
      hAe.mono (fun β hβ => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hβ)

private lemma integrable_norm_sq_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand
    (X N M : ℕ) :
    MeasureTheory.Integrable
      (fun β : ℝ => ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ^ 2)
      ((MeasureTheory.volume).restrict (Set.Ioc aβ bβ)) := by
  have hMem :
      MeasureTheory.MemLp
        (fun β : ℝ => ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖)
        2
        ((MeasureTheory.volume).restrict (Set.Ioc aβ bβ)) := by
    simpa using
      (memLp_two_norm_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M)
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      ((aestronglyMeasurable_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M).norm)).1
      hMem |> (fun hInt => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hInt)

private lemma volume_betaSmallSet_toReal_le_one_div_six_local :
    (MeasureTheory.volume betaSmallSet).toReal ≤ (1 : ℝ) / 6 := by
  have hvol :
      MeasureTheory.volume betaSmallSet = ENNReal.ofReal (2 * betaSmallRadius) := by
    simp [betaSmallSet, Real.volume_Icc, betaSmallRadius, sub_eq_add_neg, two_mul,
      add_assoc, add_left_comm, add_comm, mul_assoc]
  have htoReal :
      (MeasureTheory.volume betaSmallSet).toReal = (1 : ℝ) / (2 * Real.pi) := by
    have hnonneg : 0 ≤ (2 * betaSmallRadius : ℝ) := by
      nlinarith [le_of_lt betaSmallRadius_pos]
    calc
      (MeasureTheory.volume betaSmallSet).toReal
          = (ENNReal.ofReal (2 * betaSmallRadius)).toReal := by simpa [hvol]
      _ = 2 * betaSmallRadius := by simpa using ENNReal.toReal_ofReal hnonneg
      _ = (1 : ℝ) / (2 * Real.pi) := by
            have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
            unfold betaSmallRadius
            field_simp [hpi0]
            ring
  have h2pi : (6 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hden_le : (1 : ℝ) / (2 * Real.pi) ≤ (1 : ℝ) / 6 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) h2pi
  simpa [htoReal] using hden_le

/--
Quadratic `β`-energy of the pre-absolute-value `q = 1` common branch for a fixed ordered pair.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy
    (X N M : ℕ) : ℝ :=
  ∫ β in aβ..bβ, ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ^ 2

/--
Quadratic `β`-energy of the positive part of the pre-absolute-value `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaEnergy
    (X N M : ℕ) : ℝ :=
  ∫ β in aβ..bβ, ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β‖ ^ 2

/--
Quadratic `β`-energy of the negative part of the pre-absolute-value `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaEnergy
    (X N M : ℕ) : ℝ :=
  ∫ β in aβ..bβ, ‖canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand X N M β‖ ^ 2

/--
Ordered-pair windowed `β`-energy for the pre-absolute-value `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0

/--
Ordered-pair windowed `β`-energy for the positive pre-absolute `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaEnergy X N M else 0

/--
Ordered-pair windowed `β`-energy for the negative pre-absolute `q = 1` common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaEnergy X N M else 0

/--
The live `β`-integrand for the ordered-pair common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ^ 2 else 0

/--
The positive ordered-pair `β`-integrand.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β‖ ^ 2 else 0

/--
The negative ordered-pair `β`-integrand.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand X N M β‖ ^ 2 else 0

/--
Explicit rewrite surface for the ordered-pair `β`-energy as a restricted-measure `β`-integral of
the pairwise squared-norm integrand.

This is the live theorem shape for the q=1 `β`-energy branch. The direct proof currently hits a
Lean elaboration bottleneck on nested `integral_finset_sum` rewrites, so the statement is exposed
as a dedicated target instead of being forced in this file.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergyIntegralRewrite
    (X : ℕ) : Prop where
  eq :
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy X
      =
    ∫ β,
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaIntegrand X β
      ∂((MeasureTheory.volume).restrict (Set.Ioc aβ bβ))

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaIntegrand_le_two_mul_positive_negative
    (X : ℕ) (β : ℝ) :
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaIntegrand X β
      ≤
    2 * canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaIntegrand X β
      +
    2 * canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaIntegrand X β := by
  classical
  let g : ℕ → ℕ → ℝ := fun N M =>
    if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ^ 2 else 0
  let gpos : ℕ → ℕ → ℝ := fun N M =>
    if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveBetaPreAbsoluteIntegrand X N M β‖ ^ 2 else 0
  let gneg : ℕ → ℕ → ℝ := fun N M =>
    if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonNegativeBetaPreAbsoluteIntegrand X N M β‖ ^ 2 else 0
  change (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, g N M)
      ≤ 2 * (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, gpos N M)
        + 2 * (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, gneg N M)
  have hsum :
      ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, g N M
        ≤
      ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, (2 * gpos N M + 2 * gneg N M) := by
        refine Finset.sum_le_sum ?_
        intro N hN
        refine Finset.sum_le_sum ?_
        intro M hM
        by_cases hNM : N ≤ M
        · simp [g, gpos, gneg, hNM]
          exact
            norm_sq_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand_le_two_mul_pos_neg
              X N M β
        · simp [g, gpos, gneg, hNM]
  calc
    ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, g N M
      ≤
    ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, (2 * gpos N M + 2 * gneg N M) := hsum
    _ =
      (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, 2 * gpos N M)
        + (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, 2 * gneg N M) := by
          simp [Finset.sum_add_distrib]
    _ =
      2 * (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, gpos N M)
        + 2 * (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, gneg N M) := by
          simp [Finset.mul_sum]

/--
Abstract quadratic transport for the new `q = 1` branch.

This is the single analytic theorem the replacement attempt should now target: control the
pointwise square of the `β`-integral by a quadratic `β`-energy, preserving cancellation until
after the `β`-integration.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport : Prop where
  bound :
    ∀ X N M,
      ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2
        ≤
      ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M

theorem canonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport_explicit
    (X N M : ℕ) :
    ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2
      ≤
    ((MeasureTheory.volume betaSmallSet).toReal)
      * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M := by
  let f : ℝ → ℂ := fun β => canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β
  let μ0 : MeasureTheory.Measure ℝ := (MeasureTheory.volume).restrict (Set.Ioc aβ bβ)
  let χ : ℝ → ℝ := betaSmallSet.indicator (fun _ : ℝ => (1 : ℝ))
  haveI : MeasureTheory.IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    have hfin : MeasureTheory.volume (Set.Ioc aβ bβ) < ⊤ := by simp
    simpa [μ0, MeasureTheory.Measure.restrict_apply, measurableSet_Ioc] using hfin
  have hab : aβ ≤ bβ := Goldbach.Cert.MajorArcModules.BetaInterval.hle
  have hf_meas :
      MeasureTheory.AEStronglyMeasurable (fun β : ℝ => ‖f β‖) μ0 :=
    (aestronglyMeasurable_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M).norm
  have hf_lp :
      MeasureTheory.MemLp (fun β : ℝ => ‖f β‖) 2 μ0 :=
    memLp_two_norm_canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M
  have hχ_meas : MeasureTheory.AEStronglyMeasurable χ μ0 := by
    classical
    simpa [χ] using
      (MeasureTheory.aestronglyMeasurable_const.indicator measurableSet_betaSmallSet :
        MeasureTheory.AEStronglyMeasurable
          (betaSmallSet.indicator (fun _ : ℝ => (1 : ℝ))) μ0)
  have hχ_lp : MeasureTheory.MemLp χ 2 μ0 := by
    refine MeasureTheory.MemLp.of_bound hχ_meas 1 ?_
    exact Filter.Eventually.of_forall (fun β => by
      by_cases hβ : β ∈ betaSmallSet <;> simp [χ, hβ])
  have hχ_nonneg : 0 ≤ᵐ[μ0] χ := by
    exact Filter.Eventually.of_forall (fun β => by
      by_cases hβ : β ∈ betaSmallSet <;> simp [χ, hβ])
  have hf_nonneg : 0 ≤ᵐ[μ0] fun β : ℝ => ‖f β‖ := by
    exact Filter.Eventually.of_forall (fun β => norm_nonneg _)
  have hnorm_int :
      ‖∫ β in aβ..bβ, f β‖ ≤ ∫ β, ‖f β‖ ∂μ0 := by
    calc
      ‖∫ β in aβ..bβ, f β‖
          ≤ ∫ β in aβ..bβ, ‖f β‖ := by
              simpa [f] using
                (intervalIntegral.norm_integral_le_integral_norm
                  (μ := MeasureTheory.volume) (f := f) hab)
      _ = ∫ β, ‖f β‖ ∂μ0 := by
            simpa [μ0, f] using
              (intervalIntegral.integral_of_le
                (μ := MeasureTheory.volume) (f := fun β : ℝ => ‖f β‖)
                (a := aβ) (b := bβ) hab)
  have hmul :
      ∫ β, ‖f β‖ ∂μ0 = ∫ β, ‖f β‖ * χ β ∂μ0 := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun β => by
      by_cases hβ : β ∈ betaSmallSet <;>
        simp [χ, f, canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand, hβ])
  have hholder :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ0) Real.HolderConjugate.two_two hf_nonneg hχ_nonneg
      (by simpa using hf_lp)
      (by simpa using hχ_lp)
  have hχ_sq :
      ∫ β, χ β ^ (2 : ℝ) ∂μ0 = (MeasureTheory.volume betaSmallSet).toReal := by
    calc
      ∫ β, χ β ^ (2 : ℝ) ∂μ0 = ∫ β, χ β ∂μ0 := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun β => by
              by_cases hβ : β ∈ betaSmallSet <;> simp [χ, hβ])
      _ = μ0.real betaSmallSet := by
            simpa [χ] using
              (MeasureTheory.integral_indicator_one
                (μ := μ0) measurableSet_betaSmallSet)
      _ = (MeasureTheory.volume betaSmallSet).toReal := by
            simp [μ0, MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
              measurableSet_betaSmallSet, betaSmallSet_subset_Ioc_local,
              Set.inter_eq_left.mpr betaSmallSet_subset_Ioc_local]
  have henergy :
      ∫ β, ‖f β‖ ^ (2 : ℝ) ∂μ0
        = canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M := by
    simpa [canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy, μ0, f] using
      (intervalIntegral.integral_of_le
        (μ := MeasureTheory.volume)
        (f := fun β : ℝ => ‖f β‖ ^ (2 : ℝ))
        (a := aβ) (b := bβ) hab).symm
  have hmain :
      ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖
        ≤
      (canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M) ^ ((1 : ℝ) / 2)
        * ((MeasureTheory.volume betaSmallSet).toReal) ^ ((1 : ℝ) / 2) := by
    rw [canonicalQ1TwoSidedShiftBoundaryCommonIntegral_eq_betaIntegral_preAbsolute]
    calc
      ‖∫ β in aβ..bβ, f β‖ ≤ ∫ β, ‖f β‖ ∂μ0 := hnorm_int
      _ = ∫ β, ‖f β‖ * χ β ∂μ0 := hmul
      _ ≤ (∫ β, ‖f β‖ ^ (2 : ℝ) ∂μ0) ^ ((1 : ℝ) / 2)
            * (∫ β, χ β ^ (2 : ℝ) ∂μ0) ^ ((1 : ℝ) / 2) := hholder
      _ = (canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M) ^ ((1 : ℝ) / 2)
            * ((MeasureTheory.volume betaSmallSet).toReal) ^ ((1 : ℝ) / 2) := by
              rw [henergy, hχ_sq]
  have hbeta_nonneg : 0 ≤ canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M := by
    unfold canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy
    exact intervalIntegral.integral_nonneg (μ := MeasureTheory.volume)
      Goldbach.Cert.MajorArcModules.BetaInterval.hle
      (fun β => by
        have hsq : 0 ≤ ‖f β‖ ^ 2 := by nlinarith [sq_nonneg ‖f β‖]
        simpa using hsq)
  have hvol_nonneg : 0 ≤ (MeasureTheory.volume betaSmallSet).toReal := by positivity
  have hsquare :
      ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2
        ≤
      ((canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M) ^ ((1 : ℝ) / 2)
        * ((MeasureTheory.volume betaSmallSet).toReal) ^ ((1 : ℝ) / 2)) ^ 2 := by
    have hnorm_nonneg : 0 ≤ ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ := norm_nonneg _
    nlinarith [hmain, hnorm_nonneg]
  calc
    ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2
      ≤
    ((canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M) ^ ((1 : ℝ) / 2)
      * ((MeasureTheory.volume betaSmallSet).toReal) ^ ((1 : ℝ) / 2)) ^ 2 := hsquare
    _ =
      canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M
        * (MeasureTheory.volume betaSmallSet).toReal := by
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          rw [pow_two]
          calc
            (√(canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M)
                * √((MeasureTheory.volume betaSmallSet).toReal))
                *
              (√(canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M)
                * √((MeasureTheory.volume betaSmallSet).toReal))
                =
            (√(canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M)
                * √(canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M))
              *
            (√((MeasureTheory.volume betaSmallSet).toReal)
                * √((MeasureTheory.volume betaSmallSet).toReal)) := by
                  ring
            _ =
              canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M
                * (MeasureTheory.volume betaSmallSet).toReal := by
                  rw [Real.mul_self_sqrt hbeta_nonneg, Real.mul_self_sqrt hvol_nonneg]
    _ =
      (MeasureTheory.volume betaSmallSet).toReal
        * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M := by ring

theorem canonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport_theorem :
    CanonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport where
  bound := by
    intro X N M
    have hbeta_nonneg : 0 ≤ canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M := by
      unfold canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy
      exact intervalIntegral.integral_nonneg (μ := MeasureTheory.volume)
        Goldbach.Cert.MajorArcModules.BetaInterval.hle
        (fun β => by
          have hsq :
              0 ≤ ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖ ^ 2 := by
                nlinarith [sq_nonneg ‖canonicalQ1TwoSidedShiftBoundaryCommonBetaPreAbsoluteIntegrand X N M β‖]
          simpa using hsq)
    calc
      ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2
        ≤
      ((MeasureTheory.volume betaSmallSet).toReal)
        * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M :=
          canonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport_explicit X N M
      _ ≤ ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M := by
            exact mul_le_mul_of_nonneg_right
              volume_betaSmallSet_toReal_le_one_div_six_local
              hbeta_nonneg

/--
Route-sized target for the ordered-pair `β`-energy of the `q = 1` common branch.

The prefactor `12` is chosen so that the abstract transport with the `1/6` measure loss closes the
existing ordered-pair window target with the same route constant.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergyTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy X
        ≤
      12 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Route-sized target for the positive ordered-pair `β`-energy of the `q = 1` common branch.

The prefactor `6` is chosen so that the safe quadratic splitter
`total ≤ 2 * positive + 2 * negative` closes the full `β`-energy target with the sum of the two
route constants.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergyTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergy X
        ≤
      6 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Route-sized target for the negative ordered-pair `β`-energy of the `q = 1` common branch.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaEnergyTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaEnergy X
        ≤
      6 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Deterministic positive-branch reduction bound after factoring the pre-absolute integrand.

The only analytic input here is the helper-supplied `L²_β` bound for the plain plus/minus product
of one-dimensional finite exponential sums. The remaining factors are the kernel cap and the
Fourier-in-`u / X` difference between the ordered pair endpoints.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveProductBetaEnergyReductionBound
    (productBound : ℕ → ℝ → ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∫ u in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap ^ 2)
            * (‖((fourier (T := (1 : ℝ)) (-(N : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))
                  - ((fourier (T := (1 : ℝ)) (-(M : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))‖ ^ 2)
            * productBound N (u / (X : ℝ))
      else 0

/--
Reduction surface from the positive ordered-pair `β`-energy to the plain plus/minus product
`L²_β` helper. This is the live positive q=1 theorem surface after the factorization correction.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergyProductReduction
    (productBound : ℕ → ℝ → ℝ) : Prop where
  helper :
    FiniteGExpIcoPlusMinusProductBetaEnergyTarget productBound
  bound :
    ∀ X,
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergy X
        ≤
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveProductBetaEnergyReductionBound
        productBound X

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergyTarget_of_productReduction
    {productBound : ℕ → ℝ → ℝ} {C3 : ℝ}
    (hred :
      CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergyProductReduction
        productBound)
    (hC3 : 0 ≤ C3)
    (hcompare :
      ∀ {X : ℕ}, X0 ≤ X →
        canonicalQ1TwoSidedShiftBoundaryCommonPositiveProductBetaEnergyReductionBound
            productBound X
          ≤
        6 * (((EvenIn X H).card : ℝ)
          * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) :
    CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergyTarget C3 where
  C3_nonneg := hC3
  bound := by
    intro X hX
    exact le_trans (hred.bound X) (hcompare hX)

/--
Abstract splitter for the ordered-pair `β`-energy of the `q = 1` common branch.

This packages the step from the total `β`-energy to the positive and negative `β`-energies, leaving
the live mathematics in the positive/negative quadratic bounds rather than in more rewrite
bookkeeping.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergySplitTransport : Prop where
  bound :
    ∀ X,
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy X
        ≤
      2 * canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergy X
        + 2 * canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaEnergy X

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy_le_betaEnergy
    (htransport : CanonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport)
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
      ≤
    ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy X := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy
  calc
    (∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2 else 0)
      ≤
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0 := by
          refine Finset.sum_le_sum ?_
          intro N hN
          refine Finset.sum_le_sum ?_
          intro M hM
          by_cases hNM : N ≤ M
          · simp [hNM]
            simpa [one_div] using htransport.bound X N M
          · simp [hNM]
    _ =
    ((1 : ℝ) / 6)
      * (∑ N ∈ EvenIn X H,
          ∑ M ∈ EvenIn X H,
            if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0) := by
          calc
            (∑ N ∈ EvenIn X H,
                ∑ M ∈ EvenIn X H,
                  if N ≤ M then ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0)
                =
              ∑ N ∈ EvenIn X H,
                ((1 : ℝ) / 6)
                  * (∑ M ∈ EvenIn X H,
                      if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro N hN
                    have hfactor :
                        (∑ M ∈ EvenIn X H,
                            if N ≤ M then ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0)
                          =
                        ∑ M ∈ EvenIn X H,
                          ((1 : ℝ) / 6)
                            * (if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0) := by
                              refine Finset.sum_congr rfl ?_
                              intro M hM
                              by_cases hNM : N ≤ M <;> simp [hNM]
                    rw [hfactor, ← Finset.mul_sum]
            _ =
              ((1 : ℝ) / 6)
                * (∑ N ∈ EvenIn X H,
                    ∑ M ∈ EvenIn X H,
                      if N ≤ M then canonicalQ1TwoSidedShiftBoundaryCommonBetaEnergy X N M else 0) := by
                        rw [← Finset.mul_sum]

/--
The bounded replacement theorem surface for the next `q = 1` attempt.

If the new quadratic `β`-energy route lands at the correct scale, the existing common ordered-pair
target follows immediately.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_betaEnergy
    {C3 : ℝ}
    (htransport : CanonicalQ1TwoSidedShiftBoundaryCommonBetaL2Transport)
    (hbeta : CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergyTarget C3) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget C3 where
  C3_nonneg := hbeta.C3_nonneg
  bound := by
    intro X hX
    have hmain :=
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy_le_betaEnergy
        htransport X
    have hbetaX := hbeta.bound hX
    calc
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
        ≤ ((1 : ℝ) / 6) * canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy X := hmain
      _ ≤ ((1 : ℝ) / 6)
            * (12 * (((EvenIn X H).card : ℝ)
                * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
              gcongr
      _ =
        2 * (((EvenIn X H).card : ℝ)
          * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
            ring

/--
Deterministic combiner reducing the full ordered-pair `β`-energy target to the positive and
negative ordered-pair `β`-energy targets once a safe splitter is available.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergyTarget_of_positive_and_negative
    {C3pos C3neg : ℝ}
    (hsplit : CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergySplitTransport)
    (hpos : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergyTarget C3pos)
    (hneg : CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaEnergyTarget C3neg) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergyTarget (C3pos + C3neg) where
  C3_nonneg := add_nonneg hpos.C3_nonneg hneg.C3_nonneg
  bound := by
    intro X hX
    have hsplitX := hsplit.bound X
    have hposX := hpos.bound hX
    have hnegX := hneg.bound hX
    calc
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseBetaEnergy X
        ≤
      2 * canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseBetaEnergy X
        + 2 * canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseBetaEnergy X := hsplitX
      _ ≤
      2 * (6 * (((EvenIn X H).card : ℝ)
          * (C3pos / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))))
        +
      2 * (6 * (((EvenIn X H).card : ℝ)
          * (C3neg / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
            gcongr
      _ =
      12 * (((EvenIn X H).card : ℝ)
        * ((C3pos + C3neg) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
          ring

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1CommonEnergyTargets
