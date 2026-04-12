import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassJointBetaEnergyTargets

/-!
# Smoothed β-energy rebuild surface

The sharp `betaSmallSet.indicator` branch is frozen as negative evidence.  The collar audit shows
that recovering the sharp theorem from a smoothed interior plus boundary collars would require a
scale-dependent collar width, destroying the Fourier-coefficient decay gained by smoothing.

This file starts the fully smoothed branch: the smoothed cutoff is part of the theorem surface
itself.  The first analytic bottleneck is rapid decay of the localized kernel coefficients.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassSmoothedBetaEnergyTargets

open scoped BigOperators Interval

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open MeasureTheory

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeJointEnergyTargets
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassJointBetaEnergyTargets
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
Analytic data for the fully smoothed β cutoff.

The cutoff is real-valued, smooth to all finite orders, supported in `betaSmallSet`, and bounded
by one.  Coefficient decay is intentionally not included here; it is the first theorem target for
the smoothed branch.
-/
structure SmoothedBetaCutoff where
  psi : ℝ → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ n psi
  support_subset_betaSmall : Function.support psi ⊆ betaSmallSet
  nonneg : ∀ β, 0 ≤ psi β
  le_one : ∀ β, psi β ≤ 1

/-- The smoothed β cutoff as a real-valued function. -/
abbrev psiBeta (ψ : SmoothedBetaCutoff) : ℝ → ℝ :=
  ψ.psi

/--
Square the cutoff while staying on the same theorem surface.

This is the right object for the genuine weighted `L²` energy: once the endpoint is multiplied by
`ψ` before taking `‖·‖²`, the exact β-collapse naturally sees Fourier coefficients of
`ψ² · |kernel|²`.
-/
noncomputable def SmoothedBetaCutoff.squared (ψ : SmoothedBetaCutoff) : SmoothedBetaCutoff where
  psi := fun β => (ψ.psi β) ^ 2
  smooth := by
    intro n
    simpa [pow_two] using (ψ.smooth n).mul (ψ.smooth n)
  support_subset_betaSmall := by
    intro β hβ
    by_cases hpsi : ψ.psi β = 0
    · have hsq : (ψ.psi β) ^ 2 = 0 := by simp [hpsi]
      have : β ∉ Function.support (fun x => (ψ.psi x) ^ 2) := by
        simpa [Function.support, hsq]
      exact False.elim (this hβ)
    · exact ψ.support_subset_betaSmall (by simpa [Function.support, pow_two, hpsi] using hβ)
  nonneg := by
    intro β
    positivity
  le_one := by
    intro β
    nlinarith [ψ.nonneg β, ψ.le_one β]

/-- The smoothed localized outer β-kernel weight whose Fourier coefficients drive the rebuild. -/
noncomputable def canonicalSmoothedBetaKernelWeight
    (ψ : SmoothedBetaCutoff) (β : ℝ) : ℂ :=
  ((ψ.psi β : ℝ) : ℂ)
    * (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
      * star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)))

/--
Smoothed Fourier coefficient of the localized outer kernel.

This replaces the sharp-cutoff coefficient
`canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff`.  Rapid decay of this coefficient is
the first serious theorem of the smoothed rebuild.
-/
noncomputable def canonicalSmoothedBetaLocalizedKernelCoeff
    (ψ : SmoothedBetaCutoff) (t : ℤ) : ℂ :=
  ∫ β in aβ..bβ,
    canonicalSmoothedBetaKernelWeight ψ β
      * (fourier (T := (1 : ℝ)) t (β : UC) : ℂ)

/-- The same coefficient, named as a Fourier coefficient of the smoothed β-kernel weight. -/
noncomputable def canonicalSmoothedBetaKernelWeightFourierCoeff
    (ψ : SmoothedBetaCutoff) (t : ℤ) : ℂ :=
  ∫ β in aβ..bβ,
    canonicalSmoothedBetaKernelWeight ψ β
      * (fourier (T := (1 : ℝ)) t (β : UC) : ℂ)

/-- Exact rewrite of the smoothed localized coefficient as a Fourier coefficient. -/
theorem canonicalSmoothedBetaLocalizedKernelCoeff_eq_fourierCoeff
    (ψ : SmoothedBetaCutoff) (t : ℤ) :
    canonicalSmoothedBetaLocalizedKernelCoeff ψ t
      =
    canonicalSmoothedBetaKernelWeightFourierCoeff ψ t := by
  rfl

/-- The squared-cutoff localized outer β-kernel weight naturally attached to the smoothed `L²` energy. -/
noncomputable def canonicalSmoothedBetaSquaredKernelWeight
    (ψ : SmoothedBetaCutoff) (β : ℝ) : ℂ :=
  canonicalSmoothedBetaKernelWeight ψ.squared β

/--
Squared-cutoff Fourier coefficient of the localized outer kernel.

This is the coefficient surface that matches
`canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy`: the global smoothed
energy carries `ψ²`, so the exact mode-sum theorem must use this coefficient rather than the
single-cutoff one.
-/
noncomputable def canonicalSmoothedBetaSquaredLocalizedKernelCoeff
    (ψ : SmoothedBetaCutoff) (t : ℤ) : ℂ :=
  canonicalSmoothedBetaLocalizedKernelCoeff ψ.squared t

/-- The same squared-cutoff coefficient, named as a Fourier coefficient of the squared β-kernel weight. -/
noncomputable def canonicalSmoothedBetaSquaredKernelWeightFourierCoeff
    (ψ : SmoothedBetaCutoff) (t : ℤ) : ℂ :=
  canonicalSmoothedBetaKernelWeightFourierCoeff ψ.squared t

/-- Exact rewrite of the squared-cutoff localized coefficient as a Fourier coefficient. -/
theorem canonicalSmoothedBetaSquaredLocalizedKernelCoeff_eq_fourierCoeff
    (ψ : SmoothedBetaCutoff) (t : ℤ) :
    canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ t
      =
    canonicalSmoothedBetaSquaredKernelWeightFourierCoeff ψ t := by
  rfl


/--
Fixed-order coefficient decay target for the smoothed branch.

The intended first cases are `A = 2` or `A = 3`.  This is the theorem the sharp-cutoff branch
could not provide because of the jump at the boundary of `betaSmallSet`.
-/
structure CanonicalSmoothedBetaLocalizedKernelCoeffDecayTarget
    (ψ : SmoothedBetaCutoff) (A : ℕ) (C : ℝ) : Prop where
  A_ge_two : 2 ≤ A
  C_nonneg : 0 ≤ C
  bound :
    ∀ t : ℤ,
      ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ t‖
        ≤ C / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ A)

/-- The first fixed-order target: two integrations by parts / second-order decay. -/
abbrev CanonicalSmoothedBetaLocalizedKernelCoeffDecayTargetTwo
    (ψ : SmoothedBetaCutoff) (C : ℝ) : Prop :=
  CanonicalSmoothedBetaLocalizedKernelCoeffDecayTarget ψ 2 C

/-- The next fixed-order target, if `A = 2` is too weak in the mode-sum audit. -/
abbrev CanonicalSmoothedBetaLocalizedKernelCoeffDecayTargetThree
    (ψ : SmoothedBetaCutoff) (C : ℝ) : Prop :=
  CanonicalSmoothedBetaLocalizedKernelCoeffDecayTarget ψ 3 C

/--
Second-order coefficient-decay data.

This is deliberately separated from `SmoothedBetaCutoff`: smoothness/support define the theorem
surface, while the quantitative integration-by-parts estimate is the first analytic theorem to
prove.  A proof of this structure should come from the `A = 2` integration-by-parts argument and
Leibniz bounds for `(ψ * |kernelPolyC|²)''`.
-/
structure CanonicalSmoothedBetaLocalizedKernelCoeffSecondOrderDecay
    (ψ : SmoothedBetaCutoff) (C2 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  bound :
    ∀ t : ℤ,
      ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ t‖
        ≤ C2 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2)

/-- Package a proved second-order coefficient estimate as the fixed `A = 2` decay target. -/
theorem canonicalSmoothedBetaLocalizedKernelCoeffDecayTarget_two
    {ψ : SmoothedBetaCutoff} {C2 : ℝ}
    (h : CanonicalSmoothedBetaLocalizedKernelCoeffSecondOrderDecay ψ C2) :
    CanonicalSmoothedBetaLocalizedKernelCoeffDecayTargetTwo ψ C2 where
  A_ge_two := by norm_num
  C_nonneg := h.C2_nonneg
  bound := h.bound

/--
Quantitative input for the `A = 2` integration-by-parts route on the smoothed β-kernel weight
`F(β) = ψ(β) * |kernelPolyC(β)|²`.

This isolates the easy part of the second-order decay theorem:
- a trivial `L¹` bound for the zero Fourier mode;
- endpoint vanishing at `aβ, bβ`, so integration by parts carries no boundary terms;
- interval-integrability of the second derivative, which is the quantity that should appear after
  two integrations by parts on nonzero modes.

The genuinely hard analytic step is still to convert `secondDeriv_intervalIntegrable` and the
endpoint vanishing into the explicit nonzero-mode decay estimate.
-/
structure CanonicalSmoothedBetaKernelWeightSecondOrderControl
    (ψ : SmoothedBetaCutoff) (L1 C2 : ℝ) : Prop where
  L1_nonneg : 0 ≤ L1
  C2_nonneg : 0 ≤ C2
  weight_contDiff_two :
    ContDiff ℝ 2 (fun β => canonicalSmoothedBetaKernelWeight ψ β)
  weight_intervalIntegrable :
    IntervalIntegrable (fun β => canonicalSmoothedBetaKernelWeight ψ β) volume aβ bβ
  secondDeriv_intervalIntegrable :
    IntervalIntegrable
      (fun β => iteratedDeriv 2 (fun x => canonicalSmoothedBetaKernelWeight ψ x) β)
      volume aβ bβ
  vanishes_left :
    canonicalSmoothedBetaKernelWeight ψ aβ = 0
  vanishes_right :
    canonicalSmoothedBetaKernelWeight ψ bβ = 0
  deriv_vanishes_left :
    deriv (fun β => canonicalSmoothedBetaKernelWeight ψ β) aβ = 0
  deriv_vanishes_right :
    deriv (fun β => canonicalSmoothedBetaKernelWeight ψ β) bβ = 0
  l1_bound :
    ∫ β in aβ..bβ, ‖canonicalSmoothedBetaKernelWeight ψ β‖ ≤ L1
  secondDeriv_l1_bound :
    ∫ β in aβ..bβ,
        ‖iteratedDeriv 2 (fun x => canonicalSmoothedBetaKernelWeight ψ x) β‖
          ≤ C2
  l1_le_C2 : L1 ≤ C2

private noncomputable def smoothedFourierSlope (t : ℤ) : ℂ :=
  Complex.I * ((2 * Real.pi * (t : ℝ)) : ℂ)

private noncomputable def smoothedFourierPrimitive1 (t : ℤ) (β : ℝ) : ℂ :=
  (fourier (T := (1 : ℝ)) t (β : UC) : ℂ) * (smoothedFourierSlope t)⁻¹

private noncomputable def smoothedFourierPrimitive2 (t : ℤ) (β : ℝ) : ℂ :=
  smoothedFourierPrimitive1 t β * (smoothedFourierSlope t)⁻¹

private lemma smoothedFourierSlope_ne_zero {t : ℤ} (ht : t ≠ 0) :
    smoothedFourierSlope t ≠ 0 := by
  unfold smoothedFourierSlope
  refine mul_ne_zero Complex.I_ne_zero ?_
  norm_cast
  refine mul_ne_zero ?_ ?_
  · positivity
  · exact_mod_cast ht

private lemma hasDerivAt_smoothedFourierCharacter (t : ℤ) (β : ℝ) :
    HasDerivAt
      (fun x : ℝ => (fourier (T := (1 : ℝ)) t (x : UC) : ℂ))
      ((fourier (T := (1 : ℝ)) t (β : UC) : ℂ) * smoothedFourierSlope t)
      β := by
  have hlin :
      HasDerivAt
        (fun x : ℝ => (x : ℂ) * (smoothedFourierSlope t))
        (smoothedFourierSlope t) β := by
    have hlinC :
        HasDerivAt (fun z : ℂ => z * (smoothedFourierSlope t))
          (smoothedFourierSlope t) (β : ℂ) := by
      simpa using (hasDerivAt_id (β : ℂ)).mul_const (smoothedFourierSlope t)
    simpa using hlinC.comp_ofReal
  have hExp :
      HasDerivAt
        (fun x : ℝ => Complex.exp ((x : ℂ) * (smoothedFourierSlope t)))
        (Complex.exp ((β : ℂ) * (smoothedFourierSlope t)) * smoothedFourierSlope t)
        β := by
    exact hlin.cexp
  simpa [smoothedFourierSlope, Goldbach.Cert.MajorArcExponential.e,
    Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e, mul_assoc, mul_left_comm, mul_comm]
    using hExp

private lemma hasDerivAt_smoothedFourierPrimitive1 {t : ℤ} (ht : t ≠ 0) (β : ℝ) :
    HasDerivAt (smoothedFourierPrimitive1 t)
      ((fourier (T := (1 : ℝ)) t (β : UC) : ℂ)) β := by
  have hchar := hasDerivAt_smoothedFourierCharacter t β
  have hslope : smoothedFourierSlope t ≠ 0 := smoothedFourierSlope_ne_zero ht
  change HasDerivAt
    (fun y : ℝ => (fourier (T := (1 : ℝ)) t (y : UC) : ℂ) * (smoothedFourierSlope t)⁻¹)
    ((fourier (T := (1 : ℝ)) t (β : UC) : ℂ)) β
  simpa [smoothedFourierPrimitive1, hslope, mul_assoc, mul_left_comm, mul_comm]
    using hchar.mul_const ((smoothedFourierSlope t)⁻¹)

private lemma hasDerivAt_smoothedFourierPrimitive2 {t : ℤ} (ht : t ≠ 0) (β : ℝ) :
    HasDerivAt (smoothedFourierPrimitive2 t)
      (smoothedFourierPrimitive1 t β) β := by
  have hprim1 := hasDerivAt_smoothedFourierPrimitive1 ht β
  have hslope : smoothedFourierSlope t ≠ 0 := smoothedFourierSlope_ne_zero ht
  change HasDerivAt
    (fun y : ℝ => smoothedFourierPrimitive1 t y * (smoothedFourierSlope t)⁻¹)
    (smoothedFourierPrimitive1 t β) β
  simpa [smoothedFourierPrimitive2, smoothedFourierPrimitive1, hslope,
    mul_assoc, mul_left_comm, mul_comm]
    using hprim1.mul_const ((smoothedFourierSlope t)⁻¹)

private lemma norm_smoothedFourierPrimitive2_le_modeDecay {t : ℤ}
    (ht : t ≠ 0) (β : ℝ) :
    ‖smoothedFourierPrimitive2 t β‖
      ≤ 1 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2) := by
  have hslope_norm :
      ‖smoothedFourierSlope t‖ = 2 * Real.pi * (((t.natAbs : ℕ) : ℝ)) := by
    calc
      ‖smoothedFourierSlope t‖
          = ‖(((2 * Real.pi * (t : ℝ)) : ℂ))‖ := by
              simp [smoothedFourierSlope]
      _ = ‖2 * Real.pi * (t : ℝ)‖ := by
            simpa using (Complex.norm_real (2 * Real.pi * (t : ℝ)))
      _ = |2 * Real.pi * (t : ℝ)| := by
            simp [Real.norm_eq_abs]
      _ = (2 * Real.pi) * |(t : ℝ)| := by
            have hnonneg : 0 ≤ (2 * Real.pi : ℝ) := by positivity
            rw [abs_mul, abs_of_nonneg hnonneg]
      _ = 2 * Real.pi * (((t.natAbs : ℕ) : ℝ)) := by
            congr 1
            simpa using (Nat.cast_natAbs t : (((t.natAbs : ℕ) : ℝ)) = |(t : ℝ)|).symm
  have hslope_ne : smoothedFourierSlope t ≠ 0 := smoothedFourierSlope_ne_zero ht
  have hchar_norm : ‖(fourier (T := (1 : ℝ)) t (β : UC) : ℂ)‖ = 1 := by
    rw [Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e]
    simpa using Goldbach.Cert.MajorArcExponential.norm_e ((t : ℝ) * β)
  have hnat_pos : 0 < (((t.natAbs : ℕ) : ℝ)) := by
    exact_mod_cast Int.natAbs_pos.mpr ht
  have hscale_ge : 1 + (((t.natAbs : ℕ) : ℝ)) ≤ 2 * Real.pi * (((t.natAbs : ℕ) : ℝ)) := by
    have hnat_one : (1 : ℝ) ≤ (((t.natAbs : ℕ) : ℝ)) := by
      have hnat_nat : 1 ≤ t.natAbs := Nat.succ_le_of_lt (Int.natAbs_pos.mpr ht)
      exact_mod_cast hnat_nat
    have htwo : 1 + (((t.natAbs : ℕ) : ℝ)) ≤ 2 * (((t.natAbs : ℕ) : ℝ)) := by
      nlinarith
    have hpi : (2 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hmul :
        2 * (((t.natAbs : ℕ) : ℝ)) ≤ (2 * Real.pi) * (((t.natAbs : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hpi (le_of_lt hnat_pos)
    exact le_trans htwo (by simpa [mul_assoc] using hmul)
  have hscale_sq :
      (1 + (((t.natAbs : ℕ) : ℝ))) ^ 2
        ≤ (2 * Real.pi * (((t.natAbs : ℕ) : ℝ))) ^ 2 := by
    nlinarith [hscale_ge]
  have hrecip :
      ((2 * Real.pi * (((t.natAbs : ℕ) : ℝ)))⁻¹) ^ 2
        ≤ 1 / ((1 + (((t.natAbs : ℕ) : ℝ))) ^ 2) := by
    have hnum : 0 ≤ (1 : ℝ) := by positivity
    have hden : 0 < (1 + (((t.natAbs : ℕ) : ℝ))) ^ 2 := by positivity
    have :=
      div_le_div_of_nonneg_left hnum hden hscale_sq
    simpa [one_div, pow_two] using this
  calc
    ‖smoothedFourierPrimitive2 t β‖
      = ‖(smoothedFourierSlope t)⁻¹‖ ^ 2 := by
          calc
            ‖smoothedFourierPrimitive2 t β‖
                = ‖smoothedFourierPrimitive1 t β‖ * ‖(smoothedFourierSlope t)⁻¹‖ := by
                    simp [smoothedFourierPrimitive2, norm_mul]
            _ = (‖(fourier (T := (1 : ℝ)) t (β : UC) : ℂ)‖ * ‖(smoothedFourierSlope t)⁻¹‖)
                  * ‖(smoothedFourierSlope t)⁻¹‖ := by
                    simp [smoothedFourierPrimitive1, norm_mul, mul_assoc, mul_left_comm, mul_comm]
            _ = ‖(smoothedFourierSlope t)⁻¹‖ ^ 2 := by
                    rw [hchar_norm]
                    ring
    _ = ((2 * Real.pi * (((t.natAbs : ℕ) : ℝ)))⁻¹) ^ 2 := by
          rw [norm_inv, hslope_norm]
    _ ≤ 1 / ((1 + (((t.natAbs : ℕ) : ℝ))) ^ 2) := hrecip

/-- The zero Fourier mode is controlled by the `L¹` norm of the smoothed β-kernel weight. -/
theorem norm_canonicalSmoothedBetaLocalizedKernelCoeff_zero_le
    {ψ : SmoothedBetaCutoff} {L1 C2 : ℝ}
    (hctrl : CanonicalSmoothedBetaKernelWeightSecondOrderControl ψ L1 C2) :
    ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ 0‖ ≤ L1 := by
  have hnorm :=
    intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun β =>
        canonicalSmoothedBetaKernelWeight ψ β
          * (fourier (T := (1 : ℝ)) (0 : ℤ) (β : UC) : ℂ))
      (a := aβ) (b := bβ)
  calc
    ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ 0‖
      = ‖∫ β in aβ..bβ,
          canonicalSmoothedBetaKernelWeight ψ β
            * (fourier (T := (1 : ℝ)) (0 : ℤ) (β : UC) : ℂ)‖ := by
            rfl
    _ ≤ ∫ β in aβ..bβ,
          ‖canonicalSmoothedBetaKernelWeight ψ β
            * (fourier (T := (1 : ℝ)) (0 : ℤ) (β : UC) : ℂ)‖ := hnorm hle
    _ = ∫ β in aβ..bβ, ‖canonicalSmoothedBetaKernelWeight ψ β‖ := by
          congr 1
          ext β
          simp
    _ ≤ L1 := hctrl.l1_bound

/-- Two integrations by parts give second-order decay for every nonzero Fourier mode. -/
private theorem norm_canonicalSmoothedBetaLocalizedKernelCoeff_nonzero_le
    {ψ : SmoothedBetaCutoff} {L1 C2 : ℝ} {t : ℤ}
    (hctrl : CanonicalSmoothedBetaKernelWeightSecondOrderControl ψ L1 C2)
    (ht : t ≠ 0) :
    ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ t‖
      ≤ C2 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2) := by
  let W : ℝ → ℂ := fun β => canonicalSmoothedBetaKernelWeight ψ β
  have hW1 : ContDiff ℝ 1 W := hctrl.weight_contDiff_two.of_le (by norm_num)
  have hWdiff : Differentiable ℝ W := (contDiff_one_iff_deriv.mp hW1).1
  have hWderivCont : Continuous (deriv W) := (contDiff_one_iff_deriv.mp hW1).2
  have hWderiv1 : ContDiff ℝ 1 (deriv W) := by
    simpa using (contDiff_succ_iff_deriv.mp hctrl.weight_contDiff_two).2.2
  have hWddiff : Differentiable ℝ (deriv W) := (contDiff_one_iff_deriv.mp hWderiv1).1
  have hcharCont : Continuous (fun β : ℝ => (fourier (T := (1 : ℝ)) t (β : UC) : ℂ)) := by
    refine continuous_iff_continuousAt.mpr ?_
    intro β
    exact (hasDerivAt_smoothedFourierCharacter t β).continuousAt
  have hprim1Cont : Continuous (smoothedFourierPrimitive1 t) := by
    refine continuous_iff_continuousAt.mpr ?_
    intro β
    exact (hasDerivAt_smoothedFourierPrimitive1 ht β).continuousAt
  have hprim2Cont : Continuous (smoothedFourierPrimitive2 t) := by
    refine continuous_iff_continuousAt.mpr ?_
    intro β
    exact (hasDerivAt_smoothedFourierPrimitive2 ht β).continuousAt
  have hW'Int : IntervalIntegrable (fun β => deriv W β) volume aβ bβ :=
    hWderivCont.intervalIntegrable aβ bβ
  have hcharInt :
      IntervalIntegrable
        (fun β : ℝ => (fourier (T := (1 : ℝ)) t (β : UC) : ℂ))
        volume aβ bβ :=
    hcharCont.intervalIntegrable aβ bβ
  have hprim1Int : IntervalIntegrable (smoothedFourierPrimitive1 t) volume aβ bβ :=
    hprim1Cont.intervalIntegrable aβ bβ
  have hprim2NormInt :
      IntervalIntegrable
        (fun β => ‖iteratedDeriv 2 W β‖ * ‖smoothedFourierPrimitive2 t β‖)
        volume aβ bβ := by
    have hA :
        IntervalIntegrable (fun β => ‖iteratedDeriv 2 W β‖) volume aβ bβ :=
      hctrl.secondDeriv_intervalIntegrable.norm
    exact hA.mul_continuousOn hprim2Cont.norm.continuousOn
  have hAconstInt :
      IntervalIntegrable
        (fun β =>
          ‖iteratedDeriv 2 W β‖ * (1 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2)))
        volume aβ bβ := by
    exact hctrl.secondDeriv_intervalIntegrable.norm.mul_const
      (1 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2))
  have hu1 :
      ∀ x ∈ [[aβ, bβ]], HasDerivAt W (deriv W x) x := by
    intro x hx
    exact (hWdiff x).hasDerivAt
  have hv1 :
      ∀ x ∈ [[aβ, bβ]],
        HasDerivAt (smoothedFourierPrimitive1 t)
          ((fourier (T := (1 : ℝ)) t (x : UC) : ℂ)) x := by
    intro x hx
    exact hasDerivAt_smoothedFourierPrimitive1 ht x
  have hu2 :
      ∀ x ∈ [[aβ, bβ]], HasDerivAt (deriv W) (iteratedDeriv 2 W x) x := by
    intro x hx
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using (hWddiff x).hasDerivAt
  have hv2 :
      ∀ x ∈ [[aβ, bβ]],
        HasDerivAt (smoothedFourierPrimitive2 t) (smoothedFourierPrimitive1 t x) x := by
    intro x hx
    exact hasDerivAt_smoothedFourierPrimitive2 ht x
  have hIBP1 :
      ∫ β in aβ..bβ, W β * (fourier (T := (1 : ℝ)) t (β : UC) : ℂ)
        =
      W bβ * smoothedFourierPrimitive1 t bβ
        - W aβ * smoothedFourierPrimitive1 t aβ
        - ∫ β in aβ..bβ, deriv W β * smoothedFourierPrimitive1 t β := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := W) (u' := fun β => deriv W β)
      (v := smoothedFourierPrimitive1 t)
      (v' := fun β => (fourier (T := (1 : ℝ)) t (β : UC) : ℂ))
      hu1 hv1 hW'Int hcharInt
  have hIBP2 :
      ∫ β in aβ..bβ, deriv W β * smoothedFourierPrimitive1 t β
        =
      deriv W bβ * smoothedFourierPrimitive2 t bβ
        - deriv W aβ * smoothedFourierPrimitive2 t aβ
        - ∫ β in aβ..bβ, iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun β => deriv W β)
      (u' := fun β => iteratedDeriv 2 W β)
      (v := smoothedFourierPrimitive2 t)
      (v' := smoothedFourierPrimitive1 t)
      hu2 hv2 hctrl.secondDeriv_intervalIntegrable hprim1Int
  have hcollapse :
      canonicalSmoothedBetaLocalizedKernelCoeff ψ t
        =
      ∫ β in aβ..bβ, iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β := by
    calc
      canonicalSmoothedBetaLocalizedKernelCoeff ψ t
        = ∫ β in aβ..bβ, W β * (fourier (T := (1 : ℝ)) t (β : UC) : ℂ) := by
            rfl
      _ = - ∫ β in aβ..bβ, deriv W β * smoothedFourierPrimitive1 t β := by
            simpa [W, hctrl.vanishes_left, hctrl.vanishes_right] using hIBP1
      _ = - (-
            ∫ β in aβ..bβ, iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β) := by
            rw [hIBP2]
            simp [W, hctrl.deriv_vanishes_left, hctrl.deriv_vanishes_right]
      _ = ∫ β in aβ..bβ, iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β := by
            ring
  calc
    ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ t‖
      = ‖∫ β in aβ..bβ, iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β‖ := by
          rw [hcollapse]
    _ ≤ ∫ β in aβ..bβ, ‖iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β‖ := by
          have hnorm :=
            intervalIntegral.norm_integral_le_integral_norm (μ := volume)
              (f := fun β => iteratedDeriv 2 W β * smoothedFourierPrimitive2 t β)
              (a := aβ) (b := bβ)
          exact hnorm hle
    _ = ∫ β in aβ..bβ, ‖iteratedDeriv 2 W β‖ * ‖smoothedFourierPrimitive2 t β‖ := by
          congr 1
          ext β
          rw [norm_mul]
    _ ≤ ∫ β in aβ..bβ,
          ‖iteratedDeriv 2 W β‖ * (1 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2)) := by
            exact intervalIntegral.integral_mono_on (μ := volume) (a := aβ) (b := bβ)
              hle hprim2NormInt hAconstInt
              (by
                intro β hβ
                exact mul_le_mul_of_nonneg_left
                  (norm_smoothedFourierPrimitive2_le_modeDecay ht β)
                  (norm_nonneg _))
    _ = (1 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2))
          * ∫ β in aβ..bβ, ‖iteratedDeriv 2 W β‖ := by
            rw [intervalIntegral.integral_mul_const, mul_comm]
    _ ≤ (1 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2)) * C2 := by
          exact mul_le_mul_of_nonneg_left hctrl.secondDeriv_l1_bound (by positivity)
    _ = C2 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 2) := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Complete `A = 2` coefficient decay from the second-order smoothed weight control package. -/
theorem canonicalSmoothedBetaLocalizedKernelCoeffSecondOrderDecay_of_control
    {ψ : SmoothedBetaCutoff} {L1 C2 : ℝ}
    (hctrl : CanonicalSmoothedBetaKernelWeightSecondOrderControl ψ L1 C2) :
    CanonicalSmoothedBetaLocalizedKernelCoeffSecondOrderDecay ψ C2 where
  C2_nonneg := hctrl.C2_nonneg
  bound := by
    intro t
    by_cases ht : t = 0
    · subst ht
      calc
        ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ 0‖ ≤ L1 :=
          norm_canonicalSmoothedBetaLocalizedKernelCoeff_zero_le hctrl
        _ ≤ C2 := hctrl.l1_le_C2
        _ = C2 / ((1 + (((0 : ℤ).natAbs : ℕ) : ℝ)) ^ 2) := by norm_num
    · exact norm_canonicalSmoothedBetaLocalizedKernelCoeff_nonzero_le hctrl ht

/-- `A = 2` decay target for the squared-cutoff coefficient. -/
abbrev CanonicalSmoothedBetaSquaredLocalizedKernelCoeffDecayTargetTwo
    (ψ : SmoothedBetaCutoff) (C : ℝ) : Prop :=
  CanonicalSmoothedBetaLocalizedKernelCoeffDecayTargetTwo ψ.squared C

/-- Quantitative second-order decay surface for the squared-cutoff coefficient. -/
abbrev CanonicalSmoothedBetaSquaredLocalizedKernelCoeffSecondOrderDecay
    (ψ : SmoothedBetaCutoff) (C2 : ℝ) : Prop :=
  CanonicalSmoothedBetaLocalizedKernelCoeffSecondOrderDecay ψ.squared C2

/-- Second-order control package for the squared-cutoff β-kernel weight. -/
abbrev CanonicalSmoothedBetaSquaredKernelWeightSecondOrderControl
    (ψ : SmoothedBetaCutoff) (L1 C2 : ℝ) : Prop :=
  CanonicalSmoothedBetaKernelWeightSecondOrderControl ψ.squared L1 C2

/-- Package a proved squared-cutoff second-order estimate as the fixed `A = 2` decay target. -/
theorem canonicalSmoothedBetaSquaredLocalizedKernelCoeffDecayTarget_two
    {ψ : SmoothedBetaCutoff} {C2 : ℝ}
    (h : CanonicalSmoothedBetaSquaredLocalizedKernelCoeffSecondOrderDecay ψ C2) :
    CanonicalSmoothedBetaSquaredLocalizedKernelCoeffDecayTargetTwo ψ C2 :=
  canonicalSmoothedBetaLocalizedKernelCoeffDecayTarget_two h

/--
Complete squared-cutoff `A = 2` coefficient decay from the second-order smoothed weight control
package.
-/
theorem canonicalSmoothedBetaSquaredLocalizedKernelCoeffSecondOrderDecay_of_control
    {ψ : SmoothedBetaCutoff} {L1 C2 : ℝ}
    (hctrl : CanonicalSmoothedBetaSquaredKernelWeightSecondOrderControl ψ L1 C2) :
    CanonicalSmoothedBetaSquaredLocalizedKernelCoeffSecondOrderDecay ψ C2 :=
  canonicalSmoothedBetaLocalizedKernelCoeffSecondOrderDecay_of_control hctrl

/--
Third-order coefficient-decay data.

This should only be filled after the `A = 2` scale audit, if the smoothed mode sum still needs an
extra summability margin.
-/
structure CanonicalSmoothedBetaLocalizedKernelCoeffThirdOrderDecay
    (ψ : SmoothedBetaCutoff) (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ t : ℤ,
      ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ t‖
        ≤ C3 / ((1 + ((t.natAbs : ℕ) : ℝ)) ^ 3)

/-- Package a proved third-order coefficient estimate as the fixed `A = 3` decay target. -/
theorem canonicalSmoothedBetaLocalizedKernelCoeffDecayTarget_three
    {ψ : SmoothedBetaCutoff} {C3 : ℝ}
    (h : CanonicalSmoothedBetaLocalizedKernelCoeffThirdOrderDecay ψ C3) :
    CanonicalSmoothedBetaLocalizedKernelCoeffDecayTargetThree ψ C3 where
  A_ge_two := by norm_num
  C_nonneg := h.C3_nonneg
  bound := h.bound

/--
All-orders coefficient decay surface for the smoothed branch.

This is the natural analytic input for a summable mode-sum / TT* rebuild.
-/
structure CanonicalSmoothedBetaLocalizedKernelCoeffRapidDecayTarget
    (ψ : SmoothedBetaCutoff) (coeffConst : ℕ → ℝ) : Prop where
  coeffConst_nonneg : ∀ A, 0 ≤ coeffConst A
  bound :
    ∀ ⦃A : ℕ⦄, 2 ≤ A →
      CanonicalSmoothedBetaLocalizedKernelCoeffDecayTarget ψ A (coeffConst A)

private lemma canonicalSmoothedBetaFrequencyFactor_eq_fourier
    (β : ℝ) (n m n' m' : ℕ) :
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp β m'))
      =
    (fourier (T := (1 : ℝ))
      (((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ))) (β : UC) : ℂ) := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp
    Goldbach.Cert.MajorArcExponential.e
  simp [fourier_apply, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  repeat rw [← Complex.exp_add]
  congr 1
  ring_nf

/--
Smoothed termwise β-collapse for the moving-moving kernel.

This is the smoothed analogue of the sharp localized-coefficient collapse: once the β-frequency
factors are regrouped, the β-integral produces the smoothed localized kernel coefficient at the
integer difference mode `n - m - n' + m'`.
-/
theorem canonicalSmoothedJointFreezeDiscrepancy_movingMovingTerm_betaCollapse
    (ψ : SmoothedBetaCutoff) (θ θ' : ℝ) (n m n' m' : ℕ) :
    (∫ β in aβ..bβ,
      canonicalSmoothedBetaKernelWeight ψ β
        *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m'))))
      =
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') m'))
      * canonicalSmoothedBetaLocalizedKernelCoeff ψ
          (((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ))) := by
  let c : ℂ :=
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') m'))
  change
    (∫ β in aβ..bβ,
      canonicalSmoothedBetaKernelWeight ψ β
        *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m'))))
      =
    c * canonicalSmoothedBetaLocalizedKernelCoeff ψ
          (((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ)))
  unfold canonicalSmoothedBetaLocalizedKernelCoeff
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro β hβ
  change
    canonicalSmoothedBetaKernelWeight ψ β *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')))
      =
    c * (canonicalSmoothedBetaKernelWeight ψ β
      * (fourier (T := (1 : ℝ)) (↑n - ↑m - ↑n' + ↑m') (β : UC) : ℂ))
  rw [canonicalJointFreezeDiscrepancyBetaQMovingTerm_mul_star_factorized]
  rw [canonicalSmoothedBetaFrequencyFactor_eq_fourier]
  change
    canonicalSmoothedBetaKernelWeight ψ β *
        (c * (fourier (T := (1 : ℝ)) (↑n - ↑m - ↑n' + ↑m') (β : UC) : ℂ))
      =
    c *
      (canonicalSmoothedBetaKernelWeight ψ β *
        (fourier (T := (1 : ℝ)) (↑n - ↑m - ↑n' + ↑m') (β : UC) : ℂ))
  ring

/-- Raw ordered-pair endpoint for the fully smoothed joint freeze discrepancy. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyBetaPairEndpoint
    (X N M : ℕ) (β : ℝ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X N β
    - canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X M β

/--
Smoothed pre-absolute ordered-pair β-integrand.

Unlike the frozen sharp branch, this uses the smooth cutoff as the actual analytic endpoint.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyBetaPreAbsoluteIntegrand
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) (β : ℝ) : ℂ :=
  ((ψ.psi β : ℝ) : ℂ)
    * canonicalSmoothedJointFreezeDiscrepancyBetaPairEndpoint X N M β

/-- The exact pair endpoint written as a unified finite q-sum, with the smoothed cutoff outside. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) (β : ℝ) : ℂ :=
  ((ψ.psi β : ℝ) : ℂ)
    * canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint X N M β

theorem canonicalSmoothedJointFreezeDiscrepancyBetaPreAbsoluteIntegrand_eq_qsum
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) (β : ℝ) :
    canonicalSmoothedJointFreezeDiscrepancyBetaPreAbsoluteIntegrand ψ X N M β
      =
    canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint ψ X N M β := by
  unfold canonicalSmoothedJointFreezeDiscrepancyBetaPreAbsoluteIntegrand
    canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint
    canonicalSmoothedJointFreezeDiscrepancyBetaPairEndpoint
    canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint
  rw [canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint_eq_sum_qAtom,
    canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint_eq_sum_qAtom]
  simp [Finset.sum_sub_distrib]

/-- Global ordered-pair smoothed β-integrand with the q-sum still inside the norm square. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
    (ψ : SmoothedBetaCutoff) (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ‖canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint ψ X N M β‖ ^ 2
      else 0

/-- Global ordered-pair smoothed β-integrand. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand
    (ψ : SmoothedBetaCutoff) (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ‖canonicalSmoothedJointFreezeDiscrepancyBetaPreAbsoluteIntegrand ψ X N M β‖ ^ 2
      else 0

theorem canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand_eq_qsum
    (ψ : SmoothedBetaCutoff) (X : ℕ) (β : ℝ) :
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand ψ X β
      =
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand ψ X β := by
  unfold canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM,
      canonicalSmoothedJointFreezeDiscrepancyBetaPreAbsoluteIntegrand_eq_qsum]
  · simp [hNM]

/-- Smoothed double-q expansion of the square, with the smooth cutoff weight outside. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyBetaDoubleQSquareExpansion
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) (β : ℝ) : ℝ :=
  (ψ.psi β) ^ 2
    * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ q' ∈ Finset.Icc (1 : ℕ) Q0,
          canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β

private lemma canonicalSmoothedCutoff_norm_sq
    (ψ : SmoothedBetaCutoff) (β : ℝ) (z : ℂ) :
    ‖(((ψ.psi β : ℝ) : ℂ) * z)‖ ^ 2
      =
    (ψ.psi β) ^ 2 * ‖z‖ ^ 2 := by
  have hψ : ‖((ψ.psi β : ℝ) : ℂ)‖ = ψ.psi β := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ψ.nonneg β)]
  rw [norm_mul, hψ]
  ring

theorem norm_sq_canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) (β : ℝ) :
    ‖canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint ψ X N M β‖ ^ 2
      =
    canonicalSmoothedJointFreezeDiscrepancyBetaDoubleQSquareExpansion ψ X N M β := by
  unfold canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint
    canonicalSmoothedJointFreezeDiscrepancyBetaDoubleQSquareExpansion
  rw [canonicalSmoothedCutoff_norm_sq]
  rw [norm_sq_canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ]

/-- The global β-integrand after expanding the smoothed q-sum square into q/q′ atoms. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand
    (ψ : SmoothedBetaCutoff) (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        canonicalSmoothedJointFreezeDiscrepancyBetaDoubleQSquareExpansion ψ X N M β
      else 0

theorem canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand_eq_doubleQ
    (ψ : SmoothedBetaCutoff) (X : ℕ) (β : ℝ) :
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand ψ X β
      =
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand ψ X β := by
  unfold canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM,
      norm_sq_canonicalSmoothedJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ]
  · simp [hNM]

theorem canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand_eq_doubleQ
    (ψ : SmoothedBetaCutoff) (X : ℕ) (β : ℝ) :
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand ψ X β
      =
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand ψ X β := by
  calc
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand ψ X β
      =
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand ψ X β :=
      canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand_eq_qsum ψ X β
    _ =
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand ψ X β :=
      canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand_eq_doubleQ ψ X β

/-- Global ordered-pair smoothed β-energy. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℝ :=
  ∫ β in aβ..bβ,
    canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand ψ X β

/--
Abstract mode weights for the smoothed mode-sum audit.

This is the first post-decay bottleneck: after regrouping the smoothed global β-energy by the
integer difference mode `r`, the size of these weights decides whether the summable
`(1 + |r|)^{-2}` coefficient decay is actually strong enough at route scale.
-/
structure CanonicalSmoothedJointFreezeDiscrepancyModeSumExpansion
    (ψ : SmoothedBetaCutoff) (modeWeight : ℕ → ℤ → ℝ) : Prop where
  modeWeight_nonneg : ∀ X r, 0 ≤ modeWeight X r
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy ψ X
        ≤
      ∑' r : ℤ,
        modeWeight X r * ‖canonicalSmoothedBetaLocalizedKernelCoeff ψ r‖

/--
Route-sized mode-weight audit target for the smoothed branch at second-order coefficient decay.

This is the precise place where the `A = 2` audit lives: the smoothed branch proceeds only if the
regrouped mode weights are mild enough that summable `(1 + |r|)^{-2}` decay closes the route
target.
-/
structure CanonicalSmoothedJointFreezeDiscrepancyModeWeightTargetTwo
    (modeWeight : ℕ → ℤ → ℝ) (C2 Csm : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  Csm_nonneg : 0 ≤ Csm
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑' r : ℤ,
        modeWeight X r * (C2 / ((1 + ((r.natAbs : ℕ) : ℝ)) ^ 2)))
        ≤
      12 * (((EvenIn X H).card : ℝ)
        * (Csm / ((H : ℝ) * ((Q0 : ℕ) : ℝ) ^ 2)))

/--
Raw box of one-dimensional finite-sum indices of length `L + 1`.

This is a model for the eventual smoothed mode regrouping: before arithmetic amplitudes are
inserted, the difference mode `r` is carried by quadruples of indices in a finite box.
-/
noncomputable def canonicalSmoothedDifferenceModeBox (L : ℕ) : Finset ℕ :=
  Finset.range (L + 1)

/--
Quadruples in the length-`L + 1` box with fixed difference mode
`r = n - m - n' + m'`.

This is the first purely combinatorial mode-weight model for the smoothed audit.
-/
noncomputable def canonicalSmoothedDifferenceModeQuadruples
    (L : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((canonicalSmoothedDifferenceModeBox L).product (canonicalSmoothedDifferenceModeBox L)).product
      ((canonicalSmoothedDifferenceModeBox L).product (canonicalSmoothedDifferenceModeBox L))).filter
    (fun x =>
      (((x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ)) = r))

/-- The associated raw combinatorial difference-mode weight. -/
noncomputable def canonicalSmoothedDifferenceModeWeight (L : ℕ) (r : ℤ) : ℝ :=
  (canonicalSmoothedDifferenceModeQuadruples L r).card

/-- The difference mode carried by a quadruple of finite-sum indices. -/
noncomputable def canonicalSmoothedDifferenceMode
    (x : ((ℕ × ℕ) × (ℕ × ℕ))) : ℤ :=
  ((x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ))

/-- Finite range of possible difference modes for a box of length `L + 1`. -/
noncomputable def canonicalSmoothedDifferenceModeRange (L : ℕ) : Finset ℤ :=
  Finset.Icc (-((2 * L : ℕ) : ℤ)) ((2 * L : ℕ) : ℤ)

private lemma canonicalSmoothedDifferenceMode_mem_range
    (L : ℕ) (x : ((ℕ × ℕ) × (ℕ × ℕ)))
    (hx : x ∈
      (((canonicalSmoothedDifferenceModeBox L).product
          (canonicalSmoothedDifferenceModeBox L)).product
        ((canonicalSmoothedDifferenceModeBox L).product
          (canonicalSmoothedDifferenceModeBox L)))) :
    canonicalSmoothedDifferenceMode x ∈ canonicalSmoothedDifferenceModeRange L := by
  rcases Finset.mem_product.mp hx with ⟨hab, hcd⟩
  rcases Finset.mem_product.mp hab with ⟨hn, hm⟩
  rcases Finset.mem_product.mp hcd with ⟨hn', hm'⟩
  have hn_le : x.1.1 ≤ L := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hm_le : x.1.2 ≤ L := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hn'_le : x.2.1 ≤ L := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
  have hm'_le : x.2.2 ≤ L := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')
  have hupper :
      canonicalSmoothedDifferenceMode x ≤ ((2 * L : ℕ) : ℤ) := by
    change (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ) ≤ ((2 * L : ℕ) : ℤ)
    have h1 : (x.1.1 : ℤ) - (x.1.2 : ℤ) ≤ (L : ℤ) := by
      have hx12 : (x.1.2 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      have hx11 : (x.1.1 : ℤ) ≤ L := by exact_mod_cast hn_le
      linarith
    have h2 : -((x.2.1 : ℤ)) + (x.2.2 : ℤ) ≤ (L : ℤ) := by
      have hx21 : (x.2.1 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      have hx22 : (x.2.2 : ℤ) ≤ L := by exact_mod_cast hm'_le
      linarith
    have hsum : (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ) ≤ (L : ℤ) + (L : ℤ) := by
      linarith
    simpa [two_mul] using hsum
  have hlower :
      -((2 * L : ℕ) : ℤ) ≤ canonicalSmoothedDifferenceMode x := by
    change -((2 * L : ℕ) : ℤ) ≤ (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ)
    have h1 : -((L : ℤ)) ≤ (x.1.1 : ℤ) - (x.1.2 : ℤ) := by
      have hx11 : (x.1.1 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      have hx12 : (x.1.2 : ℤ) ≤ L := by exact_mod_cast hm_le
      linarith
    have h2 : -((L : ℤ)) ≤ -((x.2.1 : ℤ)) + (x.2.2 : ℤ) := by
      have hx21 : (x.2.1 : ℤ) ≤ L := by exact_mod_cast hn'_le
      have hx22 : (x.2.2 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      linarith
    have hsum : -((L : ℤ)) + -((L : ℤ)) ≤ (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ) := by
      linarith
    simpa [two_mul] using hsum
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

/--
Exact fiberwise regrouping of the raw difference-mode box by the single mode `r`.

This is the purely combinatorial model for the smoothed mode-sum expansion: once a summand depends
only on `r = n - m - n' + m'`, the quadruple sum can be regrouped exactly into a mode sum.
-/
theorem sum_canonicalSmoothedDifferenceMode_fiberwise
    (L : ℕ) (f : ℤ → ℂ) :
    Finset.sum
      (((canonicalSmoothedDifferenceModeBox L).product
          (canonicalSmoothedDifferenceModeBox L)).product
        ((canonicalSmoothedDifferenceModeBox L).product
          (canonicalSmoothedDifferenceModeBox L)))
      (fun x => f (canonicalSmoothedDifferenceMode x)) =
    Finset.sum (canonicalSmoothedDifferenceModeRange L)
      (fun r => ((canonicalSmoothedDifferenceModeQuadruples L r).card : ℂ) * f r) := by
  classical
  let s :
      Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)).product
      ((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)))
  have hmaps :
      ∀ x ∈ s, canonicalSmoothedDifferenceMode x ∈ canonicalSmoothedDifferenceModeRange L := by
    intro x hx
    exact canonicalSmoothedDifferenceMode_mem_range L x hx
  calc
    Finset.sum s (fun x => f (canonicalSmoothedDifferenceMode x))
      = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r => Finset.sum (s.filter fun x => canonicalSmoothedDifferenceMode x = r)
            (fun x => f (canonicalSmoothedDifferenceMode x))) := by
            simpa [s] using
              (Finset.sum_fiberwise_of_maps_to
                (s := s) (t := canonicalSmoothedDifferenceModeRange L)
                (g := canonicalSmoothedDifferenceMode)
                (f := fun x : ((ℕ × ℕ) × (ℕ × ℕ)) => f (canonicalSmoothedDifferenceMode x))
                hmaps).symm
    _ = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r => Finset.sum (canonicalSmoothedDifferenceModeQuadruples L r) (fun _ => f r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hfilter :
                s.filter (fun x => canonicalSmoothedDifferenceMode x = r) =
                  canonicalSmoothedDifferenceModeQuadruples L r := by
              ext x
              simp [s, canonicalSmoothedDifferenceModeQuadruples, canonicalSmoothedDifferenceMode]
            rw [hfilter]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxmode : canonicalSmoothedDifferenceMode x = r := by
              simp [canonicalSmoothedDifferenceModeQuadruples] at hx
              exact hx.2
            simp [hxmode]
    _ = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r => ((canonicalSmoothedDifferenceModeQuadruples L r).card : ℂ) * f r) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/--
Weighted fiber sum on the difference-mode box.

This is the exact arithmetic weight carried by a mode `r` once a quadruple summand has been
collapsed to something of the form `amplitude x * coeff (mode x)`.
-/
noncomputable def canonicalSmoothedDifferenceModeFiberWeight
    (L : ℕ) (amplitude : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) (r : ℤ) : ℂ :=
  Finset.sum (canonicalSmoothedDifferenceModeQuadruples L r) amplitude

/--
Exact weighted fiberwise regrouping by the single difference mode `r`.

This is the algebraic form needed for the smoothed mode-sum branch: once the β-collapse has turned
the oscillatory coefficient into `coeff (mode x)`, all remaining arithmetic data is pushed into the
weighted fiber sum.
-/
theorem sum_canonicalSmoothedDifferenceMode_fiberwise_weighted
    (L : ℕ) (amplitude : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) (coeff : ℤ → ℂ) :
    Finset.sum
      (((canonicalSmoothedDifferenceModeBox L).product
          (canonicalSmoothedDifferenceModeBox L)).product
        ((canonicalSmoothedDifferenceModeBox L).product
          (canonicalSmoothedDifferenceModeBox L)))
      (fun x => amplitude x * coeff (canonicalSmoothedDifferenceMode x)) =
    Finset.sum (canonicalSmoothedDifferenceModeRange L)
      (fun r => canonicalSmoothedDifferenceModeFiberWeight L amplitude r * coeff r) := by
  classical
  let s :
      Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)).product
      ((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)))
  have hmaps :
      ∀ x ∈ s, canonicalSmoothedDifferenceMode x ∈ canonicalSmoothedDifferenceModeRange L := by
    intro x hx
    exact canonicalSmoothedDifferenceMode_mem_range L x hx
  calc
    Finset.sum s (fun x => amplitude x * coeff (canonicalSmoothedDifferenceMode x))
      = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r => Finset.sum (s.filter fun x => canonicalSmoothedDifferenceMode x = r)
            (fun x => amplitude x * coeff (canonicalSmoothedDifferenceMode x))) := by
            simpa [s] using
              (Finset.sum_fiberwise_of_maps_to
                (s := s) (t := canonicalSmoothedDifferenceModeRange L)
                (g := canonicalSmoothedDifferenceMode)
                (f := fun x : ((ℕ × ℕ) × (ℕ × ℕ)) =>
                  amplitude x * coeff (canonicalSmoothedDifferenceMode x))
                hmaps).symm
    _ = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r =>
            Finset.sum (canonicalSmoothedDifferenceModeQuadruples L r)
              (fun x => amplitude x * coeff r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hfilter :
                s.filter (fun x => canonicalSmoothedDifferenceMode x = r) =
                  canonicalSmoothedDifferenceModeQuadruples L r := by
              ext x
              simp [s, canonicalSmoothedDifferenceModeQuadruples, canonicalSmoothedDifferenceMode]
            rw [hfilter]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxmode : canonicalSmoothedDifferenceMode x = r := by
              simp [canonicalSmoothedDifferenceModeQuadruples] at hx
              exact hx.2
            simp [hxmode]
    _ = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r =>
            (Finset.sum (canonicalSmoothedDifferenceModeQuadruples L r) amplitude) * coeff r) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [← Finset.sum_mul]
    _ = Finset.sum (canonicalSmoothedDifferenceModeRange L)
          (fun r => canonicalSmoothedDifferenceModeFiberWeight L amplitude r * coeff r) := by
            simp [canonicalSmoothedDifferenceModeFiberWeight]

/--
Mixed-length rectangle quadruples with fixed difference mode
`r = n - m - n' + m'`.

The first pair of indices ranges over the `L₁`-box and the second pair over the `L₂`-box.
-/
noncomputable def canonicalSmoothedDifferenceModeRectQuadruples
    (L₁ L₂ : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((canonicalSmoothedDifferenceModeBox L₁).product (canonicalSmoothedDifferenceModeBox L₁)).product
      ((canonicalSmoothedDifferenceModeBox L₂).product (canonicalSmoothedDifferenceModeBox L₂))).filter
    (fun x => canonicalSmoothedDifferenceMode x = r)

/-- Finite range of possible difference modes for a mixed-length rectangle. -/
noncomputable def canonicalSmoothedDifferenceModeRectRange (L₁ L₂ : ℕ) : Finset ℤ :=
  Finset.Icc (-(((L₁ + L₂ : ℕ)) : ℤ)) (((L₁ + L₂ : ℕ)) : ℤ)

private lemma canonicalSmoothedDifferenceMode_mem_rect_range
    (L₁ L₂ : ℕ) (x : ((ℕ × ℕ) × (ℕ × ℕ)))
    (hx : x ∈
      (((canonicalSmoothedDifferenceModeBox L₁).product
          (canonicalSmoothedDifferenceModeBox L₁)).product
        ((canonicalSmoothedDifferenceModeBox L₂).product
          (canonicalSmoothedDifferenceModeBox L₂)))) :
    canonicalSmoothedDifferenceMode x ∈ canonicalSmoothedDifferenceModeRectRange L₁ L₂ := by
  rcases Finset.mem_product.mp hx with ⟨hab, hcd⟩
  rcases Finset.mem_product.mp hab with ⟨hn, hm⟩
  rcases Finset.mem_product.mp hcd with ⟨hn', hm'⟩
  have hn_le : x.1.1 ≤ L₁ := by exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hm_le : x.1.2 ≤ L₁ := by exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hn'_le : x.2.1 ≤ L₂ := by exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
  have hm'_le : x.2.2 ≤ L₂ := by exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')
  have hupper :
      canonicalSmoothedDifferenceMode x ≤ (((L₁ + L₂ : ℕ)) : ℤ) := by
    change (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ) ≤ (((L₁ + L₂ : ℕ)) : ℤ)
    have h1 : (x.1.1 : ℤ) - (x.1.2 : ℤ) ≤ (L₁ : ℤ) := by
      have hx12 : (x.1.2 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      have hx11 : (x.1.1 : ℤ) ≤ L₁ := by exact_mod_cast hn_le
      linarith
    have h2 : -((x.2.1 : ℤ)) + (x.2.2 : ℤ) ≤ (L₂ : ℤ) := by
      have hx21 : (x.2.1 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      have hx22 : (x.2.2 : ℤ) ≤ L₂ := by exact_mod_cast hm'_le
      linarith
    have hsum : (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ) ≤ (L₁ : ℤ) + (L₂ : ℤ) := by
      linarith
    simpa [Nat.cast_add] using hsum
  have hlower :
      -((((L₁ + L₂ : ℕ)) : ℤ)) ≤ canonicalSmoothedDifferenceMode x := by
    change -((((L₁ + L₂ : ℕ)) : ℤ)) ≤ (x.1.1 : ℤ) - (x.1.2 : ℤ) - (x.2.1 : ℤ) + (x.2.2 : ℤ)
    have h1 : -((L₁ : ℤ)) ≤ (x.1.1 : ℤ) - (x.1.2 : ℤ) := by
      have hx11 : (x.1.1 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      have hx12 : (x.1.2 : ℤ) ≤ L₁ := by exact_mod_cast hm_le
      linarith
    have h2 : -((L₂ : ℤ)) ≤ -((x.2.1 : ℤ)) + (x.2.2 : ℤ) := by
      have hx21 : (x.2.1 : ℤ) ≤ L₂ := by exact_mod_cast hn'_le
      have hx22 : (x.2.2 : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le _)
      linarith
    have hcast : ((((L₁ + L₂ : ℕ)) : ℤ)) = (L₁ : ℤ) + (L₂ : ℤ) := by
      simp [Nat.cast_add]
    linarith
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

/-- Weighted fiber sum on a mixed-length rectangle. -/
noncomputable def canonicalSmoothedDifferenceModeRectFiberWeight
    (L₁ L₂ : ℕ) (amplitude : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) (r : ℤ) : ℂ :=
  Finset.sum (canonicalSmoothedDifferenceModeRectQuadruples L₁ L₂ r) amplitude

/--
Exact weighted fiberwise regrouping for the mixed-length rectangle.

This is the rectangle analogue of `sum_canonicalSmoothedDifferenceMode_fiberwise_weighted`, and is
the correct transport layer for the `NN - NM - MN + MM` decomposition.
-/
theorem sum_canonicalSmoothedDifferenceMode_rect_fiberwise_weighted
    (L₁ L₂ : ℕ) (amplitude : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) (coeff : ℤ → ℂ) :
    Finset.sum
      (((canonicalSmoothedDifferenceModeBox L₁).product
          (canonicalSmoothedDifferenceModeBox L₁)).product
        ((canonicalSmoothedDifferenceModeBox L₂).product
          (canonicalSmoothedDifferenceModeBox L₂)))
      (fun x => amplitude x * coeff (canonicalSmoothedDifferenceMode x)) =
    Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
      (fun r => canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂ amplitude r * coeff r) := by
  classical
  let s :
      Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((canonicalSmoothedDifferenceModeBox L₁).product
        (canonicalSmoothedDifferenceModeBox L₁)).product
      ((canonicalSmoothedDifferenceModeBox L₂).product
        (canonicalSmoothedDifferenceModeBox L₂)))
  have hmaps :
      ∀ x ∈ s, canonicalSmoothedDifferenceMode x ∈ canonicalSmoothedDifferenceModeRectRange L₁ L₂ := by
    intro x hx
    exact canonicalSmoothedDifferenceMode_mem_rect_range L₁ L₂ x hx
  calc
    Finset.sum s (fun x => amplitude x * coeff (canonicalSmoothedDifferenceMode x))
      = Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
          (fun r => Finset.sum (s.filter fun x => canonicalSmoothedDifferenceMode x = r)
            (fun x => amplitude x * coeff (canonicalSmoothedDifferenceMode x))) := by
            simpa [s] using
              (Finset.sum_fiberwise_of_maps_to
                (s := s) (t := canonicalSmoothedDifferenceModeRectRange L₁ L₂)
                (g := canonicalSmoothedDifferenceMode)
                (f := fun x : ((ℕ × ℕ) × (ℕ × ℕ)) =>
                  amplitude x * coeff (canonicalSmoothedDifferenceMode x))
                hmaps).symm
    _ = Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
          (fun r =>
            Finset.sum (canonicalSmoothedDifferenceModeRectQuadruples L₁ L₂ r)
              (fun x => amplitude x * coeff r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hfilter :
                s.filter (fun x => canonicalSmoothedDifferenceMode x = r) =
                  canonicalSmoothedDifferenceModeRectQuadruples L₁ L₂ r := by
              ext x
              simp [s, canonicalSmoothedDifferenceModeRectQuadruples]
            rw [hfilter]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxmode : canonicalSmoothedDifferenceMode x = r := by
              simp [canonicalSmoothedDifferenceModeRectQuadruples] at hx
              exact hx.2
            simp [hxmode]
    _ = Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
          (fun r =>
            (Finset.sum (canonicalSmoothedDifferenceModeRectQuadruples L₁ L₂ r) amplitude) * coeff r) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [← Finset.sum_mul]
    _ = Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
          (fun r => canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂ amplitude r * coeff r) := by
            simp [canonicalSmoothedDifferenceModeRectFiberWeight]

/-- The exact collapsed moving-moving amplitude attached to a quadruple of box indices. -/
noncomputable def canonicalSmoothedMovingMovingBoxAmplitude
    (θ θ' : ℝ) (x : ((ℕ × ℕ) × (ℕ × ℕ))) : ℂ :=
  ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ x.1.1
      * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ x.1.2)
    * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') x.2.1
      * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') x.2.2))

/-- Exact smoothed moving-moving contribution attached to a single equal-length quadruple box. -/
noncomputable def canonicalSmoothedMovingMovingBoxContribution
    (ψ : SmoothedBetaCutoff) (L : ℕ) (θ θ' : ℝ) : ℂ :=
  Finset.sum
    (((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)).product
      ((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)))
    (fun x =>
      ∫ β in aβ..bβ,
        canonicalSmoothedBetaKernelWeight ψ β
          *
        (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) x.1.1
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) x.1.2)
          * star
            (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) x.2.1
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) x.2.2))))

/--
Exact smoothed mode-sum expansion for a moving-moving box of equal length `L + 1`.

This is the formal transport step from the termwise smoothed β-collapse to the weighted fiber
regrouping by the single difference mode `r = n - m - n' + m'`.
-/
theorem canonicalSmoothedMovingMovingBox_modeSumExpansion
    (ψ : SmoothedBetaCutoff) (L : ℕ) (θ θ' : ℝ) :
    canonicalSmoothedMovingMovingBoxContribution ψ L θ θ'
      =
    Finset.sum (canonicalSmoothedDifferenceModeRange L)
      (fun r =>
        canonicalSmoothedDifferenceModeFiberWeight L
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
          * canonicalSmoothedBetaLocalizedKernelCoeff ψ r) := by
  classical
  let s :
      Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)).product
      ((canonicalSmoothedDifferenceModeBox L).product
        (canonicalSmoothedDifferenceModeBox L)))
  calc
    canonicalSmoothedMovingMovingBoxContribution ψ L θ θ'
      = Finset.sum s
      (fun x =>
        ∫ β in aβ..bβ,
          canonicalSmoothedBetaKernelWeight ψ β
            *
          (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) x.1.1
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) x.1.2)
            * star
              (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) x.2.1
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) x.2.2)))) := by
        simp [canonicalSmoothedMovingMovingBoxContribution, s]
    _ =
    Finset.sum s
      (fun x =>
        canonicalSmoothedMovingMovingBoxAmplitude θ θ' x
          * canonicalSmoothedBetaLocalizedKernelCoeff ψ (canonicalSmoothedDifferenceMode x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simpa [s, canonicalSmoothedMovingMovingBoxAmplitude, canonicalSmoothedDifferenceMode]
              using canonicalSmoothedJointFreezeDiscrepancy_movingMovingTerm_betaCollapse
                ψ θ θ' x.1.1 x.1.2 x.2.1 x.2.2
    _ =
      Finset.sum (canonicalSmoothedDifferenceModeRange L)
        (fun r =>
          canonicalSmoothedDifferenceModeFiberWeight L
              (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
            * canonicalSmoothedBetaLocalizedKernelCoeff ψ r) := by
              simpa [s] using
                sum_canonicalSmoothedDifferenceMode_fiberwise_weighted
                  L (canonicalSmoothedMovingMovingBoxAmplitude θ θ')
                  (canonicalSmoothedBetaLocalizedKernelCoeff ψ)

/-- Nonnegative mode weight extracted from the exact collapsed moving-moving box amplitude. -/
noncomputable def canonicalSmoothedMovingMovingBoxModeWeight
    (L : ℕ) (θ θ' : ℝ) (r : ℤ) : ℝ :=
  ‖canonicalSmoothedDifferenceModeFiberWeight
      L (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r‖

/--
Mode-sum bound for the exact smoothed moving-moving box contribution.

This is the exact mode regrouping followed only by the triangle inequality. It is the last purely
formal transport step available before one has to connect the real smoothed moving-moving global
term to this box model.
-/
theorem canonicalSmoothedMovingMovingBox_modeSumBound
    (ψ : SmoothedBetaCutoff) (L : ℕ) (θ θ' : ℝ) :
    norm (canonicalSmoothedMovingMovingBoxContribution ψ L θ θ')
      ≤
    Finset.sum (canonicalSmoothedDifferenceModeRange L)
      (fun r =>
        canonicalSmoothedMovingMovingBoxModeWeight L θ θ' r
          * norm (canonicalSmoothedBetaLocalizedKernelCoeff ψ r)) := by
  rw [canonicalSmoothedMovingMovingBox_modeSumExpansion ψ L θ θ']
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro r hr
  simp [canonicalSmoothedMovingMovingBoxModeWeight, norm_mul]

/-- The extracted box mode weight is nonnegative by construction. -/
theorem canonicalSmoothedMovingMovingBoxModeWeight_nonneg
    (L : ℕ) (θ θ' : ℝ) (r : ℤ) :
    0 ≤ canonicalSmoothedMovingMovingBoxModeWeight L θ θ' r := by
  simp [canonicalSmoothedMovingMovingBoxModeWeight]

/--
Correct narrowed theorem surface currently supported by the smoothed file.

This is the exact theorem surface the present transport establishes: the moving-moving box
contribution admits a mode-sum bound against the smoothed localized coefficients.
-/
structure CanonicalSmoothedMovingMovingBoxModeSumExpansion
    (ψ : SmoothedBetaCutoff) : Prop where
  bound :
    ∀ L θ θ',
      norm (canonicalSmoothedMovingMovingBoxContribution ψ L θ θ')
        ≤
      Finset.sum (canonicalSmoothedDifferenceModeRange L)
        (fun r =>
          canonicalSmoothedMovingMovingBoxModeWeight L θ θ' r
            * norm (canonicalSmoothedBetaLocalizedKernelCoeff ψ r))

/-- Package the exact box-level mode-sum bound at the corrected narrowed theorem surface. -/
theorem canonicalSmoothedMovingMovingBoxModeSumExpansion_theorem
    (ψ : SmoothedBetaCutoff) :
    CanonicalSmoothedMovingMovingBoxModeSumExpansion ψ where
  bound := by
    intro L θ θ'
    exact canonicalSmoothedMovingMovingBox_modeSumBound ψ L θ θ'

/-- Exact smoothed moving-moving contribution attached to a mixed-length rectangle. -/
noncomputable def canonicalSmoothedMovingMovingRectContribution
    (ψ : SmoothedBetaCutoff) (L₁ L₂ : ℕ) (θ θ' : ℝ) : ℂ :=
  Finset.sum
    (((canonicalSmoothedDifferenceModeBox L₁).product
        (canonicalSmoothedDifferenceModeBox L₁)).product
      ((canonicalSmoothedDifferenceModeBox L₂).product
        (canonicalSmoothedDifferenceModeBox L₂)))
    (fun x =>
      ∫ β in aβ..bβ,
        canonicalSmoothedBetaKernelWeight ψ β
          *
        (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) x.1.1
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) x.1.2)
          * star
            (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) x.2.1
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) x.2.2))))

/-- Exact mixed-length rectangle mode-sum expansion. -/
theorem canonicalSmoothedMovingMovingRect_modeSumExpansion
    (ψ : SmoothedBetaCutoff) (L₁ L₂ : ℕ) (θ θ' : ℝ) :
    canonicalSmoothedMovingMovingRectContribution ψ L₁ L₂ θ θ'
      =
    Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
      (fun r =>
        canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
          * canonicalSmoothedBetaLocalizedKernelCoeff ψ r) := by
  classical
  let s :
      Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((canonicalSmoothedDifferenceModeBox L₁).product
        (canonicalSmoothedDifferenceModeBox L₁)).product
      ((canonicalSmoothedDifferenceModeBox L₂).product
        (canonicalSmoothedDifferenceModeBox L₂)))
  calc
    canonicalSmoothedMovingMovingRectContribution ψ L₁ L₂ θ θ'
      = Finset.sum s
          (fun x =>
            ∫ β in aβ..bβ,
              canonicalSmoothedBetaKernelWeight ψ β
                *
              (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) x.1.1
                  * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) x.1.2)
                * star
                  (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) x.2.1
                    * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) x.2.2)))) := by
        simp [canonicalSmoothedMovingMovingRectContribution, s]
    _ =
      Finset.sum s
        (fun x =>
          canonicalSmoothedMovingMovingBoxAmplitude θ θ' x
            * canonicalSmoothedBetaLocalizedKernelCoeff ψ (canonicalSmoothedDifferenceMode x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simpa [s, canonicalSmoothedMovingMovingBoxAmplitude, canonicalSmoothedDifferenceMode]
              using canonicalSmoothedJointFreezeDiscrepancy_movingMovingTerm_betaCollapse
                ψ θ θ' x.1.1 x.1.2 x.2.1 x.2.2
    _ =
      Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
        (fun r =>
          canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
              (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
            * canonicalSmoothedBetaLocalizedKernelCoeff ψ r) := by
              simpa [s] using
                sum_canonicalSmoothedDifferenceMode_rect_fiberwise_weighted
                  L₁ L₂ (canonicalSmoothedMovingMovingBoxAmplitude θ θ')
                  (canonicalSmoothedBetaLocalizedKernelCoeff ψ)

/-- Norm-mode-sum bound for the mixed-length rectangle contribution. -/
theorem canonicalSmoothedMovingMovingRect_modeSumBound
    (ψ : SmoothedBetaCutoff) (L₁ L₂ : ℕ) (θ θ' : ℝ) :
    norm (canonicalSmoothedMovingMovingRectContribution ψ L₁ L₂ θ θ')
      ≤
    Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
      (fun r =>
        ‖canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r‖
          * norm (canonicalSmoothedBetaLocalizedKernelCoeff ψ r)) := by
  rw [canonicalSmoothedMovingMovingRect_modeSumExpansion ψ L₁ L₂ θ θ']
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro r hr
  simp [norm_mul]

private lemma canonicalSmoothedMovingMovingRectContribution_eq_nested
    (ψ : SmoothedBetaCutoff) (L₁ L₂ : ℕ) (θ θ' : ℝ) :
    canonicalSmoothedMovingMovingRectContribution ψ L₁ L₂ θ θ'
      =
    ∑ a ∈ Finset.range (L₁ + 1),
      ∑ b ∈ Finset.range (L₁ + 1),
        ∑ c ∈ Finset.range (L₂ + 1),
          ∑ d ∈ Finset.range (L₂ + 1),
            ∫ β in aβ..bβ,
              canonicalSmoothedBetaKernelWeight ψ β
                *
              (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) a
                  * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) b)
                * star
                  (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) c
                    * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) d))) := by
  let s₁ : Finset ℕ := Finset.range (L₁ + 1)
  let s₂ : Finset ℕ := Finset.range (L₂ + 1)
  let H : (ℕ × ℕ) → (ℕ × ℕ) → ℂ :=
    fun ab cd =>
      ∫ β in aβ..bβ,
        canonicalSmoothedBetaKernelWeight ψ β
          *
        (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) ab.1
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) ab.2)
          * star
            (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) cd.1
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) cd.2)))
  calc
    canonicalSmoothedMovingMovingRectContribution ψ L₁ L₂ θ θ'
      =
    ∑ ab ∈ s₁.product s₁,
      ∑ cd ∈ s₂.product s₂,
        H ab cd := by
        unfold canonicalSmoothedMovingMovingRectContribution canonicalSmoothedDifferenceModeBox
        simpa [s₁, s₂, H] using
          (Finset.sum_product (s := s₁.product s₁) (t := s₂.product s₂)
            (f := fun x : (ℕ × ℕ) × (ℕ × ℕ) => H x.1 x.2))
    _ =
    ∑ a ∈ s₁,
      ∑ b ∈ s₁,
        ∑ cd ∈ s₂.product s₂,
          H (a, b) cd := by
        simpa [H] using
          (Finset.sum_product' s₁ s₁
            (fun a b => ∑ cd ∈ s₂.product s₂, H (a, b) cd))
    _ =
    ∑ a ∈ s₁,
      ∑ b ∈ s₁,
        ∑ c ∈ s₂,
          ∑ d ∈ s₂,
            H (a, b) (c, d) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        refine Finset.sum_congr rfl ?_
        intro b hb
        simpa [H] using
          (Finset.sum_product' s₂ s₂
            (fun c d => H (a, b) (c, d)))
    _ = _ := by
        rfl

/--
Four-term `NN - NM - MN + MM` decomposition for the mixed-length moving-moving pair model.

This is the correct theorem surface for the next transport step: once the real smoothed pair term
is rewritten into this rectangle combination, the mode-sum expansion follows from the rectangle
theorems above.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyMovingMovingPairContribution
    (ψ : SmoothedBetaCutoff) (LN LM : ℕ) (θ θ' : ℝ) : ℂ :=
  canonicalSmoothedMovingMovingRectContribution ψ LN LN θ θ'
    - canonicalSmoothedMovingMovingRectContribution ψ LN LM θ θ'
    - canonicalSmoothedMovingMovingRectContribution ψ LM LN θ θ'
    + canonicalSmoothedMovingMovingRectContribution ψ LM LM θ θ'

theorem canonicalSmoothedJointFreezeDiscrepancyMovingMovingPairContribution_eq_NN_sub_NM_sub_MN_add_MM
    (ψ : SmoothedBetaCutoff) (LN LM : ℕ) (θ θ' : ℝ) :
    canonicalSmoothedJointFreezeDiscrepancyMovingMovingPairContribution ψ LN LM θ θ'
      =
    canonicalSmoothedMovingMovingRectContribution ψ LN LN θ θ'
      - canonicalSmoothedMovingMovingRectContribution ψ LN LM θ θ'
      - canonicalSmoothedMovingMovingRectContribution ψ LM LN θ θ'
      + canonicalSmoothedMovingMovingRectContribution ψ LM LM θ θ' := by
  rfl

/-- Complex indicator of the centered unit set, used to keep the moving-shell support explicit. -/
noncomputable def canonicalSmoothedCenteredUnitIndicator (u : ℝ) : ℂ :=
  (centeredUnitSet (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℂ)) u

/--
The fixed outer arithmetic scalar attached to a moving shell.

This keeps all non-β data outside the finite geometric sums:
the weighted `q ≥ 2` amplitude, the centered-unit support in `u`, and the Fourier phase
`fourier (-N) (u/(qX))`.
-/
noncomputable def canonicalSmoothedActualMovingMovingScalar
    (X q N : ℕ) (u : ℝ) : ℂ :=
  canonicalSmoothedCenteredUnitIndicator u
    * canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
    * (fourier (T := (1 : ℝ)) (-(N : ℤ))
        ((canonicalJointFreezeDiscrepancyBetaQTheta X q u : ℝ) : UC) : ℂ)

/--
The constant phase introduced by translating every finite-sum index by `4`.

It is independent of the box indices, so after reindexing from `Ico 4 ((N - 2) + 1)` to a
zero-based range it can be absorbed into the outer arithmetic coefficients.
-/
noncomputable def canonicalSmoothedMovingMovingReindexPhase
    (θ θ' : ℝ) : ℂ :=
  ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ 4
      * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ 4)
    * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') 4
      * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') 4))

/--
The actual mixed-length moving-moving rectangle contribution before abstract box transport.

This is the real fixed-parameter smoothed arithmetic object at `(ψ, N₁, N₂, θ, θ')`, still
indexed on the project’s native `Ico 4 ((N - 2) + 1)` ranges.
-/
noncomputable def canonicalSmoothedActualMovingMovingRectContribution
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N₁ - 2) + 1),
    ∑ m ∈ Finset.Ico 4 ((N₁ - 2) + 1),
      ∑ n' ∈ Finset.Ico 4 ((N₂ - 2) + 1),
        ∑ m' ∈ Finset.Ico 4 ((N₂ - 2) + 1),
          ∫ β in aβ..bβ,
            canonicalSmoothedBetaKernelWeight ψ β
              *
            (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
              * star
                (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
                  * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')))

/--
Exact transport surface from the native `Ico 4 ((N - 2) + 1)` arithmetic ranges to the abstract
mixed-length rectangle contribution.

The remaining bookkeeping content is:
- convert `Ico 4 ((N - 2) + 1)` to a zero-based range,
- absorb the resulting translation-by-`4` into the constant phase
  `canonicalSmoothedMovingMovingReindexPhase θ θ'`.
-/
structure CanonicalSmoothedActualMovingMovingRectTransport
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ) : Prop where
  eq_reindex :
    canonicalSmoothedActualMovingMovingRectContribution ψ N₁ N₂ θ θ'
      =
    canonicalSmoothedMovingMovingReindexPhase θ θ'
      * canonicalSmoothedMovingMovingRectContribution ψ (N₁ - 6) (N₂ - 6) θ θ'

private lemma sum_Ico4_eq_sum_range_shift
    {α : Type*} [AddCommMonoid α] (L : ℕ) (f : ℕ → α) :
    (∑ j ∈ Finset.Ico 4 (L + 4), f j)
      =
    ∑ t ∈ Finset.range L, f (t + 4) := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (Finset.sum_Ico_eq_sum_range (f := f) 4 (L + 4))

private lemma canonicalSmoothed_gExp_nat_add_local (θ : ℝ) (m n : ℕ) :
    Goldbach.Cert.MajorArcStep2ExpSums.gExp θ (m + n)
      =
    Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m
      * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp
  have hphase : θ * ((m + n : ℕ) : ℝ) = θ * (m : ℝ) + θ * (n : ℝ) := by
    norm_num
    ring
  rw [hphase, Goldbach.Cert.MajorArcStep5ExpSumApprox.e_add]

private lemma canonicalSmoothedDifferenceMode_shift4
    (n m n' m' : ℕ) :
    canonicalSmoothedDifferenceMode (((n + 4, m + 4), (n' + 4, m' + 4)) :
      ((ℕ × ℕ) × (ℕ × ℕ)))
      =
    canonicalSmoothedDifferenceMode (((n, m), (n', m')) :
      ((ℕ × ℕ) × (ℕ × ℕ))) := by
  simp [canonicalSmoothedDifferenceMode]
  ring

private lemma canonicalSmoothedMovingMovingBoxAmplitude_shift4
    (θ θ' : ℝ) (n m n' m' : ℕ) :
    canonicalSmoothedMovingMovingBoxAmplitude θ θ'
        (((n + 4, m + 4), (n' + 4, m' + 4)) : ((ℕ × ℕ) × (ℕ × ℕ)))
      =
    canonicalSmoothedMovingMovingReindexPhase θ θ'
      * canonicalSmoothedMovingMovingBoxAmplitude θ θ'
          (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ))) := by
  unfold canonicalSmoothedMovingMovingBoxAmplitude canonicalSmoothedMovingMovingReindexPhase
  rw [canonicalSmoothed_gExp_nat_add_local θ n 4]
  rw [canonicalSmoothed_gExp_nat_add_local θ m 4]
  rw [canonicalSmoothed_gExp_nat_add_local (-θ') n' 4]
  rw [canonicalSmoothed_gExp_nat_add_local (-θ') m' 4]
  ring

private lemma canonicalSmoothedMovingMovingTerm_betaCollapse_shift4
    (ψ : SmoothedBetaCutoff) (θ θ' : ℝ) (n m n' m' : ℕ) :
    (∫ β in aβ..bβ,
      canonicalSmoothedBetaKernelWeight ψ β
        *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) (n + 4)
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) (m + 4))
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) (n' + 4)
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) (m' + 4)))))
      =
    canonicalSmoothedMovingMovingReindexPhase θ θ'
      * canonicalSmoothedMovingMovingBoxAmplitude θ θ'
          (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ)))
      * canonicalSmoothedBetaLocalizedKernelCoeff ψ
          (canonicalSmoothedDifferenceMode
            (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ)))) := by
  calc
    (∫ β in aβ..bβ,
      canonicalSmoothedBetaKernelWeight ψ β
        *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) (n + 4)
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) (m + 4))
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) (n' + 4)
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) (m' + 4)))))
      =
      canonicalSmoothedMovingMovingBoxAmplitude θ θ'
          (((n + 4, m + 4), (n' + 4, m' + 4)) : ((ℕ × ℕ) × (ℕ × ℕ)))
        * canonicalSmoothedBetaLocalizedKernelCoeff ψ
            (canonicalSmoothedDifferenceMode
              (((n + 4, m + 4), (n' + 4, m' + 4)) : ((ℕ × ℕ) × (ℕ × ℕ)))) := by
        simpa [canonicalSmoothedDifferenceMode, canonicalSmoothedMovingMovingBoxAmplitude] using
          canonicalSmoothedJointFreezeDiscrepancy_movingMovingTerm_betaCollapse
            ψ θ θ' (n + 4) (m + 4) (n' + 4) (m' + 4)
    _ =
      (canonicalSmoothedMovingMovingReindexPhase θ θ'
        * canonicalSmoothedMovingMovingBoxAmplitude θ θ'
            (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ))))
        * canonicalSmoothedBetaLocalizedKernelCoeff ψ
            (canonicalSmoothedDifferenceMode
              (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ)))) := by
        rw [canonicalSmoothedMovingMovingBoxAmplitude_shift4,
          canonicalSmoothedDifferenceMode_shift4]

private lemma canonicalSmoothedActualMovingMovingRect_upper_eq_shifted
    {N : ℕ} (hN : 6 ≤ N) :
    ((N - 2) + 1) = ((N - 6) + 1) + 4 := by
  omega

private lemma canonicalSmoothedMovingMovingTerm_transport
    (ψ : SmoothedBetaCutoff) (θ θ' : ℝ) (n m n' m' : ℕ) :
    (∫ β in aβ..bβ,
      canonicalSmoothedBetaKernelWeight ψ β
        *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) (n + 4)
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) (m + 4))
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) (n' + 4)
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) (m' + 4)))))
      =
    canonicalSmoothedMovingMovingReindexPhase θ θ'
      * (∫ β in aβ..bβ,
          canonicalSmoothedBetaKernelWeight ψ β
            *
          (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
            * star
              (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')))) := by
  calc
    (∫ β in aβ..bβ,
      canonicalSmoothedBetaKernelWeight ψ β
        *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) (n + 4)
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) (m + 4))
        * star
          (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) (n' + 4)
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) (m' + 4)))))
      =
      canonicalSmoothedMovingMovingReindexPhase θ θ'
        * canonicalSmoothedMovingMovingBoxAmplitude θ θ'
            (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ)))
        * canonicalSmoothedBetaLocalizedKernelCoeff ψ
            (canonicalSmoothedDifferenceMode
              (((n, m), (n', m')) : ((ℕ × ℕ) × (ℕ × ℕ)))) := by
        exact canonicalSmoothedMovingMovingTerm_betaCollapse_shift4 ψ θ θ' n m n' m'
    _ =
      canonicalSmoothedMovingMovingReindexPhase θ θ'
        * (∫ β in aβ..bβ,
            canonicalSmoothedBetaKernelWeight ψ β
              *
            (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
              * star
                (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
                  * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')))) := by
        simpa [mul_assoc, canonicalSmoothedMovingMovingBoxAmplitude,
          canonicalSmoothedDifferenceMode] using
          congrArg
            (fun z : ℂ => canonicalSmoothedMovingMovingReindexPhase θ θ' * z)
            (canonicalSmoothedJointFreezeDiscrepancy_movingMovingTerm_betaCollapse
              ψ θ θ' n m n' m').symm

private lemma canonicalSmoothedActualMovingMovingRectContribution_eq_nested
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ)
    (hN₁ : 6 ≤ N₁) (hN₂ : 6 ≤ N₂) :
    canonicalSmoothedActualMovingMovingRectContribution ψ N₁ N₂ θ θ'
      =
    ∑ a ∈ Finset.range ((N₁ - 6) + 1),
      ∑ b ∈ Finset.range ((N₁ - 6) + 1),
        ∑ c ∈ Finset.range ((N₂ - 6) + 1),
          ∑ d ∈ Finset.range ((N₂ - 6) + 1),
            ∫ β in aβ..bβ,
              canonicalSmoothedBetaKernelWeight ψ β
                *
              (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) (a + 4)
                  * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) (b + 4))
                * star
                  (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) (c + 4)
                    * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) (d + 4)))) := by
  unfold canonicalSmoothedActualMovingMovingRectContribution
  rw [canonicalSmoothedActualMovingMovingRect_upper_eq_shifted hN₁,
    canonicalSmoothedActualMovingMovingRect_upper_eq_shifted hN₂]
  rw [sum_Ico4_eq_sum_range_shift]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [sum_Ico4_eq_sum_range_shift]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [sum_Ico4_eq_sum_range_shift]
  refine Finset.sum_congr rfl ?_
  intro c hc
  rw [sum_Ico4_eq_sum_range_shift]

/--
Exact transport from the native `Ico 4 ((N - 2) + 1)` arithmetic ranges to the abstract
mixed-length rectangle contribution, once the moving shell is large enough that the `Ico`
intervals really reindex to zero-based boxes.
-/
theorem canonicalSmoothedActualMovingMovingRectContribution_eq_transport
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ)
    (hN₁ : 6 ≤ N₁) (hN₂ : 6 ≤ N₂) :
    canonicalSmoothedActualMovingMovingRectContribution ψ N₁ N₂ θ θ'
      =
    canonicalSmoothedMovingMovingReindexPhase θ θ'
      * canonicalSmoothedMovingMovingRectContribution ψ (N₁ - 6) (N₂ - 6) θ θ' := by
  let s₁ : Finset ℕ := Finset.range ((N₁ - 6) + 1)
  let s₂ : Finset ℕ := Finset.range ((N₂ - 6) + 1)
  let shiftedTerm : ℕ → ℕ → ℕ → ℕ → ℂ :=
    fun a b c d =>
      ∫ β in aβ..bβ,
        canonicalSmoothedBetaKernelWeight ψ β
          *
        (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) (a + 4)
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) (b + 4))
          * star
            (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) (c + 4)
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) (d + 4))))
  let baseTerm : ℕ → ℕ → ℕ → ℕ → ℂ :=
    fun a b c d =>
      ∫ β in aβ..bβ,
        canonicalSmoothedBetaKernelWeight ψ β
          *
        (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) a
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) b)
          * star
            (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) c
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) d)))
  rw [canonicalSmoothedActualMovingMovingRectContribution_eq_nested ψ N₁ N₂ θ θ' hN₁ hN₂]
  rw [canonicalSmoothedMovingMovingRectContribution_eq_nested ψ (N₁ - 6) (N₂ - 6) θ θ']
  have hterm :
      ∀ a b c d,
        shiftedTerm a b c d
          =
        canonicalSmoothedMovingMovingReindexPhase θ θ' * baseTerm a b c d := by
    intro a b c d
    exact canonicalSmoothedMovingMovingTerm_transport ψ θ θ' a b c d
  calc
    (∑ a ∈ s₁, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₂, shiftedTerm a b c d)
      =
    ∑ a ∈ s₁, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₂,
      canonicalSmoothedMovingMovingReindexPhase θ θ' * baseTerm a b c d := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        refine Finset.sum_congr rfl ?_
        intro b hb
        refine Finset.sum_congr rfl ?_
        intro c hc
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact hterm a b c d
    _ =
      canonicalSmoothedMovingMovingReindexPhase θ θ'
        * (∑ a ∈ s₁, ∑ b ∈ s₁, ∑ c ∈ s₂, ∑ d ∈ s₂, baseTerm a b c d) := by
          simp_rw [← Finset.mul_sum]

/--
Package the rectangle transport separately from the sum-congruence proof, keeping structure
elaboration out of the main argument.
-/
theorem canonicalSmoothedActualMovingMovingRectTransport_theorem
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ)
    (hN₁ : 6 ≤ N₁) (hN₂ : 6 ≤ N₂) :
    CanonicalSmoothedActualMovingMovingRectTransport ψ N₁ N₂ θ θ' := by
  refine ⟨?_⟩
  exact canonicalSmoothedActualMovingMovingRectContribution_eq_transport
    (ψ := ψ) (N₁ := N₁) (N₂ := N₂) (θ := θ) (θ' := θ')
    hN₁ hN₂

/--
The real fixed-parameter moving-moving pair term for the smoothed weighted `q ≥ 2` branch.

This is the object built from the actual arithmetic data `(X, N, M, q, q', u, u')`, before any
abstract rectangle packaging.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  let θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u
  let θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u'
  let aN := canonicalSmoothedActualMovingMovingScalar X q N u
  let aM := canonicalSmoothedActualMovingMovingScalar X q M u
  let aN' := canonicalSmoothedActualMovingMovingScalar X q' N u'
  let aM' := canonicalSmoothedActualMovingMovingScalar X q' M u'
  aN * star aN'
      * canonicalSmoothedActualMovingMovingRectContribution ψ N N θ θ'
    - aN * star aM'
      * canonicalSmoothedActualMovingMovingRectContribution ψ N M θ θ'
    - aM * star aN'
      * canonicalSmoothedActualMovingMovingRectContribution ψ M N θ θ'
    + aM * star aM'
      * canonicalSmoothedActualMovingMovingRectContribution ψ M M θ θ'

/--
The transported weighted `NN - NM - MN + MM` rectangle combination attached to the real smoothed
moving-moving pair term.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  let θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u
  let θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u'
  let phase := canonicalSmoothedMovingMovingReindexPhase θ θ'
  let aN := canonicalSmoothedActualMovingMovingScalar X q N u
  let aM := canonicalSmoothedActualMovingMovingScalar X q M u
  let aN' := canonicalSmoothedActualMovingMovingScalar X q' N u'
  let aM' := canonicalSmoothedActualMovingMovingScalar X q' M u'
  phase *
    (aN * star aN'
        * canonicalSmoothedMovingMovingRectContribution ψ (N - 6) (N - 6) θ θ'
      - aN * star aM'
        * canonicalSmoothedMovingMovingRectContribution ψ (N - 6) (M - 6) θ θ'
      - aM * star aN'
        * canonicalSmoothedMovingMovingRectContribution ψ (M - 6) (N - 6) θ θ'
      + aM * star aM'
        * canonicalSmoothedMovingMovingRectContribution ψ (M - 6) (M - 6) θ θ')

/--
Exact transport from the real fixed-parameter smoothed moving-moving pair term to the abstract
mixed-length rectangle object.
-/
theorem canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm_eq_rectPair_of_transport
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ)
    (hNN :
      CanonicalSmoothedActualMovingMovingRectTransport ψ N N
        (canonicalJointFreezeDiscrepancyBetaQTheta X q u)
        (canonicalJointFreezeDiscrepancyBetaQTheta X q' u'))
    (hNM :
      CanonicalSmoothedActualMovingMovingRectTransport ψ N M
        (canonicalJointFreezeDiscrepancyBetaQTheta X q u)
        (canonicalJointFreezeDiscrepancyBetaQTheta X q' u'))
    (hMN :
      CanonicalSmoothedActualMovingMovingRectTransport ψ M N
        (canonicalJointFreezeDiscrepancyBetaQTheta X q u)
        (canonicalJointFreezeDiscrepancyBetaQTheta X q' u'))
    (hMM :
      CanonicalSmoothedActualMovingMovingRectTransport ψ M M
        (canonicalJointFreezeDiscrepancyBetaQTheta X q u)
        (canonicalJointFreezeDiscrepancyBetaQTheta X q' u')) :
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm ψ X N M q q' u u'
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm
      ψ X N M q q' u u' := by
  simp only [canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm,
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm]
  rw [hNN.eq_reindex, hNM.eq_reindex, hMN.eq_reindex, hMM.eq_reindex]
  ring

/--
Packaged pair-level transport: once both shell lengths are at least `6`, the four rectangle
transport obligations are discharged automatically and the real moving-moving pair term rewrites
directly to the transported `NN - NM - MN + MM` rectangle combination.
-/
theorem canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm_eq_rectPair
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ)
    (hN : 6 ≤ N) (hM : 6 ≤ M) :
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm ψ X N M q q' u u'
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm
      ψ X N M q q' u u' := by
  refine canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm_eq_rectPair_of_transport
    (ψ := ψ) (X := X) (N := N) (M := M) (q := q) (q' := q') (u := u) (u' := u')
    ?_ ?_ ?_ ?_
  · exact canonicalSmoothedActualMovingMovingRectTransport_theorem
      (ψ := ψ) (N₁ := N) (N₂ := N)
      (θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u)
      (θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u')
      hN hN
  · exact canonicalSmoothedActualMovingMovingRectTransport_theorem
      (ψ := ψ) (N₁ := N) (N₂ := M)
      (θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u)
      (θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u')
      hN hM
  · exact canonicalSmoothedActualMovingMovingRectTransport_theorem
      (ψ := ψ) (N₁ := M) (N₂ := N)
      (θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u)
      (θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u')
      hM hN
  · exact canonicalSmoothedActualMovingMovingRectTransport_theorem
      (ψ := ψ) (N₁ := M) (N₂ := M)
      (θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u)
      (θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u')
      hM hM

/--
Squared-cutoff mixed-length moving-moving rectangle contribution.

This is the exact rectangle object that matches the genuine smoothed `L²` energy surface.
-/
abbrev canonicalSmoothedMovingMovingRectContributionSq
    (ψ : SmoothedBetaCutoff) (L₁ L₂ : ℕ) (θ θ' : ℝ) : ℂ :=
  canonicalSmoothedMovingMovingRectContribution ψ.squared L₁ L₂ θ θ'

/-- Exact squared-cutoff rectangle mode-sum expansion. -/
theorem canonicalSmoothedMovingMovingRect_modeSumExpansion_sq
    (ψ : SmoothedBetaCutoff) (L₁ L₂ : ℕ) (θ θ' : ℝ) :
    canonicalSmoothedMovingMovingRectContributionSq ψ L₁ L₂ θ θ'
      =
    Finset.sum (canonicalSmoothedDifferenceModeRectRange L₁ L₂)
      (fun r =>
        canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r) := by
  simpa [canonicalSmoothedMovingMovingRectContributionSq,
    canonicalSmoothedBetaSquaredLocalizedKernelCoeff] using
    canonicalSmoothedMovingMovingRect_modeSumExpansion (ψ := ψ.squared) L₁ L₂ θ θ'

/-- The squared-cutoff actual mixed-length moving-moving rectangle contribution. -/
abbrev canonicalSmoothedActualMovingMovingRectContributionSq
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ) : ℂ :=
  canonicalSmoothedActualMovingMovingRectContribution ψ.squared N₁ N₂ θ θ'

/-- Exact squared-cutoff rectangle transport from native `Ico` ranges to zero-based boxes. -/
theorem canonicalSmoothedActualMovingMovingRectContribution_eq_transport_sq
    (ψ : SmoothedBetaCutoff) (N₁ N₂ : ℕ) (θ θ' : ℝ)
    (hN₁ : 6 ≤ N₁) (hN₂ : 6 ≤ N₂) :
    canonicalSmoothedActualMovingMovingRectContributionSq ψ N₁ N₂ θ θ'
      =
    canonicalSmoothedMovingMovingReindexPhase θ θ'
      * canonicalSmoothedMovingMovingRectContributionSq ψ (N₁ - 6) (N₂ - 6) θ θ' := by
  simpa [canonicalSmoothedActualMovingMovingRectContributionSq,
    canonicalSmoothedMovingMovingRectContributionSq] using
    canonicalSmoothedActualMovingMovingRectContribution_eq_transport
      (ψ := ψ.squared) (N₁ := N₁) (N₂ := N₂) (θ := θ) (θ' := θ')
      hN₁ hN₂

/-- The squared-cutoff fixed-parameter moving-moving pair term. -/
abbrev canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTermSq
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm ψ.squared X N M q q' u u'

/-- The squared-cutoff transported moving-moving pair term. -/
abbrev canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTermSq
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm ψ.squared X N M q q' u u'

/--
Packaged squared-cutoff pair transport.

This is the pair-level bridge that actually matches the current smoothed global `L²` energy:
after squaring the cutoff, the real moving-moving pair term rewrites to the transported
`NN - NM - MN + MM` rectangle combination on the correct β-weight.
-/
theorem canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm_eq_rectPair_sq
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ)
    (hN : 6 ≤ N) (hM : 6 ≤ M) :
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTermSq ψ X N M q q' u u'
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTermSq
      ψ X N M q q' u u' := by
  simpa [canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTermSq,
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTermSq] using
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm_eq_rectPair
      (ψ := ψ.squared) (X := X) (N := N) (M := M)
      (q := q) (q' := q') (u := u) (u' := u') hN hM

/-- Common global mode range covering every moving-moving rectangle over the window `EvenIn X H`. -/
noncomputable def canonicalSmoothedMovingMovingGlobalModeRange (X : ℕ) : Finset ℤ :=
  canonicalSmoothedDifferenceModeRectRange (X + H - 6) (X + H - 6)

private lemma canonicalSmoothedDifferenceModeRectFiberWeight_eq_zero_of_not_mem_range
    (L₁ L₂ : ℕ) (amplitude : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) {r : ℤ}
    (hr : r ∉ canonicalSmoothedDifferenceModeRectRange L₁ L₂) :
    canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂ amplitude r = 0 := by
  unfold canonicalSmoothedDifferenceModeRectFiberWeight canonicalSmoothedDifferenceModeRectQuadruples
  have hempty :
      (((canonicalSmoothedDifferenceModeBox L₁).product
          (canonicalSmoothedDifferenceModeBox L₁)).product
        ((canonicalSmoothedDifferenceModeBox L₂).product
          (canonicalSmoothedDifferenceModeBox L₂))).filter
        (fun x => canonicalSmoothedDifferenceMode x = r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxbox, hxr⟩
    exact hr (hxr ▸ canonicalSmoothedDifferenceMode_mem_rect_range L₁ L₂ x hxbox)
  rw [hempty, Finset.sum_empty]

private lemma canonicalSmoothedDifferenceModeRectRange_subset
    {L₁ L₂ G : ℕ} (hL₁ : L₁ ≤ G) (hL₂ : L₂ ≤ G) :
    canonicalSmoothedDifferenceModeRectRange L₁ L₂ ⊆
      canonicalSmoothedDifferenceModeRectRange G G := by
  intro r hr
  rcases Finset.mem_Icc.mp hr with ⟨hlow, hupp⟩
  have hsum : (L₁ + L₂ : ℤ) ≤ (G + G : ℤ) := by
    exact_mod_cast add_le_add hL₁ hL₂
  refine Finset.mem_Icc.mpr ?_
  omega

private lemma canonicalSmoothed_window_ge_six
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) : 6 ≤ N := by
  have hXleN : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  exact le_trans (by decide : 6 ≤ X0) (le_trans hX hXleN)

private lemma canonicalSmoothed_window_sub_six_le
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    N - 6 ≤ X + H - 6 := by
  exact Nat.sub_le_sub_right (Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hN) 6

private lemma canonicalSmoothedMovingMovingRect_modeSumExpansion_sq_global
    (ψ : SmoothedBetaCutoff) (X L₁ L₂ : ℕ) (θ θ' : ℝ)
    (hL₁ : L₁ ≤ X + H - 6) (hL₂ : L₂ ≤ X + H - 6) :
    canonicalSmoothedMovingMovingRectContributionSq ψ L₁ L₂ θ θ'
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
          (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  let f : ℤ → ℂ := fun r =>
    canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
        (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
  calc
    canonicalSmoothedMovingMovingRectContributionSq ψ L₁ L₂ θ θ'
      =
    ∑ r ∈ canonicalSmoothedDifferenceModeRectRange L₁ L₂, f r := by
      simpa [f, canonicalSmoothedMovingMovingGlobalModeRange] using
        canonicalSmoothedMovingMovingRect_modeSumExpansion_sq ψ L₁ L₂ θ θ'
    _ =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X, f r := by
      refine Finset.sum_subset ?_ ?_
      · intro r hr
        have hsumNat : L₁ + L₂ ≤ (X + H - 6) + (X + H - 6) := add_le_add hL₁ hL₂
        have hsum :
            (((L₁ + L₂ : ℕ) : ℤ))
              ≤ ((((X + H - 6) + (X + H - 6) : ℕ) : ℤ)) := by
          exact_mod_cast hsumNat
        rcases Finset.mem_Icc.mp hr with ⟨hlow, hupp⟩
        have hneg :
            -((((X + H - 6) + (X + H - 6) : ℕ) : ℤ))
              ≤ -(((L₁ + L₂ : ℕ) : ℤ)) := by
            linarith
        exact Finset.mem_Icc.mpr ⟨le_trans hneg hlow, le_trans hupp hsum⟩
      · intro r hrG hrNot
        have hz :
            canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
                (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r = 0 :=
          canonicalSmoothedDifferenceModeRectFiberWeight_eq_zero_of_not_mem_range
            (L₁ := L₁) (L₂ := L₂)
            (amplitude := canonicalSmoothedMovingMovingBoxAmplitude θ θ') hrNot
        dsimp [f]
        rw [hz]
        simp

/--
The exact transported moving-moving mode fiber attached to a fixed arithmetic parameter tuple.

This is the signed `NN - NM - MN + MM` rectangle fiber after the native `Ico` reindexing has been
performed.  It is independent of the cutoff; all β-dependence has already been isolated in the
squared-cutoff coefficient.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
    (X N M q q' : ℕ) (u u' : ℝ) (r : ℤ) : ℂ :=
  let θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u
  let θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u'
  let phase := canonicalSmoothedMovingMovingReindexPhase θ θ'
  let aN := canonicalSmoothedActualMovingMovingScalar X q N u
  let aM := canonicalSmoothedActualMovingMovingScalar X q M u
  let aN' := canonicalSmoothedActualMovingMovingScalar X q' N u'
  let aM' := canonicalSmoothedActualMovingMovingScalar X q' M u'
  phase *
    (aN * star aN'
        * canonicalSmoothedDifferenceModeRectFiberWeight (N - 6) (N - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      - aN * star aM'
        * canonicalSmoothedDifferenceModeRectFiberWeight (N - 6) (M - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      - aM * star aN'
        * canonicalSmoothedDifferenceModeRectFiberWeight (M - 6) (N - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      + aM * star aM'
        * canonicalSmoothedDifferenceModeRectFiberWeight (M - 6) (M - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r)

private lemma centeredUnitSet_one_eq_Icc_local :
    centeredUnitSet (1 : ℝ) = Set.Icc (-1 : ℝ) (1 : ℝ) := by
  ext u
  simp [centeredUnitSet, abs_le]

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_gExp_real_local (n : ℕ) :
    Continuous fun β : ℝ => Goldbach.Cert.MajorArcStep2ExpSums.gExp β n := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp Goldbach.Cert.MajorArcExponential.e
  have hmul : Continuous fun β : ℝ => ((β : ℂ) * (n : ℂ)) :=
    Complex.continuous_ofReal.mul continuous_const
  have hscale : Continuous fun β : ℝ => ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hmul
  have hexpArg :
      Continuous fun β : ℝ => (Complex.I : ℂ) * ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hscale
  simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.continuous_exp.comp hexpArg

private lemma continuous_canonicalJointFreezeDiscrepancyBetaQTheta
    (X q : ℕ) :
    Continuous fun u : ℝ => canonicalJointFreezeDiscrepancyBetaQTheta X q u := by
  simpa [canonicalJointFreezeDiscrepancyBetaQTheta] using
    (continuous_id.div_const (((q : ℝ) * (X : ℝ))))

/-- Indicator-free moving-shell scalar; the centered-unit support is factored separately. -/
private noncomputable def canonicalSmoothedActualMovingMovingScalarCore
    (X q N : ℕ) (u : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
    * (fourier (T := (1 : ℝ)) (-(N : ℤ))
        ((canonicalJointFreezeDiscrepancyBetaQTheta X q u : ℝ) : UC) : ℂ)

private lemma canonicalSmoothedActualMovingMovingScalar_eq_indicator_mul_core
    (X q N : ℕ) (u : ℝ) :
    canonicalSmoothedActualMovingMovingScalar X q N u
      =
    canonicalSmoothedCenteredUnitIndicator u
      * canonicalSmoothedActualMovingMovingScalarCore X q N u := by
  unfold canonicalSmoothedActualMovingMovingScalar canonicalSmoothedActualMovingMovingScalarCore
  ring

private lemma continuous_canonicalSmoothedActualMovingMovingScalarCore
    (X q N : ℕ) :
    Continuous fun u : ℝ => canonicalSmoothedActualMovingMovingScalarCore X q N u := by
  unfold canonicalSmoothedActualMovingMovingScalarCore
  exact continuous_const.mul
    ((((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp continuous_coe_UC).comp
      (continuous_canonicalJointFreezeDiscrepancyBetaQTheta X q))

/-- Indicator-free transported moving-moving pair fiber. -/
private noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
    (X N M q q' : ℕ) (u u' : ℝ) (r : ℤ) : ℂ :=
  let θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u
  let θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u'
  let phase := canonicalSmoothedMovingMovingReindexPhase θ θ'
  let aN := canonicalSmoothedActualMovingMovingScalarCore X q N u
  let aM := canonicalSmoothedActualMovingMovingScalarCore X q M u
  let aN' := canonicalSmoothedActualMovingMovingScalarCore X q' N u'
  let aM' := canonicalSmoothedActualMovingMovingScalarCore X q' M u'
  phase *
    (aN * star aN'
        * canonicalSmoothedDifferenceModeRectFiberWeight (N - 6) (N - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      - aN * star aM'
        * canonicalSmoothedDifferenceModeRectFiberWeight (N - 6) (M - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      - aM * star aN'
        * canonicalSmoothedDifferenceModeRectFiberWeight (M - 6) (N - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      + aM * star aM'
        * canonicalSmoothedDifferenceModeRectFiberWeight (M - 6) (M - 6)
            (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r)

private lemma
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicators_mul_core
    (X N M q q' : ℕ) (u u' : ℝ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber X N M q q' u u' r
      =
    canonicalSmoothedCenteredUnitIndicator u
      * canonicalSmoothedCenteredUnitIndicator u'
      * canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
          X N M q q' u u' r := by
  by_cases hu : u ∈ centeredUnitSet (1 : ℝ)
  · by_cases hu' : u' ∈ centeredUnitSet (1 : ℝ)
    · unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        canonicalSmoothedActualMovingMovingScalar
        canonicalSmoothedActualMovingMovingScalarCore
        canonicalSmoothedCenteredUnitIndicator
      simp [Set.indicator_of_mem, hu, hu']
    · unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        canonicalSmoothedActualMovingMovingScalar
        canonicalSmoothedActualMovingMovingScalarCore
        canonicalSmoothedCenteredUnitIndicator
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hu, hu']
  · unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
      canonicalSmoothedActualMovingMovingScalar
      canonicalSmoothedActualMovingMovingScalarCore
      canonicalSmoothedCenteredUnitIndicator
    simp [Set.indicator_of_notMem, hu]

private lemma continuous_canonicalSmoothedMovingMovingReindexPhase_uncurry
    (X q q' : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedMovingMovingReindexPhase
        (canonicalJointFreezeDiscrepancyBetaQTheta X q p.1)
        (canonicalJointFreezeDiscrepancyBetaQTheta X q' p.2) := by
  let hθ : Continuous fun p : ℝ × ℝ =>
      canonicalJointFreezeDiscrepancyBetaQTheta X q p.1 :=
    (continuous_canonicalJointFreezeDiscrepancyBetaQTheta X q).comp continuous_fst
  let hθ' : Continuous fun p : ℝ × ℝ =>
      canonicalJointFreezeDiscrepancyBetaQTheta X q' p.2 :=
    (continuous_canonicalJointFreezeDiscrepancyBetaQTheta X q').comp continuous_snd
  unfold canonicalSmoothedMovingMovingReindexPhase
  exact (((continuous_gExp_real_local 4).comp hθ).mul
      ((continuous_gExp_real_local 4).comp hθ)).mul
    (((continuous_gExp_real_local 4).comp hθ'.neg).mul
      ((continuous_gExp_real_local 4).comp hθ'.neg))

private lemma continuous_canonicalSmoothedDifferenceModeRectFiberWeight_uncurry
    (X q q' L₁ L₂ : ℕ) (r : ℤ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedDifferenceModeRectFiberWeight L₁ L₂
        (canonicalSmoothedMovingMovingBoxAmplitude
          (canonicalJointFreezeDiscrepancyBetaQTheta X q p.1)
          (canonicalJointFreezeDiscrepancyBetaQTheta X q' p.2)) r := by
  let hθ : Continuous fun p : ℝ × ℝ =>
      canonicalJointFreezeDiscrepancyBetaQTheta X q p.1 :=
    (continuous_canonicalJointFreezeDiscrepancyBetaQTheta X q).comp continuous_fst
  let hθ' : Continuous fun p : ℝ × ℝ =>
      canonicalJointFreezeDiscrepancyBetaQTheta X q' p.2 :=
    (continuous_canonicalJointFreezeDiscrepancyBetaQTheta X q').comp continuous_snd
  unfold canonicalSmoothedDifferenceModeRectFiberWeight
  refine continuous_finset_sum _ ?_
  intro x hx
  unfold canonicalSmoothedMovingMovingBoxAmplitude
  exact (((continuous_gExp_real_local x.1.1).comp hθ).mul
      ((continuous_gExp_real_local x.1.2).comp hθ)).mul
    (((continuous_gExp_real_local x.2.1).comp hθ'.neg).mul
      ((continuous_gExp_real_local x.2.2).comp hθ'.neg))

private lemma continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_uncurry
    (X N M q q' : ℕ) (r : ℤ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        X N M q q' p.1 p.2 r := by
  let hN : Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedActualMovingMovingScalarCore X q N p.1 :=
    (continuous_canonicalSmoothedActualMovingMovingScalarCore X q N).comp continuous_fst
  let hM : Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedActualMovingMovingScalarCore X q M p.1 :=
    (continuous_canonicalSmoothedActualMovingMovingScalarCore X q M).comp continuous_fst
  let hN' : Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedActualMovingMovingScalarCore X q' N p.2 :=
    (continuous_canonicalSmoothedActualMovingMovingScalarCore X q' N).comp continuous_snd
  let hM' : Continuous fun p : ℝ × ℝ =>
      canonicalSmoothedActualMovingMovingScalarCore X q' M p.2 :=
    (continuous_canonicalSmoothedActualMovingMovingScalarCore X q' M).comp continuous_snd
  let hphase := continuous_canonicalSmoothedMovingMovingReindexPhase_uncurry X q q'
  let hNN := continuous_canonicalSmoothedDifferenceModeRectFiberWeight_uncurry X q q' (N - 6) (N - 6) r
  let hNM := continuous_canonicalSmoothedDifferenceModeRectFiberWeight_uncurry X q q' (N - 6) (M - 6) r
  let hMN := continuous_canonicalSmoothedDifferenceModeRectFiberWeight_uncurry X q q' (M - 6) (N - 6) r
  let hMM := continuous_canonicalSmoothedDifferenceModeRectFiberWeight_uncurry X q q' (M - 6) (M - 6) r
  unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
  exact hphase.mul <|
    ((((hN.mul hN'.star).mul hNN).sub ((hN.mul hM'.star).mul hNM)).sub
      ((hM.mul hN'.star).mul hMN)).add
    ((hM.mul hM'.star).mul hMM)

private lemma continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_right
    (X N M q q' : ℕ) (u : ℝ) (r : ℤ) :
    Continuous fun u' : ℝ =>
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        X N M q q' u u' r := by
  let psi : ℝ → ℝ × ℝ := fun u' => (u, u')
  have hpsi : Continuous psi := continuous_const.prodMk continuous_id
  simpa [psi] using
    (continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_uncurry
      X N M q q' r).comp hpsi

private lemma continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_left
    (X N M q q' : ℕ) (u' : ℝ) (r : ℤ) :
    Continuous fun u : ℝ =>
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        X N M q q' u u' r := by
  let psi : ℝ → ℝ × ℝ := fun u => (u, u')
  have hpsi : Continuous psi := continuous_id.prodMk continuous_const
  simpa [psi] using
    (continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_uncurry
      X N M q q' r).comp hpsi

private lemma integral_canonicalSmoothedCenteredUnitIndicator_mul_eq_intervalIntegral
    (f : ℝ → ℂ) (hcont : Continuous f) :
    (∫ u : ℝ, canonicalSmoothedCenteredUnitIndicator u * f u)
      =
    ∫ u in (-1 : ℝ)..(1 : ℝ), f u := by
  have hEq :
      (fun u : ℝ => canonicalSmoothedCenteredUnitIndicator u * f u)
        =
      (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator f := by
    funext u
    by_cases hu : u ∈ Set.Icc (-1 : ℝ) (1 : ℝ)
    · simp [canonicalSmoothedCenteredUnitIndicator, centeredUnitSet_one_eq_Icc_local,
        Set.indicator_of_mem, hu]
    · simp [canonicalSmoothedCenteredUnitIndicator, centeredUnitSet_one_eq_Icc_local,
        Set.indicator_of_notMem, hu]
  rw [hEq]
  calc
    (∫ u : ℝ, (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator f u)
      =
    ∫ u in Set.Icc (-1 : ℝ) (1 : ℝ), f u := by
      simpa using
        (MeasureTheory.integral_indicator (μ := volume)
          (s := Set.Icc (-1 : ℝ) (1 : ℝ)) (f := f) measurableSet_Icc)
    _ = ∫ u in Set.Ioc (-1 : ℝ) (1 : ℝ), f u := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := volume) (f := f) (x := (-1 : ℝ)) (y := (1 : ℝ)))
    _ = ∫ u in (-1 : ℝ)..(1 : ℝ), f u := by
      simpa using
        (intervalIntegral.integral_of_le (μ := volume)
          (f := f) (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)).symm

private lemma integral_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicator_mul_interval
    (X N M q q' : ℕ) (u : ℝ) (r : ℤ) :
    (∫ u' : ℝ,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
        X N M q q' u u' r)
      =
    canonicalSmoothedCenteredUnitIndicator u
      * ∫ u' in (-1 : ℝ)..(1 : ℝ),
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
            X N M q q' u u' r := by
  have hEq :
      (fun u' : ℝ =>
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r)
        =
      (fun u' : ℝ =>
        canonicalSmoothedCenteredUnitIndicator u
          * (canonicalSmoothedCenteredUnitIndicator u'
              * canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
                  X N M q q' u u' r)) := by
    funext u'
    rw [canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicators_mul_core]
    ring
  rw [hEq, integral_const_mul]
  rw [integral_canonicalSmoothedCenteredUnitIndicator_mul_eq_intervalIntegral
    (f := fun u' : ℝ =>
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        X N M q q' u u' r)]
  exact
    continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_right
      X N M q q' u r

theorem integrable_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_inner
    (X N M q q' : ℕ) (u : ℝ) (r : ℤ) :
    Integrable (fun u' : ℝ =>
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
        X N M q q' u u' r) := by
  have hEq :
      (fun u' : ℝ =>
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r)
        =
      (fun u' : ℝ =>
        canonicalSmoothedCenteredUnitIndicator u
          * (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator
              (fun u' : ℝ =>
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
                  X N M q q' u u' r) u') := by
    funext u'
    by_cases hu' : u' ∈ Set.Icc (-1 : ℝ) (1 : ℝ)
    · simp [centeredUnitSet_one_eq_Icc_local,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicators_mul_core,
        canonicalSmoothedCenteredUnitIndicator, Set.indicator_of_mem, hu']
    · simp [centeredUnitSet_one_eq_Icc_local,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicators_mul_core,
        canonicalSmoothedCenteredUnitIndicator, Set.indicator_of_notMem, hu']
  rw [hEq]
  exact
    ((continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_right
      X N M q q' u r).integrableOn_Icc.integrable_indicator measurableSet_Icc).const_mul _

theorem integrable_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_outer
    (X N M q q' : ℕ) (r : ℤ) :
    Integrable (fun u : ℝ =>
      ∫ u' : ℝ,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r) := by
  let F : ℝ → ℂ := fun u =>
    ∫ u' in (-1 : ℝ)..(1 : ℝ),
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
        X N M q q' u u' r
  have hFcont : Continuous F := by
    simpa [F] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun u u' =>
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore
            X N M q q' u u' r)
        (a₀ := (-1 : ℝ)) (b₀ := (1 : ℝ))
        (continuous_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiberCore_uncurry
          X N M q q' r))
  have hEq :
      (fun u : ℝ =>
        ∫ u' : ℝ,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r)
        =
      (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator F := by
    funext u
    by_cases hu : u ∈ Set.Icc (-1 : ℝ) (1 : ℝ)
    · have hu' : u ∈ centeredUnitSet (1 : ℝ) := by
        simpa [centeredUnitSet_one_eq_Icc_local] using hu
      rw [integral_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicator_mul_interval]
      simp [F, canonicalSmoothedCenteredUnitIndicator, centeredUnitSet_one_eq_Icc_local,
        Set.indicator_of_mem, hu, hu']
    · have hu' : u ∉ centeredUnitSet (1 : ℝ) := by
        simpa [centeredUnitSet_one_eq_Icc_local] using hu
      rw [integral_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_eq_indicator_mul_interval]
      simp [F, canonicalSmoothedCenteredUnitIndicator, centeredUnitSet_one_eq_Icc_local,
        Set.indicator_of_notMem, hu, hu']
  rw [hEq]
  exact hFcont.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem integrable_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_scaled
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (r : ℤ) :
    Integrable (fun u : ℝ =>
      (∫ u' : ℝ,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r)
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r) := by
  exact
    (integrable_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_outer
      X N M q q' r).mul_const _

private theorem
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeExternalization
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) :
    (∫ u : ℝ, ∫ u' : ℝ,
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r)
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      (∫ u : ℝ, ∫ u' : ℝ,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r)
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  let g := canonicalSmoothedMovingMovingGlobalModeRange X
  have hInner :
      ∀ r ∈ g, ∀ u : ℝ,
        Integrable (fun u' : ℝ =>
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
              X N M q q' u u' r
            * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r) := by
    intro r hr u
    exact
      (integrable_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_inner
        X N M q q' u r).mul_const _
  have hOuter :
      ∀ r ∈ g,
        Integrable (fun u : ℝ =>
          (∫ u' : ℝ,
            canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
              X N M q q' u u' r)
            * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r) := by
    intro r hr
    exact
      integrable_canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber_scaled
        ψ X N M q q' r
  calc
    (∫ u : ℝ, ∫ u' : ℝ,
      ∑ r ∈ g,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r)
      =
    ∫ u : ℝ,
      ∑ r ∈ g, ∫ u' : ℝ,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
        refine integral_congr_ae ?_
        filter_upwards with u
        simpa using
          (integral_finset_sum g (fun r hr => hInner r hr u))
    _ =
    ∫ u : ℝ,
      ∑ r ∈ g,
        (∫ u' : ℝ,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r)
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
        refine integral_congr_ae ?_
        filter_upwards with u
        refine Finset.sum_congr rfl ?_
        intro r hr
        simpa using
          (integral_mul_const
            (r := canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r)
            (f := fun u' : ℝ =>
              canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
                X N M q q' u u' r))
    _ =
    ∑ r ∈ g, ∫ u : ℝ,
      (∫ u' : ℝ,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r)
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
        rw [integral_finset_sum g hOuter]
    _ =
    ∑ r ∈ g,
      (∫ u : ℝ, ∫ u' : ℝ,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r)
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        simpa using
          (integral_mul_const
            (r := canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r)
            (f := fun u : ℝ =>
              ∫ u' : ℝ,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
                  X N M q q' u u' r))

theorem canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm_modeSumExpansion_sq
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (u u' : ℝ)
    (hNle : N ≤ X + H) (hMle : M ≤ X + H) :
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTermSq
      ψ X N M q q' u u'
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  let θ := canonicalJointFreezeDiscrepancyBetaQTheta X q u
  let θ' := canonicalJointFreezeDiscrepancyBetaQTheta X q' u'
  let phase := canonicalSmoothedMovingMovingReindexPhase θ θ'
  let aN := canonicalSmoothedActualMovingMovingScalar X q N u
  let aM := canonicalSmoothedActualMovingMovingScalar X q M u
  let aN' := canonicalSmoothedActualMovingMovingScalar X q' N u'
  let aM' := canonicalSmoothedActualMovingMovingScalar X q' M u'
  let g := canonicalSmoothedMovingMovingGlobalModeRange X
  let fNN : ℤ → ℂ := fun r =>
    canonicalSmoothedDifferenceModeRectFiberWeight (N - 6) (N - 6)
        (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
  let fNM : ℤ → ℂ := fun r =>
    canonicalSmoothedDifferenceModeRectFiberWeight (N - 6) (M - 6)
        (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
  let fMN : ℤ → ℂ := fun r =>
    canonicalSmoothedDifferenceModeRectFiberWeight (M - 6) (N - 6)
        (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
  let fMM : ℤ → ℂ := fun r =>
    canonicalSmoothedDifferenceModeRectFiberWeight (M - 6) (M - 6)
        (canonicalSmoothedMovingMovingBoxAmplitude θ θ') r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
  have hNN :
      canonicalSmoothedMovingMovingRectContribution ψ.squared (N - 6) (N - 6) θ θ'
        =
      ∑ r ∈ g, fNN r := by
    simpa [canonicalSmoothedMovingMovingRectContributionSq, g, fNN] using
      canonicalSmoothedMovingMovingRect_modeSumExpansion_sq_global
        (ψ := ψ) (X := X) (L₁ := N - 6) (L₂ := N - 6) (θ := θ) (θ' := θ')
        (Nat.sub_le_sub_right hNle 6) (Nat.sub_le_sub_right hNle 6)
  have hNM :
      canonicalSmoothedMovingMovingRectContribution ψ.squared (N - 6) (M - 6) θ θ'
        =
      ∑ r ∈ g, fNM r := by
    simpa [canonicalSmoothedMovingMovingRectContributionSq, g, fNM] using
      canonicalSmoothedMovingMovingRect_modeSumExpansion_sq_global
        (ψ := ψ) (X := X) (L₁ := N - 6) (L₂ := M - 6) (θ := θ) (θ' := θ')
        (Nat.sub_le_sub_right hNle 6) (Nat.sub_le_sub_right hMle 6)
  have hMN :
      canonicalSmoothedMovingMovingRectContribution ψ.squared (M - 6) (N - 6) θ θ'
        =
      ∑ r ∈ g, fMN r := by
    simpa [canonicalSmoothedMovingMovingRectContributionSq, g, fMN] using
      canonicalSmoothedMovingMovingRect_modeSumExpansion_sq_global
        (ψ := ψ) (X := X) (L₁ := M - 6) (L₂ := N - 6) (θ := θ) (θ' := θ')
        (Nat.sub_le_sub_right hMle 6) (Nat.sub_le_sub_right hNle 6)
  have hMM :
      canonicalSmoothedMovingMovingRectContribution ψ.squared (M - 6) (M - 6) θ θ'
        =
      ∑ r ∈ g, fMM r := by
    simpa [canonicalSmoothedMovingMovingRectContributionSq, g, fMM] using
      canonicalSmoothedMovingMovingRect_modeSumExpansion_sq_global
        (ψ := ψ) (X := X) (L₁ := M - 6) (L₂ := M - 6) (θ := θ) (θ' := θ')
        (Nat.sub_le_sub_right hMle 6) (Nat.sub_le_sub_right hMle 6)
  unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTermSq
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm
  dsimp [θ, θ', phase, aN, aM, aN', aM']
  rw [hNN, hNM, hMN, hMM]
  have hcombine :
      aN * star aN' * ∑ r ∈ g, fNN r
        - aN * star aM' * ∑ r ∈ g, fNM r
        - aM * star aN' * ∑ r ∈ g, fMN r
        + aM * star aM' * ∑ r ∈ g, fMM r
      =
    ∑ r ∈ g,
      (aN * star aN' * fNN r
        - aN * star aM' * fNM r
        - aM * star aN' * fMN r
        + aM * star aM' * fMM r) := by
      classical
      refine Finset.induction_on g ?_ ?_
      · simp
      · intro s x hx hs
        rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx,
          Finset.sum_insert hx]
        calc
          aN * star aN' * (fNN s + ∑ r ∈ x, fNN r)
              - aN * star aM' * (fNM s + ∑ r ∈ x, fNM r)
              - aM * star aN' * (fMN s + ∑ r ∈ x, fMN r)
              + aM * star aM' * (fMM s + ∑ r ∈ x, fMM r)
            =
          (aN * star aN' * fNN s
              - aN * star aM' * fNM s
              - aM * star aN' * fMN s
              + aM * star aM' * fMM s)
            +
          (aN * star aN' * ∑ r ∈ x, fNN r
              - aN * star aM' * ∑ r ∈ x, fNM r
              - aM * star aN' * ∑ r ∈ x, fMN r
              + aM * star aM' * ∑ r ∈ x, fMM r) := by
                ring
          _ =
          (aN * star aN' * fNN s
              - aN * star aM' * fNM s
              - aM * star aN' * fMN s
              + aM * star aM' * fMM s)
            +
          ∑ r ∈ x,
            (aN * star aN' * fNN r
              - aN * star aM' * fNM r
              - aM * star aN' * fMN r
              + aM * star aM' * fMM r) := by
                rw [hs]
          _ =
          ∑ r ∈ insert s x,
            (aN * star aN' * fNN r
              - aN * star aM' * fNM r
              - aM * star aN' * fMN r
              + aM * star aM' * fMM r) := by
                rw [Finset.sum_insert hx]
  calc
    phase *
        (aN * star aN' * ∑ r ∈ g, fNN r
          - aN * star aM' * ∑ r ∈ g, fNM r
          - aM * star aN' * ∑ r ∈ g, fMN r
          + aM * star aM' * ∑ r ∈ g, fMM r)
      =
    phase *
      (∑ r ∈ g,
        (aN * star aN' * fNN r
          - aN * star aM' * fNM r
          - aM * star aN' * fMN r
          + aM * star aM' * fMM r)) := by
        rw [hcombine]
    _ =
    ∑ r ∈ g,
      phase *
        (aN * star aN' * fNN r
          - aN * star aM' * fNM r
          - aM * star aN' * fMN r
          + aM * star aM' * fMM r) := by
        rw [Finset.mul_sum]
    _ =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
          X N M q q' u u' r
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
        dsimp [θ, θ', phase, aN, aM, aN', aM', g, fNN, fNM, fMN, fMM]
        ring

/--
The actual weighted `q,q' ≥ 2` moving-moving global contribution on the squared-cutoff surface.

This is the genuine smoothed `L²` moving-moving term after summing over ordered window pairs and
integrating the fixed-parameter moving-moving pair term over `u,u'`.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
          ∑ q' ∈ Finset.Icc (2 : ℕ) Q0,
            ∫ u : ℝ, ∫ u' : ℝ,
              canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTermSq
                ψ X N M q q' u u'
      else 0

/-- The same global moving-moving contribution after exact rectangle transport. -/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
          ∑ q' ∈ Finset.Icc (2 : ℕ) Q0,
            ∫ u : ℝ, ∫ u' : ℝ,
              canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTermSq
                ψ X N M q q' u u'
      else 0

/--
The transported moving-moving global contribution with the finite mode sum already inserted
pointwise inside the `u,u'` integrals.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
          ∑ q' ∈ Finset.Icc (2 : ℕ) Q0,
            ∫ u : ℝ, ∫ u' : ℝ,
              ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
                    X N M q q' u u' r
                  * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
      else 0

/--
The true signed transported moving-moving mode weight.

This is the exact coefficient attached to a fixed mode `r` before any absolute values or cubic
dominance estimates are introduced.
-/
noncomputable def canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight
    (_ψ : SmoothedBetaCutoff) (X : ℕ) (r : ℤ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
          ∑ q' ∈ Finset.Icc (2 : ℕ) Q0,
            ∫ u : ℝ, ∫ u' : ℝ,
              canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
                X N M q q' u u' r
      else 0

/--
Staged externalization surface for the exact moving-moving global mode sum.

This is the remaining Fubini step: pull the finite `r`-sum out of the `u,u'` integrals on the
mode-expanded global contribution.
-/
structure CanonicalSmoothedJointFreezeDiscrepancyMovingMovingModeSumExternalization
    (ψ : SmoothedBetaCutoff) : Prop where
  eq :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X
        =
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight ψ X r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

/-!
Implementation note:

The missing theorem on this branch is still the exact moving-moving externalization promised by the
staged surfaces below.  Mathematically, the remaining bridge is only the finite-sum rewrite chain

* `modeExpanded = pairExternalizedGlobal`
* `pairExternalizedGlobal = summedScaledOuterFibers`
* `summedScaledOuterFibers = summedRawOuterFibers`
* `summedRawOuterFibers = summedTrueModeWeights`

using the already-proved pair-level externalization
`canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeExternalization`
and the outer-fiber factorization
`canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber_eq_raw`.

What currently blocks packaging this as a theorem is Lean kernel/elaboration deep recursion on the
declaration surface once the final `summedRawOuterFibers = summedTrueModeWeights` equality is stated
explicitly.  So the unresolved issue here is proof-engineering around reducibility/normalization,
not missing arithmetic or analysis.
-/

/--
Exact complex mode-sum surface for the weighted `q,q' ≥ 2` moving-moving global contribution.

This replaces the stale real/nonnegative single-cutoff mode-sum target on the current smoothed
branch.
-/
structure CanonicalSmoothedJointFreezeDiscrepancyMovingMovingModeSumExpansion
    (ψ : SmoothedBetaCutoff) : Prop where
  eq :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution ψ X
        =
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight ψ X r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

theorem canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution_eq_transport
    (ψ : SmoothedBetaCutoff) {X : ℕ} (hX : X0 ≤ X) :
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution ψ X := by
  unfold canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM]
    refine Finset.sum_congr rfl ?_
    intro q hq
    refine Finset.sum_congr rfl ?_
    intro q' hq'
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u'
    exact canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingPairTerm_eq_rectPair_sq
      (ψ := ψ) (X := X) (N := N) (M := M) (q := q) (q' := q') (u := u) (u' := u')
      (canonicalSmoothed_window_ge_six hX hN)
      (canonicalSmoothed_window_ge_six hX hM)
  · simp [hNM]

theorem canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution_eq_modeExpanded
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X := by
  unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM]
    refine Finset.sum_congr rfl ?_
    intro q hq
    refine Finset.sum_congr rfl ?_
    intro q' hq'
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u'
    exact canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairTerm_modeSumExpansion_sq
      (ψ := ψ) (X := X) (N := N) (M := M) (q := q) (q' := q') (u := u) (u' := u')
      (Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hN)
      (Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hM)
  · simp [hNM]

private abbrev canonicalSmoothedMovingMovingGlobalQRange : Finset ℕ :=
  Finset.Icc (2 : ℕ) Q0

private noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
    (ψ : SmoothedBetaCutoff) (X N M q q' : ℕ) (r : ℤ) : ℂ :=
  (∫ u : ℝ, ∫ u' : ℝ,
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
      X N M q q' u u' r)
    * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

private noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairIntegral
    (X N M q q' : ℕ) (r : ℤ) : ℂ :=
  ∫ u : ℝ, ∫ u' : ℝ,
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
      X N M q q' u u' r

private noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairQSum
    (X N M : ℕ) (r : ℤ) : ℂ :=
  ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
    ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairIntegral
        X N M q q' r

noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber
    (X N : ℕ) (r : ℤ) : ℂ :=
  ∑ M ∈ EvenIn X H,
    (if N ≤ M then
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairQSum X N M r
    else 0)

noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber
    (ψ : SmoothedBetaCutoff) (X N : ℕ) (r : ℤ) : ℂ :=
  ∑ M ∈ EvenIn X H,
    (if N ≤ M then
      ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
        ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
            ψ X N M q q' r
    else 0)

noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawGlobalModeWeightBody
    (X : ℕ) (r : ℤ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber X N r

private noncomputable def canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledGlobalModeWeightBody
    (ψ : SmoothedBetaCutoff) (X : ℕ) (r : ℤ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber ψ X N r

private theorem
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution_eq_pairExternalized
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X
      =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0 := by
  unfold canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM, canonicalSmoothedMovingMovingGlobalQRange,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeExternalization]
  · simp [hNM, canonicalSmoothedMovingMovingGlobalQRange]

private theorem
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral_sum_comm_q'
    (ψ : SmoothedBetaCutoff) (X N M q : ℕ) :
    ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
          ψ X N M q q' r
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
          ψ X N M q q' r := by
  simpa using
    (Finset.sum_comm
      (s := canonicalSmoothedMovingMovingGlobalQRange)
      (t := canonicalSmoothedMovingMovingGlobalModeRange X)
      (f := fun q' r =>
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
          ψ X N M q q' r))

private theorem
    canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_q'
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    (∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0)
      =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0 := by
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM]
    refine Finset.sum_congr rfl ?_
    intro q hq
    exact canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral_sum_comm_q'
      (ψ := ψ) (X := X) (N := N) (M := M) (q := q)
  · simp [hNM]

private theorem
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral_sum_comm_q
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) :
    ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
            ψ X N M q q' r
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
        ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
            ψ X N M q q' r := by
  simpa using
    (Finset.sum_comm
      (s := canonicalSmoothedMovingMovingGlobalQRange)
      (t := canonicalSmoothedMovingMovingGlobalModeRange X)
      (f := fun q r =>
        ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
            ψ X N M q q' r))

private theorem
    canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_q
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    (∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0)
      =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0 := by
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM]
    exact canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral_sum_comm_q
      (ψ := ψ) (X := X) (N := N) (M := M)
  · simp [hNM]

private theorem
    canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_M
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    (∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0)
      =
    ∑ N ∈ EvenIn X H,
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
          else 0 := by
  refine Finset.sum_congr rfl ?_
  intro N hN
  simpa using
    (Finset.sum_comm
      (s := EvenIn X H)
      (t := canonicalSmoothedMovingMovingGlobalModeRange X)
      (f := fun M r =>
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
              canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                ψ X N M q q' r
        else 0))

private theorem
    canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_N
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    (∑ N ∈ EvenIn X H,
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
          else 0)
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      ∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
          else 0 := by
  simpa using
    (Finset.sum_comm
      (s := EvenIn X H)
      (t := canonicalSmoothedMovingMovingGlobalModeRange X)
      (f := fun N r =>
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
          else 0))

private theorem
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral_qsum_eq_coeff
    (ψ : SmoothedBetaCutoff) (X N M : ℕ) (r : ℤ) :
    ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
          ψ X N M q q' r
      =
    (∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        ∫ u : ℝ, ∫ u' : ℝ,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r)
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  change
    ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairIntegral
          X N M q q' r
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairQSum X N M r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
  unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairQSum
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairIntegral
  calc
    ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        (∫ u : ℝ, ∫ u' : ℝ,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r)
          * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r
      =
    ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      (∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        ∫ u : ℝ, ∫ u' : ℝ,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r)
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          rw [← Finset.sum_mul]
    _ =
    (∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
      ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
        ∫ u : ℝ, ∫ u' : ℝ,
          canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingPairModeFiber
            X N M q q' u u' r)
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
          rw [← Finset.sum_mul]

theorem
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber_eq_raw
    (ψ : SmoothedBetaCutoff) (X N : ℕ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber ψ X N r
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber X N r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  unfold canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber
  calc
    ∑ M ∈ EvenIn X H,
      (if N ≤ M then
        ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
          ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
            canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
              ψ X N M q q' r
      else 0)
      =
    ∑ M ∈ EvenIn X H,
      ((if N ≤ M then
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairQSum X N M r
      else 0)
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r) := by
        refine Finset.sum_congr rfl ?_
        intro M hM
        by_cases hNM : N ≤ M
        · simpa [hNM] using
            canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral_qsum_eq_coeff
              (ψ := ψ) (X := X) (N := N) (M := M) (r := r)
        · simp [hNM]
    _ =
    (∑ M ∈ EvenIn X H,
      (if N ≤ M then
        canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawPairQSum X N M r
      else 0))
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
        rw [← Finset.sum_mul]

noncomputable def canonicalSmoothedJointFreezeDiscrepancyOpaqueRawModeWeightOuterFiber
    (X N : ℕ) (r : ℤ) : ℂ :=
  canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber X N r

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueRawModeWeightOuterFiber_eq
    (X N : ℕ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueRawModeWeightOuterFiber X N r
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber X N r := by
  rfl

attribute [irreducible] canonicalSmoothedJointFreezeDiscrepancyOpaqueRawModeWeightOuterFiber

noncomputable def canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody
    (X : ℕ) (r : ℤ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    canonicalSmoothedJointFreezeDiscrepancyOpaqueRawModeWeightOuterFiber X N r

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody_eq
    (X : ℕ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody X r
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawGlobalModeWeightBody X r := by
  unfold canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawGlobalModeWeightBody
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [canonicalSmoothedJointFreezeDiscrepancyOpaqueRawModeWeightOuterFiber_eq]

attribute [irreducible] canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody

noncomputable def canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight
    (ψ : SmoothedBetaCutoff) (X : ℕ) (r : ℤ) : ℂ :=
  canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody X r

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight_eq
    (ψ : SmoothedBetaCutoff) (X : ℕ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight ψ X r
      =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody X r := by
  rfl

attribute [irreducible] canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight_eq_rawGlobalBody
    (ψ : SmoothedBetaCutoff) (X : ℕ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight ψ X r
      =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody X r := by
  rw [canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight_eq]

noncomputable def canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
    canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody X r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers_eq_unfold
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers ψ X
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      canonicalSmoothedJointFreezeDiscrepancyOpaqueRawGlobalModeWeightBody X r
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  rfl

attribute [irreducible] canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers

noncomputable def canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
    canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight ψ X r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights_eq_unfold
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights ψ X
      =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight ψ X r
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r := by
  rfl

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers_eq_true
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights ψ X := by
  rw [canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers_eq_unfold]
  rw [canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights_eq_unfold]
  refine Finset.sum_congr rfl ?_
  intro r hr
  exact congrArg
    (fun z : ℂ => z * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r)
    (canonicalSmoothedJointFreezeDiscrepancyOpaqueTrueMovingMovingModeWeight_eq_rawGlobalBody
      (ψ := ψ) (X := X) (r := r)).symm

attribute [irreducible] canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights

noncomputable def canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        (if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
              canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                ψ X N M q q' r
        else 0)

noncomputable def canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
    ∑ N ∈ EvenIn X H,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber
        ψ X N r

noncomputable def canonicalSmoothedJointFreezeDiscrepancySummedRawOuterFibers
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
    ∑ N ∈ EvenIn X H,
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawModeWeightOuterFiber
        X N r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

noncomputable def canonicalSmoothedJointFreezeDiscrepancySummedTrueModeWeights
    (ψ : SmoothedBetaCutoff) (X : ℕ) : ℂ :=
  ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
    canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight ψ X r
      * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r

theorem
    canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight_eq_rawGlobalBody
    (ψ : SmoothedBetaCutoff) (X : ℕ) (r : ℤ) :
    canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight ψ X r
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingRawGlobalModeWeightBody X r := by
  rfl

theorem
    canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal_eq_summedScaledOuterFibers
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal ψ X
      =
      canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers ψ X := by
  rfl

theorem
    canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers_eq_summedRawOuterFibers
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancySummedRawOuterFibers ψ X := by
  unfold canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers
    canonicalSmoothedJointFreezeDiscrepancySummedRawOuterFibers
  refine Finset.sum_congr rfl ?_
  intro r hr
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledModeWeightOuterFiber_eq_raw
    (ψ := ψ) (X := X) (N := N) (r := r)

theorem canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution_eq_pairExternalizedGlobal
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal ψ X := by
  calc
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X
      =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0 :=
      canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution_eq_pairExternalized
        (ψ := ψ) (X := X)
    _ =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
            ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0 :=
      canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_q'
        (ψ := ψ) (X := X)
    _ =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
        else 0 :=
      canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_q
        (ψ := ψ) (X := X)
    _ =
    ∑ N ∈ EvenIn X H,
      ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
          else 0 :=
      canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_M
        (ψ := ψ) (X := X)
    _ =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      ∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∑ q ∈ canonicalSmoothedMovingMovingGlobalQRange,
              ∑ q' ∈ canonicalSmoothedMovingMovingGlobalQRange,
                canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingScaledPairIntegral
                  ψ X N M q q' r
          else 0 :=
      canonicalSmoothedJointFreezeDiscrepancyPairExternalized_commute_r_N
        (ψ := ψ) (X := X)
    _ =
    canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal ψ X := by
      rfl

/--
Temporary axiom for the last opaque externalization bridge.

This isolates the Lean normalization failure at the exact point where the scaled outer-fiber sum
should be identified with the opaque raw global mode-weight sum. The intended proof is purely
finite-sum algebra; this is not intended to be an end-state theorem.
-/
axiom canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers_eq_opaqueSummedRawOuterFibers
    (ψ : SmoothedBetaCutoff) (X : ℕ) :
    canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers ψ X

structure CanonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExternalization
    (ψ : SmoothedBetaCutoff) : Prop where
  eq :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X
        =
      canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights ψ X

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExternalization_axiomatically
    (ψ : SmoothedBetaCutoff) :
    CanonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExternalization ψ := by
  refine ⟨?_⟩
  intro X hX
  calc
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution_eq_pairExternalizedGlobal
        (ψ := ψ) (X := X)
    _ =
    canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyPairExternalizedGlobal_eq_summedScaledOuterFibers
        (ψ := ψ) (X := X)
    _ =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers ψ X :=
      canonicalSmoothedJointFreezeDiscrepancySummedScaledOuterFibers_eq_opaqueSummedRawOuterFibers
        (ψ := ψ) (X := X)
    _ =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedRawOuterFibers_eq_true
        (ψ := ψ) (X := X)

structure CanonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExpansion
    (ψ : SmoothedBetaCutoff) : Prop where
  eq :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution ψ X
        =
      canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights ψ X

theorem canonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExpansion_of_externalization
    (ψ : SmoothedBetaCutoff)
    (hExt :
      CanonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExternalization ψ) :
    CanonicalSmoothedJointFreezeDiscrepancyOpaqueMovingMovingModeSumExpansion ψ := by
  refine ⟨?_⟩
  intro X hX
  calc
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution_eq_transport
        (ψ := ψ) hX
    _ =
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution_eq_modeExpanded
        (ψ := ψ) X
    _ =
    canonicalSmoothedJointFreezeDiscrepancyOpaqueSummedTrueModeWeights ψ X :=
      hExt.eq hX

/--
Once the finite mode sum has been externalized from the `u,u'` integrals, the exact moving-moving
global contribution follows immediately from the already-proved transport bridges.
-/
theorem canonicalSmoothedJointFreezeDiscrepancyMovingMovingModeSumExpansion_of_externalization
    (ψ : SmoothedBetaCutoff)
    (hExt : CanonicalSmoothedJointFreezeDiscrepancyMovingMovingModeSumExternalization ψ) :
    CanonicalSmoothedJointFreezeDiscrepancyMovingMovingModeSumExpansion ψ := by
  refine ⟨?_⟩
  intro X hX
  calc
    canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution ψ X
      =
    canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyActualMovingMovingGlobalContribution_eq_transport
        (ψ := ψ) hX
    _ =
    canonicalSmoothedJointFreezeDiscrepancyModeExpandedMovingMovingGlobalContribution ψ X :=
      canonicalSmoothedJointFreezeDiscrepancyTransportedMovingMovingGlobalContribution_eq_modeExpanded
        (ψ := ψ) X
    _ =
    ∑ r ∈ canonicalSmoothedMovingMovingGlobalModeRange X,
      canonicalSmoothedJointFreezeDiscrepancyTrueMovingMovingModeWeight ψ X r
        * canonicalSmoothedBetaSquaredLocalizedKernelCoeff ψ r :=
      hExt.eq hX

/--
First combinatorial estimate for the smoothed mode audit.

Fixing the mode relation `n - m - n' + m' = r`, the fourth index is determined by the first three.
So the raw multiplicity of difference mode `r` in a length-`L + 1` box is at most cubic.
-/
theorem card_canonicalSmoothedDifferenceModeQuadruples_le_cube
    (L : ℕ) (r : ℤ) :
    (canonicalSmoothedDifferenceModeQuadruples L r).card ≤ (L + 1) ^ 3 := by
  classical
  let box := canonicalSmoothedDifferenceModeBox L
  let s := canonicalSmoothedDifferenceModeQuadruples L r
  let t : Finset ((ℕ × ℕ) × ℕ) := (box.product box).product box
  let proj : ((ℕ × ℕ) × (ℕ × ℕ)) → ((ℕ × ℕ) × ℕ) := fun x => (x.1, x.2.1)
  have hmaps : Set.MapsTo proj s t := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxbox, _hmode⟩
    rcases Finset.mem_product.mp hxbox with ⟨hab, hcd⟩
    rcases Finset.mem_product.mp hab with ⟨hn, hm⟩
    rcases Finset.mem_product.mp hcd with ⟨hn', hm'⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hn, hm⟩, hn'⟩
  have hinj : Set.InjOn proj s := by
    intro x hx y hy hxy
    rcases x with ⟨⟨n, m⟩, ⟨n', m'⟩⟩
    rcases y with ⟨⟨n₂, m₂⟩, ⟨n₂', m₂'⟩⟩
    have hmodex : ((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ)) = r := by
      simpa [s, canonicalSmoothedDifferenceModeQuadruples]
        using (Finset.mem_filter.mp hx).2
    have hmodey : ((n₂ : ℤ) - (m₂ : ℤ) - (n₂' : ℤ) + (m₂' : ℤ)) = r := by
      simpa [s, canonicalSmoothedDifferenceModeQuadruples]
        using (Finset.mem_filter.mp hy).2
    have hn : n = n₂ := by
      simpa [proj] using congrArg (fun z : ((ℕ × ℕ) × ℕ) => z.1.1) hxy
    have hm : m = m₂ := by
      simpa [proj] using congrArg (fun z : ((ℕ × ℕ) × ℕ) => z.1.2) hxy
    have hn' : n' = n₂' := by
      simpa [proj] using congrArg (fun z : ((ℕ × ℕ) × ℕ) => z.2) hxy
    subst hn hm hn'
    have hm' : m' = m₂' := by
      linarith [hmodex, hmodey]
    subst hm'
    rfl
  have hcard :
      s.card ≤ t.card := by
    exact Finset.card_le_card_of_injOn proj hmaps hinj
  calc
    s.card ≤ t.card := hcard
    _ = (L + 1) ^ 3 := by
      simp [t, box, canonicalSmoothedDifferenceModeBox]
      ring

/-- Real-valued version of the cubic raw mode-weight bound. -/
theorem canonicalSmoothedDifferenceModeWeight_le_cube
    (L : ℕ) (r : ℤ) :
    canonicalSmoothedDifferenceModeWeight L r ≤ ((L + 1 : ℕ) : ℝ) ^ 3 := by
  unfold canonicalSmoothedDifferenceModeWeight
  exact_mod_cast card_canonicalSmoothedDifferenceModeQuadruples_le_cube L r

/--
Route-sized smoothed global β-energy target.

This is the smoothed replacement for the sharp global β-energy target.  It should only be
attacked after proving summable decay for `canonicalSmoothedBetaLocalizedKernelCoeff`.
-/
structure CanonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergyTarget
    (ψ : SmoothedBetaCutoff) (Csm : ℝ) : Prop where
  Csm_nonneg : 0 ≤ Csm
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmoothedJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy ψ X
        ≤
      12 * (((EvenIn X H).card : ℝ)
        * (Csm / ((H : ℝ) * ((Q0 : ℕ) : ℝ) ^ 2)))

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassSmoothedBetaEnergyTargets
