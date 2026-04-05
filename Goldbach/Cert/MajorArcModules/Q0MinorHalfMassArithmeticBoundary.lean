import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
import Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy

/-!
Paper-facing arithmetic boundary for the zero-mode side of Vaughan's bridge.

This file deliberately keeps the scalar abstract.  Its purpose is to expose a theorem-shaped
statement for the half-mass-recentered observable and only then transport that statement into the
internal endpoint interface used by the assembled bridge.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy

noncomputable section

/--
Paper-facing arithmetic theorem surface for the zero-mode side.

The content is exactly the abstract-scalar statement

`halfMassRecenteredZeroModeObservable = κ + error`

with error controlled in the canonical window norm.  The bridge's finer transport machinery should
be recovered from this theorem surface, not built into it.
-/
structure HalfMassArithmeticPaperTarget where
  κ : ℝ
  C2 : ℝ
  C3 : ℝ
  target : HalfMassRecenteredZeroModeTarget κ C2 C3
  shape_target : ZeroModeEnvelopeShapeTarget κ C2 C3

theorem HalfMassArithmeticPaperTarget.to_target (h : HalfMassArithmeticPaperTarget) :
    HalfMassRecenteredZeroModeTarget h.κ h.C2 h.C3 :=
  h.target

theorem HalfMassArithmeticPaperTarget.to_shape_target (h : HalfMassArithmeticPaperTarget) :
    ZeroModeEnvelopeShapeTarget h.κ h.C2 h.C3 :=
  h.shape_target

/--
Canonical scalar witness for the half-mass-recentered observable on the even window: the window
average.
-/
noncomputable def halfMassWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, halfMassRecenteredZeroModeObservable X N

/-- Exact second moment of the half-mass-recentered observable on the canonical even window. -/
noncomputable def halfMassWindowRawSecondMoment (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeObservable X N‖ ^ 2

noncomputable def halfMassRecenteredWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹
    * halfMassWindowRawSum X

/--
Canonical scale-dependent scalar witness for the half-mass-recentered observable: the exact
even-window average at scale `X`.
-/
noncomputable def halfMassCanonicalAverageWitness (X : ℕ) : ℂ :=
  halfMassRecenteredWindowAverage X

theorem halfMassCanonicalAverageWitness_eq_average
    (X : ℕ) :
    halfMassCanonicalAverageWitness X = halfMassRecenteredWindowAverage X := by
  rfl

theorem halfMassRecenteredWindowAverage_eq_card_inv_mul_rawSum
    (X : ℕ) :
    halfMassRecenteredWindowAverage X
      =
    ((EvenIn X H).card : ℂ)⁻¹ * halfMassWindowRawSum X := by
  rfl

theorem halfMassWindowRawSum_eq_card_mul_average
    (X : ℕ) :
    halfMassWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * halfMassRecenteredWindowAverage X := by
  rw [halfMassRecenteredWindowAverage_eq_card_inv_mul_rawSum]
  by_cases hcard : (EvenIn X H).card = 0
  · have hsum : halfMassWindowRawSum X = 0 := by
      have hempty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard
      rw [halfMassWindowRawSum, hempty, Finset.sum_empty]
    simp [hcard, hsum]
  · have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
      exact_mod_cast hcard
    calc
      halfMassWindowRawSum X
          = ((EvenIn X H).card : ℂ) * (((EvenIn X H).card : ℂ)⁻¹ * halfMassWindowRawSum X) := by
              field_simp [hcardC]
      _ = ((EvenIn X H).card : ℂ) * halfMassRecenteredWindowAverage X := by
              rw [halfMassRecenteredWindowAverage_eq_card_inv_mul_rawSum]

/-- Squared `ℓ²` energy of the observable centered at its canonical window average. -/
noncomputable def halfMassRecenteredVarianceWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2

/--
Exact centered second-moment expression on the canonical even window.

This is just a named form of the variance quantity, but the name reflects the second-moment role
it plays in the arithmetic proof plan.
-/
noncomputable def halfMassWindowCenteredSecondMoment (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2

theorem halfMassWindowCenteredSecondMoment_eq_variance
    (X : ℕ) :
    halfMassWindowCenteredSecondMoment X = halfMassRecenteredVarianceWindowEnergy X := by
  rfl

/--
Finite-window centered second-moment identity for the half-mass observable.

This is the arithmetic variance formula in the exact window-average normalization used by the
current boundary file.
-/
theorem halfMassWindowCenteredSecondMoment_eq_rawSecondMoment_sub_card_mul_sqNorm_average
    (X : ℕ) :
    halfMassWindowCenteredSecondMoment X
      =
    halfMassWindowRawSecondMoment X
      - ((EvenIn X H).card : ℝ) * ‖halfMassRecenteredWindowAverage X‖ ^ 2 := by
  let a : ℂ := halfMassRecenteredWindowAverage X
  have hstep :
      halfMassWindowCenteredSecondMoment X
        =
      ∑ N ∈ EvenIn X H,
        (‖halfMassRecenteredZeroModeObservable X N‖ ^ 2
          + ‖a‖ ^ 2
          - 2 * ((halfMassRecenteredZeroModeObservable X N * star a).re)) := by
    refine Finset.sum_congr rfl ?_
    intro N hN
    simp [a, Complex.sq_norm, Complex.normSq_sub]
  have hconst :
      ∑ N ∈ EvenIn X H, ‖a‖ ^ 2
        =
      ((EvenIn X H).card : ℝ) * ‖a‖ ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcross_sum :
      ∑ N ∈ EvenIn X H, ((halfMassRecenteredZeroModeObservable X N * star a).re)
        =
      ((halfMassWindowRawSum X * star a).re) := by
    rw [halfMassWindowRawSum]
    exact Q0FinitePairwiseEnergy.sum_mul_star_re
      (EvenIn X H) (fun N => halfMassRecenteredZeroModeObservable X N) a
  have hcross :
      ∑ N ∈ EvenIn X H, 2 * ((halfMassRecenteredZeroModeObservable X N * star a).re)
        =
      2 * (((EvenIn X H).card : ℝ) * ‖a‖ ^ 2) := by
    have hraw :
        halfMassWindowRawSum X = ((EvenIn X H).card : ℂ) * halfMassRecenteredWindowAverage X :=
      halfMassWindowRawSum_eq_card_mul_average X
    calc
      ∑ N ∈ EvenIn X H, 2 * ((halfMassRecenteredZeroModeObservable X N * star a).re)
          = 2 * ∑ N ∈ EvenIn X H, ((halfMassRecenteredZeroModeObservable X N * star a).re) := by
              rw [Finset.mul_sum]
      _ = 2 * ((halfMassWindowRawSum X * star a).re) := by rw [hcross_sum]
      _ = 2 * ((((EvenIn X H).card : ℂ) * halfMassRecenteredWindowAverage X * star a).re) := by
            rw [hraw]
      _ = 2 * ((((EvenIn X H).card : ℂ) * a * star a).re) := by
            rfl
      _ = 2 * (((EvenIn X H).card : ℝ) * ‖a‖ ^ 2) := by
            calc
              2 * ((((EvenIn X H).card : ℂ) * a * star a).re)
                  = 2 * ((((EvenIn X H).card : ℂ) * (Complex.normSq a : ℂ)).re) := by
                      have hmulconj : a * star a = (Complex.normSq a : ℂ) := by
                        simpa using (Complex.mul_conj a)
                      have hmul :
                          ((EvenIn X H).card : ℂ) * a * star a
                            =
                          ((EvenIn X H).card : ℂ) * (Complex.normSq a : ℂ) := by
                        calc
                          ((EvenIn X H).card : ℂ) * a * star a
                              = ((EvenIn X H).card : ℂ) * (a * star a) := by
                                  rw [mul_assoc]
                          _ = ((EvenIn X H).card : ℂ) * (Complex.normSq a : ℂ) := by
                                  exact congrArg (fun z : ℂ => ((EvenIn X H).card : ℂ) * z) hmulconj
                      exact congrArg (fun z : ℂ => 2 * z.re) hmul
              _ = 2 * (((EvenIn X H).card : ℝ) * Complex.normSq a) := by
                      have hcast :
                          ((EvenIn X H).card : ℂ) * (Complex.normSq a : ℂ)
                            =
                          ((((EvenIn X H).card : ℝ) * Complex.normSq a : ℝ) : ℂ) := by
                        exact
                          (Complex.ofReal_mul ((EvenIn X H).card : ℝ) (Complex.normSq a)).symm
                      exact congrArg (fun z : ℂ => 2 * z.re) hcast
              _ = 2 * (((EvenIn X H).card : ℝ) * ‖a‖ ^ 2) := by
                      rw [Complex.normSq_eq_norm_sq]
  calc
    halfMassWindowCenteredSecondMoment X
        =
      ∑ N ∈ EvenIn X H,
        (‖halfMassRecenteredZeroModeObservable X N‖ ^ 2
          + ‖a‖ ^ 2
          - 2 * ((halfMassRecenteredZeroModeObservable X N * star a).re)) := hstep
    _ =
      (∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeObservable X N‖ ^ 2)
        + (∑ N ∈ EvenIn X H, ‖a‖ ^ 2)
        - (∑ N ∈ EvenIn X H, 2 * ((halfMassRecenteredZeroModeObservable X N * star a).re)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ =
      halfMassWindowRawSecondMoment X
        + ((EvenIn X H).card : ℝ) * ‖a‖ ^ 2
        - (2 * (((EvenIn X H).card : ℝ) * ‖a‖ ^ 2)) := by
      rw [hconst, hcross, halfMassWindowRawSecondMoment]
    _ =
      halfMassWindowRawSecondMoment X
        - ((EvenIn X H).card : ℝ) * ‖a‖ ^ 2 := by
      ring
    _ =
      halfMassWindowRawSecondMoment X
        - ((EvenIn X H).card : ℝ) * ‖halfMassRecenteredWindowAverage X‖ ^ 2 := by
      rfl

/--
Centered fluctuation of the half-mass-recentered observable around its canonical even-window
average.
-/
noncomputable def halfMassCenteredFluctuation (X N : ℕ) : ℂ :=
  halfMassRecenteredZeroModeObservable X N - halfMassCanonicalAverageWitness X

theorem halfMassCenteredFluctuation_eq_observable_sub_average
    (X N : ℕ) :
    halfMassCenteredFluctuation X N
      =
    halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X := by
  rfl

theorem halfMassWindowCenteredSecondMoment_eq_fluctuationEnergy
    (X : ℕ) :
    halfMassWindowCenteredSecondMoment X
      =
    ∑ N ∈ EvenIn X H, ‖halfMassCenteredFluctuation X N‖ ^ 2 := by
  rfl

theorem halfMassCenteredFluctuation_window_sum_eq_zero
    (X : ℕ) :
    ∑ N ∈ EvenIn X H, halfMassCenteredFluctuation X N = 0 := by
  unfold halfMassCenteredFluctuation halfMassCanonicalAverageWitness
  rw [Finset.sum_sub_distrib]
  change halfMassWindowRawSum X - ∑ N ∈ EvenIn X H, halfMassRecenteredWindowAverage X = 0
  rw [halfMassWindowRawSum_eq_card_mul_average]
  have hconst :
      ∑ N ∈ EvenIn X H, halfMassRecenteredWindowAverage X
        =
      ((EvenIn X H).card : ℂ) * halfMassRecenteredWindowAverage X := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  ring

theorem halfMassCenteredFluctuation_eq_error_sub_averageDefect
    {κ : ℝ} (X N : ℕ) :
    halfMassCenteredFluctuation X N
      =
    halfMassRecenteredZeroModeError κ X N
      - (halfMassCanonicalAverageWitness X - (κ : ℂ)) := by
  unfold halfMassCenteredFluctuation halfMassCanonicalAverageWitness halfMassRecenteredZeroModeError
  ring

/--
Pairwise energy of the centered half-mass fluctuation on the canonical even window.
-/
noncomputable def halfMassCenteredPairwiseDifferenceEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, ‖halfMassCenteredFluctuation X N - halfMassCenteredFluctuation X M‖ ^ 2

theorem halfMassCenteredFluctuation_sub_eq_error_sub_error
    {κ : ℝ} (X N M : ℕ) :
    halfMassCenteredFluctuation X N - halfMassCenteredFluctuation X M
      =
    halfMassRecenteredZeroModeError κ X N - halfMassRecenteredZeroModeError κ X M := by
  rw [halfMassCenteredFluctuation_eq_error_sub_averageDefect (κ := κ)]
  rw [halfMassCenteredFluctuation_eq_error_sub_averageDefect (κ := κ)]
  ring

theorem halfMassCenteredPairwiseDifferenceEnergy_eq_two_card_mul_centeredSecondMoment
    (X : ℕ) :
    halfMassCenteredPairwiseDifferenceEnergy X
      =
    2 * (((EvenIn X H).card : ℝ) * halfMassWindowCenteredSecondMoment X) := by
  change
    Finset.sum (EvenIn X H)
      (fun N => Finset.sum (EvenIn X H)
        (fun M => ‖halfMassCenteredFluctuation X N - halfMassCenteredFluctuation X M‖ ^ 2))
      =
    2 * (((EvenIn X H).card : ℝ)
      * Finset.sum (EvenIn X H) (fun N => ‖halfMassCenteredFluctuation X N‖ ^ 2))
  exact
    Q0FinitePairwiseEnergy.sum_pairwise_norm_sq_eq_two_card_mul_sum_norm_sq_of_sum_eq_zero
      (s := EvenIn X H) (f := fun N => halfMassCenteredFluctuation X N)
      (hzero := halfMassCenteredFluctuation_window_sum_eq_zero X)

/--
Pairwise energy of the existing half-mass-recentered zero-mode error layer.
-/
noncomputable def halfMassRecenteredZeroModeErrorPairwiseEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H,
    ‖halfMassRecenteredZeroModeError κ X N - halfMassRecenteredZeroModeError κ X M‖ ^ 2

theorem halfMassCenteredPairwiseDifferenceEnergy_eq_errorPairwiseEnergy
    {κ : ℝ} (X : ℕ) :
    halfMassCenteredPairwiseDifferenceEnergy X
      =
    halfMassRecenteredZeroModeErrorPairwiseEnergy κ X := by
  unfold halfMassCenteredPairwiseDifferenceEnergy halfMassRecenteredZeroModeErrorPairwiseEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  rw [halfMassCenteredFluctuation_sub_eq_error_sub_error (κ := κ)]

theorem halfMassVarianceEnergy_mul_two_card_eq_errorPairwiseEnergy
    {κ : ℝ} (X : ℕ) :
    2 * (((EvenIn X H).card : ℝ) * halfMassRecenteredVarianceWindowEnergy X)
      =
    halfMassRecenteredZeroModeErrorPairwiseEnergy κ X := by
  calc
    2 * (((EvenIn X H).card : ℝ) * halfMassRecenteredVarianceWindowEnergy X)
        =
      2 * (((EvenIn X H).card : ℝ) * halfMassWindowCenteredSecondMoment X) := by
          rw [← halfMassWindowCenteredSecondMoment_eq_variance]
    _ = halfMassCenteredPairwiseDifferenceEnergy X := by
          rw [halfMassCenteredPairwiseDifferenceEnergy_eq_two_card_mul_centeredSecondMoment]
    _ = halfMassRecenteredZeroModeErrorPairwiseEnergy κ X := by
          rw [halfMassCenteredPairwiseDifferenceEnergy_eq_errorPairwiseEnergy (κ := κ)]

/--
Pairwise-error theorem surface for the arithmetic variance step.

This is the arithmetic frontier after centering at the exact window average: control the pairwise
energy of the existing half-mass-recentered zero-mode error layer in the natural
`2 * |EvenIn(X,H)|` normalization.
-/
structure HalfMassErrorPairwiseTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassRecenteredZeroModeErrorPairwiseEnergy κ X
        ≤
      2 * (((EvenIn X H).card : ℝ) *
        (C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Scale-dependent average-identification target: the canonical even-window average matches a chosen
window witness `κX` exactly at every scale.
-/
structure HalfMassWindowAverageWitnessTarget (κX : ℕ → ℂ) : Prop where
  average_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassRecenteredWindowAverage X = κX X

/--
The canonical average witness is immediate by definition.
-/
theorem halfMassCanonicalAverageWitness_target :
    HalfMassWindowAverageWitnessTarget halfMassCanonicalAverageWitness := by
  refine ⟨?_⟩
  intro X hX
  rfl

/--
Variance-form arithmetic target: control the half-mass-recentered observable after projection to
constants on the canonical even window.
-/
structure HalfMassArithmeticVarianceTarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassRecenteredVarianceWindowEnergy X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem HalfMassErrorPairwiseTarget.to_varianceTarget
    {κ C2 C3 : ℝ} (hPair : HalfMassErrorPairwiseTarget κ C2 C3) :
    HalfMassArithmeticVarianceTarget C2 C3 := by
  refine ⟨hPair.C2_nonneg, hPair.C3_nonneg, ?_⟩
  intro X hX
  let budget : ℝ :=
    C2 * ((H : ℝ) / (X : ℝ))
      + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  have hbudget_nonneg : 0 ≤ budget := by
    have hHX_nonneg : 0 ≤ ((H : ℝ) / (X : ℝ)) := by positivity
    have hterm1_nonneg : 0 ≤ C2 * ((H : ℝ) / (X : ℝ)) := by
      exact mul_nonneg hPair.C2_nonneg hHX_nonneg
    have hdenom_nonneg :
        0 ≤ ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      positivity
    have htail_nonneg :
        0 ≤ C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      exact div_nonneg hPair.C3_nonneg hdenom_nonneg
    dsimp [budget]
    exact add_nonneg hterm1_nonneg htail_nonneg
  by_cases hcard0 : (EvenIn X H).card = 0
  · have hempty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard0
    have hvar_zero : halfMassRecenteredVarianceWindowEnergy X = 0 := by
      unfold halfMassRecenteredVarianceWindowEnergy
      simp [hempty]
    rw [hvar_zero]
    exact hbudget_nonneg
  · have hcard_pos : 0 < ((EvenIn X H).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard0
    have hpair_bound := hPair.bound (X := X) hX
    rw [← halfMassVarianceEnergy_mul_two_card_eq_errorPairwiseEnergy (κ := κ) (X := X)] at hpair_bound
    have hscaled :
        2 * (((EvenIn X H).card : ℝ) * halfMassRecenteredVarianceWindowEnergy X)
          ≤
        2 * (((EvenIn X H).card : ℝ) * budget) := by
      dsimp [budget]
      exact hpair_bound
    nlinarith [hscaled, hcard_pos, hbudget_nonneg]

/--
Average-identification target for the arithmetic endpoint: the canonical even-window average of the
half-mass observable is the same scalar `κ` at every scale.
-/
structure HalfMassWindowAverageTarget (κ : ℝ) : Prop where
  average_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassRecenteredWindowAverage X = (κ : ℂ)

theorem HalfMassWindowAverageTarget.to_scaleWitness
    {κ : ℝ} (h : HalfMassWindowAverageTarget κ) :
    HalfMassWindowAverageWitnessTarget (fun _ => (κ : ℂ)) := by
  refine ⟨?_⟩
  intro X hX
  simpa using h.average_eq hX

/--
Energy of the scale-by-scale average defect relative to a fixed scalar `κ`.

This is the exact contribution that appears when one expands
`∑ ‖obs - κ‖²` around the canonical window average.
-/
noncomputable def halfMassWindowAverageStabilityEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ((EvenIn X H).card : ℝ) * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2

theorem halfMassWindowAverageStabilityEnergy_eq_zero_of_averageTarget
    {κ : ℝ} (hAvg : HalfMassWindowAverageTarget κ)
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassWindowAverageStabilityEnergy κ X = 0 := by
  rw [halfMassWindowAverageStabilityEnergy, hAvg.average_eq hX]
  rw [sub_self, norm_zero]
  rw [pow_two]
  ring

/--
Average-stability target for the arithmetic endpoint: the canonical window average itself is close
to a fixed scalar `κ`, in the exact energy normalization needed to combine with the centered
variance estimate.
-/
structure HalfMassWindowAverageStabilityTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassWindowAverageStabilityEnergy κ X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Generator-facing arithmetic window expression for the scale-by-scale average defect.
-/
noncomputable def halfMassAverageStabilityWindowUpper (κ : ℝ) (X : ℕ) : ℝ :=
  halfMassWindowAverageStabilityEnergy κ X

/--
Any certified upper bound for the exact average-stability expression upgrades to the corresponding
stability target.
-/
theorem halfMassWindowAverageStabilityTarget_of_windowUpper
    {κ C2 C3 : ℝ}
    (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        halfMassAverageStabilityWindowUpper κ X
          ≤
        C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) :
    HalfMassWindowAverageStabilityTarget κ C2 C3 := by
  refine ⟨hC2, hC3, ?_⟩
  intro X hX
  simpa [halfMassAverageStabilityWindowUpper] using hUpper (X := X) hX

theorem halfMassWindowAverageStabilityTarget_of_averageTarget
    {κ : ℝ} (hAvg : HalfMassWindowAverageTarget κ) :
    HalfMassWindowAverageStabilityTarget κ 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro X hX
  rw [halfMassWindowAverageStabilityEnergy_eq_zero_of_averageTarget hAvg hX]
  simp

/--
Generator-facing arithmetic window expression: the exact centered variance on the canonical even
window.
-/
noncomputable def halfMassVarianceWindowUpper (X : ℕ) : ℝ :=
  halfMassRecenteredVarianceWindowEnergy X

/--
Any certified upper bound for the exact centered variance expression upgrades to the variance-form
arithmetic target.
-/
theorem halfMassArithmeticVarianceTarget_of_windowUpper
    {C2 C3 : ℝ}
    (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        halfMassVarianceWindowUpper X
          ≤
        C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) :
    HalfMassArithmeticVarianceTarget C2 C3 := by
  refine ⟨hC2, hC3, ?_⟩
  intro X hX
  simpa [halfMassVarianceWindowUpper] using hUpper (X := X) hX

private lemma norm_sub_sq_le_two_mul_norm_sub_sq_add_two_mul_norm_sub_sq
    (z a b : ℂ) :
    ‖z - b‖ ^ 2 ≤ 2 * ‖z - a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have htri : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
    have := norm_add_le (z - a) (a - b)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hsq : ‖z - b‖ ^ 2 ≤ (‖z - a‖ + ‖a - b‖) ^ 2 := by
    nlinarith [htri, norm_nonneg (z - b), norm_nonneg (z - a), norm_nonneg (a - b)]
  have hquad : (‖z - a‖ + ‖a - b‖) ^ 2 ≤ 2 * ‖z - a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z - a‖ - ‖a - b‖)]
  exact le_trans hsq hquad

/--
Formal reduction from a variance estimate to the endpoint target.

The only extra input needed is that the canonical window average has already been identified with a
single scalar `κ`. This keeps scalar identification separate from the variance bound itself.
-/
theorem halfMassRecenteredZeroModeTarget_of_average_and_variance
    {κ C2 C3 : ℝ}
    (hκ : HalfMassWindowAverageTarget κ)
    (hVar : HalfMassArithmeticVarianceTarget C2 C3) :
    HalfMassRecenteredZeroModeTarget κ C2 C3 := by
  refine ⟨hVar.C2_nonneg, hVar.C3_nonneg, ?_⟩
  intro X hX
  have hbound := hVar.bound (X := X) hX
  unfold halfMassRecenteredVarianceWindowEnergy at hbound
  unfold halfMassRecenteredZeroModeErrorWindowEnergy
  rw [show
      (∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2)
        =
      ∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2 by
        refine Finset.sum_congr rfl ?_
        intro N hN
        rw [show halfMassRecenteredZeroModeError κ X N
            = halfMassRecenteredZeroModeObservable X N - (κ : ℂ) by rfl]
        rw [hκ.average_eq hX]
        ]
  exact hbound

/--
Formal reduction from the centered variance bound plus a scale-by-scale average-stability bound to
the fixed-scalar endpoint.

This is the mathematically honest version of the projection-to-constants reduction: the window
average handles the local projection, and the stability term controls how far that projected scalar
is from a single global `κ`.
-/
theorem halfMassRecenteredZeroModeTarget_of_variance_and_averageStability
    {κ C2v C3v C2a C3a : ℝ}
    (hVar : HalfMassArithmeticVarianceTarget C2v C3v)
    (hAvg : HalfMassWindowAverageStabilityTarget κ C2a C3a) :
    HalfMassRecenteredZeroModeTarget κ (2 * C2v + 2 * C2a) (2 * C3v + 2 * C3a) := by
  refine ⟨by nlinarith [hVar.C2_nonneg, hAvg.C2_nonneg],
    by nlinarith [hVar.C3_nonneg, hAvg.C3_nonneg], ?_⟩
  intro X hX
  have hterm :
      ∀ N ∈ EvenIn X H,
        ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2
          ≤
        2 * ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2
          + 2 * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2 := by
    intro N hN
    simpa [halfMassRecenteredZeroModeError] using
      norm_sub_sq_le_two_mul_norm_sub_sq_add_two_mul_norm_sub_sq
        (halfMassRecenteredZeroModeObservable X N) (halfMassRecenteredWindowAverage X) (κ : ℂ)
  have hsum :
      (∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2)
        ≤
      ∑ N ∈ EvenIn X H,
        (2 * ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2
          + 2 * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2) := by
    exact Finset.sum_le_sum (fun N hN => hterm N hN)
  have hsplit :
      ∑ N ∈ EvenIn X H,
        (2 * ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2
          + 2 * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2)
        =
      2 * halfMassRecenteredVarianceWindowEnergy X
        + 2 * halfMassWindowAverageStabilityEnergy κ X := by
    unfold halfMassRecenteredVarianceWindowEnergy halfMassWindowAverageStabilityEnergy
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    have hconst :
        ∑ x ∈ EvenIn X H, 2 * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2
          =
        ((EvenIn X H).card : ℝ) * (2 * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    ring
  have hVarBound := hVar.bound (X := X) hX
  have hAvgBound := hAvg.bound (X := X) hX
  calc
    halfMassRecenteredZeroModeErrorWindowEnergy κ X
        = ∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2 := by
            rfl
    _ ≤
      ∑ N ∈ EvenIn X H,
        (2 * ‖halfMassRecenteredZeroModeObservable X N - halfMassRecenteredWindowAverage X‖ ^ 2
          + 2 * ‖halfMassRecenteredWindowAverage X - (κ : ℂ)‖ ^ 2) := hsum
    _ =
      2 * halfMassRecenteredVarianceWindowEnergy X
        + 2 * halfMassWindowAverageStabilityEnergy κ X := hsplit
    _ ≤
      2 * (C2v * ((H : ℝ) / (X : ℝ))
          + C3v / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        + 2 * (C2a * ((H : ℝ) / (X : ℝ))
          + C3a / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hVarBound (by norm_num))
        (mul_le_mul_of_nonneg_left hAvgBound (by norm_num))
    _ =
      (2 * C2v + 2 * C2a) * ((H : ℝ) / (X : ℝ))
        + (2 * C3v + 2 * C3a) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      ring

theorem halfMassRecenteredZeroModeTarget_of_averageTarget_and_variance
    {κ C2 C3 : ℝ}
    (hAvg : HalfMassWindowAverageTarget κ)
    (hVar : HalfMassArithmeticVarianceTarget C2 C3) :
    HalfMassRecenteredZeroModeTarget κ (2 * C2) (2 * C3) := by
  simpa using
    halfMassRecenteredZeroModeTarget_of_variance_and_averageStability
      hVar
      (halfMassWindowAverageStabilityTarget_of_averageTarget hAvg)

/--
Arithmetic endpoint reduced to two pieces:
1. identify the canonical window average with a scalar `κ`;
2. prove the centered variance bound.
-/
def halfMassArithmeticPaperTarget_of_average_and_variance
    {κ C2 C3 : ℝ}
    (hκ : HalfMassWindowAverageTarget κ)
    (hVar : HalfMassArithmeticVarianceTarget C2 C3)
    (hShape : ZeroModeEnvelopeShapeTarget κ C2 C3) :
    HalfMassArithmeticPaperTarget where
  κ := κ
  C2 := C2
  C3 := C3
  target := halfMassRecenteredZeroModeTarget_of_average_and_variance hκ hVar
  shape_target := hShape

/--
More realistic paper-facing construction: combine the centered variance estimate with a separate
stability bound for the scale-by-scale window average.
-/
def halfMassArithmeticPaperTarget_of_variance_and_averageStability
    {κ C2v C3v C2a C3a : ℝ}
    (hVar : HalfMassArithmeticVarianceTarget C2v C3v)
    (hAvg : HalfMassWindowAverageStabilityTarget κ C2a C3a)
    (hShape : ZeroModeEnvelopeShapeTarget κ (2 * C2v + 2 * C2a) (2 * C3v + 2 * C3a)) :
    HalfMassArithmeticPaperTarget where
  κ := κ
  C2 := 2 * C2v + 2 * C2a
  C3 := 2 * C3v + 2 * C3a
  target := halfMassRecenteredZeroModeTarget_of_variance_and_averageStability hVar hAvg
  shape_target := hShape

def HalfMassArithmeticPaperTarget.of_endpoint (e : HalfMassRecenteredEndpoint) :
    HalfMassArithmeticPaperTarget where
  κ := e.κ
  C2 := e.C2
  C3 := e.C3
  target := e.target
  shape_target := e.shape_target

/--
The canonical arithmetic endpoint exported to the assembled bridge.
-/
def HalfMassArithmeticPaperTarget.to_endpoint (h : HalfMassArithmeticPaperTarget) :
    HalfMassRecenteredEndpoint where
  κ := h.κ
  C2 := h.C2
  C3 := h.C3
  target := h.target
  shape_target := h.shape_target

/--
Current arithmetic frontier: a theorem-shaped paper boundary for the half-mass-recentered
observable.
-/
def vaughanHalfMassArithmeticPaperTarget : HalfMassArithmeticPaperTarget :=
  HalfMassArithmeticPaperTarget.of_endpoint vaughanHalfMassRecenteredEndpoint

def vaughanHalfMassRecenteredEndpoint_of_paperBoundary :
    HalfMassRecenteredEndpoint :=
  vaughanHalfMassArithmeticPaperTarget.to_endpoint

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
