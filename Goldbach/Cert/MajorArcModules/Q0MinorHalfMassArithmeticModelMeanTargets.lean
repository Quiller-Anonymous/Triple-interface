import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassGeometricScalarBounds
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks

/-!
Average-native theorem surfaces for the half-mass arithmetic-model object.

The recent recentering audit shows that the arithmetic-model window average is exactly the old
half-mass window average multiplied by the explicit scalar `((2 : ℂ) * exactGeometricScalar X)⁻¹`.
So the right next interface layer is not another decomposition file. It is the mean-theorem
surface for:

* the arithmetic-model raw window sum;
* the arithmetic-model window average;
* exact transport between those statements and the existing half-mass average witness.

This file deliberately stays deterministic. It does not try to prove the arithmetic mean theorem.
It only packages the target that such a theorem would need to hit.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassGeometricScalarBounds

noncomputable section

private lemma even_window_card_ne_zero
    {X : ℕ} (_hX : X0 ≤ X) :
    (EvenIn X H).card ≠ 0 := by
  refine Finset.card_ne_zero.mpr ?_
  by_cases hEven : Goldbach.Windows.IsEven X
  · exact ⟨X, Goldbach.Windows.mem_EvenIn_self (N := X) (H := H) hEven⟩
  · have h1 : 1 ∈ Finset.range (H + 1) := by
      norm_num [H]
    have hEvenSucc : Goldbach.Windows.IsEven (X + 1) := by
      dsimp [Goldbach.Windows.IsEven] at hEven ⊢
      omega
    unfold Goldbach.Windows.EvenIn Goldbach.Windows.IccShift
    refine ⟨X + 1, Finset.mem_filter.mpr ?_⟩
    refine ⟨Finset.mem_image.mpr ?_, hEvenSucc⟩
    exact ⟨1, h1, by simp⟩

private lemma even_window_card_inv_le_one
    {X : ℕ} (hX : X0 ≤ X) :
    ((EvenIn X H).card : ℝ)⁻¹ ≤ 1 := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcard_pos : 0 < ((EvenIn X H).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard_nat
  have hcard_ge_one : 1 ≤ ((EvenIn X H).card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcard_nat)
  exact (inv_le_one₀ hcard_pos).2 hcard_ge_one

/-- The arithmetic-model window average itself, viewed as the canonical scale-dependent witness. -/
noncomputable def halfMassArithmeticModelAverageWitness (X : ℕ) : ℂ :=
  halfMassArithmeticModelWindowAverage X

/--
The old half-mass window average rewritten through the arithmetic model and the exact geometric
recentering scalar.
-/
noncomputable def halfMassArithmeticModelScaledAverageWitness (X : ℕ) : ℂ :=
  ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModelWindowAverage X

theorem halfMassArithmeticModelAverageWitness_eq_average
    (X : ℕ) :
    halfMassArithmeticModelAverageWitness X = halfMassArithmeticModelWindowAverage X := by
  rfl

theorem halfMassArithmeticModelScaledAverageWitness_eq_scaled_average
    (X : ℕ) :
    halfMassArithmeticModelScaledAverageWitness X
      =
    ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModelWindowAverage X := by
  rfl

theorem halfMassArithmeticModelScaledAverageWitness_eq_halfMassCanonicalAverageWitness
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassArithmeticModelScaledAverageWitness X = halfMassCanonicalAverageWitness X := by
  unfold halfMassArithmeticModelScaledAverageWitness halfMassCanonicalAverageWitness
  rw [halfMassRecenteredWindowAverage_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowAverage hX]

theorem halfMassArithmeticModelWindowAverage_eq_card_inv_mul_rawSum
    (X : ℕ) :
    halfMassArithmeticModelWindowAverage X
      =
    ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelWindowRawSum X := by
  rfl

theorem halfMassArithmeticModelWindowRawSum_eq_card_mul_average
    (X : ℕ) :
    halfMassArithmeticModelWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * halfMassArithmeticModelWindowAverage X := by
  rw [halfMassArithmeticModelWindowAverage_eq_card_inv_mul_rawSum]
  by_cases hcard : (EvenIn X H).card = 0
  · have hsum : halfMassArithmeticModelWindowRawSum X = 0 := by
      have hempty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard
      rw [halfMassArithmeticModelWindowRawSum, hempty, Finset.sum_empty]
    simp [hcard, hsum]
  · have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
      exact_mod_cast hcard
    calc
      halfMassArithmeticModelWindowRawSum X
          =
        ((EvenIn X H).card : ℂ)
          * (((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelWindowRawSum X) := by
            field_simp [hcardC]
      _ = ((EvenIn X H).card : ℂ) * halfMassArithmeticModelWindowAverage X := by
            rw [halfMassArithmeticModelWindowAverage_eq_card_inv_mul_rawSum]

/--
Scale-dependent witness target for the arithmetic-model average. This is the exact average-native
surface that a future half-mass mean theorem should hit.
-/
structure HalfMassArithmeticModelWindowAverageWitnessTarget (κX : ℕ → ℂ) : Prop where
  average_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassArithmeticModelWindowAverage X = κX X

/--
Equivalent raw-sum witness target for the arithmetic model on the canonical even window.
-/
structure HalfMassArithmeticModelWindowRawSumWitnessTarget (κX : ℕ → ℂ) : Prop where
  rawSum_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassArithmeticModelWindowRawSum X = ((EvenIn X H).card : ℂ) * κX X

/--
Real-part lower-bound target for the arithmetic-model average. This is the one-sided mean theorem
surface naturally suggested by the Route A and half-mass audits.
-/
structure HalfMassArithmeticModelWindowAverageLowerBoundTarget (μ : ℕ → ℝ) : Prop where
  lower :
    ∀ {X : ℕ}, X0 ≤ X →
      μ X ≤ (halfMassArithmeticModelWindowAverage X).re

theorem halfMassArithmeticModelAverageWitness_target :
    HalfMassArithmeticModelWindowAverageWitnessTarget halfMassArithmeticModelAverageWitness := by
  refine ⟨?_⟩
  intro X hX
  rfl

theorem halfMassArithmeticModelScaledAverageWitness_target :
    HalfMassWindowAverageWitnessTarget halfMassArithmeticModelScaledAverageWitness := by
  refine ⟨?_⟩
  intro X hX
  simpa [halfMassCanonicalAverageWitness] using
    (halfMassArithmeticModelScaledAverageWitness_eq_halfMassCanonicalAverageWitness (X := X) hX).symm

theorem HalfMassArithmeticModelWindowAverageWitnessTarget.to_rawSumTarget
    {κX : ℕ → ℂ} (h : HalfMassArithmeticModelWindowAverageWitnessTarget κX) :
    HalfMassArithmeticModelWindowRawSumWitnessTarget κX := by
  refine ⟨?_⟩
  intro X hX
  rw [halfMassArithmeticModelWindowRawSum_eq_card_mul_average, h.average_eq hX]

theorem halfMassArithmeticModelWindowAverageWitnessTarget_of_rawSum
    {κX : ℕ → ℂ} (h : HalfMassArithmeticModelWindowRawSumWitnessTarget κX) :
    HalfMassArithmeticModelWindowAverageWitnessTarget κX := by
  refine ⟨?_⟩
  intro X hX
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  rw [halfMassArithmeticModelWindowAverage_eq_card_inv_mul_rawSum, h.rawSum_eq hX]
  field_simp [hcardC]

/--
Transport an arithmetic-model average witness into the existing half-mass average witness by
reinstalling the exact geometric recentering scalar.
-/
theorem HalfMassArithmeticModelWindowAverageWitnessTarget.to_halfMassWindowAverageWitnessTarget
    {κX : ℕ → ℂ} (h : HalfMassArithmeticModelWindowAverageWitnessTarget κX) :
    HalfMassWindowAverageWitnessTarget
      (fun X => ((2 : ℂ) * exactGeometricScalar X) * κX X) := by
  refine ⟨?_⟩
  intro X hX
  calc
    halfMassRecenteredWindowAverage X
        =
      ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModelWindowAverage X := by
          exact
            halfMassRecenteredWindowAverage_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowAverage hX
    _ = ((2 : ℂ) * exactGeometricScalar X) * κX X := by rw [h.average_eq hX]

/--
Inverse transport from the existing half-mass average witness to the arithmetic-model average
witness.
-/
theorem HalfMassWindowAverageWitnessTarget.to_halfMassArithmeticModelWindowAverageWitnessTarget
    {κX : ℕ → ℂ} (h : HalfMassWindowAverageWitnessTarget κX) :
    HalfMassArithmeticModelWindowAverageWitnessTarget
      (fun X => (((2 : ℂ) * exactGeometricScalar X)⁻¹) * κX X) := by
  refine ⟨?_⟩
  intro X hX
  calc
    halfMassArithmeticModelWindowAverage X
        =
      (((2 : ℂ) * exactGeometricScalar X)⁻¹) * halfMassRecenteredWindowAverage X := by
          exact
            halfMassArithmeticModelWindowAverage_eq_inv_two_mul_exactGeometricScalar_mul_average hX
    _ = (((2 : ℂ) * exactGeometricScalar X)⁻¹) * κX X := by rw [h.average_eq hX]

/--
Constant-scalar transport from a half-mass average target to the arithmetic-model average witness.
-/
theorem HalfMassWindowAverageTarget.to_halfMassArithmeticModelWindowAverageWitnessTarget
    {κ : ℝ} (h : HalfMassWindowAverageTarget κ) :
    HalfMassArithmeticModelWindowAverageWitnessTarget
      (fun X => (((2 : ℂ) * exactGeometricScalar X)⁻¹) * (κ : ℂ)) := by
  exact
    HalfMassWindowAverageWitnessTarget.to_halfMassArithmeticModelWindowAverageWitnessTarget
      (h := h.to_scaleWitness)

/--
If the arithmetic-model average is exactly the inverse-scaled constant witness, then the old
half-mass average target follows immediately.
-/
theorem HalfMassArithmeticModelWindowAverageWitnessTarget.to_halfMassWindowAverageTarget
    {κ : ℝ}
    (h :
      HalfMassArithmeticModelWindowAverageWitnessTarget
        (fun X => (((2 : ℂ) * exactGeometricScalar X)⁻¹) * (κ : ℂ))) :
    HalfMassWindowAverageTarget κ := by
  refine ⟨?_⟩
  intro X hX
  have hmain := h.average_eq (X := X) hX
  calc
    halfMassRecenteredWindowAverage X
        =
      ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModelWindowAverage X := by
          exact
            halfMassRecenteredWindowAverage_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowAverage hX
    _ =
      ((2 : ℂ) * exactGeometricScalar X)
        * ((((2 : ℂ) * exactGeometricScalar X)⁻¹) * (κ : ℂ)) := by
          rw [hmain]
    _ = (κ : ℂ) := by
          have hγ : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
          have hfac : ((2 : ℂ) * exactGeometricScalar X) ≠ 0 := by
            exact mul_ne_zero (by norm_num) hγ
          field_simp [hfac]

theorem HalfMassArithmeticModelWindowAverageWitnessTarget.to_lowerBoundTarget
    {κX : ℕ → ℂ}
    (h : HalfMassArithmeticModelWindowAverageWitnessTarget κX) :
    HalfMassArithmeticModelWindowAverageLowerBoundTarget (fun X => (κX X).re) := by
  refine ⟨?_⟩
  intro X hX
  rw [h.average_eq hX]

/--
Scale-dependent main scalar for the arithmetic-model object induced by an intrinsic scalar witness
for the unscaled post-`σ` ratio.
-/
noncomputable def halfMassArithmeticModelMainScalar (κ : ℝ) (X : ℕ) : ℂ :=
  (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹ * (κ : ℂ)

/--
Scale-dependent pointwise error term for the arithmetic-model object induced by the corresponding
unscaled ratio error.
-/
noncomputable def halfMassArithmeticModelScalarError (κ : ℝ) (X N : ℕ) : ℂ :=
  (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
    * Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N

/-- Raw window sum of the induced arithmetic-model error term on the canonical even window. -/
noncomputable def halfMassArithmeticModelScalarErrorWindowRawSum (κ : ℝ) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, halfMassArithmeticModelScalarError κ X N

/-- Canonical even-window average of the induced arithmetic-model error term. -/
noncomputable def halfMassArithmeticModelScalarErrorWindowAverage (κ : ℝ) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelScalarErrorWindowRawSum κ X

/--
Pointwise `main + error` decomposition for the arithmetic-model object, transported directly from
the intrinsic scalar-plus-error decomposition of the unscaled post-`σ` ratio.
-/
theorem halfMassArithmeticModel_eq_mainScalar_add_scalarError
    (κ : ℝ) {X N : ℕ} :
    halfMassArithmeticModel X N
      =
    halfMassArithmeticModelMainScalar κ X
      + halfMassArithmeticModelScalarError κ X N := by
  unfold halfMassArithmeticModel halfMassArithmeticModelMainScalar
    halfMassArithmeticModelScalarError
  rw [Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable_eq_scalar_add_error]
  ring

/--
Raw-sum `main + error` decomposition for the arithmetic-model object on the canonical even window.

This is the smallest average-native identity for the half-mass arithmetic-model mean problem.
Any future arithmetic proof should supply the main scalar and then control the error sum.
-/
theorem halfMassArithmeticModelWindowRawSum_eq_card_mul_mainScalar_add_errorRawSum
    (κ : ℝ) (X : ℕ) :
    halfMassArithmeticModelWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * halfMassArithmeticModelMainScalar κ X
      + halfMassArithmeticModelScalarErrorWindowRawSum κ X := by
  unfold halfMassArithmeticModelWindowRawSum halfMassArithmeticModelScalarErrorWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, halfMassArithmeticModel X N
        =
      ∑ N ∈ EvenIn X H,
        (halfMassArithmeticModelMainScalar κ X + halfMassArithmeticModelScalarError κ X N) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          exact halfMassArithmeticModel_eq_mainScalar_add_scalarError κ
    _ =
      (∑ _N ∈ EvenIn X H, halfMassArithmeticModelMainScalar κ X)
        + ∑ N ∈ EvenIn X H, halfMassArithmeticModelScalarError κ X N := by
          rw [Finset.sum_add_distrib]
    _ =
      ((EvenIn X H).card : ℂ) * halfMassArithmeticModelMainScalar κ X
        + ∑ N ∈ EvenIn X H, halfMassArithmeticModelScalarError κ X N := by
          rw [Finset.sum_const, nsmul_eq_mul]

/--
Average-form `main + error` decomposition for the arithmetic-model object on the canonical even
window.
-/
theorem halfMassArithmeticModelWindowAverage_eq_mainScalar_add_errorAverage
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    halfMassArithmeticModelWindowAverage X
      =
    halfMassArithmeticModelMainScalar κ X
      + halfMassArithmeticModelScalarErrorWindowAverage κ X := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  unfold halfMassArithmeticModelWindowAverage halfMassArithmeticModelScalarErrorWindowAverage
  rw [halfMassArithmeticModelWindowRawSum_eq_card_mul_mainScalar_add_errorRawSum]
  calc
    ((EvenIn X H).card : ℂ)⁻¹
        * (((EvenIn X H).card : ℂ) * halfMassArithmeticModelMainScalar κ X
            + halfMassArithmeticModelScalarErrorWindowRawSum κ X)
        =
      (((EvenIn X H).card : ℂ)⁻¹ * ((EvenIn X H).card : ℂ))
          * halfMassArithmeticModelMainScalar κ X
        + ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelScalarErrorWindowRawSum κ X := by
            ring
    _ =
      halfMassArithmeticModelMainScalar κ X
        + ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelScalarErrorWindowRawSum κ X := by
            rw [inv_mul_cancel₀ hcardC, one_mul]
    _ =
      halfMassArithmeticModelMainScalar κ X
        + halfMassArithmeticModelScalarErrorWindowAverage κ X := by
            rfl

/--
If the arithmetic-model error average vanishes, the arithmetic-model average is exactly the main
scalar induced by the unscaled intrinsic witness `κ`.
-/
theorem halfMassArithmeticModelWindowAverage_eq_mainScalar_of_errorAverage_eq_zero
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X)
    (hErr : halfMassArithmeticModelScalarErrorWindowAverage κ X = 0) :
    halfMassArithmeticModelWindowAverage X = halfMassArithmeticModelMainScalar κ X := by
  rw [halfMassArithmeticModelWindowAverage_eq_mainScalar_add_errorAverage κ hX, hErr, add_zero]

/-- Raw window sum of the unscaled post-`σ` ratio observable on the canonical even window. -/
noncomputable def unscaledZeroModeMassRatioWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable X N

/-- Canonical even-window average of the unscaled post-`σ` ratio observable. -/
noncomputable def unscaledZeroModeMassRatioWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeMassRatioWindowRawSum X

theorem unscaledZeroModeMassRatioWindowAverage_eq_card_inv_mul_rawSum
    (X : ℕ) :
    unscaledZeroModeMassRatioWindowAverage X
      =
    ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeMassRatioWindowRawSum X := by
  rfl

theorem unscaledZeroModeMassRatioWindowRawSum_eq_card_mul_average
    (X : ℕ) :
    unscaledZeroModeMassRatioWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * unscaledZeroModeMassRatioWindowAverage X := by
  rw [unscaledZeroModeMassRatioWindowAverage_eq_card_inv_mul_rawSum]
  by_cases hcard : (EvenIn X H).card = 0
  · have hsum : unscaledZeroModeMassRatioWindowRawSum X = 0 := by
      have hempty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard
      rw [unscaledZeroModeMassRatioWindowRawSum, hempty, Finset.sum_empty]
    simp [hcard, hsum]
  · have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
      exact_mod_cast hcard
    calc
      unscaledZeroModeMassRatioWindowRawSum X
          =
        ((EvenIn X H).card : ℂ)
          * (((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeMassRatioWindowRawSum X) := by
            field_simp [hcardC]
      _ = ((EvenIn X H).card : ℂ) * unscaledZeroModeMassRatioWindowAverage X := by
            rw [unscaledZeroModeMassRatioWindowAverage_eq_card_inv_mul_rawSum]

/--
Scale-dependent witness target for the unscaled post-`σ` ratio average.

This is now the cleanest live arithmetic theorem surface in the half-mass route.
-/
structure UnscaledZeroModeMassRatioWindowAverageWitnessTarget (κX : ℕ → ℂ) : Prop where
  average_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      unscaledZeroModeMassRatioWindowAverage X = κX X

/-- Raw-sum witness target for the unscaled post-`σ` ratio on the canonical even window. -/
structure UnscaledZeroModeMassRatioWindowRawSumWitnessTarget (κX : ℕ → ℂ) : Prop where
  rawSum_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      unscaledZeroModeMassRatioWindowRawSum X = ((EvenIn X H).card : ℂ) * κX X

/-- One-sided real-part lower-bound target for the unscaled post-`σ` ratio average. -/
structure UnscaledZeroModeMassRatioWindowAverageLowerBoundTarget (μ : ℕ → ℝ) : Prop where
  lower :
    ∀ {X : ℕ}, X0 ≤ X →
      μ X ≤ (unscaledZeroModeMassRatioWindowAverage X).re

/-- The exact window average itself is the canonical scale-dependent witness. -/
noncomputable def unscaledZeroModeMassRatioAverageWitness (X : ℕ) : ℂ :=
  unscaledZeroModeMassRatioWindowAverage X

theorem unscaledZeroModeMassRatioAverageWitness_target :
    UnscaledZeroModeMassRatioWindowAverageWitnessTarget unscaledZeroModeMassRatioAverageWitness := by
  refine ⟨?_⟩
  intro X hX
  rfl

theorem UnscaledZeroModeMassRatioWindowAverageWitnessTarget.to_rawSumTarget
    {κX : ℕ → ℂ} (h : UnscaledZeroModeMassRatioWindowAverageWitnessTarget κX) :
    UnscaledZeroModeMassRatioWindowRawSumWitnessTarget κX := by
  refine ⟨?_⟩
  intro X hX
  rw [unscaledZeroModeMassRatioWindowRawSum_eq_card_mul_average, h.average_eq hX]

theorem unscaledZeroModeMassRatioWindowAverageWitnessTarget_of_rawSum
    {κX : ℕ → ℂ} (h : UnscaledZeroModeMassRatioWindowRawSumWitnessTarget κX) :
    UnscaledZeroModeMassRatioWindowAverageWitnessTarget κX := by
  refine ⟨?_⟩
  intro X hX
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  rw [unscaledZeroModeMassRatioWindowAverage_eq_card_inv_mul_rawSum, h.rawSum_eq hX]
  field_simp [hcardC]

theorem UnscaledZeroModeMassRatioWindowAverageWitnessTarget.to_lowerBoundTarget
    {κX : ℕ → ℂ} (h : UnscaledZeroModeMassRatioWindowAverageWitnessTarget κX) :
    UnscaledZeroModeMassRatioWindowAverageLowerBoundTarget (fun X => (κX X).re) := by
  refine ⟨?_⟩
  intro X hX
  rw [h.average_eq hX]

/-- Raw even-window sum of the unscaled post-`σ` ratio error against the scalar `κ`. -/
noncomputable def unscaledZeroModeMassRatioErrorWindowRawSum (κ : ℝ) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N

/-- Canonical even-window average of the unscaled post-`σ` ratio error against the scalar `κ`. -/
noncomputable def unscaledZeroModeMassRatioErrorWindowAverage (κ : ℝ) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeMassRatioErrorWindowRawSum κ X

/--
Pointwise split of the unscaled post-`σ` ratio observable into the scalar `κ` plus its intrinsic
window error.
-/
theorem unscaledZeroModeMassRatioObservable_eq_scalar_add_error
    (κ : ℝ) (X N : ℕ) :
    Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable X N
      =
    (κ : ℂ) + Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N := by
  exact Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable_eq_scalar_add_error κ X N

/--
Raw-sum split of the unscaled post-`σ` ratio observable into the scalar `κ` plus its window error.
-/
theorem unscaledZeroModeMassRatioWindowRawSum_eq_card_mul_scalar_add_errorRawSum
    (κ : ℝ) (X : ℕ) :
    unscaledZeroModeMassRatioWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * (κ : ℂ)
      + unscaledZeroModeMassRatioErrorWindowRawSum κ X := by
  unfold unscaledZeroModeMassRatioWindowRawSum unscaledZeroModeMassRatioErrorWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable X N
        =
      ∑ N ∈ EvenIn X H,
        ((κ : ℂ) + Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          exact unscaledZeroModeMassRatioObservable_eq_scalar_add_error κ X N
    _ =
      (∑ _N ∈ EvenIn X H, (κ : ℂ))
        + ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N := by
          rw [Finset.sum_add_distrib]
    _ =
      ((EvenIn X H).card : ℂ) * (κ : ℂ)
        + ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N := by
          rw [Finset.sum_const, nsmul_eq_mul]

/--
Average split of the unscaled post-`σ` ratio observable into the scalar `κ` plus its window
average error.
-/
theorem unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeMassRatioWindowAverage X
      =
    (κ : ℂ) + unscaledZeroModeMassRatioErrorWindowAverage κ X := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  unfold unscaledZeroModeMassRatioWindowAverage unscaledZeroModeMassRatioErrorWindowAverage
  rw [unscaledZeroModeMassRatioWindowRawSum_eq_card_mul_scalar_add_errorRawSum]
  calc
    ((EvenIn X H).card : ℂ)⁻¹
        * (((EvenIn X H).card : ℂ) * (κ : ℂ)
            + unscaledZeroModeMassRatioErrorWindowRawSum κ X)
        =
      (((EvenIn X H).card : ℂ)⁻¹ * ((EvenIn X H).card : ℂ)) * (κ : ℂ)
        + ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeMassRatioErrorWindowRawSum κ X := by
            ring
    _ =
      (κ : ℂ) + ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeMassRatioErrorWindowRawSum κ X := by
        rw [inv_mul_cancel₀ hcardC, one_mul]
    _ = (κ : ℂ) + unscaledZeroModeMassRatioErrorWindowAverage κ X := by
        rfl

/--
The native unscaled ratio-average error vanishes exactly when the unscaled ratio window average
equals the scalar `κ`.

This is the sharp exact-centering criterion on the normalized route before any packet terms enter.
-/
theorem unscaledZeroModeMassRatioErrorWindowAverage_eq_zero_iff
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeMassRatioErrorWindowAverage κ X = 0
      ↔
    unscaledZeroModeMassRatioWindowAverage X = (κ : ℂ) := by
  constructor
  · intro herr
    rw [unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage κ hX, herr, add_zero]
  · intro havg
    have hsplit := unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage κ hX
    rw [havg] at hsplit
    have hsub := congrArg (fun z : ℂ => z - (κ : ℂ)) hsplit
    simpa using hsub.symm

/--
Raw-sum version of the exact-centering criterion for the native unscaled ratio error.
-/
theorem unscaledZeroModeMassRatioErrorWindowRawSum_eq_zero_iff
    (κ : ℝ) {X : ℕ} (_hX : X0 ≤ X) :
    unscaledZeroModeMassRatioErrorWindowRawSum κ X = 0
      ↔
    unscaledZeroModeMassRatioWindowRawSum X = ((EvenIn X H).card : ℂ) * (κ : ℂ) := by
  constructor
  · intro herr
    rw [unscaledZeroModeMassRatioWindowRawSum_eq_card_mul_scalar_add_errorRawSum, herr, add_zero]
  · intro hraw
    have hsplit := unscaledZeroModeMassRatioWindowRawSum_eq_card_mul_scalar_add_errorRawSum κ X
    rw [hraw] at hsplit
    have hs := hsplit.symm
    have hs0 :
        ((EvenIn X H).card : ℂ) * (κ : ℂ) + unscaledZeroModeMassRatioErrorWindowRawSum κ X
          =
        ((EvenIn X H).card : ℂ) * (κ : ℂ) + 0 := by
      calc
        ((EvenIn X H).card : ℂ) * (κ : ℂ) + unscaledZeroModeMassRatioErrorWindowRawSum κ X
            =
          ((EvenIn X H).card : ℂ) * (κ : ℂ) := hs
        _ =
          ((EvenIn X H).card : ℂ) * (κ : ℂ) + 0 := by rw [add_zero]
    exact add_left_cancel hs0

/-- Post-`σ` numerator quotient before dividing by the geometric zero-slice mass. -/
noncomputable def unscaledZeroModeSigmaQuotientObservable (X N : ℕ) : ℂ :=
  Q0MinorZeroModeEnvelope.rawExactZeroModeMass X N
    / Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N

/-- Raw even-window sum of the post-`σ` numerator quotient. -/
noncomputable def unscaledZeroModeSigmaQuotientWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientObservable X N

/-- Canonical even-window average of the post-`σ` numerator quotient. -/
noncomputable def unscaledZeroModeSigmaQuotientWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeSigmaQuotientWindowRawSum X

/--
Centered numerator defect for the unscaled post-`σ` ratio after freezing the geometric factor to
`exactGeometricScalar X`.
-/
noncomputable def unscaledZeroModeSigmaQuotientCenteredError (κ : ℝ) (X N : ℕ) : ℂ :=
  unscaledZeroModeSigmaQuotientObservable X N - (κ : ℂ) * exactGeometricScalar X

/-- Raw even-window sum of the centered post-`σ` numerator defect. -/
noncomputable def unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum (κ : ℝ) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientCenteredError κ X N

/-- Canonical even-window average of the centered post-`σ` numerator defect. -/
noncomputable def unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage (κ : ℝ) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X

theorem unscaledZeroModeSigmaQuotientWindowRawSum_eq_card_mul_average
    (X : ℕ) :
    unscaledZeroModeSigmaQuotientWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * unscaledZeroModeSigmaQuotientWindowAverage X := by
  unfold unscaledZeroModeSigmaQuotientWindowAverage
  by_cases hcard : (EvenIn X H).card = 0
  · have hsum : unscaledZeroModeSigmaQuotientWindowRawSum X = 0 := by
      have hempty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard
      rw [unscaledZeroModeSigmaQuotientWindowRawSum, hempty, Finset.sum_empty]
    simp [hcard, hsum]
  · have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
      exact_mod_cast hcard
    calc
      unscaledZeroModeSigmaQuotientWindowRawSum X
          =
        ((EvenIn X H).card : ℂ)
          * (((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeSigmaQuotientWindowRawSum X) := by
            field_simp [hcardC]
      _ = ((EvenIn X H).card : ℂ) * unscaledZeroModeSigmaQuotientWindowAverage X := by
            rfl

theorem unscaledZeroModeSigmaQuotientWindowRawSum_eq_card_mul_scalar_add_centeredErrorRawSum
    (κ : ℝ) (X : ℕ) :
    unscaledZeroModeSigmaQuotientWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X)
      + unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X := by
  unfold unscaledZeroModeSigmaQuotientWindowRawSum
    unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientObservable X N
        =
      ∑ N ∈ EvenIn X H,
        (((κ : ℂ) * exactGeometricScalar X)
          + unscaledZeroModeSigmaQuotientCenteredError κ X N) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          unfold unscaledZeroModeSigmaQuotientCenteredError
          ring
    _ =
      (∑ _N ∈ EvenIn X H, ((κ : ℂ) * exactGeometricScalar X))
        + ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientCenteredError κ X N := by
          rw [Finset.sum_add_distrib]
    _ =
      ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X)
        + ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientCenteredError κ X N := by
          rw [Finset.sum_const, nsmul_eq_mul]

theorem unscaledZeroModeSigmaQuotientWindowAverage_eq_scalar_mul_exactGeometricScalar_add_centeredErrorAverage
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeSigmaQuotientWindowAverage X
      =
    ((κ : ℂ) * exactGeometricScalar X)
      + unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  unfold unscaledZeroModeSigmaQuotientWindowAverage
    unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
  rw [unscaledZeroModeSigmaQuotientWindowRawSum_eq_card_mul_scalar_add_centeredErrorRawSum]
  calc
    ((EvenIn X H).card : ℂ)⁻¹
        * (((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X)
            + unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X)
        =
      (((EvenIn X H).card : ℂ)⁻¹ * ((EvenIn X H).card : ℂ))
          * ((κ : ℂ) * exactGeometricScalar X)
        + ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X := by
            ring
    _ =
      ((κ : ℂ) * exactGeometricScalar X)
        + ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X := by
            rw [inv_mul_cancel₀ hcardC, one_mul]
    _ =
      ((κ : ℂ) * exactGeometricScalar X)
        + unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X := by
            rfl

theorem unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage_eq_zero_iff
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X = 0
      ↔
    unscaledZeroModeSigmaQuotientWindowAverage X = (κ : ℂ) * exactGeometricScalar X := by
  constructor
  · intro herr
    rw [unscaledZeroModeSigmaQuotientWindowAverage_eq_scalar_mul_exactGeometricScalar_add_centeredErrorAverage κ hX,
      herr, add_zero]
  · intro havg
    have hsplit :=
      unscaledZeroModeSigmaQuotientWindowAverage_eq_scalar_mul_exactGeometricScalar_add_centeredErrorAverage κ hX
    rw [havg] at hsplit
    have hsub := congrArg (fun z : ℂ => z - ((κ : ℂ) * exactGeometricScalar X)) hsplit
    simpa using hsub.symm

theorem unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum_eq_zero_iff
    (κ : ℝ) {X : ℕ} (_hX : X0 ≤ X) :
    unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X = 0
      ↔
    unscaledZeroModeSigmaQuotientWindowRawSum X
      = ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X) := by
  constructor
  · intro herr
    rw [unscaledZeroModeSigmaQuotientWindowRawSum_eq_card_mul_scalar_add_centeredErrorRawSum, herr, add_zero]
  · intro hraw
    have hsplit := unscaledZeroModeSigmaQuotientWindowRawSum_eq_card_mul_scalar_add_centeredErrorRawSum κ X
    rw [hraw] at hsplit
    have hs :
        ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X)
          + unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X
          =
        ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X) + 0 := by
      calc
        ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X)
            + unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum κ X
          =
        ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X) := hsplit.symm
        _ =
        ((EvenIn X H).card : ℂ) * ((κ : ℂ) * exactGeometricScalar X) + 0 := by
          rw [add_zero]
    exact add_left_cancel hs

private lemma sigmaNormalizedSeries_re_eq_real_local (N : ℕ) :
    (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re
      =
    Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
      / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) := by
  simpa [Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries] using
    (Complex.ofReal_re
      (Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)))

private lemma sigmaNormalizedSeries_im_eq_zero_local (N : ℕ) :
    (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).im = 0 := by
  simpa [Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries] using
    (Complex.ofReal_im
      (Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)))

private lemma one_le_sigmaNormalizedSeries_re_of_mem_even_window_local
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    1 ≤ (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re := by
  rw [sigmaNormalizedSeries_re_eq_real_local]
  have hσ := Goldbach.Analytic.SigmaLowerOn_working.bound hX hN
  have hden_pos : 0 < ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) := by
    nlinarith [Goldbach.Analytic.C2_numeric.pos]
  have hden_le :
      ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)
        ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N := by
    simpa [Goldbach.Analytic.σmin_working] using hσ
  have hratio :
      1
        ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
            / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) := by
    exact (one_le_div_iff).2 <| Or.inl ⟨hden_pos, hden_le⟩
  simpa [div_eq_mul_inv] using hratio

theorem sigmaNormalizedSeries_ne_zero_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0 := by
  have hreal_pos :
      0 < (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re := by
    linarith [one_le_sigmaNormalizedSeries_re_of_mem_even_window_local hX hN]
  intro hzero
  have hre : (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re = 0 := by
    simp [hzero]
  linarith

theorem norm_inv_sigmaNormalizedSeries_le_one_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖(Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N)⁻¹‖ ≤ 1 := by
  have hσre_one :
      1 ≤ (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re :=
    one_le_sigmaNormalizedSeries_re_of_mem_even_window_local hX hN
  have hσeq :
      Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N
        =
      (((Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · exact sigmaNormalizedSeries_im_eq_zero_local N
  rw [hσeq]
  rw [norm_inv]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) hσre_one)]
  have hσre_pos : 0 < (Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N).re := by
    linarith
  rw [inv_le_one₀ hσre_pos]
  exact hσre_one

theorem norm_inv_exactGeometricScalar_le_inv_Kfull_zero
    {X : ℕ} (hX : X0 ≤ X) :
    ‖(exactGeometricScalar X)⁻¹‖ ≤ (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹ := by
  have hγeq : exactGeometricScalar X = (((exactGeometricScalar X).re : ℝ) : ℂ) :=
    exactGeometricScalar_eq_realPart X
  have hγnonneg : 0 ≤ (exactGeometricScalar X).re := exactGeometricScalar_re_nonneg hX
  have hγlower : Goldbach.BG_Identity.K_full (0 : ℤ) ≤ (exactGeometricScalar X).re :=
    exactGeometricScalar_re_lower hX
  have hKpos : 0 < Goldbach.BG_Identity.K_full (0 : ℤ) :=
    Goldbach.BG_Identity.K_full_pos_at_zero
  rw [hγeq, norm_inv]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγnonneg]
  exact Goldbach.BG_Bank.inv_le_inv_of_le_real hKpos hγlower

/--
Exact numerator/denominator rewrite of the unscaled ratio error.

This is the first native pointwise form of the live arithmetic seam.
-/
theorem unscaledZeroModeMassRatioError_eq_numeratorDefect_div_denominator
    (κ : ℝ) {X N : ℕ}
    (hunscaled : Q0MinorZeroModeEnvelope.unscaledGeometricZeroSliceMass X N ≠ 0)
    (hsig : Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0) :
    Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N
      =
    (Q0MinorZeroModeEnvelope.rawExactZeroModeMass X N
        - (κ : ℂ) * (Q0MinorZeroModeEnvelope.unscaledGeometricZeroSliceMass X N
            * Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N))
      / (Q0MinorZeroModeEnvelope.unscaledGeometricZeroSliceMass X N
          * Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N) := by
  unfold Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError
    Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable
  field_simp [hunscaled, hsig]

/--
On the canonical even window, the ratio error is the inverse exact geometric scalar times a
centered post-`σ` numerator defect.

This removes the varying geometric denominator entirely; only the `σ`-weighted numerator average
remains.
-/
theorem unscaledZeroModeMassRatioError_eq_exactGeometricScalar_inv_mul_sigmaQuotientCenteredError
    (κ : ℝ) {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hsig : Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0) :
    Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N
      =
    (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaQuotientCenteredError κ X N := by
  have hγne : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  rw [Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError]
  rw [Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable]
  rw [unscaledGeometricZeroSliceMass_eq_exactGeometricScalar hX hN]
  unfold unscaledZeroModeSigmaQuotientCenteredError unscaledZeroModeSigmaQuotientObservable
  field_simp [hγne, hsig]

/--
Window-average reduction of the unscaled ratio error to the centered post-`σ` numerator average.
-/
theorem unscaledZeroModeMassRatioErrorWindowAverage_eq_exactGeometricScalar_inv_mul_sigmaQuotientCenteredErrorAverage
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0) :
    unscaledZeroModeMassRatioErrorWindowAverage κ X
      =
    (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X := by
  have hγne : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  unfold unscaledZeroModeMassRatioErrorWindowAverage
    unscaledZeroModeMassRatioErrorWindowRawSum
    unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
    unscaledZeroModeSigmaQuotientCenteredErrorWindowRawSum
  calc
    ((EvenIn X H).card : ℂ)⁻¹
        * ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N
      =
    ((EvenIn X H).card : ℂ)⁻¹
        * ∑ N ∈ EvenIn X H,
            ((exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaQuotientCenteredError κ X N) := by
          refine congrArg (fun z : ℂ => ((EvenIn X H).card : ℂ)⁻¹ * z) ?_
          refine Finset.sum_congr rfl ?_
          intro N hN
          rw [unscaledZeroModeMassRatioError_eq_exactGeometricScalar_inv_mul_sigmaQuotientCenteredError
            κ hX hN (hsig (N := N) hN)]
    _ =
      (((EvenIn X H).card : ℂ)⁻¹ * (exactGeometricScalar X)⁻¹)
        * ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientCenteredError κ X N := by
          have hsum :
              (∑ N ∈ EvenIn X H,
                  (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaQuotientCenteredError κ X N)
                =
              (exactGeometricScalar X)⁻¹
                * ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientCenteredError κ X N := by
            rw [← Finset.mul_sum]
          rw [hsum]
          ring
    _ =
      (exactGeometricScalar X)⁻¹
        * (((EvenIn X H).card : ℂ)⁻¹
            * ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaQuotientCenteredError κ X N) := by
          ring

theorem unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage_eq_exactGeometricScalar_mul_ratioErrorAverage
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0) :
    unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X
      =
    exactGeometricScalar X * unscaledZeroModeMassRatioErrorWindowAverage κ X := by
  have hγne : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  calc
    unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X
        =
      exactGeometricScalar X
        * ((exactGeometricScalar X)⁻¹
            * unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X) := by
          field_simp [hγne]
    _ =
      exactGeometricScalar X * unscaledZeroModeMassRatioErrorWindowAverage κ X := by
          rw [← unscaledZeroModeMassRatioErrorWindowAverage_eq_exactGeometricScalar_inv_mul_sigmaQuotientCenteredErrorAverage
            κ hX hsig]

/--
Intrinsic scale-dependent main witness for the arithmetic-model average, induced by the exact
window average of the unscaled post-`σ` ratio.
-/
noncomputable def halfMassArithmeticModelIntrinsicMainWitness (X : ℕ) : ℂ :=
  (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
    * unscaledZeroModeMassRatioWindowAverage X

/--
Intrinsic centered error term for the arithmetic model after subtracting the exact window-average
main witness of the unscaled post-`σ` ratio.
-/
noncomputable def halfMassArithmeticModelIntrinsicCenteredError (X N : ℕ) : ℂ :=
  (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
    * (Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable X N
        - unscaledZeroModeMassRatioWindowAverage X)

/-- Raw window sum of the intrinsic centered arithmetic-model error term. -/
noncomputable def halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, halfMassArithmeticModelIntrinsicCenteredError X N

/-- Canonical even-window average of the intrinsic centered arithmetic-model error term. -/
noncomputable def halfMassArithmeticModelIntrinsicCenteredErrorWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X

private lemma centered_window_rawSum_eq_zero
    {X : ℕ} (f : ℕ → ℂ) :
    (∑ N ∈ EvenIn X H,
        (f N - ((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, f M))
      = 0 := by
  by_cases hcard_nat : (EvenIn X H).card = 0
  · have hEmpty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard_nat
    simp [hEmpty]
  · have hcard : ((EvenIn X H).card : ℂ) ≠ 0 := by
      exact_mod_cast hcard_nat
    have hmul :
        ((EvenIn X H).card : ℂ) * (((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, f M)
          =
        ∑ M ∈ EvenIn X H, f M := by
      calc
        ((EvenIn X H).card : ℂ) * (((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, f M)
            =
          ((((EvenIn X H).card : ℂ) * ((EvenIn X H).card : ℂ)⁻¹)
            * ∑ M ∈ EvenIn X H, f M) := by ring
        _ = ∑ M ∈ EvenIn X H, f M := by
          rw [mul_inv_cancel₀ hcard, one_mul]
    calc
      (∑ N ∈ EvenIn X H,
          (f N - ((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, f M))
          =
        (∑ N ∈ EvenIn X H, f N)
          - ∑ _N ∈ EvenIn X H, (((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, f M) := by
            rw [Finset.sum_sub_distrib]
      _ =
        (∑ N ∈ EvenIn X H, f N)
          - (((EvenIn X H).card : ℂ)
              * (((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, f M)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (∑ N ∈ EvenIn X H, f N) - (∑ M ∈ EvenIn X H, f M) := by
            rw [hmul]
      _ = 0 := by rw [sub_self]

/--
Pointwise split of the arithmetic-model object into its intrinsic scale-dependent window average
and its intrinsic centered error.
-/
theorem halfMassArithmeticModel_eq_intrinsicMainWitness_add_intrinsicCenteredError
    (X N : ℕ) :
    halfMassArithmeticModel X N
      =
    halfMassArithmeticModelIntrinsicMainWitness X
      + halfMassArithmeticModelIntrinsicCenteredError X N := by
  unfold halfMassArithmeticModel halfMassArithmeticModelIntrinsicMainWitness
    halfMassArithmeticModelIntrinsicCenteredError
    unscaledZeroModeMassRatioWindowAverage unscaledZeroModeMassRatioWindowRawSum
  ring

/--
The intrinsic centered arithmetic-model error has zero raw sum on the canonical even window.
-/
theorem halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum_eq_zero
    (X : ℕ) :
    halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X = 0 := by
  unfold halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum
    halfMassArithmeticModelIntrinsicCenteredError
    unscaledZeroModeMassRatioWindowAverage unscaledZeroModeMassRatioWindowRawSum
  rw [← Finset.mul_sum]
  rw [centered_window_rawSum_eq_zero]
  simp

/--
The intrinsic centered arithmetic-model error has zero window average on the canonical even
window.
-/
theorem halfMassArithmeticModelIntrinsicCenteredErrorWindowAverage_eq_zero
    {X : ℕ} (_hX : X0 ≤ X) :
    halfMassArithmeticModelIntrinsicCenteredErrorWindowAverage X = 0 := by
  have hraw : halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X = 0 :=
    halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum_eq_zero X
  unfold halfMassArithmeticModelIntrinsicCenteredErrorWindowAverage
  rw [hraw]
  ring

/--
Raw-sum split of the arithmetic-model object into its intrinsic main witness plus intrinsic
centered error.
-/
theorem halfMassArithmeticModelWindowRawSum_eq_card_mul_intrinsicMainWitness_add_intrinsicCenteredErrorRawSum
    (X : ℕ) :
    halfMassArithmeticModelWindowRawSum X
      =
    ((EvenIn X H).card : ℂ) * halfMassArithmeticModelIntrinsicMainWitness X
      + halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X := by
  unfold halfMassArithmeticModelWindowRawSum halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, halfMassArithmeticModel X N
        =
      ∑ N ∈ EvenIn X H,
        (halfMassArithmeticModelIntrinsicMainWitness X
          + halfMassArithmeticModelIntrinsicCenteredError X N) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          exact halfMassArithmeticModel_eq_intrinsicMainWitness_add_intrinsicCenteredError X N
    _ =
      (∑ _N ∈ EvenIn X H, halfMassArithmeticModelIntrinsicMainWitness X)
        + ∑ N ∈ EvenIn X H, halfMassArithmeticModelIntrinsicCenteredError X N := by
          rw [Finset.sum_add_distrib]
    _ =
      ((EvenIn X H).card : ℂ) * halfMassArithmeticModelIntrinsicMainWitness X
        + ∑ N ∈ EvenIn X H, halfMassArithmeticModelIntrinsicCenteredError X N := by
          rw [Finset.sum_const, nsmul_eq_mul]

/--
The arithmetic-model window average is exactly its intrinsic scale-dependent main witness.

This is the strongest average-native fact available without any new arithmetic input: the centered
error vanishes identically after averaging by construction.
-/
theorem halfMassArithmeticModelWindowAverage_eq_intrinsicMainWitness
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassArithmeticModelWindowAverage X = halfMassArithmeticModelIntrinsicMainWitness X := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hErrAvg0 := halfMassArithmeticModelIntrinsicCenteredErrorWindowAverage_eq_zero hX
  unfold halfMassArithmeticModelWindowAverage
  rw [halfMassArithmeticModelWindowRawSum_eq_card_mul_intrinsicMainWitness_add_intrinsicCenteredErrorRawSum]
  have hErrRaw0 : halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X = 0 :=
    halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum_eq_zero X
  calc
    ((EvenIn X H).card : ℂ)⁻¹
        * (((EvenIn X H).card : ℂ) * halfMassArithmeticModelIntrinsicMainWitness X
            + halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X)
        =
      (((EvenIn X H).card : ℂ)⁻¹ * ((EvenIn X H).card : ℂ))
          * halfMassArithmeticModelIntrinsicMainWitness X
        + ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X := by
            ring
    _ =
      halfMassArithmeticModelIntrinsicMainWitness X
        + ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelIntrinsicCenteredErrorWindowRawSum X := by
            rw [inv_mul_cancel₀ hcardC, one_mul]
    _ = halfMassArithmeticModelIntrinsicMainWitness X := by
            rw [hErrRaw0, mul_zero, add_zero]


/--
Transport an unscaled post-`σ` ratio average witness directly to the intrinsic arithmetic-model
main witness.
-/
theorem UnscaledZeroModeMassRatioWindowAverageWitnessTarget.to_intrinsicMainWitnessTarget
    {κX : ℕ → ℂ} (h : UnscaledZeroModeMassRatioWindowAverageWitnessTarget κX) :
    HalfMassArithmeticModelWindowAverageWitnessTarget
      (fun X => (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹ * κX X) := by
  refine ⟨?_⟩
  intro X hX
  calc
    halfMassArithmeticModelWindowAverage X
        = halfMassArithmeticModelIntrinsicMainWitness X := by
            exact halfMassArithmeticModelWindowAverage_eq_intrinsicMainWitness hX
    _ =
      (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
        * unscaledZeroModeMassRatioWindowAverage X := by
          rfl
    _ =
      (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹ * κX X := by
          rw [h.average_eq hX]

/--
Transport an unscaled post-`σ` ratio average witness all the way to the old half-mass average
surface through the explicit deterministic recentering scalars.
-/
theorem UnscaledZeroModeMassRatioWindowAverageWitnessTarget.to_halfMassWindowAverageWitnessTarget
    {κX : ℕ → ℂ} (h : UnscaledZeroModeMassRatioWindowAverageWitnessTarget κX) :
    HalfMassWindowAverageWitnessTarget
      (fun X =>
        ((2 : ℂ) * exactGeometricScalar X)
          * ((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹ * κX X)) := by
  exact
    HalfMassArithmeticModelWindowAverageWitnessTarget.to_halfMassWindowAverageWitnessTarget
      (h := h.to_intrinsicMainWitnessTarget)

/--
The exact zero-mode mass with only the singular-series normalization divided out.

This is the clean averaged arithmetic object sitting immediately below the unscaled ratio average
once the geometric zero slice is frozen on the canonical even window.
-/
noncomputable def unscaledZeroModeSigmaDivObservable (X N : ℕ) : ℂ :=
  Q0MinorZeroModeEnvelope.rawExactZeroModeMass X N
    / Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N

/-- Raw even-window sum of the post-`σ` observable before dividing by the geometric zero slice. -/
noncomputable def unscaledZeroModeSigmaDivWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaDivObservable X N

/-- Canonical even-window average of the post-`σ` observable before geometric division. -/
noncomputable def unscaledZeroModeSigmaDivWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * unscaledZeroModeSigmaDivWindowRawSum X

/-- One-sided real-part lower-bound target for the post-`σ` sigma-divided window average. -/
structure UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget (μ : ℕ → ℝ) : Prop where
  lower :
    ∀ {X : ℕ}, X0 ≤ X →
      μ X ≤ (unscaledZeroModeSigmaDivWindowAverage X).re

/--
On the canonical even window, the unscaled ratio observable is exactly the inverse frozen
geometric scalar times the sigma-divided observable.
-/
theorem unscaledZeroModeMassRatioObservable_eq_exactGeometricScalar_inv_mul_sigmaDiv_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable X N
      =
    (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaDivObservable X N := by
  unfold Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable
    unscaledZeroModeSigmaDivObservable
  rw [unscaledGeometricZeroSliceMass_eq_exactGeometricScalar hX hN]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]

/--
Raw-sum version of the frozen-geometric-scalar factorization for the unscaled ratio average.
-/
theorem unscaledZeroModeMassRatioWindowRawSum_eq_exactGeometricScalar_inv_mul_sigmaDivRawSum
    {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeMassRatioWindowRawSum X
      =
    (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaDivWindowRawSum X := by
  unfold unscaledZeroModeMassRatioWindowRawSum unscaledZeroModeSigmaDivWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioObservable X N
        =
      ∑ N ∈ EvenIn X H, (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaDivObservable X N := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          exact
            unscaledZeroModeMassRatioObservable_eq_exactGeometricScalar_inv_mul_sigmaDiv_of_mem_even_window
              hX hN
    _ = (exactGeometricScalar X)⁻¹ * ∑ N ∈ EvenIn X H, unscaledZeroModeSigmaDivObservable X N := by
          rw [Finset.mul_sum]

/--
Average version of the frozen-geometric-scalar factorization for the unscaled ratio average.
-/
theorem unscaledZeroModeMassRatioWindowAverage_eq_exactGeometricScalar_inv_mul_sigmaDivAverage
    {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeMassRatioWindowAverage X
      =
    (exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaDivWindowAverage X := by
  unfold unscaledZeroModeMassRatioWindowAverage unscaledZeroModeSigmaDivWindowAverage
  rw [unscaledZeroModeMassRatioWindowRawSum_eq_exactGeometricScalar_inv_mul_sigmaDivRawSum hX]
  ring

/--
Average decomposition of the post-`σ` observable into the frozen geometric scalar times the
intrinsic scalar `κ`, plus the same scalar times the averaged unscaled ratio error.
-/
theorem unscaledZeroModeSigmaDivWindowAverage_eq_exactGeometricScalar_mul_scalar_add_errorAverage
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    unscaledZeroModeSigmaDivWindowAverage X
      =
    exactGeometricScalar X * (κ : ℂ)
      + exactGeometricScalar X * unscaledZeroModeMassRatioErrorWindowAverage κ X := by
  have hγne : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  calc
    unscaledZeroModeSigmaDivWindowAverage X
        =
      exactGeometricScalar X
        * ((exactGeometricScalar X)⁻¹ * unscaledZeroModeSigmaDivWindowAverage X) := by
          field_simp [hγne]
    _ = exactGeometricScalar X * unscaledZeroModeMassRatioWindowAverage X := by
          rw [← unscaledZeroModeMassRatioWindowAverage_eq_exactGeometricScalar_inv_mul_sigmaDivAverage hX]
    _ =
      exactGeometricScalar X
        * ((κ : ℂ) + unscaledZeroModeMassRatioErrorWindowAverage κ X) := by
          rw [unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage κ hX]
    _ =
      exactGeometricScalar X * (κ : ℂ)
        + exactGeometricScalar X * unscaledZeroModeMassRatioErrorWindowAverage κ X := by
          ring

private lemma norm_exactGeometricScalar_le_two
    {X : ℕ} (hX : X0 ≤ X) :
    ‖exactGeometricScalar X‖ ≤ 2 := by
  rw [exactGeometricScalar_eq_realPart]
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (exactGeometricScalar_re_nonneg hX)] using
    exactGeometricScalar_re_le_two hX

private lemma unscaledZeroModeMassRatioErrorWindowAverage_norm_sq_le_cardInv_mul_windowEnergy
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖ ^ 2
      ≤
    ((EvenIn X H).card : ℝ)⁻¹
      * Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioErrorWindowEnergy κ X := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hcard_pos : 0 < ((EvenIn X H).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard_nat
  have hcard_nonzero : ((EvenIn X H).card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hsum :
      ‖∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2
        ≤
      ((EvenIn X H).card : ℝ)
        * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
    exact
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks.norm_sum_sq_le_card_mul_sum_norm_sq
        (s := EvenIn X H)
        (z := fun N => Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N)
  unfold unscaledZeroModeMassRatioErrorWindowAverage
    unscaledZeroModeMassRatioErrorWindowRawSum
    Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioErrorWindowEnergy
  have havg :
      ‖((↑(EvenIn X H).card : ℂ)⁻¹
          * ∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N)‖ ^ 2
        =
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
        * ‖∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
    rw [norm_mul]
    have hnorm_inv : ‖((↑(EvenIn X H).card : ℂ)⁻¹)‖ = (((EvenIn X H).card : ℝ)⁻¹) := by
      rw [norm_inv, Complex.norm_natCast]
    rw [hnorm_inv]
    ring
  rw [havg]
  have hmain :
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
        * ‖∑ N ∈ EvenIn X H, Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2
        ≤
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
        * (((EvenIn X H).card : ℝ)
            * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
  refine le_trans hmain ?_
  have hfactor_eq :
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
          * (((EvenIn X H).card : ℝ)
              * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2)
        =
      ((EvenIn X H).card : ℝ)⁻¹
        * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
    calc
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
          * (((EvenIn X H).card : ℝ)
              * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2)
        =
      ((((EvenIn X H).card : ℝ)⁻¹) ^ 2 * ((EvenIn X H).card : ℝ))
          * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
            ring
      _ =
        ((((EvenIn X H).card : ℝ)⁻¹)
            * ((((EvenIn X H).card : ℝ)⁻¹) * ((EvenIn X H).card : ℝ)))
          * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
            ring
      _ =
        ((((EvenIn X H).card : ℝ)⁻¹) * 1)
          * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
            rw [inv_mul_cancel₀ hcard_nonzero]
      _ =
        ((EvenIn X H).card : ℝ)⁻¹
          * ∑ N ∈ EvenIn X H, ‖Q0MinorZeroModeEnvelope.unscaledZeroModeMassRatioError κ X N‖ ^ 2 := by
            ring
  exact le_of_eq hfactor_eq

private lemma unscaledZeroModeMassRatioErrorWindowAverage_norm_le_shapeBound
    {κ C2 C3 : ℝ}
    (hshape : Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget κ C2 C3)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖
      ≤
    Real.sqrt
      (((EvenIn X H).card : ℝ)⁻¹
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
  have hsquare :=
    unscaledZeroModeMassRatioErrorWindowAverage_norm_sq_le_cardInv_mul_windowEnergy κ hX
  have hbound := hshape.bound (X := X) hX
  have hmain :
      ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖ ^ 2
        ≤
      ((EvenIn X H).card : ℝ)⁻¹
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
    have hcard_inv_nonneg : 0 ≤ ((EvenIn X H).card : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (by
        exact_mod_cast Nat.pos_of_ne_zero (even_window_card_ne_zero hX)))
    exact le_trans hsquare (mul_le_mul_of_nonneg_left hbound hcard_inv_nonneg)
  have hinside_nonneg :
      0 ≤
        ((EvenIn X H).card : ℝ)⁻¹
          * (C2 * ((H : ℝ) / (X : ℝ))
              + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
    have hcard_inv_nonneg : 0 ≤ ((EvenIn X H).card : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (by
        exact_mod_cast Nat.pos_of_ne_zero (even_window_card_ne_zero hX)))
    have hterm_nonneg :
        0 ≤
          C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      have hHX_nonneg : 0 ≤ ((H : ℝ) / (X : ℝ)) := by
        exact div_nonneg (by positivity) (by positivity)
      have hQ_nonneg :
          0 ≤ C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
        exact div_nonneg hshape.C3_nonneg (by positivity)
      nlinarith [hshape.C2_nonneg, hshape.C3_nonneg, hHX_nonneg, hQ_nonneg]
    exact mul_nonneg hcard_inv_nonneg hterm_nonneg
  have hsqrt_sq :
      ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖ ^ 2
        ≤
      (Real.sqrt
        (((EvenIn X H).card : ℝ)⁻¹
          * (C2 * ((H : ℝ) / (X : ℝ))
              + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) ^ 2 := by
    convert hmain using 1
    rw [Real.sq_sqrt hinside_nonneg]
  exact le_of_sq_le_sq hsqrt_sq (Real.sqrt_nonneg _)

theorem unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage_norm_le_shapeBound
    {κ C2 C3 : ℝ}
    (hshape : Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget κ C2 C3)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X‖
      ≤
    2 * Real.sqrt
      (((EvenIn X H).card : ℝ)⁻¹
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
  have hsig :
      ∀ {N : ℕ}, N ∈ EvenIn X H →
        Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0 := by
    intro N hN
    exact sigmaNormalizedSeries_ne_zero_of_mem_even_window hX hN
  have hsplit :
      unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X
        =
      exactGeometricScalar X * unscaledZeroModeMassRatioErrorWindowAverage κ X := by
    exact
      unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage_eq_exactGeometricScalar_mul_ratioErrorAverage
        κ hX hsig
  have herrAvg_norm :
      ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖
        ≤
      Real.sqrt
        (((EvenIn X H).card : ℝ)⁻¹
          * (C2 * ((H : ℝ) / (X : ℝ))
              + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
    exact unscaledZeroModeMassRatioErrorWindowAverage_norm_le_shapeBound hshape hX
  have hγnorm : ‖exactGeometricScalar X‖ ≤ 2 := norm_exactGeometricScalar_le_two hX
  calc
    ‖unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage κ X‖
        =
      ‖exactGeometricScalar X * unscaledZeroModeMassRatioErrorWindowAverage κ X‖ := by
          rw [hsplit]
    _ = ‖exactGeometricScalar X‖ * ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖ := by
          rw [norm_mul]
    _ ≤ 2 * ‖unscaledZeroModeMassRatioErrorWindowAverage κ X‖ := by
          exact mul_le_mul_of_nonneg_right hγnorm (norm_nonneg _)
    _ ≤ 2 * Real.sqrt
        (((EvenIn X H).card : ℝ)⁻¹
          * (C2 * ((H : ℝ) / (X : ℝ))
              + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
          exact mul_le_mul_of_nonneg_left herrAvg_norm (by positivity)

/--
Average-native lower bound for the post-`σ` observable from the unscaled ratio shape target.

This is the precise one-sided theorem surface now needed by the half-mass mean route: a positive
main term carried by the frozen geometric scalar, minus a Cauchy-controlled averaged error on the
intrinsic unscaled ratio.
-/
theorem unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_unscaledMassShape
    {κ C2 C3 : ℝ}
    (hshape : Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget κ C2 C3)
    (hκ_nonneg : 0 ≤ κ) :
    UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget
      (fun X =>
        Goldbach.BG_Identity.K_full (0 : ℤ) * κ
          - 2
              * Real.sqrt
                  (((EvenIn X H).card : ℝ)⁻¹
                    * (C2 * ((H : ℝ) / (X : ℝ))
                        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
  refine ⟨?_⟩
  intro X hX
  let errAvg := unscaledZeroModeMassRatioErrorWindowAverage κ X
  let errBound : ℝ :=
    Real.sqrt
      (((EvenIn X H).card : ℝ)⁻¹
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
  have hsplit :
      unscaledZeroModeSigmaDivWindowAverage X
        =
      exactGeometricScalar X * (κ : ℂ)
        + exactGeometricScalar X * errAvg := by
    simpa [errAvg] using
      unscaledZeroModeSigmaDivWindowAverage_eq_exactGeometricScalar_mul_scalar_add_errorAverage κ hX
  have herrAvg_norm : ‖errAvg‖ ≤ errBound := by
    dsimp [errAvg, errBound]
    exact unscaledZeroModeMassRatioErrorWindowAverage_norm_le_shapeBound hshape hX
  have hγnorm : ‖exactGeometricScalar X‖ ≤ 2 := norm_exactGeometricScalar_le_two hX
  have hErrTermNorm :
      ‖exactGeometricScalar X * errAvg‖ ≤ 2 * errBound := by
    calc
      ‖exactGeometricScalar X * errAvg‖
          = ‖exactGeometricScalar X‖ * ‖errAvg‖ := by rw [norm_mul]
      _ ≤ 2 * ‖errAvg‖ := by
            exact mul_le_mul_of_nonneg_right hγnorm (norm_nonneg _)
      _ ≤ 2 * errBound := by
            exact mul_le_mul_of_nonneg_left herrAvg_norm (by positivity)
  have hErrTermLower :
      -(2 * errBound) ≤ (exactGeometricScalar X * errAvg).re := by
    have hAbs :
        |(exactGeometricScalar X * errAvg).re| ≤ ‖exactGeometricScalar X * errAvg‖ := by
      simpa using Complex.abs_re_le_norm (exactGeometricScalar X * errAvg)
    have hre_lower : -‖exactGeometricScalar X * errAvg‖ ≤ (exactGeometricScalar X * errAvg).re := by
      exact (abs_le.mp hAbs).1
    have hneg_compare : -(2 * errBound) ≤ -‖exactGeometricScalar X * errAvg‖ := by
      nlinarith [hErrTermNorm]
    exact le_trans hneg_compare hre_lower
  have hMainLower :
      Goldbach.BG_Identity.K_full (0 : ℤ) * κ
        ≤
      (exactGeometricScalar X * (κ : ℂ)).re := by
    have hmain_re :
        (exactGeometricScalar X * (κ : ℂ)).re = (exactGeometricScalar X).re * κ := by
      rw [exactGeometricScalar_eq_realPart]
      simp [Complex.mul_re]
    rw [hmain_re]
    exact mul_le_mul_of_nonneg_right (exactGeometricScalar_re_lower hX) hκ_nonneg
  have hre_split :
      (unscaledZeroModeSigmaDivWindowAverage X).re
        =
      (exactGeometricScalar X * (κ : ℂ)).re
        + (exactGeometricScalar X * errAvg).re := by
    rw [hsplit]
    simp
  linarith

/-- Positivity of the canonical bookkeeping scalar used by the zero-mode envelope route. -/
lemma zeroModeBookkeepingScalarCandidate_pos :
    0 < Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate := by
  unfold Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate
  norm_num [Q0MinorRouteVisibleDecomposition.sigmaEnvelopeKappa]

/-- Explicit positive signal floor coming from the kernel mass at zero and the bookkeeping scalar. -/
lemma K_full_zero_mul_zeroModeBookkeepingScalarCandidate_pos :
    0 < Goldbach.BG_Identity.K_full (0 : ℤ)
          * Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate := by
  exact mul_pos Goldbach.BG_Identity.K_full_pos_at_zero zeroModeBookkeepingScalarCandidate_pos

/-- Exact value of the full tent kernel at the origin. -/
lemma K_full_zero_eq_inv_Ucut :
    Goldbach.BG_Identity.K_full (0 : ℤ) = ((Goldbach.BG_Identity.Ucut : ℝ) : ℝ)⁻¹ := by
  simpa using
    (Goldbach.BG_Identity.K_full_ofNat_le
      (m := 0) (hm := Nat.zero_le Goldbach.BG_Identity.Ucut))

/--
Explicit signal carried by the bookkeeping scalar after dividing by the canonical full tent mass
at the origin.
-/
noncomputable def zeroModeBookkeepingSigmaDivSignal : ℝ :=
  Goldbach.BG_Identity.K_full (0 : ℤ)
    * Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate

/--
Squared threshold naturally associated to the decisive sigma-divided comparison. If the coarse
shape radicand is at most this value, then the bookkeeping lower profile is nonnegative.
-/
noncomputable def zeroModeBookkeepingSigmaDivThreshold : ℝ :=
  zeroModeBookkeepingSigmaDivSignal ^ 2 / 4

lemma zeroModeBookkeepingSigmaDivSignal_eq_explicit :
    zeroModeBookkeepingSigmaDivSignal
      =
    Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate
      / (Goldbach.BG_Identity.Ucut : ℝ) := by
  simp [zeroModeBookkeepingSigmaDivSignal, K_full_zero_eq_inv_Ucut, div_eq_mul_inv, mul_comm]

lemma zeroModeBookkeepingSigmaDivSignal_pos :
    0 < zeroModeBookkeepingSigmaDivSignal := by
  simpa [zeroModeBookkeepingSigmaDivSignal] using
    K_full_zero_mul_zeroModeBookkeepingScalarCandidate_pos

lemma zeroModeBookkeepingSigmaDivThreshold_eq_explicit :
    zeroModeBookkeepingSigmaDivThreshold
      =
    Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate ^ 2
      / (4 * (Goldbach.BG_Identity.Ucut : ℝ) ^ 2) := by
  have hU : (Goldbach.BG_Identity.Ucut : ℝ) ≠ 0 := Goldbach.BG_Identity.Ucut_ne_zero_real
  rw [zeroModeBookkeepingSigmaDivThreshold, zeroModeBookkeepingSigmaDivSignal_eq_explicit]
  field_simp [hU]

lemma zeroModeBookkeepingSigmaDivThreshold_pos :
    0 < zeroModeBookkeepingSigmaDivThreshold := by
  have hsig : 0 < zeroModeBookkeepingSigmaDivSignal := zeroModeBookkeepingSigmaDivSignal_pos
  unfold zeroModeBookkeepingSigmaDivThreshold
  nlinarith

/--
Coarse comparison dropping the window-cardinality gain in the sigma-divided shape radicand.

This is weaker than the native lower bound, but isolates the remaining arithmetic comparison into a
plain positive signal minus a plain shape envelope.
-/
theorem unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_unscaledMassShape_coarse
    {κ C2 C3 : ℝ}
    (hshape : Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget κ C2 C3)
    (hκ_nonneg : 0 ≤ κ) :
    UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget
      (fun X =>
        Goldbach.BG_Identity.K_full (0 : ℤ) * κ
          - 2
              * Real.sqrt
                  (C2 * ((H : ℝ) / (X : ℝ))
                    + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
  let μnative : ℕ → ℝ :=
    fun X =>
      Goldbach.BG_Identity.K_full (0 : ℤ) * κ
        - 2
            * Real.sqrt
                (((EvenIn X H).card : ℝ)⁻¹
                  * (C2 * ((H : ℝ) / (X : ℝ))
                      + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
  have hnative :
      UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget μnative :=
    unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_unscaledMassShape
      (hshape := hshape) (hκ_nonneg := hκ_nonneg)
  refine ⟨?_⟩
  intro X hX
  have hcard_inv_le : ((EvenIn X H).card : ℝ)⁻¹ ≤ 1 := even_window_card_inv_le_one hX
  have hshape_nonneg :
      0 ≤
        C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
    have hHX_nonneg : 0 ≤ ((H : ℝ) / (X : ℝ)) := by
      exact div_nonneg (by positivity) (by positivity)
    have hQ_nonneg :
        0 ≤ C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      exact div_nonneg hshape.C3_nonneg (by positivity)
    nlinarith [hshape.C2_nonneg, hshape.C3_nonneg, hHX_nonneg, hQ_nonneg]
  have hrad_le :
      ((EvenIn X H).card : ℝ)⁻¹
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
    exact mul_le_of_le_one_left hshape_nonneg hcard_inv_le
  have hsqrt_le :
      Real.sqrt
          (((EvenIn X H).card : ℝ)⁻¹
            * (C2 * ((H : ℝ) / (X : ℝ))
                + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
        ≤
      Real.sqrt
          (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
    exact Real.sqrt_le_sqrt hrad_le
  have hneg_sqrt_compare :
      -2
          * Real.sqrt
              (C2 * ((H : ℝ) / (X : ℝ))
                + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        ≤
      -2
          * Real.sqrt
              (((EvenIn X H).card : ℝ)⁻¹
                * (C2 * ((H : ℝ) / (X : ℝ))
                    + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
    nlinarith [hsqrt_le]
  have hμ_compare :
      Goldbach.BG_Identity.K_full (0 : ℤ) * κ
        - 2
            * Real.sqrt
                (C2 * ((H : ℝ) / (X : ℝ))
                  + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
      ≤
      μnative X := by
    dsimp [μnative]
    have hneg_sqrt_compare' :
        -(2
            * Real.sqrt
                (C2 * ((H : ℝ) / (X : ℝ))
                  + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
          ≤
        -(2
            * Real.sqrt
                (((EvenIn X H).card : ℝ)⁻¹
                  * (C2 * ((H : ℝ) / (X : ℝ))
                      + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
      convert hneg_sqrt_compare using 1 <;> ring
    simpa only [sub_eq_add_neg] using
      add_le_add_left hneg_sqrt_compare' (Goldbach.BG_Identity.K_full (0 : ℤ) * κ)
  exact le_trans hμ_compare (hnative.lower hX)

/--
Coarse explicit sigma-divided lower profile specialized to the bookkeeping scalar
`zeroModeBookkeepingScalarCandidate`.
-/
noncomputable def zeroModeBookkeepingSigmaDivCoarseLowerProfile
    (C2 C3 : ℝ) (X : ℕ) : ℝ :=
  zeroModeBookkeepingSigmaDivSignal
    - 2
        * Real.sqrt
            (C2 * ((H : ℝ) / (X : ℝ))
              + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

/--
Decisive comparison target for the half-mass mean route at the bookkeeping scalar.

This is the remaining scale question after all transport and normalization work:
does the explicit positive signal `K_full(0) * κ` dominate the coarse shape envelope?
-/
structure ZeroModeBookkeepingSigmaDivCoarseComparisonTarget (C2 C3 : ℝ) : Prop where
  nonneg :
    ∀ {X : ℕ}, X0 ≤ X →
      0 ≤ zeroModeBookkeepingSigmaDivCoarseLowerProfile C2 C3 X

/--
Threshold form of the decisive sigma-divided comparison.

This is the clean calibration inequality for the remaining shape constants:
if the coarse shape radicand stays below `signal^2 / 4`, then the bookkeeping lower profile is
nonnegative.
-/
theorem ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_threshold
    {C2 C3 : ℝ}
    (hthreshold :
      ∀ {X : ℕ}, X0 ≤ X →
        C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
        ≤
        zeroModeBookkeepingSigmaDivThreshold) :
    ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3 := by
  refine ⟨?_⟩
  intro X hX
  let radicand : ℝ :=
    C2 * ((H : ℝ) / (X : ℝ))
      + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  have hsig_nonneg : 0 ≤ zeroModeBookkeepingSigmaDivSignal := by
    exact le_of_lt zeroModeBookkeepingSigmaDivSignal_pos
  have hsqrt_le :
      Real.sqrt radicand ≤ zeroModeBookkeepingSigmaDivSignal / 2 := by
    calc
      Real.sqrt radicand ≤ Real.sqrt zeroModeBookkeepingSigmaDivThreshold := by
        exact Real.sqrt_le_sqrt (hthreshold hX)
      _ = zeroModeBookkeepingSigmaDivSignal / 2 := by
        rw [zeroModeBookkeepingSigmaDivThreshold]
        have hhalf_nonneg : 0 ≤ zeroModeBookkeepingSigmaDivSignal / 2 := by
          exact div_nonneg hsig_nonneg (by positivity)
        have hsquare :
            zeroModeBookkeepingSigmaDivSignal ^ 2 / 4
              =
            (zeroModeBookkeepingSigmaDivSignal / 2) ^ 2 := by
          ring
        rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hhalf_nonneg]
  have hdouble :
      2 * Real.sqrt radicand ≤ zeroModeBookkeepingSigmaDivSignal := by
    nlinarith
  unfold zeroModeBookkeepingSigmaDivCoarseLowerProfile
  dsimp [radicand]
  exact sub_nonneg.mpr hdouble

/--
Explicit threshold form of the decisive sigma-divided comparison, using the closed-form signal
`κ / Ucut`.
-/
theorem ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_explicit_threshold
    {C2 C3 : ℝ}
    (hthreshold :
      ∀ {X : ℕ}, X0 ≤ X →
        C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
        ≤
        Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate ^ 2
          / (4 * (Goldbach.BG_Identity.Ucut : ℝ) ^ 2)) :
    ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3 := by
  apply ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_threshold
  intro X hX
  calc
    C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
      ≤
    Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate ^ 2
        / (4 * (Goldbach.BG_Identity.Ucut : ℝ) ^ 2) := hthreshold hX
    _ = zeroModeBookkeepingSigmaDivThreshold := by
      rw [zeroModeBookkeepingSigmaDivThreshold_eq_explicit]

/--
Admissibility at the left endpoint `X0` is enough for the decisive coarse comparison, provided
`C2` is nonnegative. The `C3` term is independent of `X`, while `H / X` is largest at `X = X0`.
-/
theorem ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_X0_admissible
    {C2 C3 : ℝ}
    (hC2_nonneg : 0 ≤ C2)
    (hX0 :
      C2 * ((H : ℝ) / (X0 : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
      ≤
      zeroModeBookkeepingSigmaDivThreshold) :
    ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3 := by
  apply ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_threshold
  intro X hX
  have hdiv :
      ((H : ℝ) / (X : ℝ)) ≤ ((H : ℝ) / (X0 : ℝ)) := by
    exact
      div_le_div_of_nonneg_left
        (by positivity)
        (by
          exact_mod_cast (show 0 < X0 by norm_num [Goldbach.BankParams.X0]) :
            (0 : ℝ) < (X0 : ℝ))
        (by exact_mod_cast hX)
  have hC2_term :
      C2 * ((H : ℝ) / (X : ℝ))
        ≤
      C2 * ((H : ℝ) / (X0 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hdiv hC2_nonneg
  calc
    C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
      ≤
    C2 * ((H : ℝ) / (X0 : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
          gcongr
    _ ≤ zeroModeBookkeepingSigmaDivThreshold := hX0

/--
Split-cap admissibility criterion.

It is enough to allocate half the threshold budget to the `C2` contribution at `X0` and the other
half to the `C3` contribution.
-/
theorem ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_split_caps
    {C2 C3 : ℝ}
    (hC2_nonneg : 0 ≤ C2)
    (hC2_cap :
      C2 ≤ zeroModeBookkeepingSigmaDivThreshold * ((X0 : ℝ) / (2 * (H : ℝ))))
    (hC3_cap :
      C3 ≤
        zeroModeBookkeepingSigmaDivThreshold
          * (((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) / 2)) :
    ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3 := by
  apply ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_X0_admissible
    (hC2_nonneg := hC2_nonneg)
  have hH_ne : (H : ℝ) ≠ 0 := by
    exact_mod_cast (show H ≠ 0 by norm_num [Goldbach.BankParams.H])
  have hX0_ne : (X0 : ℝ) ≠ 0 := by
    exact_mod_cast (show X0 ≠ 0 by norm_num [Goldbach.BankParams.X0])
  have hHQ_ne :
      ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) ≠ 0 := by
    have hH : (H : ℝ) ≠ 0 := hH_ne
    have hQ : (((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (show Goldbach.AO_OffDiag.TailBlock.Q0 ≠ 0 by norm_num)
    positivity
  have hC2_term :
      C2 * ((H : ℝ) / (X0 : ℝ)) ≤ zeroModeBookkeepingSigmaDivThreshold / 2 := by
    calc
      C2 * ((H : ℝ) / (X0 : ℝ))
        ≤
      (zeroModeBookkeepingSigmaDivThreshold * ((X0 : ℝ) / (2 * (H : ℝ))))
        * ((H : ℝ) / (X0 : ℝ)) := by
          gcongr
      _ = zeroModeBookkeepingSigmaDivThreshold / 2 := by
          field_simp [hH_ne, hX0_ne]
  have hC3_term :
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
        ≤
      zeroModeBookkeepingSigmaDivThreshold / 2 := by
    calc
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
        ≤
      (zeroModeBookkeepingSigmaDivThreshold
          * (((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) / 2))
        / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
          gcongr
      _ = zeroModeBookkeepingSigmaDivThreshold / 2 := by
          field_simp [hHQ_ne]
  linarith

/--
Negative calibration at `X0`: if the coarse shape radicand already exceeds the threshold at the
left endpoint, then the decisive comparison target cannot hold.
-/
theorem not_ZeroModeBookkeepingSigmaDivCoarseComparisonTarget_of_X0_radicand_gt_threshold
    {C2 C3 : ℝ}
    (hgt :
      zeroModeBookkeepingSigmaDivThreshold
        <
      C2 * ((H : ℝ) / (X0 : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) :
    ¬ ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3 := by
  intro hcmp
  let radicand : ℝ :=
    C2 * ((H : ℝ) / (X0 : ℝ))
      + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  have hsqrt_lt :
      zeroModeBookkeepingSigmaDivSignal / 2 < Real.sqrt radicand := by
    calc
      zeroModeBookkeepingSigmaDivSignal / 2 = Real.sqrt zeroModeBookkeepingSigmaDivThreshold := by
        rw [zeroModeBookkeepingSigmaDivThreshold]
        have hhalf_nonneg : 0 ≤ zeroModeBookkeepingSigmaDivSignal / 2 := by
          exact div_nonneg (le_of_lt zeroModeBookkeepingSigmaDivSignal_pos) (by positivity)
        have hsquare :
            zeroModeBookkeepingSigmaDivSignal ^ 2 / 4
              =
            (zeroModeBookkeepingSigmaDivSignal / 2) ^ 2 := by
          ring
        rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hhalf_nonneg]
      _ < Real.sqrt radicand := by
        exact Real.sqrt_lt_sqrt (le_of_lt zeroModeBookkeepingSigmaDivThreshold_pos) hgt
  have hsignal_lt :
      zeroModeBookkeepingSigmaDivSignal < 2 * Real.sqrt radicand := by
    nlinarith
  have hneg :
      zeroModeBookkeepingSigmaDivCoarseLowerProfile C2 C3 X0 < 0 := by
    have : zeroModeBookkeepingSigmaDivSignal - 2 * Real.sqrt radicand < 0 := by
      linarith
    simpa [zeroModeBookkeepingSigmaDivCoarseLowerProfile, radicand] using this
  exact not_lt_of_ge (hcmp.nonneg (X := X0) le_rfl) hneg

/--
Specialized sigma-divided lower-bound theorem at the bookkeeping scalar.

This is the theorem obtained from the unscaled mass-shape target before imposing the final
signal-versus-noise comparison.
-/
theorem unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_zeroModeBookkeepingShape
    {C2 C3 : ℝ}
    (hshape :
      Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget
        Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate C2 C3) :
    UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget
      (zeroModeBookkeepingSigmaDivCoarseLowerProfile C2 C3) := by
  simpa [zeroModeBookkeepingSigmaDivCoarseLowerProfile] using
    unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_unscaledMassShape_coarse
      (hshape := hshape)
      (hκ_nonneg := zeroModeBookkeepingScalarCandidate_pos.le)

/--
If the explicit bookkeeping comparison target holds, then the sigma-divided window average is
nonnegative on the canonical even window.
-/
theorem unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_zeroModeBookkeepingShape_and_comparison
    {C2 C3 : ℝ}
    (hshape :
      Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget
        Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate C2 C3)
    (hcmp : ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3) :
    UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget (fun _ => 0) := by
  let hbase :=
    unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_zeroModeBookkeepingShape
      (hshape := hshape)
  refine ⟨?_⟩
  intro X hX
  exact le_trans (hcmp.nonneg hX) (hbase.lower hX)

/--
Deterministic one-sided transport from a lower bound for the sigma-divided window average to a
lower bound for the unscaled ratio window average.

The remaining input is now explicit:
* a lower bound on the simpler post-`σ` averaged arithmetic object;
* reality and size control for the frozen geometric scalar on the canonical even window.
-/
theorem unscaledZeroModeMassRatioWindowAverageLowerBoundTarget_of_sigmaDiv
    {μ B : ℕ → ℝ}
    (havg : UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget μ)
    (hgamma_im :
      ∀ {X : ℕ}, X0 ≤ X → (exactGeometricScalar X).im = 0)
    (hgamma_nonneg :
      ∀ {X : ℕ}, X0 ≤ X → 0 ≤ (exactGeometricScalar X).re)
    (hgamma_upper :
      ∀ {X : ℕ}, X0 ≤ X → (exactGeometricScalar X).re ≤ B X)
    (_hB_pos :
      ∀ {X : ℕ}, X0 ≤ X → 0 < B X)
    (hμ_nonneg :
      ∀ {X : ℕ}, X0 ≤ X → 0 ≤ μ X) :
    UnscaledZeroModeMassRatioWindowAverageLowerBoundTarget (fun X => μ X / B X) := by
  refine ⟨?_⟩
  intro X hX
  have hγne : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  have hγeq : exactGeometricScalar X = ((exactGeometricScalar X).re : ℂ) := by
    apply Complex.ext <;> simp [hgamma_im hX]
  have hγre_ne : (exactGeometricScalar X).re ≠ 0 := by
    intro hre
    apply hγne
    apply Complex.ext <;> simp [hre, hgamma_im hX]
  have hγre_pos : 0 < (exactGeometricScalar X).re := by
    have hnonneg := hgamma_nonneg hX
    exact lt_of_le_of_ne hnonneg (Ne.symm hγre_ne)
  have hre_formula :
      (unscaledZeroModeMassRatioWindowAverage X).re
        =
      ((exactGeometricScalar X).re)⁻¹ * (unscaledZeroModeSigmaDivWindowAverage X).re := by
    rw [unscaledZeroModeMassRatioWindowAverage_eq_exactGeometricScalar_inv_mul_sigmaDivAverage hX]
    rw [hγeq]
    simp [Complex.mul_re]
  have hscaled :
      ((exactGeometricScalar X).re)⁻¹ * μ X
        ≤
      (unscaledZeroModeMassRatioWindowAverage X).re := by
    rw [hre_formula]
    exact
      mul_le_mul_of_nonneg_left
        (havg.lower hX)
        (inv_nonneg.mpr (hgamma_nonneg hX))
  have hdiv_compare :
      μ X / B X
        ≤
      ((exactGeometricScalar X).re)⁻¹ * μ X := by
    have hquot :
        μ X / B X
          ≤
        μ X / (exactGeometricScalar X).re := by
      exact div_le_div_of_nonneg_left (hμ_nonneg hX) hγre_pos (hgamma_upper hX)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hquot
  exact le_trans hdiv_compare hscaled

/--
Explicit coarse version of the one-sided sigma-divided transport theorem using the deterministic
bound `(exactGeometricScalar X).re ≤ 2`.
-/
theorem unscaledZeroModeMassRatioWindowAverageLowerBoundTarget_of_sigmaDiv_explicit
    {μ : ℕ → ℝ}
    (havg : UnscaledZeroModeSigmaDivWindowAverageLowerBoundTarget μ)
    (hμ_nonneg :
      ∀ {X : ℕ}, X0 ≤ X → 0 ≤ μ X) :
    UnscaledZeroModeMassRatioWindowAverageLowerBoundTarget (fun X => μ X / 2) := by
  refine
    unscaledZeroModeMassRatioWindowAverageLowerBoundTarget_of_sigmaDiv
      (B := fun _ => 2)
      (havg := havg)
      (hgamma_im := ?_)
      (hgamma_nonneg := ?_)
      (hgamma_upper := ?_)
      (_hB_pos := ?_)
      (hμ_nonneg := hμ_nonneg)
  · intro X hX
    exact exactGeometricScalar_im_eq_zero
  · intro X hX
    exact exactGeometricScalar_re_nonneg hX
  · intro X hX
    exact exactGeometricScalar_re_le_two hX
  · intro X hX
    norm_num

/--
If the bookkeeping comparison target holds, then the unscaled post-`σ` ratio window average is
also nonnegative by the explicit frozen-geometric transport.
-/
theorem unscaledZeroModeMassRatioWindowAverageLowerBoundTarget_of_zeroModeBookkeepingShape_and_comparison
    {C2 C3 : ℝ}
    (hshape :
      Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget
        Q0MinorZeroModeEnvelope.zeroModeBookkeepingScalarCandidate C2 C3)
    (hcmp : ZeroModeBookkeepingSigmaDivCoarseComparisonTarget C2 C3) :
    UnscaledZeroModeMassRatioWindowAverageLowerBoundTarget (fun _ => 0) := by
  have hμ_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ (0 : ℝ) := by
    intro X hX
    exact le_rfl
  simpa using
    unscaledZeroModeMassRatioWindowAverageLowerBoundTarget_of_sigmaDiv_explicit
      (havg :=
        unscaledZeroModeSigmaDivWindowAverageLowerBoundTarget_of_zeroModeBookkeepingShape_and_comparison
          (hshape := hshape) (hcmp := hcmp))
      (hμ_nonneg := hμ_nonneg)

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets
