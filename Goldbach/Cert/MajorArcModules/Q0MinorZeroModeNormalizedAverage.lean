import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets
import Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
import Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailOnly
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
open Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

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

private lemma even_window_card_le_H_add_one (X : ℕ) :
    (EvenIn X H).card ≤ H + 1 := by
  classical
  unfold EvenIn IccShift
  have hsub :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)
        ⊆
      (Finset.range (H + 1)).image (fun k : ℕ => X + k) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard_le :
      (((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)).card
        ≤
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card :=
    Finset.card_le_card hsub
  have hcard_eq :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card = H + 1 := by
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b hab
    exact Nat.add_left_cancel hab
  exact le_trans hcard_le (le_of_eq hcard_eq)

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

theorem centeredTrueSigmaSeries_windowRawSum_eq_zero
    (S : TrueSingularSeriesOnWindow)
    {X : ℕ} (_hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, centeredTrueSigmaSeries S X N) = 0 := by
  unfold centeredTrueSigmaSeries trueSigmaWindowAverage
  unfold trueSigmaWindowRawSum
  exact centered_window_rawSum_eq_zero (f := fun N => trueSigmaNormalizedSeries S N)

theorem centeredNormalizedSigmaTrunc_windowRawSum_eq_zero
    (S : TrueSingularSeriesOnWindow)
    {X : ℕ} (_hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, centeredNormalizedSigmaTrunc S X N) = 0 := by
  unfold centeredNormalizedSigmaTrunc normalizedSigmaTruncWindowAverage
  unfold normalizedSigmaTruncWindowRawSum
  exact centered_window_rawSum_eq_zero (f := fun N => normalizedSigmaTruncQ0 S N)

/-- Canonical-window average of one fixed `q ≤ Q0` truncation summand. -/
noncomputable def normalizedSigmaTruncSummandWindowAverage
    (S : TrueSingularSeriesOnWindow) (X q : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹
    * ∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand S q N

/-- Centered fixed-`q` truncation summand on the canonical even window. -/
noncomputable def centeredNormalizedSigmaTruncSummand
    (S : TrueSingularSeriesOnWindow) (X q N : ℕ) : ℂ :=
  normalizedSigmaTruncSummand S q N - normalizedSigmaTruncSummandWindowAverage S X q

/-- Raw window sum of the fixed `q ≤ Q0` truncation summands. -/
theorem normalizedSigmaTruncWindowRawSum_eq_sum_summandRawSums
    (S : TrueSingularSeriesOnWindow) (X : ℕ) :
    normalizedSigmaTruncWindowRawSum S X
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      ∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand S q N := by
  unfold normalizedSigmaTruncWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 S N
        =
      ∑ N ∈ EvenIn X H,
        ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          normalizedSigmaTruncSummand S q N := by
            refine Finset.sum_congr rfl ?_
            intro N _hN
            rw [normalizedSigmaTruncQ0_eq_sum_truncSummand]
    _ =
      ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        ∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand S q N := by
          rw [Finset.sum_comm]

theorem centeredNormalizedSigmaTrunc_eq_sum_truncSummands_sub_average
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    centeredNormalizedSigmaTrunc S X N
      =
    (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      normalizedSigmaTruncSummand S q N)
      - normalizedSigmaTruncWindowAverage S X := by
  unfold centeredNormalizedSigmaTrunc
  rw [normalizedSigmaTruncQ0_eq_sum_truncSummand]

theorem centeredNormalizedSigmaTruncSummand_windowRawSum_eq_zero
    (S : TrueSingularSeriesOnWindow) {X q : ℕ} :
    (∑ N ∈ EvenIn X H, centeredNormalizedSigmaTruncSummand S X q N) = 0 := by
  unfold centeredNormalizedSigmaTruncSummand normalizedSigmaTruncSummandWindowAverage
  exact centered_window_rawSum_eq_zero (f := fun N => normalizedSigmaTruncSummand S q N)

/-- Squared `ℓ²(EvenIn X H)` energy of one centered fixed-`q` truncation summand. -/
noncomputable def centeredNormalizedSigmaTruncSummandWindowEnergy
    (S : TrueSingularSeriesOnWindow) (X q : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTruncSummand S X q N‖ ^ 2

theorem centeredRawHalfMassTrueTailResidual_windowRawSum_eq_zero
    (S : TrueSingularSeriesOnWindow)
    {X : ℕ} (_hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, centeredRawHalfMassTrueTailResidual S X N) = 0 := by
  unfold centeredRawHalfMassTrueTailResidual rawHalfMassTrueTailResidualWindowAverage
  unfold rawHalfMassTrueTailResidualWindowRawSum
  exact centered_window_rawSum_eq_zero (f := fun N => rawHalfMassTrueTailResidual S X N)

theorem centeredRawHalfMassTrueSeriesCorrection_windowRawSum_eq_zero
    (S : TrueSingularSeriesOnWindow)
    {X : ℕ} (_hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, centeredRawHalfMassTrueSeriesCorrection S X N) = 0 := by
  unfold centeredRawHalfMassTrueSeriesCorrection rawHalfMassTrueSeriesCorrectionWindowAverage
  unfold rawHalfMassTrueSeriesCorrectionWindowRawSum
  exact centered_window_rawSum_eq_zero (f := fun N => rawHalfMassTrueSeriesCorrection S X N)

private lemma routeVisibleWindowNormFloor_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    ((routeVisibleWindowNormFloor X : ℝ) : ℂ) ≠ 0 := by
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlog_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hlog_ne : Real.log ((X + H : ℕ) : ℝ) ≠ 0 := by
    linarith
  have hfloor_ne : routeVisibleWindowNormFloor X ≠ 0 := by
    unfold routeVisibleWindowNormFloor
    positivity
  exact_mod_cast hfloor_ne

private lemma uniformWindowNormalization_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    uniformWindowNormalization X ≠ 0 := by
  have hlog_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hlog_ne : Real.log (X : ℝ) ≠ 0 := by
    linarith
  have hcard_ne : (((2 * H + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * H + 1 : ℕ) ≠ 0 by omega)
  have hscale_ne : ((((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hlog_ne) hcard_ne
  unfold uniformWindowNormalization
  exact inv_ne_zero hscale_ne

private lemma geometricZeroSliceNormalization_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    geometricZeroSliceNormalization X ≠ 0 := by
  unfold geometricZeroSliceNormalization
  exact pow_ne_zero 2 (uniformWindowNormalization_ne_zero hX)

private lemma q0NormFactor_ne_zero_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Q0MinorNormalizationBridge.q0NormFactor N ≠ 0 := by
  have hlow :
      (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2)
        ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ :=
    Q0MinorNormalizedEnergy.q0NormFactor_lower_on_window (X := X) (N := N) hX hN
  have hpos_left : 0 < (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
    have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
    have hlog_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
      Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
    have hlog_pos : 0 < Real.log ((X + H : ℕ) : ℝ) := by
      linarith
    positivity
  have hnorm_pos : 0 < ‖Q0MinorNormalizationBridge.q0NormFactor N‖ := lt_of_lt_of_le hpos_left hlow
  intro hq0
  have : ‖Q0MinorNormalizationBridge.q0NormFactor N‖ = 0 := by simp [hq0]
  linarith

/--
Exact inverse formula for the `q0` normalization factor.

This is the normalized-window arithmetic content remaining after the geometric slice has been
removed from the correction factor.
-/
theorem q0NormFactor_inv_eq_explicit_log_sq
    {N : ℕ} (hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0) :
    (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      =
    (((800 : ℝ) * (Real.log (N : ℝ)) ^ 2) : ℂ) := by
  have hq0' := hq0
  unfold Q0MinorNormalizationBridge.q0NormFactor
  field_simp [hq0']
  have hconst : (((1 / 800 : ℝ) : ℂ) * (800 : ℂ)) = (1 : ℂ) := by
    norm_num
  calc
    (((Real.log (N : ℝ)) : ℂ) ^ 2)
        = (((Real.log (N : ℝ)) : ℂ) ^ 2) * ((((1 / 800 : ℝ) : ℂ) * (800 : ℂ))) := by
            rw [hconst, mul_one]
    _ = ((((1 / 800 : ℝ) : ℂ) * (((Real.log (N : ℝ)) : ℂ) ^ 2)) * (800 : ℂ)) := by
          ring

/--
Exact window-sum formula for the inverse `q0` normalization factor on `EvenIn X H`.
-/
theorem q0NormFactor_inv_windowRawSum_eq_explicit_log_sq_sum
    {X : ℕ} (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹)
      =
    ∑ N ∈ EvenIn X H, (((800 : ℝ) * (Real.log (N : ℝ)) ^ 2) : ℂ) := by
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact q0NormFactor_inv_eq_explicit_log_sq (q0NormFactor_ne_zero_of_mem_even_window hX hN)

/--
On the canonical even window, the normalized correction factor is exactly a fixed `X`-scalar times
the inverse `q0` normalization.

This is the cleanest structural form of the correction term presently available. It shows that the
direct normalized average problem has reduced to the window-average behavior of `q0NormFactor⁻¹`,
not to the geometric zero slice itself.
-/
theorem halfMassToNormalizedShapeCorrection_eq_windowScalar_mul_q0NormFactor_inv_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    halfMassToNormalizedShapeCorrection X N
      =
    (unscaledGeometricZeroSliceHalfMass
        / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
      * (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹ := by
  have hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0 :=
    q0NormFactor_ne_zero_of_mem_even_window hX hN
  have hgeom : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  have hfloor : ((routeVisibleWindowNormFloor X : ℝ) : ℂ) ≠ 0 :=
    routeVisibleWindowNormFloor_ne_zero hX
  unfold halfMassToNormalizedShapeCorrection halfMassToZeroModeEnvelopeCorrection
  rw [unscaledGeometricZeroSliceMass_eq_exactGeometricScalar hX hN]
  field_simp [hq0, hgeom, hfloor]

/--
Raw-sum rewrite of the normalized correction factor on the canonical even window.

This packages the previous pointwise identity into the exact window sum consumed by the direct
normalized average theorem.
-/
theorem halfMassToNormalizedShapeCorrection_windowRawSum_eq_windowScalar_mul_q0NormFactor_inv_sum
    {X : ℕ} (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N)
      =
    (unscaledGeometricZeroSliceHalfMass
        / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹ := by
  calc
    (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N)
        =
      ∑ N ∈ EvenIn X H,
        ((unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
          * (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact halfMassToNormalizedShapeCorrection_eq_windowScalar_mul_q0NormFactor_inv_of_mem_even_window hX hN
    _ =
      (unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
        * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹ := by
          rw [← Finset.mul_sum]

/--
Pointwise normalized zero-mode shape decomposition on the canonical even window.

This is the direct normalized analogue of the true-sigma/truncation/correction split:
the normalized observable equals a window-average term plus weighted centered true-sigma,
weighted centered truncation, and weighted centered residual.
-/
theorem normalizedZeroModeShapeObservable_eq_weighted_average_plus_trueSigma_trunc_residual
    {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    normalizedZeroModeShapeObservable X N
      =
    halfMassToNormalizedShapeCorrection X N * halfMassCanonicalAverageWitness X
      + halfMassToNormalizedShapeCorrection X N
          * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
      - halfMassToNormalizedShapeCorrection X N
          * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N
      + halfMassToNormalizedShapeCorrection X N
          * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N := by
  rw [normalizedZeroModeShapeObservable_eq_halfMassToCorrection_mul_halfMassRecentered
    X N hq0 hw0 hunscaled hgeom hsig hfloor]
  rw [Q0MinorHalfMassShellRecentering.halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window
    hX hN]
  have havg :
      Q0MinorHalfMassShellRecentering.exactGeometricArithmeticModel X N
        =
      halfMassCanonicalAverageWitness X + halfMassTailOnlyObservable X N := by
    unfold halfMassTailOnlyObservable
    ring
  rw [havg]
  rw [halfMassTailOnlyObservable_eq_centeredTrueSigmaSeries_add_seriesCorrection
    (S := ramanujanSeriesOnWindow) (X := X) (N := N)]
  rw [halfMassTrueSeriesCorrection_eq_neg_centeredTrunc_add_centeredResidual_of_mem_even_window
    (S := ramanujanSeriesOnWindow) hX hN]
  ring

/--
Exact raw-sum decomposition of the normalized zero-mode shape observable on the canonical even
window.

This isolates the live average theorem for the direct Route-A branch. If the correction factor were
constant on the window and the centered residual vanished, the raw sum would collapse to the
window-average term plus centered true-sigma/truncation sums, which are themselves zero.
-/
theorem normalizedZeroModeShapeWindowRawSum_eq_weighted_average_plus_trueSigma_trunc_residual
    {X : ℕ}
    (hX : X0 ≤ X)
    (hq0 : ∀ {N : ℕ}, N ∈ EvenIn X H → Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : ∀ {N : ℕ}, N ∈ EvenIn X H → unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    _root_.Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope.normalizedZeroModeShapeWindowRawSum X
      =
    halfMassCanonicalAverageWitness X
      * (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N)
      + ∑ N ∈ EvenIn X H,
          halfMassToNormalizedShapeCorrection X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
      - ∑ N ∈ EvenIn X H,
          halfMassToNormalizedShapeCorrection X N
            * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N
      + ∑ N ∈ EvenIn X H,
          halfMassToNormalizedShapeCorrection X N
            * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N := by
  unfold _root_.Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope.normalizedZeroModeShapeWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, normalizedZeroModeShapeObservable X N
        =
      ∑ N ∈ EvenIn X H,
        (halfMassToNormalizedShapeCorrection X N * halfMassCanonicalAverageWitness X
          + halfMassToNormalizedShapeCorrection X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
          - halfMassToNormalizedShapeCorrection X N
              * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N
          + halfMassToNormalizedShapeCorrection X N
              * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          exact normalizedZeroModeShapeObservable_eq_weighted_average_plus_trueSigma_trunc_residual
            hX hN (hq0 hN) hw0 (hunscaled hN) hgeom (hsig hN) hfloor
    _ =
      (∑ N ∈ EvenIn X H,
          (halfMassToNormalizedShapeCorrection X N * halfMassCanonicalAverageWitness X
            + halfMassToNormalizedShapeCorrection X N
                * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
            - halfMassToNormalizedShapeCorrection X N
                * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N))
        + ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N := by
          rw [Finset.sum_add_distrib]
    _ =
      ((∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N * halfMassCanonicalAverageWitness X)
        + ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
        - ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N)
        + ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_add_distrib]
    _ =
      halfMassCanonicalAverageWitness X
        * (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N)
        + ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
        - ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N
        + ∑ N ∈ EvenIn X H,
            halfMassToNormalizedShapeCorrection X N
              * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N := by
          have hmain :
              (∑ N ∈ EvenIn X H,
                  halfMassToNormalizedShapeCorrection X N * halfMassCanonicalAverageWitness X)
                =
              halfMassCanonicalAverageWitness X
                * (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N) := by
            calc
              (∑ N ∈ EvenIn X H,
                  halfMassToNormalizedShapeCorrection X N * halfMassCanonicalAverageWitness X)
                  =
                (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N)
                  * halfMassCanonicalAverageWitness X := by
                    simp [Finset.sum_mul]
              _ =
                halfMassCanonicalAverageWitness X
                  * (∑ N ∈ EvenIn X H, halfMassToNormalizedShapeCorrection X N) := by
                    ring
          rw [hmain]

/--
Fully substituted raw-sum identity for the direct normalized Route-A branch.

This is the decisive main-term exposure step: after eliminating the geometric zero slice from the
correction average, the raw normalized window sum is governed by the product of
`halfMassCanonicalAverageWitness X` with a fixed `X`-scalar and the window sum of
`q0NormFactor⁻¹`, together with the three weighted centered packets.
-/
theorem normalizedZeroModeShapeWindowRawSum_eq_q0NormFactor_inv_mainTerm_plus_centered_packets
    {X : ℕ}
    (hX : X0 ≤ X)
    (hq0 : ∀ {N : ℕ}, N ∈ EvenIn X H → Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : ∀ {N : ℕ}, N ∈ EvenIn X H → unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    normalizedZeroModeShapeWindowRawSum X
      =
    (halfMassCanonicalAverageWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      + ∑ N ∈ EvenIn X H,
          halfMassToNormalizedShapeCorrection X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
      - ∑ N ∈ EvenIn X H,
          halfMassToNormalizedShapeCorrection X N
            * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N
      + ∑ N ∈ EvenIn X H,
          halfMassToNormalizedShapeCorrection X N
            * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N := by
  rw [normalizedZeroModeShapeWindowRawSum_eq_weighted_average_plus_trueSigma_trunc_residual
    hX hq0 hw0 hunscaled hgeom hsig hfloor]
  rw [halfMassToNormalizedShapeCorrection_windowRawSum_eq_windowScalar_mul_q0NormFactor_inv_sum hX]
  ring

/--
Exposed normalized main product in the raw-sum decomposition.

This is the only non-centered term remaining in the direct normalized average problem.
-/
noncomputable def normalizedZeroModeExposedMainProduct (X : ℕ) : ℂ :=
  (halfMassCanonicalAverageWitness X
      * (unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
    * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹

/-- Weighted centered true-sigma packet in the normalized raw-sum decomposition. -/
noncomputable def normalizedZeroModeTrueSigmaPacketRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    halfMassToNormalizedShapeCorrection X N
      * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N

/-- Weighted centered truncation packet in the normalized raw-sum decomposition. -/
noncomputable def normalizedZeroModeTruncPacketRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    halfMassToNormalizedShapeCorrection X N
      * centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N

/-- Weighted centered residual packet in the normalized raw-sum decomposition. -/
noncomputable def normalizedZeroModeResidualPacketRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    halfMassToNormalizedShapeCorrection X N
      * centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N

/--
Defect between the exposed normalized main product and the bookkeeping scalar multiplied by the
window cardinality.

This is the main-term identity that must be understood natively on the normalized surface.
-/
noncomputable def normalizedZeroModeMainProductDefect (X : ℕ) : ℂ :=
  normalizedZeroModeExposedMainProduct X
    - ((EvenIn X H).card : ℂ)
        * (zeroModeBookkeepingScalarCandidate : ℂ)

theorem normalizedZeroModeShapeWindowRawSum_eq_exposedMainProduct_add_centeredPackets
    {X : ℕ}
    (hX : X0 ≤ X)
    (hq0 : ∀ {N : ℕ}, N ∈ EvenIn X H → Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : ∀ {N : ℕ}, N ∈ EvenIn X H → unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    normalizedZeroModeShapeWindowRawSum X
      =
    normalizedZeroModeExposedMainProduct X
      + normalizedZeroModeTrueSigmaPacketRawSum X
      - normalizedZeroModeTruncPacketRawSum X
      + normalizedZeroModeResidualPacketRawSum X := by
  simpa [
    normalizedZeroModeExposedMainProduct,
    normalizedZeroModeTrueSigmaPacketRawSum,
    normalizedZeroModeTruncPacketRawSum,
    normalizedZeroModeResidualPacketRawSum
  ] using
    normalizedZeroModeShapeWindowRawSum_eq_q0NormFactor_inv_mainTerm_plus_centered_packets
      hX hq0 hw0 hunscaled hgeom hsig hfloor

/--
Raw normalized sum, centered at the bookkeeping scalar, split into the main-product defect and the
three weighted centered packets.

This is the exact native normalized statement that the remaining Route-A arithmetic must close.
-/
theorem normalizedZeroModeShapeWindowRawSum_sub_card_mul_bookkeepingScalar_eq_mainProductDefect_add_centeredPackets
    {X : ℕ}
    (hX : X0 ≤ X)
    (hq0 : ∀ {N : ℕ}, N ∈ EvenIn X H → Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : ∀ {N : ℕ}, N ∈ EvenIn X H → unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    normalizedZeroModeShapeWindowRawSum X
      - ((EvenIn X H).card : ℂ) * (zeroModeBookkeepingScalarCandidate : ℂ)
      =
    normalizedZeroModeMainProductDefect X
      + normalizedZeroModeTrueSigmaPacketRawSum X
      - normalizedZeroModeTruncPacketRawSum X
      + normalizedZeroModeResidualPacketRawSum X := by
  rw [normalizedZeroModeShapeWindowRawSum_eq_exposedMainProduct_add_centeredPackets
    hX hq0 hw0 hunscaled hgeom hsig hfloor]
  unfold normalizedZeroModeMainProductDefect
  ring

/--
The exposed normalized main term is exactly a product of two window sums: the half-mass raw window
sum and the `q0NormFactor⁻¹` window sum, multiplied by a fixed `X`-scalar and one card inverse.

This is the sharpest exact form of the remaining average obstruction currently available. Any proof
that this matches `|EvenIn(X,H)| * zeroModeBookkeepingScalarCandidate` must now explain this
product-of-sums structure directly.
-/
theorem normalizedZeroModeExposedMainTerm_eq_cardInv_mul_halfMassRawSum_mul_q0InvSum
    (X : ℕ) :
    (halfMassCanonicalAverageWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      =
    (((EvenIn X H).card : ℂ)⁻¹
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * (halfMassWindowRawSum X * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹) := by
  rw [halfMassCanonicalAverageWitness_eq_average]
  rw [halfMassRecenteredWindowAverage_eq_card_inv_mul_rawSum]
  ring

/--
If the half-mass window average is identified with a fixed scalar `κ`, the exposed normalized main
term reduces to an explicit `κ`-weighted `q0NormFactor⁻¹` window sum.

This theorem is diagnostic: it shows exactly where the old half-mass average witness re-enters if
one wants to turn the normalized main term into a scalar target.
-/
theorem normalizedZeroModeExposedMainTerm_eq_of_halfMassAverageTarget
    {κ : ℝ} (hAvg : HalfMassWindowAverageTarget κ) {X : ℕ} (hX : X0 ≤ X) :
    (halfMassCanonicalAverageWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      =
    ((κ : ℂ)
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹ := by
  rw [halfMassCanonicalAverageWitness_eq_average]
  rw [hAvg.average_eq hX]

/--
If the half-mass window average is identified with a fixed scalar `κ`, the exposed normalized main
term becomes a `κ`-weighted explicit log-square window sum.

This removes the last hidden normalization from the direct normalized average branch. What remains
is an honest average theorem for the explicit window sum of `800 * log(N)^2`.
-/
theorem normalizedZeroModeExposedMainTerm_eq_of_halfMassAverageTarget_and_explicitLogSqSum
    {κ : ℝ} (hAvg : HalfMassWindowAverageTarget κ) {X : ℕ} (hX : X0 ≤ X) :
    (halfMassCanonicalAverageWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      =
    ((κ : ℂ)
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (((800 : ℝ) * (Real.log (N : ℝ)) ^ 2) : ℂ) := by
  rw [normalizedZeroModeExposedMainTerm_eq_of_halfMassAverageTarget hAvg hX]
  rw [q0NormFactor_inv_windowRawSum_eq_explicit_log_sq_sum hX]

/--
The exposed normalized main term splits according to the arithmetic/shell decomposition of the
half-mass window average.

This localizes the remaining old-route dependency: any future obstruction must come from the
arithmetic-model average, the shell-residual average, or their interaction with the explicit
`q0^{-1}` window average, not from hidden normalization.
-/
theorem normalizedZeroModeExposedMainTerm_eq_arithmeticModelAverage_part_add_shellResidualAverage_part
    (X : ℕ) :
    (halfMassCanonicalAverageWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      =
    ((halfMassArithmeticModelWindowAverage X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹)
      +
    ((halfMassShellResidualWindowAverage X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹) := by
  rw [halfMassCanonicalAverageWitness_eq_average]
  rw [halfMassWindowAverage_eq_arithmeticModelAverage_add_shellResidualAverage]
  ring

/--
Generic packaging theorem for the exposed normalized main term.

This is the precise remaining direct-normalized input: once one has a half-mass window average
theorem and a native average theorem for the explicit `q0NormFactor⁻¹` window sum, the normalized
main term becomes a pure scalar multiple of the window cardinality.
-/
theorem normalizedZeroModeExposedMainTerm_eq_card_mul_of_halfMassAverageTarget_and_q0InvAverage
    {κ : ℝ} {β : ℕ → ℂ}
    (hAvg : HalfMassWindowAverageTarget κ)
    (hq0avg : ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹)
        = (((EvenIn X H).card : ℂ) * β X))
    {X : ℕ} (hX : X0 ≤ X) :
    (halfMassCanonicalAverageWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
      * ∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
      =
    (((EvenIn X H).card : ℂ)
        * (((κ : ℂ)
            * (unscaledGeometricZeroSliceHalfMass
                / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))))
          * β X)) := by
  rw [normalizedZeroModeExposedMainTerm_eq_of_halfMassAverageTarget hAvg hX]
  rw [hq0avg hX]
  ring

/--
Real-valued explicit window sum for the inverse `q0` normalization factor.

This removes the final complex wrapper from the native normalized-window average problem.
-/
noncomputable def q0InvExplicitWindowRawSumRe (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, (800 : ℝ) * (Real.log (N : ℝ)) ^ 2

private lemma log_XH_le_14_13_mul_log_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Real.log ((X + H : ℕ) : ℝ) ≤ ((14 : ℝ) / 13) * Real.log (N : ℝ) := by
  have hXleN : X ≤ N := X_le_of_mem_EvenIn (X := X) (N := N) hN
  have hX0leN : X0 ≤ N := le_trans hX hXleN
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leN
  have hlogXH_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hXH_le_twoX : X + H ≤ 2 * X := by
    have hHX : H ≤ X := le_trans (by decide : H ≤ X0) hX
    omega
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos_nat
  have hXHpos : (0 : ℝ) < (((X + H : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX0leXH)
  have hlogXH_le :
      Real.log ((X + H : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    exact Real.log_le_log hXHpos (by exact_mod_cast hXH_le_twoX)
  have hlog_two_mul :
      Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 : ℝ) + Real.log (X : ℝ) := by
    have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hXpos_nat)
    simpa [Nat.cast_mul] using Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXne
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hlogX_leN : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log hXpos (by exact_mod_cast hXleN)
  have hone :
      1 ≤ ((1 : ℝ) / 13) * Real.log (N : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hlogN_ge13 (show 0 ≤ (1 : ℝ) / 13 by positivity)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    Real.log ((X + H : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := hlogXH_le
    _ = Real.log (2 : ℝ) + Real.log (X : ℝ) := hlog_two_mul
    _ ≤ 1 + Real.log (N : ℝ) := by linarith
    _ ≤ ((1 : ℝ) / 13) * Real.log (N : ℝ) + Real.log (N : ℝ) := by
          exact add_le_add_right hone _
    _ = ((14 : ℝ) / 13) * Real.log (N : ℝ) := by ring

private lemma explicitLogSq_term_le_windowTop_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (800 : ℝ) * (Real.log (N : ℝ)) ^ 2
      ≤
    (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
  have hX0leN : X0 ≤ N := le_trans hX (X_le_of_mem_EvenIn (X := X) (N := N) hN)
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by simp [X0]) hX0leN)
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  have hlogle : Real.log (N : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := by
    exact Real.log_le_log hNpos (by exact_mod_cast hNle)
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leN
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by linarith
  have hsq :
      (Real.log (N : ℝ)) ^ 2 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hlogN_nonneg hlogle 2
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

private lemma windowBottom_le_explicitLogSq_term_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)
      ≤
    (800 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
  have hX0leN : X0 ≤ N := le_trans hX (X_le_of_mem_EvenIn (X := X) (N := N) hN)
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leN
  have hlogXH_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hscale :
      ((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    have hmain := log_XH_le_14_13_mul_log_of_mem_even_window hX hN
    have hmul :=
      mul_le_mul_of_nonneg_left hmain (show 0 ≤ (13 : ℝ) / 14 by positivity)
    calc
      ((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)
          ≤ ((13 : ℝ) / 14) * (((14 : ℝ) / 13) * Real.log (N : ℝ)) := hmul
      _ = Real.log (N : ℝ) := by ring
  have hleft_nonneg : 0 ≤ ((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ) := by
    have hlogXH_nonneg : 0 ≤ Real.log ((X + H : ℕ) : ℝ) := by linarith
    positivity
  have hsq :
      (((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hleft_nonneg hscale 2
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/--
Upper bound for the explicit real `q0^{-1}` window sum coming purely from deterministic window
geometry.
-/
theorem q0InvExplicitWindowRawSumRe_upper_bound
    {X : ℕ} (hX : X0 ≤ X) :
    q0InvExplicitWindowRawSumRe X
      ≤
    ((EvenIn X H).card : ℝ) * ((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
  unfold q0InvExplicitWindowRawSumRe
  calc
    ∑ N ∈ EvenIn X H, (800 : ℝ) * (Real.log (N : ℝ)) ^ 2
        ≤
      ∑ _N ∈ EvenIn X H, (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact explicitLogSq_term_le_windowTop_of_mem_even_window hX hN
    _ = ((EvenIn X H).card : ℝ) * ((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/--
Lower bound for the explicit real `q0^{-1}` window sum coming purely from deterministic window
geometry.
-/
theorem q0InvExplicitWindowRawSumRe_lower_bound
    {X : ℕ} (hX : X0 ≤ X) :
    ((EvenIn X H).card : ℝ) * ((800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2))
      ≤
    q0InvExplicitWindowRawSumRe X := by
  unfold q0InvExplicitWindowRawSumRe
  calc
    ((EvenIn X H).card : ℝ) * ((800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2))
        =
      ∑ _N ∈ EvenIn X H, (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ N ∈ EvenIn X H, (800 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact windowBottom_le_explicitLogSq_term_of_mem_even_window hX hN

/--
Deterministic average of the explicit real `q0^{-1}` window sum.
-/
noncomputable def q0InvExplicitWindowAverageRe (X : ℕ) : ℝ :=
  q0InvExplicitWindowRawSumRe X / ((EvenIn X H).card : ℝ)

private lemma even_window_card_pos
    {X : ℕ} (hX : X0 ≤ X) :
    0 < ((EvenIn X H).card : ℝ) := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  exact_mod_cast Nat.pos_of_ne_zero hcard_nat

/--
Upper bound for the native deterministic average of the explicit `q0^{-1}` window sum.
-/
theorem q0InvExplicitWindowAverageRe_upper_bound
    {X : ℕ} (hX : X0 ≤ X) :
    q0InvExplicitWindowAverageRe X
      ≤
    (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
  unfold q0InvExplicitWindowAverageRe
  have hcard_pos : 0 < ((EvenIn X H).card : ℝ) := even_window_card_pos hX
  refine (div_le_iff₀ hcard_pos).2 ?_
  calc
    q0InvExplicitWindowRawSumRe X
        ≤ ((EvenIn X H).card : ℝ) * ((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) :=
          q0InvExplicitWindowRawSumRe_upper_bound hX
    _ = ((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) * ((EvenIn X H).card : ℝ) := by
          ring

/--
Lower bound for the native deterministic average of the explicit `q0^{-1}` window sum.
-/
theorem q0InvExplicitWindowAverageRe_lower_bound
    {X : ℕ} (hX : X0 ≤ X) :
    (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)
      ≤
    q0InvExplicitWindowAverageRe X := by
  unfold q0InvExplicitWindowAverageRe
  have hcard_pos : 0 < ((EvenIn X H).card : ℝ) := even_window_card_pos hX
  refine (le_div_iff₀ hcard_pos).2 ?_
  calc
    (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2) * ((EvenIn X H).card : ℝ)
        =
      ((EvenIn X H).card : ℝ) * ((800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)) := by
          ring
    _ ≤ q0InvExplicitWindowRawSumRe X := q0InvExplicitWindowRawSumRe_lower_bound hX

private lemma q0InvExplicitWindowAverageRe_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) ≠ 0 := by
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlog_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hpos_left :
      0 < (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
    have hlog_pos : 0 < Real.log ((X + H : ℕ) : ℝ) := by
      linarith
    positivity
  have hpos : 0 < q0InvExplicitWindowAverageRe X := by
    exact lt_of_lt_of_le hpos_left (q0InvExplicitWindowAverageRe_lower_bound hX)
  exact_mod_cast (ne_of_gt hpos)

/--
Complex raw-sum form of the native deterministic `q0^{-1}` window average.

This is the exact bridge that converts the exposed normalized main product from a product of raw
sums into a window-cardinality multiple of a product of averages.
-/
theorem q0NormFactor_inv_windowRawSum_eq_card_mul_explicitAverage
    {X : ℕ} (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹)
      =
    ((EvenIn X H).card : ℂ) * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hcardR : ((EvenIn X H).card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  rw [q0NormFactor_inv_windowRawSum_eq_explicit_log_sq_sum hX]
  have hreal :
      q0InvExplicitWindowRawSumRe X
        =
      ((EvenIn X H).card : ℝ) * q0InvExplicitWindowAverageRe X := by
    unfold q0InvExplicitWindowAverageRe
    field_simp [hcardR]
  calc
    ∑ N ∈ EvenIn X H, (((800 : ℝ) * (Real.log (N : ℝ)) ^ 2) : ℂ)
        =
      (((q0InvExplicitWindowRawSumRe X : ℝ) : ℂ)) := by
          simp [q0InvExplicitWindowRawSumRe]
    _ =
      ((((EvenIn X H).card : ℝ) * q0InvExplicitWindowAverageRe X : ℝ) : ℂ) := by
          rw [hreal]
    _ = ((((EvenIn X H).card : ℝ) : ℂ) * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))) := by
          exact
            Complex.ofReal_mul
              ((EvenIn X H).card : ℝ)
              (q0InvExplicitWindowAverageRe X)
    _ = ((EvenIn X H).card : ℂ) * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) := by
          change ((((EvenIn X H).card : ℝ) : ℂ) * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
            = ((((EvenIn X H).card : ℝ) : ℂ) * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
          rfl

/-- The centered explicit `q0⁻¹` observable on the canonical even window. -/
noncomputable def centeredQ0InvExplicitObservable (X N : ℕ) : ℂ :=
  (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹ - (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))

/-- The centered explicit `q0⁻¹` observable has zero raw sum on the canonical even window. -/
theorem centeredQ0InvExplicitObservable_windowRawSum_eq_zero
    {X : ℕ} (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, centeredQ0InvExplicitObservable X N) = 0 := by
  unfold centeredQ0InvExplicitObservable
  rw [Finset.sum_sub_distrib]
  rw [q0NormFactor_inv_windowRawSum_eq_card_mul_explicitAverage hX]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Deterministic top-minus-bottom span for the explicit real `q0⁻¹` observable on `EvenIn X H`. -/
noncomputable def q0InvExplicitWindowSpanRe (X : ℕ) : ℝ :=
  (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2
    - (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)

private lemma q0InvExplicitWindowSpanRe_nonneg
    {X : ℕ} (hX : X0 ≤ X) :
    0 ≤ q0InvExplicitWindowSpanRe X := by
  unfold q0InvExplicitWindowSpanRe
  have hlow :
      (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)
        ≤
      q0InvExplicitWindowAverageRe X :=
    q0InvExplicitWindowAverageRe_lower_bound hX
  have hupp :
      q0InvExplicitWindowAverageRe X
        ≤
      (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 :=
    q0InvExplicitWindowAverageRe_upper_bound hX
  linarith

private lemma centeredQ0InvExplicitObservable_eq_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    centeredQ0InvExplicitObservable X N
      =
    ((((800 : ℝ) * (Real.log (N : ℝ)) ^ 2 - q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) := by
  unfold centeredQ0InvExplicitObservable
  rw [q0NormFactor_inv_eq_explicit_log_sq (q0NormFactor_ne_zero_of_mem_even_window hX hN)]
  simpa [Complex.ofReal_mul] using
    (Complex.ofReal_sub ((800 : ℝ) * (Real.log (N : ℝ)) ^ 2) (q0InvExplicitWindowAverageRe X)).symm

private lemma centeredQ0InvExplicitObservable_norm_le_windowSpan
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖centeredQ0InvExplicitObservable X N‖ ≤ q0InvExplicitWindowSpanRe X := by
  have hterm_low :
      (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)
        ≤
      (800 : ℝ) * (Real.log (N : ℝ)) ^ 2 :=
    windowBottom_le_explicitLogSq_term_of_mem_even_window hX hN
  have hterm_high :
      (800 : ℝ) * (Real.log (N : ℝ)) ^ 2
        ≤
      (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 :=
    explicitLogSq_term_le_windowTop_of_mem_even_window hX hN
  have havg_low :
      (800 : ℝ) * ((((13 : ℝ) / 14) * Real.log ((X + H : ℕ) : ℝ)) ^ 2)
        ≤
      q0InvExplicitWindowAverageRe X :=
    q0InvExplicitWindowAverageRe_lower_bound hX
  have havg_high :
      q0InvExplicitWindowAverageRe X
        ≤
      (800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 :=
    q0InvExplicitWindowAverageRe_upper_bound hX
  have hlow :
      -(q0InvExplicitWindowSpanRe X)
        ≤
      (800 : ℝ) * (Real.log (N : ℝ)) ^ 2 - q0InvExplicitWindowAverageRe X := by
    unfold q0InvExplicitWindowSpanRe
    linarith
  have hhigh :
      (800 : ℝ) * (Real.log (N : ℝ)) ^ 2 - q0InvExplicitWindowAverageRe X
        ≤
      q0InvExplicitWindowSpanRe X := by
    unfold q0InvExplicitWindowSpanRe
    linarith
  rw [centeredQ0InvExplicitObservable_eq_of_mem_even_window hX hN]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-- Squared `ℓ²(EvenIn X H)` energy of the centered explicit `q0⁻¹` observable. -/
noncomputable def centeredQ0InvExplicitWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredQ0InvExplicitObservable X N‖ ^ 2

theorem centeredQ0InvExplicitWindowEnergy_le_card_mul_span_sq
    {X : ℕ} (hX : X0 ≤ X) :
    centeredQ0InvExplicitWindowEnergy X
      ≤
    ((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2 := by
  unfold centeredQ0InvExplicitWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖centeredQ0InvExplicitObservable X N‖ ^ 2
        ≤
      ∑ _N ∈ EvenIn X H, (q0InvExplicitWindowSpanRe X) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact pow_le_pow_left₀ (norm_nonneg _) (centeredQ0InvExplicitObservable_norm_le_windowSpan hX hN) 2
    _ = ((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- Squared `ℓ²(EvenIn X H)` energy of the centered true-sigma series on the canonical window. -/
noncomputable def centeredTrueSigmaWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the centered fixed-`Q0` truncation on the canonical window. -/
noncomputable def centeredNormalizedSigmaTruncWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2

/-- Diagonal part of the local `q,q'` truncation energy expansion. -/
noncomputable def centeredNormalizedSigmaTruncDiagonalEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re ^ 2

/-- Off-diagonal part of the local `q,q'` truncation energy expansion. -/
noncomputable def centeredNormalizedSigmaTruncOffDiagonalCorrelation (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      ∑ q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        if q = q' then 0
        else
          (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
            * (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re

/-- The fixed real `q`-amplitude in the normalized truncation summand. -/
noncomputable def normalizedSigmaTruncSummandRealCoeff (q : ℕ) : ℝ :=
  ((Goldbach.AO_OffDiag.TailBlock.muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)))
    / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2)

theorem normalizedSigmaTruncSummand_re_eq_coeff_mul_ramanujan
    (q N : ℕ) :
    (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re
      =
    normalizedSigmaTruncSummandRealCoeff q
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
  unfold normalizedSigmaTruncSummand normalizedSigmaTruncSummandRealCoeff
  rw [Complex.ofReal_re]
  ring

theorem centeredNormalizedSigmaTruncSummand_re_eq_coeff_mul_ramanujan_sub_average
    (X q N : ℕ) :
    (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
      =
    normalizedSigmaTruncSummandRealCoeff q
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
      - (normalizedSigmaTruncSummandWindowAverage ramanujanSeriesOnWindow X q).re := by
  unfold centeredNormalizedSigmaTruncSummand
  rw [Complex.sub_re, normalizedSigmaTruncSummand_re_eq_coeff_mul_ramanujan]

/-- Canonical-window average of the raw Ramanujan sum at fixed `q`. -/
noncomputable def ramanujanWindowAverage (X q : ℕ) : ℝ :=
  (((EvenIn X H).card : ℝ)⁻¹)
    * ∑ N ∈ EvenIn X H, Goldbach.AO_OffDiag.TailBlock.ramanujanR q N

/-- Centered Ramanujan observable on the canonical even window. -/
noncomputable def centeredRamanujanObservable (X q N : ℕ) : ℝ :=
  Goldbach.AO_OffDiag.TailBlock.ramanujanR q N - ramanujanWindowAverage X q

/-- Per-pair centered Ramanujan covariance on the canonical even window. -/
noncomputable def centeredRamanujanPairCorrelation (X q q' : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, centeredRamanujanObservable X q N * centeredRamanujanObservable X q' N

/-- Centered Ramanujan window energy at fixed `q`. -/
noncomputable def centeredRamanujanWindowEnergy (X q : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, (centeredRamanujanObservable X q N) ^ 2

/-- Coefficient of the gcd-class `g | q` in the closed-form Ramanujan sum. -/
noncomputable def ramanujanGcdClassCoeff (q g : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (q / g) : ℤ) : ℝ)
    * (Nat.totient g : ℝ)

/-- Indicator that `N` lands in the gcd-class `g` for modulus `q`. -/
noncomputable def ramanujanGcdClassIndicator (q g N : ℕ) : ℝ :=
  if Nat.gcd q N = g then (1 : ℝ) else 0

/-- Divisibility-plus-coprimality form of the gcd-class indicator. -/
noncomputable def ramanujanGcdClassCoprimeIndicator (q g N : ℕ) : ℝ :=
  if g ∣ N ∧ Nat.Coprime (q / g) (N / g) then (1 : ℝ) else 0

/-- Window average of a gcd-class indicator on the canonical even window. -/
noncomputable def ramanujanGcdClassWindowAverage (X q g : ℕ) : ℝ :=
  (((EvenIn X H).card : ℝ)⁻¹)
    * ∑ N ∈ EvenIn X H, ramanujanGcdClassIndicator q g N

/-- Centered gcd-class observable on the canonical even window. -/
noncomputable def centeredRamanujanGcdClassObservable (X q g N : ℕ) : ℝ :=
  ramanujanGcdClassIndicator q g N - ramanujanGcdClassWindowAverage X q g

/-- Centered covariance of gcd-class indicators on the canonical even window. -/
noncomputable def centeredRamanujanGcdClassPairCorrelation
    (X q q' g h : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    centeredRamanujanGcdClassObservable X q g N
      * centeredRamanujanGcdClassObservable X q' h N

private lemma gcd_eq_dvd_and_coprime_div_iff_of_mem_divisors
    {q g N : ℕ} (hg : g ∈ q.divisors) :
    Nat.gcd q N = g ↔ g ∣ N ∧ Nat.Coprime (q / g) (N / g) := by
  have hgq : g ∣ q := (Nat.mem_divisors.mp hg).1
  have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
  constructor
  · intro hgcd
    have hgn : g ∣ N := by
      rw [← hgcd]
      exact Nat.gcd_dvd_right q N
    rcases hgq with ⟨q1, hq1⟩
    rcases hgn with ⟨n1, hn1⟩
    subst q
    subst N
    have hmul :
        Nat.gcd (g * q1) (g * n1) = g * Nat.gcd q1 n1 := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.gcd_mul_left g q1 n1
    rw [hmul] at hgcd
    have hgcd' : g * Nat.gcd q1 n1 = g * 1 := by simpa using hgcd
    have hcop : Nat.gcd q1 n1 = 1 := by
      exact Nat.eq_of_mul_eq_mul_left hgpos hgcd'
    refine ⟨dvd_mul_right g n1, ?_⟩
    rw [Nat.coprime_iff_gcd_eq_one]
    have hqdiv : (g * q1) / g = q1 := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right q1 hgpos)
    have hndiv : (g * n1) / g = n1 := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right n1 hgpos)
    simpa [hqdiv, hndiv] using hcop
  · rintro ⟨hgn, hcop⟩
    rcases hgq with ⟨q1, hq1⟩
    rcases hgn with ⟨n1, hn1⟩
    subst q
    subst N
    have hqdiv : (g * q1) / g = q1 := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right q1 hgpos)
    have hndiv : (g * n1) / g = n1 := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right n1 hgpos)
    have hcop' : Nat.Coprime q1 n1 := by
      simpa [hqdiv, hndiv] using hcop
    rw [Nat.coprime_iff_gcd_eq_one] at hcop'
    calc
      Nat.gcd (g * q1) (g * n1) = g * Nat.gcd q1 n1 := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.gcd_mul_left g q1 n1
      _ = g * 1 := by simp [hcop']
      _ = g := by simp

theorem ramanujanGcdClassIndicator_eq_coprimeIndicator_of_mem_divisors
    {q g N : ℕ} (hg : g ∈ q.divisors) :
    ramanujanGcdClassIndicator q g N = ramanujanGcdClassCoprimeIndicator q g N := by
  unfold ramanujanGcdClassIndicator ramanujanGcdClassCoprimeIndicator
  rw [if_congr (gcd_eq_dvd_and_coprime_div_iff_of_mem_divisors (N := N) hg)]
  · simp
  · simp

theorem centeredRamanujanGcdClassObservable_eq_coprimeIndicator_sub_average_of_mem_divisors
    {X q g N : ℕ} (hg : g ∈ q.divisors) :
    centeredRamanujanGcdClassObservable X q g N
      =
    ramanujanGcdClassCoprimeIndicator q g N - ramanujanGcdClassWindowAverage X q g := by
  unfold centeredRamanujanGcdClassObservable
  rw [ramanujanGcdClassIndicator_eq_coprimeIndicator_of_mem_divisors (N := N) hg]

theorem ramanujanR_eq_moebius_mul_totient_gcd
    (q N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
      =
    (((ArithmeticFunction.moebius : ArithmeticFunction ℤ)
        (q / Nat.gcd q N) : ℤ) : ℝ)
      * (Nat.totient (Nat.gcd q N) : ℝ) := by
  simp [Goldbach.AO_OffDiag.TailBlock.ramanujanR, Goldbach.AO_OffDiag.TailBlock.ramanujanZ]

theorem ramanujanR_eq_sum_gcdClassIndicators
    {q N : ℕ} (hq : 1 ≤ q) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
      =
    ∑ g ∈ q.divisors, ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hgmem : Nat.gcd q N ∈ q.divisors := by
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q N, hq0⟩
  rw [Finset.sum_eq_single_of_mem (Nat.gcd q N) hgmem]
  · simp [ramanujanGcdClassCoeff, ramanujanGcdClassIndicator, ramanujanR_eq_moebius_mul_totient_gcd]
  · intro g hg hg_ne
    have hne : Nat.gcd q N ≠ g := by
      exact hg_ne.symm
    simp [ramanujanGcdClassCoeff, ramanujanGcdClassIndicator, hne]

theorem ramanujanWindowAverage_eq_sum_gcdClassAverages
    {X q : ℕ} (hq : 1 ≤ q) :
    ramanujanWindowAverage X q
      =
    ∑ g ∈ q.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassWindowAverage X q g := by
  unfold ramanujanWindowAverage ramanujanGcdClassWindowAverage
  have hrewrite :
      (((EvenIn X H).card : ℝ)⁻¹)
        * ∑ N ∈ EvenIn X H, Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
        =
      (((EvenIn X H).card : ℝ)⁻¹)
        * ∑ N ∈ EvenIn X H, ∑ g ∈ q.divisors,
            ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N := by
    refine congrArg ((((EvenIn X H).card : ℝ)⁻¹) * ·) ?_
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [ramanujanR_eq_sum_gcdClassIndicators (q := q) (N := N) hq]
  rw [hrewrite]
  calc
    (((EvenIn X H).card : ℝ)⁻¹)
        * ∑ N ∈ EvenIn X H, ∑ g ∈ q.divisors,
            ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N
      =
    ∑ N ∈ EvenIn X H, (((EvenIn X H).card : ℝ)⁻¹)
      * ∑ g ∈ q.divisors,
          ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N := by
            rw [Finset.mul_sum]
    _ =
    ∑ N ∈ EvenIn X H, ∑ g ∈ q.divisors,
      (((EvenIn X H).card : ℝ)⁻¹)
        * (ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          rw [Finset.mul_sum]
    _ =
    ∑ g ∈ q.divisors, ∑ N ∈ EvenIn X H,
      (((EvenIn X H).card : ℝ)⁻¹)
        * (ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N) := by
          rw [Finset.sum_comm]
    _ =
    ∑ g ∈ q.divisors,
      ramanujanGcdClassCoeff q g
        * ((((EvenIn X H).card : ℝ)⁻¹)
            * ∑ N ∈ EvenIn X H, ramanujanGcdClassIndicator q g N) := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          calc
            ∑ N ∈ EvenIn X H,
                (((EvenIn X H).card : ℝ)⁻¹)
                  * (ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N)
              =
            (((EvenIn X H).card : ℝ)⁻¹)
              * ∑ N ∈ EvenIn X H,
                  (ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N) := by
                    rw [← Finset.mul_sum]
            _ =
            (((EvenIn X H).card : ℝ)⁻¹)
              * (ramanujanGcdClassCoeff q g
                  * ∑ N ∈ EvenIn X H, ramanujanGcdClassIndicator q g N) := by
                    have hsum :
                        (∑ N ∈ EvenIn X H,
                            ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N)
                          =
                        ramanujanGcdClassCoeff q g
                          * ∑ N ∈ EvenIn X H, ramanujanGcdClassIndicator q g N := by
                            rw [← Finset.mul_sum]
                    rw [hsum]
            _ =
            ramanujanGcdClassCoeff q g
              * ((((EvenIn X H).card : ℝ)⁻¹)
                  * ∑ N ∈ EvenIn X H, ramanujanGcdClassIndicator q g N) := by
                    ring

theorem centeredRamanujanObservable_eq_sum_centeredGcdClasses
    {X q N : ℕ} (hq : 1 ≤ q) :
    centeredRamanujanObservable X q N
      =
    ∑ g ∈ q.divisors,
      ramanujanGcdClassCoeff q g
        * centeredRamanujanGcdClassObservable X q g N := by
  unfold centeredRamanujanObservable centeredRamanujanGcdClassObservable
  rw [ramanujanR_eq_sum_gcdClassIndicators (q := q) (N := N) hq]
  rw [ramanujanWindowAverage_eq_sum_gcdClassAverages (X := X) (q := q) hq]
  calc
    (∑ g ∈ q.divisors, ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N)
      -
        ∑ g ∈ q.divisors,
          ramanujanGcdClassCoeff q g * ramanujanGcdClassWindowAverage X q g
      =
    ∑ g ∈ q.divisors,
      (ramanujanGcdClassCoeff q g * ramanujanGcdClassIndicator q g N
        - ramanujanGcdClassCoeff q g * ramanujanGcdClassWindowAverage X q g) := by
          rw [Finset.sum_sub_distrib]
    _ =
    ∑ g ∈ q.divisors,
      ramanujanGcdClassCoeff q g
        * (ramanujanGcdClassIndicator q g N - ramanujanGcdClassWindowAverage X q g) := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          ring

theorem centeredRamanujanPairCorrelation_eq_sum_gcdClassCovariances
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCorrelation X q q'
      =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * centeredRamanujanGcdClassPairCorrelation X q q' g h := by
  unfold centeredRamanujanPairCorrelation centeredRamanujanGcdClassPairCorrelation
  calc
    ∑ N ∈ EvenIn X H, centeredRamanujanObservable X q N * centeredRamanujanObservable X q' N
      =
    ∑ N ∈ EvenIn X H,
      (∑ g ∈ q.divisors,
        ramanujanGcdClassCoeff q g * centeredRamanujanGcdClassObservable X q g N)
      * (∑ h ∈ q'.divisors,
          ramanujanGcdClassCoeff q' h * centeredRamanujanGcdClassObservable X q' h N) := by
            refine Finset.sum_congr rfl ?_
            intro N hN
            rw [centeredRamanujanObservable_eq_sum_centeredGcdClasses (X := X) (q := q) (N := N) hq]
            rw [centeredRamanujanObservable_eq_sum_centeredGcdClasses (X := X) (q := q') (N := N) hq']
    _ =
    ∑ N ∈ EvenIn X H,
      ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
        (ramanujanGcdClassCoeff q g * centeredRamanujanGcdClassObservable X q g N)
          * (ramanujanGcdClassCoeff q' h * centeredRamanujanGcdClassObservable X q' h N) := by
            refine Finset.sum_congr rfl ?_
            intro N hN
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro g hg
            rw [Finset.mul_sum]
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors, ∑ N ∈ EvenIn X H,
      (ramanujanGcdClassCoeff q g * centeredRamanujanGcdClassObservable X q g N)
        * (ramanujanGcdClassCoeff q' h * centeredRamanujanGcdClassObservable X q' h N) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [Finset.sum_comm]
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * (∑ N ∈ EvenIn X H,
            centeredRamanujanGcdClassObservable X q g N
              * centeredRamanujanGcdClassObservable X q' h N) := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          refine Finset.sum_congr rfl ?_
          intro h hh
          calc
            ∑ N ∈ EvenIn X H,
                (ramanujanGcdClassCoeff q g * centeredRamanujanGcdClassObservable X q g N)
                  * (ramanujanGcdClassCoeff q' h * centeredRamanujanGcdClassObservable X q' h N)
              =
            ∑ N ∈ EvenIn X H,
                (ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h)
                  * (centeredRamanujanGcdClassObservable X q g N
                      * centeredRamanujanGcdClassObservable X q' h N) := by
                        refine Finset.sum_congr rfl ?_
                        intro N hN
                        ring
            _ =
            (ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h)
              * ∑ N ∈ EvenIn X H,
                  centeredRamanujanGcdClassObservable X q g N
                    * centeredRamanujanGcdClassObservable X q' h N := by
                      rw [← Finset.mul_sum]

theorem ramanujanR_add_q_mul_periodic
    (q N t : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q (N + q * t)
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
  rw [ramanujanR_eq_moebius_mul_totient_gcd]
  rw [ramanujanR_eq_moebius_mul_totient_gcd]
  rw [Nat.mul_comm q t, Nat.gcd_add_mul_right_right]

theorem ramanujanR_add_mul_q_periodic
    (q N t : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q (q * t + N)
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
  simpa [Nat.add_comm] using ramanujanR_add_q_mul_periodic q N t

theorem ramanujanR_add_period_of_dvd
    {q P N : ℕ} (hP : q ∣ P) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q (N + P)
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
  rcases hP with ⟨t, rfl⟩
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    ramanujanR_add_q_mul_periodic q N t

theorem ramanujanR_add_lcm_periodic_left
    (q q' N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q (N + Nat.lcm q q')
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
  exact ramanujanR_add_period_of_dvd (q := q) (P := Nat.lcm q q') (N := N) (dvd_lcm_left q q')

theorem ramanujanR_add_lcm_periodic_right
    (q q' N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (N + Nat.lcm q q')
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR q' N := by
  exact ramanujanR_add_period_of_dvd (q := q') (P := Nat.lcm q q') (N := N) (dvd_lcm_right q q')

theorem centeredRamanujanObservable_eq_closedForm_sub_average
    (X q N : ℕ) :
    centeredRamanujanObservable X q N
      =
    ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ)
        (q / Nat.gcd q N) : ℤ) : ℝ)
        * (Nat.totient (Nat.gcd q N) : ℝ))
      - ramanujanWindowAverage X q := by
  unfold centeredRamanujanObservable
  rw [ramanujanR_eq_moebius_mul_totient_gcd]

theorem centeredRamanujanObservable_add_q_mul_periodic
    (X q N t : ℕ) :
    centeredRamanujanObservable X q (N + q * t)
      =
    centeredRamanujanObservable X q N := by
  unfold centeredRamanujanObservable
  rw [ramanujanR_add_q_mul_periodic]

theorem centeredRamanujanObservable_add_period_of_dvd
    {X q P N : ℕ} (hP : q ∣ P) :
    centeredRamanujanObservable X q (N + P)
      =
    centeredRamanujanObservable X q N := by
  unfold centeredRamanujanObservable
  rw [ramanujanR_add_period_of_dvd hP]

/-- Pointwise centered Ramanujan covariance kernel at fixed `(q,q')`. -/
noncomputable def centeredRamanujanPairKernel
    (X q q' N : ℕ) : ℝ :=
  centeredRamanujanObservable X q N * centeredRamanujanObservable X q' N

theorem centeredRamanujanPairKernel_add_lcm_periodic
    (X q q' N : ℕ) :
    centeredRamanujanPairKernel X q q' (N + Nat.lcm q q')
      =
    centeredRamanujanPairKernel X q q' N := by
  unfold centeredRamanujanPairKernel
  rw [centeredRamanujanObservable_add_period_of_dvd (X := X) (q := q)
        (P := Nat.lcm q q') (N := N) (dvd_lcm_left q q')]
  rw [centeredRamanujanObservable_add_period_of_dvd (X := X) (q := q')
        (P := Nat.lcm q q') (N := N) (dvd_lcm_right q q')]

private lemma isEven_add_two_mul_iff (n t : ℕ) :
    Goldbach.Windows.IsEven (n + 2 * t) ↔ Goldbach.Windows.IsEven n := by
  dsimp [Goldbach.Windows.IsEven]
  omega

/-- Offset-kernel on `range (H+1)` whose sum is the centered Ramanujan covariance on `EvenIn X H`. -/
noncomputable def centeredEvenRamanujanPairOffset
    (X q q' k : ℕ) : ℝ :=
  if Goldbach.Windows.IsEven (X + k) then centeredRamanujanPairKernel X q q' (X + k) else 0

/-- Common even-block period for the centered Ramanujan pair kernel. -/
@[simp] def centeredRamanujanPairBlockPeriod (q q' : ℕ) : ℕ :=
  2 * Nat.lcm q q'

theorem centeredEvenRamanujanPairOffset_add_blockPeriod
    (X q q' k : ℕ) :
    centeredEvenRamanujanPairOffset X q q' (k + centeredRamanujanPairBlockPeriod q q')
      =
    centeredEvenRamanujanPairOffset X q q' k := by
  unfold centeredEvenRamanujanPairOffset centeredRamanujanPairBlockPeriod
  have hpar :
      Goldbach.Windows.IsEven (X + (k + 2 * Nat.lcm q q'))
        ↔
      Goldbach.Windows.IsEven (X + k) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      isEven_add_two_mul_iff (X + k) (Nat.lcm q q')
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos ((hpar).2 hEven), if_pos hEven]
    have hk :
        X + (k + 2 * Nat.lcm q q')
          =
        (X + k) + Nat.lcm q q' + Nat.lcm q q' := by
      ring
    rw [hk]
    rw [centeredRamanujanPairKernel_add_lcm_periodic]
    rw [centeredRamanujanPairKernel_add_lcm_periodic]
  · have hnot :
        ¬ Goldbach.Windows.IsEven (X + (k + 2 * Nat.lcm q q')) := by
          intro h
          exact hEven ((hpar).1 h)
    rw [if_neg hnot, if_neg hEven]

theorem sum_range_centeredEvenRamanujanPairOffset_eq_pairCorrelation
    (X q q' : ℕ) :
    ∑ k ∈ Finset.range (H + 1), centeredEvenRamanujanPairOffset X q q' k
      =
    centeredRamanujanPairCorrelation X q q' := by
  unfold centeredRamanujanPairCorrelation EvenIn IccShift centeredEvenRamanujanPairOffset
    centeredRamanujanPairKernel
  rw [Finset.sum_filter]
  rw [Finset.sum_image]
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

private theorem periodic_shift_mul
    {α : Type*} (f : ℕ → α) {P : ℕ}
    (hper : ∀ k, f (k + P) = f k) :
    ∀ m k : ℕ, f (k + m * P) = f k
  | 0, k => by simp
  | m + 1, k => by
      rw [Nat.succ_mul, ← Nat.add_assoc, hper]
      exact periodic_shift_mul f hper m k

private theorem periodic_sum_range_mul
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {P : ℕ} (hP : 0 < P)
    (hper : ∀ k, f (k + P) = f k) :
    ∀ m : ℕ, ∑ k ∈ Finset.range (m * P), f k = m • ∑ k ∈ Finset.range P, f k
  | 0 => by simp
  | m + 1 => by
      calc
        ∑ k ∈ Finset.range ((m + 1) * P), f k
            =
          ∑ k ∈ Finset.range (m * P), f k
            + ∑ k ∈ Finset.range P, f (m * P + k) := by
                simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  (Finset.sum_range_add f (m * P) P)
        _ = m • ∑ k ∈ Finset.range P, f k + ∑ k ∈ Finset.range P, f (m * P + k) := by
              rw [periodic_sum_range_mul f hP hper m]
        _ = m • ∑ k ∈ Finset.range P, f k + ∑ k ∈ Finset.range P, f k := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hshift : f (k + m * P) = f k :=
                periodic_shift_mul f hper m k
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift
        _ = (m + 1) • ∑ k ∈ Finset.range P, f k := by
              simpa [add_comm] using (succ_nsmul (∑ k ∈ Finset.range P, f k) m).symm

private theorem periodic_sum_range_blocks_add_remainder
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {P : ℕ} (hP : 0 < P)
    (hper : ∀ k, f (k + P) = f k)
    (m r : ℕ) :
    ∑ k ∈ Finset.range (m * P + r), f k
      =
    m • ∑ k ∈ Finset.range P, f k
      + ∑ k ∈ Finset.range r, f (m * P + k) := by
  calc
    ∑ k ∈ Finset.range (m * P + r), f k
        =
      ∑ k ∈ Finset.range (m * P), f k
        + ∑ k ∈ Finset.range r, f (m * P + k) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Finset.sum_range_add f (m * P) r)
    _ =
      m • ∑ k ∈ Finset.range P, f k
        + ∑ k ∈ Finset.range r, f (m * P + k) := by
          rw [periodic_sum_range_mul f hP hper m]

/-- Full centered Ramanujan covariance over one complete even block of length `2*lcm(q,q')`. -/
noncomputable def centeredRamanujanPairFullEvenBlockSum
    (X q q' : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    centeredEvenRamanujanPairOffset X q q' k

/-- Raw one-variable Ramanujan block sum over one complete even block of length `2*lcm(q,q')`. -/
noncomputable def rawEvenRamanujanBlockSum
    (X q q' q0 : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + k)
    else 0

/-- Raw pair Ramanujan block sum over one complete even block of length `2*lcm(q,q')`. -/
noncomputable def rawEvenRamanujanPairBlockSum
    (X q q' : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
    else 0

/-- Number of even points in one complete `2*lcm(q,q')` block. -/
noncomputable def evenRamanujanBlockCount
    (X q q' : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0

theorem evenRamanujanBlockCount_pos
    (X q q' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    0 < evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hnonneg :
      ∀ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        0 ≤ (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0) := by
    intro k hk
    by_cases hEven : Goldbach.Windows.IsEven (X + k) <;> simp [hEven]
  unfold evenRamanujanBlockCount
  by_cases hEvenX : Goldbach.Windows.IsEven X
  · have hk0 : 0 ∈ Finset.range (centeredRamanujanPairBlockPeriod q q') := by
      exact Finset.mem_range.mpr hPpos
    have hle :
        (if Goldbach.Windows.IsEven (X + 0) then (1 : ℝ) else 0)
          ≤
        ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
          if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0 := by
      exact Finset.single_le_sum hnonneg hk0
    have hterm : 0 < (if Goldbach.Windows.IsEven (X + 0) then (1 : ℝ) else 0) := by
      simpa [hEvenX]
    exact lt_of_lt_of_le hterm hle
  · have hPgt1 : 1 < centeredRamanujanPairBlockPeriod q q' := by
      dsimp [centeredRamanujanPairBlockPeriod]
      have hlcmpos : 0 < Nat.lcm q q' := Nat.lcm_pos hq hq'
      omega
    have hk1 : 1 ∈ Finset.range (centeredRamanujanPairBlockPeriod q q') := by
      exact Finset.mem_range.mpr hPgt1
    have hEvenSucc : Goldbach.Windows.IsEven (X + 1) := by
      dsimp [Goldbach.Windows.IsEven] at hEvenX ⊢
      omega
    have hle :
        (if Goldbach.Windows.IsEven (X + 1) then (1 : ℝ) else 0)
          ≤
        ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
          if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0 := by
      exact Finset.single_le_sum hnonneg hk1
    have hterm : 0 < (if Goldbach.Windows.IsEven (X + 1) then (1 : ℝ) else 0) := by
      simpa [hEvenSucc]
    exact lt_of_lt_of_le hterm hle

theorem evenRamanujanBlockCount_eq_lcm
    (X q q' : ℕ) :
    evenRamanujanBlockCount X q q' = (Nat.lcm q q' : ℝ) := by
  let f : ℕ → ℝ := fun k => if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0
  have hper : ∀ k, f (k + 2) = f k := by
    intro k
    unfold f
    have hpar :
        Goldbach.Windows.IsEven (X + (k + 2)) ↔ Goldbach.Windows.IsEven (X + k) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (isEven_add_two_mul_iff (X + k) 1)
    by_cases hEven : Goldbach.Windows.IsEven (X + k)
    · simp [hEven, hpar.2 hEven]
    · have hEven' : ¬ Goldbach.Windows.IsEven (X + (k + 2)) := mt hpar.mp hEven
      simp [hEven, hEven']
  have hsum2 : ∑ k ∈ Finset.range 2, f k = (1 : ℝ) := by
    by_cases hEvenX : Goldbach.Windows.IsEven X
    · have hOddSucc : ¬ Goldbach.Windows.IsEven (X + 1) := by
        dsimp [Goldbach.Windows.IsEven] at hEvenX ⊢
        omega
      have hsum : ∑ k ∈ Finset.range 2, f k = f 0 + f 1 := by
        simp [Finset.range_add_one, add_comm, add_left_comm, add_assoc]
      rw [hsum]
      simp [f, hEvenX, hOddSucc]
    · have hEvenSucc : Goldbach.Windows.IsEven (X + 1) := by
        dsimp [Goldbach.Windows.IsEven] at hEvenX ⊢
        omega
      have hsum : ∑ k ∈ Finset.range 2, f k = f 0 + f 1 := by
        simp [Finset.range_add_one, add_comm, add_left_comm, add_assoc]
      rw [hsum]
      simp [f, hEvenX, hEvenSucc]
  unfold evenRamanujanBlockCount centeredRamanujanPairBlockPeriod
  calc
    (∑ k ∈ Finset.range (2 * Nat.lcm q q'),
      (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0))
        =
      ∑ k ∈ Finset.range (Nat.lcm q q' * 2), f k := by
            simp [f, Nat.mul_comm]
    _ = (Nat.lcm q q') • ∑ k ∈ Finset.range 2, f k := by
          rw [periodic_sum_range_mul f (by norm_num) hper (Nat.lcm q q')]
    _ = (Nat.lcm q q' : ℝ) := by simp [hsum2]

theorem centeredRamanujanPairFullEvenBlockSum_eq_rawBlock_decomposition
    (X q q' : ℕ) :
    centeredRamanujanPairFullEvenBlockSum X q q'
      =
    rawEvenRamanujanPairBlockSum X q q'
      - ramanujanWindowAverage X q' * rawEvenRamanujanBlockSum X q q' q
      - ramanujanWindowAverage X q * rawEvenRamanujanBlockSum X q q' q'
      + ramanujanWindowAverage X q * ramanujanWindowAverage X q'
          * evenRamanujanBlockCount X q q' := by
  unfold centeredRamanujanPairFullEvenBlockSum centeredEvenRamanujanPairOffset
    centeredRamanujanPairKernel rawEvenRamanujanPairBlockSum rawEvenRamanujanBlockSum
    evenRamanujanBlockCount centeredRamanujanObservable
  calc
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ite (Goldbach.Windows.IsEven (X + k))
        (((Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k) - ramanujanWindowAverage X q)
          * (Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k) - ramanujanWindowAverage X q')))
        0
      =
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ((if Goldbach.Windows.IsEven (X + k) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
        else 0)
        -
        ramanujanWindowAverage X q'
          * (if Goldbach.Windows.IsEven (X + k) then
              Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
             else 0)
        -
        ramanujanWindowAverage X q
          * (if Goldbach.Windows.IsEven (X + k) then
              Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
             else 0)
        +
        ramanujanWindowAverage X q * ramanujanWindowAverage X q'
          * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        by_cases hEven : Goldbach.Windows.IsEven (X + k)
        · rw [if_pos hEven, if_pos hEven, if_pos hEven, if_pos hEven, if_pos hEven]
          ring
        · rw [if_neg hEven, if_neg hEven, if_neg hEven, if_neg hEven, if_neg hEven]
          ring
    _ =
      (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        (if Goldbach.Windows.IsEven (X + k) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
         else 0))
      -
      ramanujanWindowAverage X q'
        * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
            (if Goldbach.Windows.IsEven (X + k) then
              Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
             else 0))
      -
      ramanujanWindowAverage X q
        * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
            (if Goldbach.Windows.IsEven (X + k) then
              Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
             else 0))
      +
      ramanujanWindowAverage X q * ramanujanWindowAverage X q'
        * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
            (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0)) := by
              calc
                ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                  ((((if Goldbach.Windows.IsEven (X + k) then
                        Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
                          * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
                      else 0)
                    -
                    ramanujanWindowAverage X q'
                      * (if Goldbach.Windows.IsEven (X + k) then
                          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
                        else 0))
                    -
                    ramanujanWindowAverage X q
                      * (if Goldbach.Windows.IsEven (X + k) then
                          Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
                        else 0))
                    +
                    ramanujanWindowAverage X q * ramanujanWindowAverage X q'
                      * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0))
                    =
                (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                  (((if Goldbach.Windows.IsEven (X + k) then
                        Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
                          * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
                      else 0)
                    -
                    ramanujanWindowAverage X q'
                      * (if Goldbach.Windows.IsEven (X + k) then
                          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
                        else 0))
                    -
                    ramanujanWindowAverage X q
                      * (if Goldbach.Windows.IsEven (X + k) then
                          Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
                        else 0)))
                  +
                ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                  ramanujanWindowAverage X q * ramanujanWindowAverage X q'
                    * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0) := by
                      rw [Finset.sum_add_distrib]
                _ =
                (((∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                    (if Goldbach.Windows.IsEven (X + k) then
                      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
                        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
                     else 0))
                  -
                  ramanujanWindowAverage X q'
                    * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                        (if Goldbach.Windows.IsEven (X + k) then
                          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
                         else 0)))
                  -
                  ramanujanWindowAverage X q
                    * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                        (if Goldbach.Windows.IsEven (X + k) then
                          Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
                         else 0)))
                  +
                  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                    ramanujanWindowAverage X q * ramanujanWindowAverage X q'
                      * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0) := by
                        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
                        rw [Finset.mul_sum, Finset.mul_sum]
                _ = _ := by
                      rw [Finset.mul_sum]
                      have hconst_last :
                          (∑ x ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                              ramanujanWindowAverage X q * ramanujanWindowAverage X q'
                                * (if Goldbach.Windows.IsEven (X + x) then (1 : ℝ) else 0))
                            =
                          ramanujanWindowAverage X q * ramanujanWindowAverage X q'
                            * ∑ x ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                                (if Goldbach.Windows.IsEven (X + x) then (1 : ℝ) else 0) := by
                                  rw [← Finset.mul_sum]
                      rw [hconst_last]
    _ =
      rawEvenRamanujanPairBlockSum X q q'
        - ramanujanWindowAverage X q' * rawEvenRamanujanBlockSum X q q' q
        - ramanujanWindowAverage X q * rawEvenRamanujanBlockSum X q q' q'
        + ramanujanWindowAverage X q * ramanujanWindowAverage X q'
            * evenRamanujanBlockCount X q q' := by
              simp [rawEvenRamanujanPairBlockSum, rawEvenRamanujanBlockSum, evenRamanujanBlockCount]

/-- Boundary remainder after extracting all complete `2*lcm(q,q')` even blocks. -/
noncomputable def centeredRamanujanPairBoundaryRemainder
    (X q q' : ℕ) : ℝ :=
  let P := centeredRamanujanPairBlockPeriod q q'
  let m := (H + 1) / P
  let r := (H + 1) % P
  ∑ k ∈ Finset.range r, centeredEvenRamanujanPairOffset X q q' (m * P + k)

theorem centeredRamanujanPairCorrelation_eq_fullBlocks_add_boundary
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCorrelation X q q'
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
      • centeredRamanujanPairFullEvenBlockSum X q q'
      + centeredRamanujanPairBoundaryRemainder X q q' := by
  let P := centeredRamanujanPairBlockPeriod q q'
  let m := (H + 1) / P
  let r := (H + 1) % P
  have hP : 0 < P := by
    dsimp [P, centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hper : ∀ k, centeredEvenRamanujanPairOffset X q q' (k + P) =
      centeredEvenRamanujanPairOffset X q q' k := by
    intro k
    simpa [P] using centeredEvenRamanujanPairOffset_add_blockPeriod X q q' k
  rw [← sum_range_centeredEvenRamanujanPairOffset_eq_pairCorrelation]
  calc
    ∑ k ∈ Finset.range (H + 1), centeredEvenRamanujanPairOffset X q q' k
        =
      ∑ k ∈ Finset.range (m * P + r), centeredEvenRamanujanPairOffset X q q' k := by
          congr 2
          dsimp [m, r]
          rw [Nat.mul_comm]
          exact (Nat.div_add_mod (H + 1) P).symm
    _ =
      m • ∑ k ∈ Finset.range P, centeredEvenRamanujanPairOffset X q q' k
        + ∑ k ∈ Finset.range r, centeredEvenRamanujanPairOffset X q q' (m * P + k) := by
            exact periodic_sum_range_blocks_add_remainder
              (f := centeredEvenRamanujanPairOffset X q q') hP hper m r
    _ =
      (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
        • centeredRamanujanPairFullEvenBlockSum X q q'
        + centeredRamanujanPairBoundaryRemainder X q q' := by
          simp [centeredRamanujanPairFullEvenBlockSum, centeredRamanujanPairBoundaryRemainder,
            P, m, r]

/-- Pointwise centered gcd-class covariance kernel at fixed `(q,q',g,h)`. -/
noncomputable def centeredRamanujanGcdClassPairKernel
    (X q q' g h N : ℕ) : ℝ :=
  centeredRamanujanGcdClassObservable X q g N
    * centeredRamanujanGcdClassObservable X q' h N

theorem centeredRamanujanGcdClassPairKernel_eq_coprimeKernel_of_mem_divisors
    {X q q' g h N : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairKernel X q q' g h N
      =
    (ramanujanGcdClassCoprimeIndicator q g N - ramanujanGcdClassWindowAverage X q g)
      * (ramanujanGcdClassCoprimeIndicator q' h N - ramanujanGcdClassWindowAverage X q' h) := by
  unfold centeredRamanujanGcdClassPairKernel
  rw [centeredRamanujanGcdClassObservable_eq_coprimeIndicator_sub_average_of_mem_divisors
        (X := X) (q := q) (g := g) (N := N) hg]
  rw [centeredRamanujanGcdClassObservable_eq_coprimeIndicator_sub_average_of_mem_divisors
        (X := X) (q := q') (g := h) (N := N) hh]

theorem centeredRamanujanGcdClassObservable_add_period_of_dvd
    {X q g P N : ℕ} (hP : q ∣ P) :
    centeredRamanujanGcdClassObservable X q g (N + P)
      =
    centeredRamanujanGcdClassObservable X q g N := by
  unfold centeredRamanujanGcdClassObservable ramanujanGcdClassIndicator
  rcases hP with ⟨t, rfl⟩
  rw [Nat.mul_comm q t, Nat.gcd_add_mul_right_right]

theorem centeredRamanujanGcdClassPairKernel_add_lcm_periodic
    {X q q' g h N : ℕ} :
    centeredRamanujanGcdClassPairKernel X q q' g h (N + Nat.lcm q q')
      =
    centeredRamanujanGcdClassPairKernel X q q' g h N := by
  unfold centeredRamanujanGcdClassPairKernel
  rw [centeredRamanujanGcdClassObservable_add_period_of_dvd (X := X) (q := q)
        (g := g) (P := Nat.lcm q q') (N := N) (dvd_lcm_left q q')]
  rw [centeredRamanujanGcdClassObservable_add_period_of_dvd (X := X) (q := q')
        (g := h) (P := Nat.lcm q q') (N := N) (dvd_lcm_right q q')]

/-- Offset-kernel on `range (H+1)` whose sum is the centered gcd-class covariance. -/
noncomputable def centeredEvenRamanujanGcdClassPairOffset
    (X q q' g h k : ℕ) : ℝ :=
  if Goldbach.Windows.IsEven (X + k) then centeredRamanujanGcdClassPairKernel X q q' g h (X + k)
  else 0

theorem centeredEvenRamanujanGcdClassPairOffset_add_blockPeriod
    {X q q' g h k : ℕ} :
    centeredEvenRamanujanGcdClassPairOffset X q q' g h (k + centeredRamanujanPairBlockPeriod q q')
      =
    centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
  unfold centeredEvenRamanujanGcdClassPairOffset centeredRamanujanPairBlockPeriod
  have hpar :
      Goldbach.Windows.IsEven (X + (k + 2 * Nat.lcm q q'))
        ↔ Goldbach.Windows.IsEven (X + k) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      isEven_add_two_mul_iff (X + k) (Nat.lcm q q')
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos ((hpar).2 hEven), if_pos hEven]
    have hk :
        X + (k + 2 * Nat.lcm q q')
          =
        (X + k) + Nat.lcm q q' + Nat.lcm q q' := by
      ring
    rw [hk]
    rw [centeredRamanujanGcdClassPairKernel_add_lcm_periodic]
    rw [centeredRamanujanGcdClassPairKernel_add_lcm_periodic]
  · have hnot :
        ¬ Goldbach.Windows.IsEven (X + (k + 2 * Nat.lcm q q')) := by
        intro h
        exact hEven ((hpar).1 h)
    rw [if_neg hnot, if_neg hEven]

theorem sum_range_centeredEvenRamanujanGcdClassPairOffset_eq_pairCorrelation
    (X q q' g h : ℕ) :
    ∑ k ∈ Finset.range (H + 1), centeredEvenRamanujanGcdClassPairOffset X q q' g h k
      =
    centeredRamanujanGcdClassPairCorrelation X q q' g h := by
  unfold centeredRamanujanGcdClassPairCorrelation EvenIn IccShift
    centeredEvenRamanujanGcdClassPairOffset centeredRamanujanGcdClassPairKernel
  rw [Finset.sum_filter]
  rw [Finset.sum_image]
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

/-- Full centered gcd-class covariance over one complete even block of length `2*lcm(q,q')`. -/
noncomputable def centeredRamanujanGcdClassPairFullEvenBlockSum
    (X q q' g h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    centeredEvenRamanujanGcdClassPairOffset X q q' g h k

/-- Raw one-variable gcd-class block sum over one complete even block of length `2*lcm(q,q')`. -/
noncomputable def rawEvenRamanujanGcdClassBlockSum
    (X q q' q0 g0 : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if Goldbach.Windows.IsEven (X + k) then
      ramanujanGcdClassCoprimeIndicator q0 g0 (X + k)
    else 0

/-- Raw pair gcd-class block sum over one complete even block of length `2*lcm(q,q')`. -/
noncomputable def rawEvenRamanujanGcdClassPairBlockSum
    (X q q' g h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if Goldbach.Windows.IsEven (X + k) then
      ramanujanGcdClassCoprimeIndicator q g (X + k)
        * ramanujanGcdClassCoprimeIndicator q' h (X + k)
    else 0

/-- Arithmetic hit condition for one gcd-class on a single input. -/
def ramanujanGcdClassHit (q g N : ℕ) : Prop :=
  g ∣ N ∧ Nat.Coprime (q / g) (N / g)

instance instDecidablePredRamanujanGcdClassHit (q g : ℕ) :
    DecidablePred (ramanujanGcdClassHit q g) := by
  intro N
  unfold ramanujanGcdClassHit
  infer_instance

/-- Single gcd-class hit on one even block offset. -/
def rawEvenRamanujanGcdClassBlockHit
    (X q0 g0 k : ℕ) : Prop :=
  Goldbach.Windows.IsEven (X + k) ∧ ramanujanGcdClassHit q0 g0 (X + k)

instance instDecidablePredRawEvenRamanujanGcdClassBlockHit (X q0 g0 : ℕ) :
    DecidablePred (rawEvenRamanujanGcdClassBlockHit X q0 g0) := by
  intro k
  unfold rawEvenRamanujanGcdClassBlockHit
  infer_instance

/-- Pair gcd-class hit on one even block offset. -/
def rawEvenRamanujanGcdClassPairBlockHit
    (X q q' g h k : ℕ) : Prop :=
  Goldbach.Windows.IsEven (X + k)
    ∧ ramanujanGcdClassHit q g (X + k)
    ∧ ramanujanGcdClassHit q' h (X + k)

/-- Joint arithmetic condition for two gcd-classes on one input. -/
def ramanujanGcdClassJointHit
    (q q' g h N : ℕ) : Prop :=
  Nat.lcm g h ∣ N
    ∧ Nat.Coprime (q / g) (N / g)
    ∧ Nat.Coprime (q' / h) (N / h)

/-- Reduced-variable form of the joint gcd-class condition after factoring out `lcm(g,h)`. -/
def ramanujanGcdClassJointReducedHit
    (q q' g h m : ℕ) : Prop :=
  Nat.Coprime (q / g) (((Nat.lcm g h) / g) * m)
    ∧ Nat.Coprime (q' / h) (((Nat.lcm g h) / h) * m)

/-- Fixed compatibility constraints in the reduced gcd-class joint condition. -/
def ramanujanGcdClassJointCompatibility
    (q q' g h : ℕ) : Prop :=
  Nat.Coprime (q / g) ((Nat.lcm g h) / g)
    ∧ Nat.Coprime (q' / h) ((Nat.lcm g h) / h)

/-- Combined reduced modulus governing the `m`-coprimality condition. -/
def ramanujanGcdClassJointModulus
    (q q' g h : ℕ) : ℕ :=
  (q / g) * (q' / h)

instance instDecidablePredRamanujanGcdClassJointHit (q q' g h : ℕ) :
    DecidablePred (ramanujanGcdClassJointHit q q' g h) := by
  intro N
  unfold ramanujanGcdClassJointHit
  infer_instance

instance instDecidablePredRamanujanGcdClassJointReducedHit (q q' g h : ℕ) :
    DecidablePred (ramanujanGcdClassJointReducedHit q q' g h) := by
  intro m
  unfold ramanujanGcdClassJointReducedHit
  infer_instance

instance instDecidableRamanujanGcdClassJointCompatibility (q q' g h : ℕ) :
    Decidable (ramanujanGcdClassJointCompatibility q q' g h) := by
  unfold ramanujanGcdClassJointCompatibility
  infer_instance

theorem ramanujanGcdClassJointReducedHit_iff_compatibility_and_coprime_modulus
    {q q' g h m : ℕ} :
    ramanujanGcdClassJointReducedHit q q' g h m
      ↔
    ramanujanGcdClassJointCompatibility q q' g h
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  unfold ramanujanGcdClassJointReducedHit ramanujanGcdClassJointCompatibility
    ramanujanGcdClassJointModulus
  have hsplit_left :
      Nat.Coprime (q / g) (((Nat.lcm g h) / g) * m)
        ↔
      Nat.Coprime (q / g) ((Nat.lcm g h) / g) ∧ Nat.Coprime (q / g) m := by
    simpa [Nat.coprime_comm] using
      (Nat.coprime_mul_iff_left (m := ((Nat.lcm g h) / g)) (n := m) (k := (q / g)))
  have hsplit_right :
      Nat.Coprime (q' / h) (((Nat.lcm g h) / h) * m)
        ↔
      Nat.Coprime (q' / h) ((Nat.lcm g h) / h) ∧ Nat.Coprime (q' / h) m := by
    simpa [Nat.coprime_comm] using
      (Nat.coprime_mul_iff_left (m := ((Nat.lcm g h) / h)) (n := m) (k := (q' / h)))
  have hmod :
      Nat.Coprime ((q / g) * (q' / h)) m
        ↔
      Nat.Coprime (q / g) m ∧ Nat.Coprime (q' / h) m := by
    simpa using
      (Nat.coprime_mul_iff_left (m := (q / g)) (n := (q' / h)) (k := m))
  rw [hsplit_left, hsplit_right, hmod]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

theorem not_ramanujanGcdClassJointReducedHit_of_not_compatibility
    {q q' g h m : ℕ}
    (hcompat : ¬ ramanujanGcdClassJointCompatibility q q' g h) :
    ¬ ramanujanGcdClassJointReducedHit q q' g h m := by
  rw [ramanujanGcdClassJointReducedHit_iff_compatibility_and_coprime_modulus]
  intro h
  exact hcompat h.1

/-- Pair gcd-class hit expressed as one evenness condition plus one joint arithmetic condition. -/
def rawEvenRamanujanGcdClassJointBlockHit
    (X q q' g h k : ℕ) : Prop :=
  Goldbach.Windows.IsEven (X + k)
    ∧ ramanujanGcdClassJointHit q q' g h (X + k)

/-- Reduced-variable form of the pair block hit. -/
def rawEvenRamanujanGcdClassReducedBlockHit
    (X q q' g h k : ℕ) : Prop :=
  Goldbach.Windows.IsEven (X + k)
    ∧ Nat.lcm g h ∣ (X + k)
    ∧ ramanujanGcdClassJointReducedHit q q' g h ((X + k) / Nat.lcm g h)

/-- Compatible reduced-variable form: only the explicit modulus-coprimality remains. -/
def rawEvenRamanujanGcdClassCompatibleReducedBlockHit
    (X q q' g h k : ℕ) : Prop :=
  Goldbach.Windows.IsEven (X + k)
    ∧ Nat.lcm g h ∣ (X + k)
    ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) ((X + k) / Nat.lcm g h)

instance instDecidablePredRawEvenRamanujanGcdClassJointBlockHit (X q q' g h : ℕ) :
    DecidablePred (rawEvenRamanujanGcdClassJointBlockHit X q q' g h) := by
  intro k
  unfold rawEvenRamanujanGcdClassJointBlockHit
  infer_instance

instance instDecidablePredRawEvenRamanujanGcdClassReducedBlockHit (X q q' g h : ℕ) :
    DecidablePred (rawEvenRamanujanGcdClassReducedBlockHit X q q' g h) := by
  intro k
  unfold rawEvenRamanujanGcdClassReducedBlockHit
  infer_instance

instance instDecidablePredRawEvenRamanujanGcdClassCompatibleReducedBlockHit (X q q' g h : ℕ) :
    DecidablePred (rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h) := by
  intro k
  unfold rawEvenRamanujanGcdClassCompatibleReducedBlockHit
  infer_instance

instance instDecidablePredRawEvenRamanujanGcdClassPairBlockHit (X q q' g h : ℕ) :
    DecidablePred (rawEvenRamanujanGcdClassPairBlockHit X q q' g h) := by
  intro k
  unfold rawEvenRamanujanGcdClassPairBlockHit
  infer_instance

theorem ramanujanGcdClassHit_pair_iff_joint
    {q q' g h N : ℕ} :
    ramanujanGcdClassHit q g N ∧ ramanujanGcdClassHit q' h N
      ↔
    ramanujanGcdClassJointHit q q' g h N := by
  constructor
  · rintro ⟨⟨hgN, hcop⟩, ⟨hhN, hcop'⟩⟩
    refine ⟨Nat.lcm_dvd hgN hhN, hcop, hcop'⟩
  · rintro ⟨hlcmN, hcop, hcop'⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, hcop⟩
      exact (Nat.dvd_lcm_left g h).trans hlcmN
    · refine ⟨?_, hcop'⟩
      exact (Nat.dvd_lcm_right g h).trans hlcmN

theorem ramanujanGcdClassJointHit_lcm_mul_iff
    {q q' g h m : ℕ} :
    ramanujanGcdClassJointHit q q' g h (Nat.lcm g h * m)
      ↔
    ramanujanGcdClassJointReducedHit q q' g h m := by
  unfold ramanujanGcdClassJointHit ramanujanGcdClassJointReducedHit
  have hquotg : Nat.lcm g h * m / g = (Nat.lcm g h / g) * m := by
    rw [Nat.mul_comm, Nat.mul_div_assoc _ (Nat.dvd_lcm_left g h)]
    rw [Nat.mul_comm]
  have hquoth : Nat.lcm g h * m / h = (Nat.lcm g h / h) * m := by
    rw [Nat.mul_comm, Nat.mul_div_assoc _ (Nat.dvd_lcm_right g h)]
    rw [Nat.mul_comm]
  constructor
  · rintro ⟨_, hcop, hcop'⟩
    refine ⟨?_, ?_⟩
    · simpa [hquotg] using hcop
    · simpa [hquoth] using hcop'
  · rintro ⟨hcop, hcop'⟩
    refine ⟨dvd_mul_right _ _, ?_, ?_⟩
    · simpa [hquotg] using hcop
    · simpa [hquoth] using hcop'

theorem ramanujanGcdClassJointHit_iff_dvd_and_reduced
    {q q' g h N : ℕ} (hLpos : 0 < Nat.lcm g h) :
    ramanujanGcdClassJointHit q q' g h N
      ↔
    Nat.lcm g h ∣ N ∧ ramanujanGcdClassJointReducedHit q q' g h (N / Nat.lcm g h) := by
  constructor
  · rintro ⟨hL, hcop, hcop'⟩
    refine ⟨hL, ?_⟩
    rcases hL with ⟨m, rfl⟩
    have hJoint : ramanujanGcdClassJointHit q q' g h (Nat.lcm g h * m) := by
      exact ⟨dvd_mul_right _ _, hcop, hcop'⟩
    change ramanujanGcdClassJointReducedHit q q' g h ((Nat.lcm g h * m) / Nat.lcm g h)
    rw [Nat.mul_div_right _ hLpos]
    exact
      (ramanujanGcdClassJointHit_lcm_mul_iff
        (q := q) (q' := q') (g := g) (h := h) (m := m)).1 hJoint
  · rintro ⟨hL, hred⟩
    rcases hL with ⟨m, rfl⟩
    have hred' : ramanujanGcdClassJointReducedHit q q' g h m := by
      change ramanujanGcdClassJointReducedHit q q' g h ((Nat.lcm g h * m) / Nat.lcm g h) at hred
      rw [Nat.mul_div_right _ hLpos] at hred
      exact hred
    exact
      (ramanujanGcdClassJointHit_lcm_mul_iff (q := q) (q' := q') (g := g) (h := h) (m := m)).2 hred'

theorem rawEvenRamanujanGcdClassPairBlockHit_iff_joint
    {X q q' g h k : ℕ} :
    rawEvenRamanujanGcdClassPairBlockHit X q q' g h k
      ↔
    rawEvenRamanujanGcdClassJointBlockHit X q q' g h k := by
  unfold rawEvenRamanujanGcdClassPairBlockHit rawEvenRamanujanGcdClassJointBlockHit
  constructor
  · rintro ⟨hEven, hq, hq'⟩
    refine ⟨hEven, ?_⟩
    exact (ramanujanGcdClassHit_pair_iff_joint
      (q := q) (q' := q') (g := g) (h := h) (N := X + k)).1 ⟨hq, hq'⟩
  · rintro ⟨hEven, hjoint⟩
    refine ⟨hEven, ?_⟩
    exact (ramanujanGcdClassHit_pair_iff_joint
      (q := q) (q' := q') (g := g) (h := h) (N := X + k)).2 hjoint

theorem rawEvenRamanujanGcdClassJointBlockHit_iff_reduced
    {X q q' g h k : ℕ} (hLpos : 0 < Nat.lcm g h) :
    rawEvenRamanujanGcdClassJointBlockHit X q q' g h k
      ↔
    rawEvenRamanujanGcdClassReducedBlockHit X q q' g h k := by
  unfold rawEvenRamanujanGcdClassJointBlockHit rawEvenRamanujanGcdClassReducedBlockHit
  constructor
  · rintro ⟨hEven, hJoint⟩
    rcases (ramanujanGcdClassJointHit_iff_dvd_and_reduced
      (q := q) (q' := q') (g := g) (h := h) (N := X + k) hLpos).1 hJoint with ⟨hL, hred⟩
    exact ⟨hEven, hL, hred⟩
  · rintro ⟨hEven, hL, hred⟩
    refine ⟨hEven, ?_⟩
    exact (ramanujanGcdClassJointHit_iff_dvd_and_reduced
      (q := q) (q' := q') (g := g) (h := h) (N := X + k) hLpos).2 ⟨hL, hred⟩

theorem rawEvenRamanujanGcdClassReducedBlockHit_iff_compatibility_and_coprime_modulus
    {X q q' g h k : ℕ} :
    rawEvenRamanujanGcdClassReducedBlockHit X q q' g h k
      ↔
    Goldbach.Windows.IsEven (X + k)
      ∧ Nat.lcm g h ∣ (X + k)
      ∧ ramanujanGcdClassJointCompatibility q q' g h
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) ((X + k) / Nat.lcm g h) := by
  unfold rawEvenRamanujanGcdClassReducedBlockHit
  rw [ramanujanGcdClassJointReducedHit_iff_compatibility_and_coprime_modulus]

theorem not_rawEvenRamanujanGcdClassReducedBlockHit_of_not_compatibility
    {X q q' g h k : ℕ}
    (hcompat : ¬ ramanujanGcdClassJointCompatibility q q' g h) :
    ¬ rawEvenRamanujanGcdClassReducedBlockHit X q q' g h k := by
  rw [rawEvenRamanujanGcdClassReducedBlockHit_iff_compatibility_and_coprime_modulus]
  intro h
  exact hcompat h.2.2.1

theorem rawEvenRamanujanGcdClassReducedBlockHit_iff_compatible
    {X q q' g h k : ℕ}
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassReducedBlockHit X q q' g h k
      ↔
    rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h k := by
  unfold rawEvenRamanujanGcdClassCompatibleReducedBlockHit
  rw [rawEvenRamanujanGcdClassReducedBlockHit_iff_compatibility_and_coprime_modulus]
  constructor
  · rintro ⟨hEven, hL, -, hcop⟩
    exact ⟨hEven, hL, hcop⟩
  · rintro ⟨hEven, hL, hcop⟩
    exact ⟨hEven, hL, hcompat, hcop⟩

/-- Counting version of the raw one-variable gcd-class block sum. -/
noncomputable def rawEvenRamanujanGcdClassBlockCount
    (X q q' q0 g0 : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if rawEvenRamanujanGcdClassBlockHit X q0 g0 k then (1 : ℝ) else 0

/-- Counting version of the raw pair gcd-class block sum. -/
noncomputable def rawEvenRamanujanGcdClassPairBlockCount
    (X q q' g h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
    if rawEvenRamanujanGcdClassPairBlockHit X q q' g h k then (1 : ℝ) else 0

theorem ramanujanGcdClassCoprimeIndicator_eq_hitIndicator_of_mem_divisors
    {q g N : ℕ} (_hg : g ∈ q.divisors) :
    ramanujanGcdClassCoprimeIndicator q g N
      =
    if ramanujanGcdClassHit q g N then (1 : ℝ) else 0 := by
  unfold ramanujanGcdClassCoprimeIndicator ramanujanGcdClassHit
  simp

theorem rawEvenRamanujanGcdClassBlockSum_eq_count
    {X q q' q0 g0 : ℕ} (hg0 : g0 ∈ q0.divisors) :
    rawEvenRamanujanGcdClassBlockSum X q q' q0 g0
      =
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0 := by
  unfold rawEvenRamanujanGcdClassBlockSum rawEvenRamanujanGcdClassBlockCount
    rawEvenRamanujanGcdClassBlockHit
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos hEven]
    rw [ramanujanGcdClassCoprimeIndicator_eq_hitIndicator_of_mem_divisors (N := X + k) hg0]
    simp [hEven]
  · rw [if_neg hEven]
    simp [hEven]

theorem rawEvenRamanujanGcdClassPairBlockSum_eq_count
    {X q q' g h : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPairBlockSum X q q' g h
      =
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h := by
  unfold rawEvenRamanujanGcdClassPairBlockSum rawEvenRamanujanGcdClassPairBlockCount
    rawEvenRamanujanGcdClassPairBlockHit
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos hEven]
    rw [ramanujanGcdClassCoprimeIndicator_eq_hitIndicator_of_mem_divisors (N := X + k) hg]
    rw [ramanujanGcdClassCoprimeIndicator_eq_hitIndicator_of_mem_divisors (N := X + k) hh]
    by_cases hq : ramanujanGcdClassHit q g (X + k)
    · by_cases hq' : ramanujanGcdClassHit q' h (X + k)
      · simp [hEven, hq, hq']
      · simp [hEven, hq, hq']
    · by_cases hq' : ramanujanGcdClassHit q' h (X + k)
      · simp [hEven, hq, hq']
      · simp [hEven, hq, hq']
  · rw [if_neg hEven]
    simp [hEven]

theorem rawEvenRamanujanGcdClassBlockCount_eq_card_filter
    (X q q' q0 g0 : ℕ) :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      =
    (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassBlockHit X q0 g0)).card : ℝ) := by
  classical
  unfold rawEvenRamanujanGcdClassBlockCount
  rw [← Finset.sum_filter]
  simp

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_card_filter
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassPairBlockHit X q q' g h)).card : ℝ) := by
  classical
  unfold rawEvenRamanujanGcdClassPairBlockCount
  rw [← Finset.sum_filter]
  simp

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_joint_card_filter
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassJointBlockHit X q q' g h)).card : ℝ) := by
  classical
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_card_filter]
  refine congrArg (fun t : ℕ => (t : ℝ)) <| congrArg Finset.card <| Finset.filter_congr (by
    intro k hk
    show rawEvenRamanujanGcdClassPairBlockHit X q q' g h k ↔
        rawEvenRamanujanGcdClassJointBlockHit X q q' g h k
    simpa using (rawEvenRamanujanGcdClassPairBlockHit_iff_joint
      (X := X) (q := q) (q' := q') (g := g) (h := h) (k := k)))

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_reduced_card_filter
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassReducedBlockHit X q q' g h)).card : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_joint_card_filter]
  refine congrArg (fun t : ℕ => (t : ℝ)) <| congrArg Finset.card <| Finset.filter_congr (by
    intro k hk
    show rawEvenRamanujanGcdClassJointBlockHit X q q' g h k ↔
        rawEvenRamanujanGcdClassReducedBlockHit X q q' g h k
    simpa using (rawEvenRamanujanGcdClassJointBlockHit_iff_reduced
      (X := X) (q := q) (q' := q') (g := g) (h := h) (k := k) hLpos))

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_zero_of_not_compatibility
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hcompat : ¬ ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h = 0 := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_reduced_card_filter X q q' g h hLpos]
  have hempty :
      (Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassReducedBlockHit X q q' g h) = ∅ := by
    ext k
    simp [not_rawEvenRamanujanGcdClassReducedBlockHit_of_not_compatibility hcompat]
  rw [hempty]
  norm_num

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_card_filter
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h)).card : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_reduced_card_filter X q q' g h hLpos]
  refine congrArg (fun t : ℕ => (t : ℝ)) <| congrArg Finset.card <| Finset.filter_congr (by
    intro k hk
    show rawEvenRamanujanGcdClassReducedBlockHit X q q' g h k ↔
        rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h k
    simpa using (rawEvenRamanujanGcdClassReducedBlockHit_iff_compatible
      (X := X) (q := q) (q' := q') (g := g) (h := h) (k := k) hcompat))

/-- The reduced-variable quotient values arising from the compatible gcd-class block hits. -/
noncomputable def rawEvenRamanujanGcdClassCompatibleReducedQuotientSet
    (X q q' g h : ℕ) : Finset ℕ :=
  Finset.image
    (fun k => (X + k) / Nat.lcm g h)
    ((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
      (rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h))

/-- The exact reduced-variable slice cut out by one compatible gcd-class block. -/
noncomputable def rawEvenRamanujanGcdClassCompatibleReducedSlice
    (X q q' g h : ℕ) : Finset ℕ :=
  (Finset.Icc (X / Nat.lcm g h)
      ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h)).filter
    (fun m =>
      X ≤ Nat.lcm g h * m
        ∧ Nat.lcm g h * m < X + centeredRamanujanPairBlockPeriod q q'
        ∧ Goldbach.Windows.IsEven (Nat.lcm g h * m)
        ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m)

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff
    {X q q' g h m : ℕ} :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h
      ↔
    ∃ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h k
        ∧ m = (X + k) / Nat.lcm g h := by
  unfold rawEvenRamanujanGcdClassCompatibleReducedQuotientSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2, rfl⟩
  · rintro ⟨k, hkRange, hkHit, hm⟩
    refine ⟨k, Finset.mem_filter.mpr ⟨hkRange, hkHit⟩, hm.symm⟩

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_coprime
    {X q q' g h m : ℕ}
    (hm : m ∈ rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h) :
    Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  rcases (mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff.mp hm) with
    ⟨k, hkRange, hkHit, rfl⟩
  exact hkHit.2.2

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_le
    {X q q' g h m : ℕ}
    (hm : m ∈ rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h) :
    m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h := by
  rcases (mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff.mp hm) with
    ⟨k, hkRange, hkHit, rfl⟩
  have hklt : k < centeredRamanujanPairBlockPeriod q q' := Finset.mem_range.mp hkRange
  have hle : X + k ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 := by
    omega
  exact Nat.div_le_div_right hle

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_lower
    {X q q' g h m : ℕ}
    (hm : m ∈ rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h) :
    X / Nat.lcm g h ≤ m := by
  rcases (mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff.mp hm) with
    ⟨k, hkRange, hkHit, rfl⟩
  exact Nat.div_le_div_right (Nat.le_add_right X k)

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_bounds_and_coprime
    {X q q' g h m : ℕ}
    (hm : m ∈ rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h) :
    X / Nat.lcm g h ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  exact ⟨mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_lower hm,
    mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_le hm,
    mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_coprime hm⟩

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff
    {X q q' g h m : ℕ} :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
      ↔
    X / Nat.lcm g h ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h
      ∧ X ≤ Nat.lcm g h * m
      ∧ Nat.lcm g h * m < X + centeredRamanujanPairBlockPeriod q q'
      ∧ Goldbach.Windows.IsEven (Nat.lcm g h * m)
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  unfold rawEvenRamanujanGcdClassCompatibleReducedSlice
  simp [and_left_comm, and_assoc]

theorem isEven_mul_iff_of_not_isEven_left
    {a m : ℕ} (ha : ¬ Goldbach.Windows.IsEven a) :
    Goldbach.Windows.IsEven (a * m) ↔ Goldbach.Windows.IsEven m := by
  constructor
  · intro hm
    have hmEven : Even (a * m) := Goldbach.Windows.even_of_isEven hm
    have hsplit : Even a ∨ Even m := (Nat.even_mul).1 hmEven
    cases hsplit with
    | inl haEven =>
        exact False.elim (ha (Goldbach.Windows.isEven_of_even haEven))
    | inr hmEven =>
        exact Goldbach.Windows.isEven_of_even hmEven
  · intro hm
    exact Goldbach.Windows.isEven_of_even <| (Nat.even_mul).2 <|
      Or.inr (Goldbach.Windows.even_of_isEven hm)

theorem isEven_mul_of_isEven_left
    {a m : ℕ} (ha : Goldbach.Windows.IsEven a) :
    Goldbach.Windows.IsEven (a * m) := by
  exact Goldbach.Windows.isEven_of_even <| (Nat.even_mul).2 <|
    Or.inl (Goldbach.Windows.even_of_isEven ha)

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_isEven_lcm
    {X q q' g h m : ℕ} (hL : Goldbach.Windows.IsEven (Nat.lcm g h)) :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
      ↔
    X / Nat.lcm g h ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h
      ∧ X ≤ Nat.lcm g h * m
      ∧ Nat.lcm g h * m < X + centeredRamanujanPairBlockPeriod q q'
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff]
  constructor
  · rintro ⟨hlo, hhi, hXle, hlt, -, hcop⟩
    exact ⟨hlo, hhi, hXle, hlt, hcop⟩
  · rintro ⟨hlo, hhi, hXle, hlt, hcop⟩
    exact ⟨hlo, hhi, hXle, hlt, isEven_mul_of_isEven_left hL, hcop⟩

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_not_isEven_lcm
    {X q q' g h m : ℕ} (hL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
      ↔
    X / Nat.lcm g h ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h
      ∧ X ≤ Nat.lcm g h * m
      ∧ Nat.lcm g h * m < X + centeredRamanujanPairBlockPeriod q q'
      ∧ Goldbach.Windows.IsEven m
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff,
    isEven_mul_iff_of_not_isEven_left hL]

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_isEven_lcm_ceildiv
    {X q q' g h m : ℕ} (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hL : Goldbach.Windows.IsEven (Nat.lcm g h)) :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
      ↔
    X ⌈/⌉ Nat.lcm g h ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_isEven_lcm hL]
  constructor
  · rintro ⟨_, hhi, hXle, _, hcop⟩
    refine ⟨?_, hhi, hcop⟩
    exact (ceilDiv_le_iff_le_mul hLpos).2 hXle
  · rintro ⟨hlo, hhi, hcop⟩
    refine ⟨?_, hhi, ?_, ?_, hcop⟩
    · exact (floorDiv_le_ceilDiv (b := X) (a := Nat.lcm g h)).trans hlo
    · exact (ceilDiv_le_iff_le_mul hLpos).1 hlo
    · have hmulpred :
        Nat.lcm g h * m ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 := by
        have hmulpred' : m * Nat.lcm g h ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 :=
          Nat.mul_le_of_le_div _ _ _ hhi
        simpa [Nat.mul_comm] using hmulpred'
      omega

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_not_isEven_lcm_ceildiv
    {X q q' g h m : ℕ} (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
      ↔
    X ⌈/⌉ Nat.lcm g h ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h
      ∧ Goldbach.Windows.IsEven m
      ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m := by
  rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_not_isEven_lcm hL]
  constructor
  · rintro ⟨_, hhi, hXle, _, hmEven, hcop⟩
    refine ⟨?_, hhi, hmEven, hcop⟩
    exact (ceilDiv_le_iff_le_mul hLpos).2 hXle
  · rintro ⟨hlo, hhi, hmEven, hcop⟩
    refine ⟨?_, hhi, ?_, ?_, hmEven, hcop⟩
    · exact (floorDiv_le_ceilDiv (b := X) (a := Nat.lcm g h)).trans hlo
    · exact (ceilDiv_le_iff_le_mul hLpos).1 hlo
    · have hmulpred :
        Nat.lcm g h * m ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 := by
        have hmulpred' : m * Nat.lcm g h ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 :=
          Nat.mul_le_of_le_div _ _ _ hhi
        simpa [Nat.mul_comm] using hmulpred'
      omega

private theorem card_filter_range_eq_sum_indicator
    (L : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (((Finset.range L).filter p).card : ℕ)
      =
    ∑ k ∈ Finset.range L, if p k then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp

private theorem coprime_shiftedRange_card_eq_fullPeriods_add_remainder
    (A L M : ℕ) (hM : 0 < M) :
    (((Finset.range L).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
      =
    (L / M) * (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
      + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card : ℕ) := by
  let f : ℕ → ℕ := fun k => if Nat.Coprime M (A + k) then 1 else 0
  have hper : ∀ k, f (k + M) = f k := by
    intro k
    unfold f
    have hcop :
        Nat.Coprime M (A + (k + M)) ↔ Nat.Coprime M (A + k) := by
      simpa [Nat.add_assoc, Nat.mul_one] using
        (Nat.coprime_add_mul_left_right M (A + k) 1)
    by_cases hk : Nat.Coprime M (A + k) <;> simp [hcop, hk]
  have hLen : (L / M) * M + (L % M) = L := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod L M)
  calc
    (((Finset.range L).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
        =
      ∑ k ∈ Finset.range L, f k := by
        unfold f
        rw [card_filter_range_eq_sum_indicator]
    _ =
      ∑ k ∈ Finset.range ((L / M) * M + (L % M)), f k := by
        rw [hLen]
    _ =
      (L / M) • ∑ k ∈ Finset.range M, f k
        + ∑ k ∈ Finset.range (L % M), f ((L / M) * M + k) := by
          simpa [Nat.mul_comm] using
            (periodic_sum_range_blocks_add_remainder f hM hper (L / M) (L % M))
      _ =
        (L / M) * (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
          + (((Finset.range (L % M)).filter
                (fun t => Nat.Coprime M (A + (L / M) * M + t))).card : ℕ) := by
            unfold f
            rw [card_filter_range_eq_sum_indicator, card_filter_range_eq_sum_indicator]
            simp [Nat.add_assoc]

private theorem card_filter_range_coprime_shift_eq_totient
    (A M : ℕ) (_hM : 0 < M) :
    (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
      = Nat.totient M := by
  calc
    (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
        = (((Finset.Ico A (A + M)).filter (fun x => Nat.Coprime M x)).card : ℕ) := by
          classical
          refine Finset.card_bij
            (fun t _ => A + t)
            (fun t ht => ?_)
            (fun t₁ _ t₂ _ hEq => Nat.add_left_cancel hEq)
            (fun x hx => ?_)
          · rcases Finset.mem_filter.mp ht with ⟨htRange, hcop⟩
            refine Finset.mem_filter.mpr ?_
            refine ⟨?_, ?_⟩
            · exact Finset.mem_Ico.mpr ⟨Nat.le_add_right A t, by
                simpa using Nat.add_lt_add_left (Finset.mem_range.mp htRange) A⟩
            · simpa [Nat.coprime_comm] using hcop
          · rcases Finset.mem_filter.mp hx with ⟨hxIco, hcop⟩
            refine ⟨x - A, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ?_
              refine ⟨Finset.mem_range.mpr ?_, ?_⟩
              · have hxlo := (Finset.mem_Ico.mp hxIco).1
                have hxhi : A + (x - A) < A + M := by
                  simpa [Nat.add_sub_of_le hxlo] using (Finset.mem_Ico.mp hxIco).2
                exact Nat.add_lt_add_iff_left.mp hxhi
              · simpa [Nat.add_sub_of_le (Finset.mem_Ico.mp hxIco).1, Nat.coprime_comm] using hcop
            · exact Nat.add_sub_of_le (Finset.mem_Ico.mp hxIco).1
    _ = Nat.totient M := by
        simpa [Nat.coprime_comm] using (Nat.filter_coprime_Ico_eq_totient M A)

private theorem evenCoprime_shiftedRange_card_eq_fullPeriods_add_remainder
    (A L M : ℕ) :
    (((Finset.range L).filter
        (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card : ℕ)
      =
    (L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card : ℕ)
      + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card : ℕ) := by
  let P := 2 * M
  by_cases hP : 0 < P
  · let f : ℕ → ℕ := fun k =>
      if Goldbach.Windows.IsEven (A + k) ∧ Nat.Coprime M (A + k) then 1 else 0
    have hper : ∀ k, f (k + P) = f k := by
      intro k
      unfold f P
      have hEven :
          Goldbach.Windows.IsEven (A + (k + 2 * M))
            ↔ Goldbach.Windows.IsEven (A + k) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul] using
          (isEven_add_two_mul_iff (n := A + k) (t := M))
      have hcop :
          Nat.Coprime M (A + (k + 2 * M)) ↔ Nat.Coprime M (A + k) := by
        simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.coprime_add_mul_left_right M (A + k) 2)
      by_cases hk : Goldbach.Windows.IsEven (A + k) ∧ Nat.Coprime M (A + k) <;>
        simp [hEven, hcop, hk]
    have hLen : (L / P) * P + (L % P) = L := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod L P)
    calc
      (((Finset.range L).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card : ℕ)
          =
        ∑ k ∈ Finset.range L, f k := by
          unfold f
          rw [card_filter_range_eq_sum_indicator]
      _ =
        ∑ k ∈ Finset.range ((L / P) * P + (L % P)), f k := by
          rw [hLen]
      _ =
        (L / P) • ∑ k ∈ Finset.range P, f k
          + ∑ k ∈ Finset.range (L % P), f ((L / P) * P + k) := by
            simpa [Nat.mul_comm] using
              (periodic_sum_range_blocks_add_remainder f hP hper (L / P) (L % P))
      _ =
        (L / (2 * M)) * (((Finset.range (2 * M)).filter
            (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card : ℕ)
          + (((Finset.range (L % (2 * M))).filter
                (fun t =>
                  Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                    ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card : ℕ) := by
            unfold f P
            rw [card_filter_range_eq_sum_indicator, card_filter_range_eq_sum_indicator]
            simp [Nat.add_assoc]
  · have hM0 : M = 0 := by omega
    subst hM0
    norm_num

/-- Quotient image of the single gcd-class block-hit set under `m = (X+k)/g0`. -/
noncomputable def rawEvenRamanujanGcdClassReducedQuotientSet
    (X q q' q0 g0 : ℕ) : Finset ℕ :=
  Finset.image
    (fun k => (X + k) / g0)
    ((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
      (rawEvenRamanujanGcdClassBlockHit X q0 g0))

/-- Exact reduced-variable slice for a single gcd-class block count. -/
noncomputable def rawEvenRamanujanGcdClassReducedSlice
    (X q q' q0 g0 : ℕ) : Finset ℕ :=
  (Finset.Icc (X ⌈/⌉ g0)
      ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0)).filter
    (fun m =>
      X ≤ g0 * m
        ∧ g0 * m < X + centeredRamanujanPairBlockPeriod q q'
        ∧ Goldbach.Windows.IsEven (g0 * m)
        ∧ Nat.Coprime (q0 / g0) m)

theorem mem_rawEvenRamanujanGcdClassReducedQuotientSet_iff
    {X q q' q0 g0 m : ℕ} :
    m ∈ rawEvenRamanujanGcdClassReducedQuotientSet X q q' q0 g0
      ↔
    ∃ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      rawEvenRamanujanGcdClassBlockHit X q0 g0 k
        ∧ m = (X + k) / g0 := by
  unfold rawEvenRamanujanGcdClassReducedQuotientSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2, rfl⟩
  · rintro ⟨k, hkRange, hkHit, hm⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨hkRange, hkHit⟩, hm.symm⟩

theorem rawEvenRamanujanGcdClassReducedQuotient_injOn
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0) :
    Set.InjOn
      (fun k => (X + k) / g0)
      ↑(((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassBlockHit X q0 g0))) := by
  intro k1 hk1 k2 hk2 hq
  have hk1f :
      k1 ∈ ((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassBlockHit X q0 g0)) := by simpa using hk1
  have hk2f :
      k2 ∈ ((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassBlockHit X q0 g0)) := by simpa using hk2
  have hk1' : rawEvenRamanujanGcdClassBlockHit X q0 g0 k1 := (Finset.mem_filter.mp hk1f).2
  have hk2' : rawEvenRamanujanGcdClassBlockHit X q0 g0 k2 := (Finset.mem_filter.mp hk2f).2
  rcases hk1'.2.1 with ⟨m1, hm1⟩
  rcases hk2'.2.1 with ⟨m2, hm2⟩
  have hq1 : (X + k1) / g0 = m1 := by rw [hm1, Nat.mul_div_right _ hg0pos]
  have hq2 : (X + k2) / g0 = m2 := by rw [hm2, Nat.mul_div_right _ hg0pos]
  have hm : m1 = m2 := by simpa [hq1, hq2] using hq
  have hsum : X + k1 = X + k2 := by simpa [hm1, hm2, hm]
  exact Nat.add_left_cancel hsum

theorem mem_rawEvenRamanujanGcdClassReducedSlice_iff
    {X q q' q0 g0 m : ℕ} :
    m ∈ rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
      ↔
    X ⌈/⌉ g0 ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0
      ∧ X ≤ g0 * m
      ∧ g0 * m < X + centeredRamanujanPairBlockPeriod q q'
      ∧ Goldbach.Windows.IsEven (g0 * m)
      ∧ Nat.Coprime (q0 / g0) m := by
  unfold rawEvenRamanujanGcdClassReducedSlice
  simp [and_left_comm, and_assoc]

theorem mem_rawEvenRamanujanGcdClassReducedQuotientSet_iff_mem_slice
    {X q q' q0 g0 m : ℕ} (hg0pos : 0 < g0) :
    m ∈ rawEvenRamanujanGcdClassReducedQuotientSet X q q' q0 g0
      ↔
    m ∈ rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0 := by
  constructor
  · intro hm
    rcases (mem_rawEvenRamanujanGcdClassReducedQuotientSet_iff.mp hm) with
      ⟨k, hkRange, hkHit, rfl⟩
    rcases hkHit.2.1 with ⟨m, hmEq⟩
    have hquot : (X + k) / g0 = m := by rw [hmEq, Nat.mul_div_right _ hg0pos]
    have hXle : X ≤ g0 * m := by rw [← hmEq]; exact Nat.le_add_right X k
    have hlt : g0 * m < X + centeredRamanujanPairBlockPeriod q q' := by
      rw [← hmEq]
      exact Nat.add_lt_add_left (Finset.mem_range.mp hkRange) X
    rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff, hquot]
    refine ⟨(ceilDiv_le_iff_le_mul hg0pos).2 hXle, ?_, hXle, hlt, ?_, ?_⟩
    · have hmul : g0 * m ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 :=
        Nat.le_pred_of_lt hlt
      have hsum : X + k ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 := by
        simpa [hmEq] using hmul
      rw [← hquot]
      exact Nat.div_le_div_right hsum
    · simpa [hmEq] using hkHit.1
    · simpa [hquot] using hkHit.2.2
  · intro hm
    rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff] at hm
    rcases hm with ⟨_, hupper, hXle, hlt, hEven, hcop⟩
    let k := g0 * m - X
    have hkEq : X + k = g0 * m := by
      dsimp [k]
      exact Nat.add_sub_of_le hXle
    have hklt : k < centeredRamanujanPairBlockPeriod q q' := by
      omega
    have hkRange : k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q') := Finset.mem_range.mpr hklt
    have hkHit : rawEvenRamanujanGcdClassBlockHit X q0 g0 k := by
      refine ⟨?_, ?_⟩
      · simpa [hkEq] using hEven
      · refine ⟨?_, ?_⟩
        · exact ⟨m, hkEq⟩
        · simpa [hkEq, Nat.mul_div_right _ hg0pos] using hcop
    refine mem_rawEvenRamanujanGcdClassReducedQuotientSet_iff.mpr ?_
    refine ⟨k, hkRange, hkHit, ?_⟩
    dsimp [k]
    rw [hkEq, Nat.mul_div_right _ hg0pos]

theorem rawEvenRamanujanGcdClassReducedQuotientSet_eq_reducedSlice
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0) :
    rawEvenRamanujanGcdClassReducedQuotientSet X q q' q0 g0
      =
    rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0 := by
  ext m
  exact mem_rawEvenRamanujanGcdClassReducedQuotientSet_iff_mem_slice
    (X := X) (q := q) (q' := q') (q0 := q0) (g0 := g0) (m := m) hg0pos

theorem rawEvenRamanujanGcdClassBlockCount_eq_reducedSlice_card
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0) :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      =
    ((rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0).card : ℝ) := by
  calc
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
        = (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
              (rawEvenRamanujanGcdClassBlockHit X q0 g0)).card : ℝ) := by
            rw [rawEvenRamanujanGcdClassBlockCount_eq_card_filter]
    _ = ((rawEvenRamanujanGcdClassReducedQuotientSet X q q' q0 g0).card : ℝ) := by
          unfold rawEvenRamanujanGcdClassReducedQuotientSet
          rw [← Finset.card_image_of_injOn
            (H := rawEvenRamanujanGcdClassReducedQuotient_injOn X q q' q0 g0 hg0pos)]
    _ = ((rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0).card : ℝ) := by
          rw [rawEvenRamanujanGcdClassReducedQuotientSet_eq_reducedSlice X q q' q0 g0 hg0pos]

theorem mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_isEven_g
    {X q q' q0 g0 m : ℕ} (hgEven : Goldbach.Windows.IsEven g0) :
    m ∈ rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
      ↔
    X ⌈/⌉ g0 ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0
      ∧ X ≤ g0 * m
      ∧ g0 * m < X + centeredRamanujanPairBlockPeriod q q'
      ∧ Nat.Coprime (q0 / g0) m := by
  rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff]
  constructor
  · rintro ⟨h1,h2,h3,h4,_,h6⟩; exact ⟨h1,h2,h3,h4,h6⟩
  · rintro ⟨h1,h2,h3,h4,h5⟩
    exact ⟨h1,h2,h3,h4,isEven_mul_of_isEven_left hgEven,h5⟩

theorem mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_not_isEven_g
    {X q q' q0 g0 m : ℕ} (hgOdd : ¬ Goldbach.Windows.IsEven g0) :
    m ∈ rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
      ↔
    X ⌈/⌉ g0 ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0
      ∧ X ≤ g0 * m
      ∧ g0 * m < X + centeredRamanujanPairBlockPeriod q q'
      ∧ Goldbach.Windows.IsEven m
      ∧ Nat.Coprime (q0 / g0) m := by
  rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff, isEven_mul_iff_of_not_isEven_left hgOdd]

theorem mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_isEven_g_ceildiv
    {X q q' q0 g0 m : ℕ} (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgEven : Goldbach.Windows.IsEven g0) :
    m ∈ rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
      ↔
    X ⌈/⌉ g0 ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0
      ∧ Nat.Coprime (q0 / g0) m := by
  rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_isEven_g hgEven]
  constructor
  · rintro ⟨_, h2, h3, _, h5⟩
    exact ⟨(ceilDiv_le_iff_le_mul hg0pos).2 h3, h2, h5⟩
  · rintro ⟨h1, h2, h5⟩
    refine ⟨h1, h2, ?_, ?_, h5⟩
    · exact (ceilDiv_le_iff_le_mul hg0pos).1 h1
    · have hmul : g0 * m ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 := by
        have hmul' : m * g0 ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 :=
          Nat.mul_le_of_le_div _ _ _ h2
        simpa [Nat.mul_comm] using hmul'
      omega

theorem mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_not_isEven_g_ceildiv
    {X q q' q0 g0 m : ℕ} (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgOdd : ¬ Goldbach.Windows.IsEven g0) :
    m ∈ rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
      ↔
    X ⌈/⌉ g0 ≤ m
      ∧ m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0
      ∧ Goldbach.Windows.IsEven m
      ∧ Nat.Coprime (q0 / g0) m := by
  rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_not_isEven_g hgOdd]
  constructor
  · rintro ⟨_, h2, h3, _, h5, h6⟩
    exact ⟨(ceilDiv_le_iff_le_mul hg0pos).2 h3, h2, h5, h6⟩
  · rintro ⟨h1, h2, h5, h6⟩
    refine ⟨h1, h2, ?_, ?_, h5, h6⟩
    · exact (ceilDiv_le_iff_le_mul hg0pos).1 h1
    · have hmul : g0 * m ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 := by
        have hmul' : m * g0 ≤ X + centeredRamanujanPairBlockPeriod q q' - 1 :=
          Nat.mul_le_of_le_div _ _ _ h2
        simpa [Nat.mul_comm] using hmul'
      omega

private theorem card_filter_Icc_eq_card_filter_shiftedRange
    (A B : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (((Finset.Icc A B).filter p).card : ℕ)
      =
    (((Finset.range (B + 1 - A)).filter (fun t => p (A + t))).card : ℕ) := by
  let e : ℕ ↪ ℕ := ⟨fun t => A + t, by intro x y h; exact Nat.add_left_cancel h⟩
  have hmap :
      (((Finset.range (B + 1 - A)).filter (fun t => p (A + t))).map e)
        =
      ((Finset.Icc A B).filter p) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨t, ht, rfl⟩
      rcases Finset.mem_filter.mp ht with ⟨htRange, htP⟩
      refine Finset.mem_filter.mpr ⟨?_, htP⟩
      rw [Finset.mem_Icc]
      refine ⟨Nat.le_add_right A t, ?_⟩
      have ht' : t < B + 1 - A := Finset.mem_range.mp htRange
      have hAB : A ≤ B := by omega
      have hAt : A + t < A + (B + 1 - A) := Nat.add_lt_add_left ht' A
      have hR : A + (B + 1 - A) = B + 1 := by omega
      exact Nat.lt_succ_iff.mp (by simpa [hR] using hAt)
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxP⟩
      rcases Finset.mem_Icc.mp hxIcc with ⟨hAx, hxB⟩
      refine Finset.mem_map.mpr ⟨x - A, Finset.mem_filter.mpr ?_, Nat.add_sub_of_le hAx⟩
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · simpa [Nat.add_sub_of_le hAx] using hxP
  rw [← hmap, Finset.card_map]

theorem rawEvenRamanujanGcdClassBlockCount_eq_even_g_shiftedRange_card
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgEven : Goldbach.Windows.IsEven g0) :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      =
    ((((Finset.range
          (((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1)
            - (X ⌈/⌉ g0))).filter
        (fun t => Nat.Coprime (q0 / g0) (X ⌈/⌉ g0 + t))).card : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassBlockCount_eq_reducedSlice_card X q q' q0 g0 hg0pos]
  have hsliceeq :
      rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
        =
      ((Finset.Icc (X ⌈/⌉ g0)
          ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0)).filter
        (fun m => Nat.Coprime (q0 / g0) m)) := by
    ext m
    rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_isEven_g_ceildiv
      (X := X) (q := q) (q' := q') (q0 := q0) (g0 := g0) (m := m) hg0pos hPpos hgEven]
    simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  rw [hsliceeq]
  rw [card_filter_Icc_eq_card_filter_shiftedRange
    (A := X ⌈/⌉ g0)
    (B := (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0)
    (p := fun m => Nat.Coprime (q0 / g0) m)]

theorem rawEvenRamanujanGcdClassBlockCount_eq_odd_g_shiftedRange_card
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgOdd : ¬ Goldbach.Windows.IsEven g0) :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      =
    ((((Finset.range
          (((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1)
            - (X ⌈/⌉ g0))).filter
        (fun t =>
          Goldbach.Windows.IsEven (X ⌈/⌉ g0 + t)
            ∧ Nat.Coprime (q0 / g0) (X ⌈/⌉ g0 + t))).card : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassBlockCount_eq_reducedSlice_card X q q' q0 g0 hg0pos]
  have hsliceeq :
      rawEvenRamanujanGcdClassReducedSlice X q q' q0 g0
        =
      ((Finset.Icc (X ⌈/⌉ g0)
          ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0)).filter
        (fun m => Goldbach.Windows.IsEven m ∧ Nat.Coprime (q0 / g0) m)) := by
    ext m
    rw [mem_rawEvenRamanujanGcdClassReducedSlice_iff_of_not_isEven_g_ceildiv
      (X := X) (q := q) (q' := q') (q0 := q0) (g0 := g0) (m := m) hg0pos hPpos hgOdd]
    simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  rw [hsliceeq]
  rw [card_filter_Icc_eq_card_filter_shiftedRange
    (A := X ⌈/⌉ g0)
    (B := (X + centeredRamanujanPairBlockPeriod q q' - 1) / g0)
    (p := fun m => Goldbach.Windows.IsEven m ∧ Nat.Coprime (q0 / g0) m)]

theorem rawEvenRamanujanGcdClassBlockCount_eq_even_g_fullPeriods_add_remainder
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgEven : Goldbach.Windows.IsEven g0)
    (hMpos : 0 < q0 / g0) :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      =
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    ((((L / M) * (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card)) : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassBlockCount_eq_even_g_shiftedRange_card X q q' q0 g0 hg0pos hPpos hgEven]
  simpa using
    congrArg (fun n : ℕ => (n : ℝ))
      (coprime_shiftedRange_card_eq_fullPeriods_add_remainder
        (A := X ⌈/⌉ g0)
        (L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - (X ⌈/⌉ g0))
        (M := q0 / g0) hMpos)

theorem rawEvenRamanujanGcdClassBlockCount_eq_odd_g_fullPeriods_add_remainder
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgOdd : ¬ Goldbach.Windows.IsEven g0) :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      =
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    ((((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card)) : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassBlockCount_eq_odd_g_shiftedRange_card X q q' q0 g0 hg0pos hPpos hgOdd]
  simpa using
    congrArg (fun n : ℕ => (n : ℝ))
      (evenCoprime_shiftedRange_card_eq_fullPeriods_add_remainder
        (A := X ⌈/⌉ g0)
        (L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - (X ⌈/⌉ g0))
        (M := q0 / g0))

theorem mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff_mem_slice
    {X q q' g h m : ℕ} (hLpos : 0 < Nat.lcm g h) :
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h
      ↔
    m ∈ rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h := by
  constructor
  · intro hm
    rcases (mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff.mp hm) with
      ⟨k, hkRange, hkHit, rfl⟩
    have hklt : k < centeredRamanujanPairBlockPeriod q q' := Finset.mem_range.mp hkRange
    have hdiv : Nat.lcm g h ∣ X + k := hkHit.2.1
    rcases hdiv with ⟨m, hmEq⟩
    have hquot : (X + k) / Nat.lcm g h = m := by
      rw [hmEq, Nat.mul_div_right _ hLpos]
    have hXle : X ≤ Nat.lcm g h * m := by
      rw [← hmEq]
      exact Nat.le_add_right X k
    have hlt : Nat.lcm g h * m < X + centeredRamanujanPairBlockPeriod q q' := by
      rw [← hmEq]
      omega
    have hlower : X / Nat.lcm g h ≤ m := by
      rw [← hquot]
      exact mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_lower hm
    have hupper : m ≤ (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h := by
      rw [← hquot]
      exact mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_implies_le hm
    rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff]
    rw [hquot]
    refine ⟨hlower, hupper, hXle, hlt, ?_, ?_⟩
    · simpa [hmEq] using hkHit.1
    · simpa [hquot] using hkHit.2.2
  · intro hm
    rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff] at hm
    rcases hm with ⟨hmLower, hmUpper, hXle, hlt, hEven, hcop⟩
    let k := Nat.lcm g h * m - X
    have hkEq : X + k = Nat.lcm g h * m := by
      dsimp [k]
      exact Nat.add_sub_of_le hXle
    have hkltX : X + k < X + centeredRamanujanPairBlockPeriod q q' := by
      simpa [hkEq] using hlt
    have hklt : k < centeredRamanujanPairBlockPeriod q q' := by
      omega
    have hkRange : k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q') := by
      exact Finset.mem_range.mpr hklt
    have hkHit : rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h k := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [hkEq] using hEven
      · refine ⟨m, ?_⟩
        exact hkEq
      · simpa [hkEq, Nat.mul_div_right _ hLpos] using hcop
    refine mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff.mpr ?_
    refine ⟨k, hkRange, hkHit, ?_⟩
    dsimp [k]
    rw [hkEq, Nat.mul_div_right _ hLpos]

theorem rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_eq_reducedSlice
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h) :
    rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h
      =
    rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h := by
  ext m
  exact mem_rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_iff_mem_slice
    (X := X) (q := q) (q' := q') (g := g) (h := h) (m := m) hLpos

theorem rawEvenRamanujanGcdClassCompatibleReducedQuotient_injOn
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h) :
    Set.InjOn
      (fun k => (X + k) / Nat.lcm g h)
      ↑(((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h))) := by
  intro k1 hk1 k2 hk2 hq
  have hk1f :
      k1 ∈ ((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h)) := by
    simpa using hk1
  have hk2f :
      k2 ∈ ((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h)) := by
    simpa using hk2
  have hk1' : rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h k1 := by
    exact (Finset.mem_filter.mp hk1f).2
  have hk2' : rawEvenRamanujanGcdClassCompatibleReducedBlockHit X q q' g h k2 := by
    exact (Finset.mem_filter.mp hk2f).2
  have hdiv1 : Nat.lcm g h ∣ X + k1 := hk1'.2.1
  have hdiv2 : Nat.lcm g h ∣ X + k2 := hk2'.2.1
  have hEq1 : X + k1 = Nat.lcm g h * ((X + k1) / Nat.lcm g h) := by
    rcases hdiv1 with ⟨m1, hm1⟩
    have hquot1 : (X + k1) / Nat.lcm g h = m1 := by
      rw [hm1, Nat.mul_div_right _ hLpos]
    calc
      X + k1 = Nat.lcm g h * m1 := hm1
      _ = Nat.lcm g h * ((X + k1) / Nat.lcm g h) := by rw [hquot1]
  have hEq2 : X + k2 = Nat.lcm g h * ((X + k2) / Nat.lcm g h) := by
    rcases hdiv2 with ⟨m2, hm2⟩
    have hquot2 : (X + k2) / Nat.lcm g h = m2 := by
      rw [hm2, Nat.mul_div_right _ hLpos]
    calc
      X + k2 = Nat.lcm g h * m2 := hm2
      _ = Nat.lcm g h * ((X + k2) / Nat.lcm g h) := by rw [hquot2]
  have hsum : X + k1 = X + k2 := by
    rw [hEq1, hEq2]
    exact congrArg (fun t => Nat.lcm g h * t) hq
  exact Nat.add_left_cancel hsum

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_quotient_card
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    ((rawEvenRamanujanGcdClassCompatibleReducedQuotientSet X q q' g h).card : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_card_filter X q q' g h hLpos hcompat]
  unfold rawEvenRamanujanGcdClassCompatibleReducedQuotientSet
  rw [← Finset.card_image_of_injOn
    (H := rawEvenRamanujanGcdClassCompatibleReducedQuotient_injOn X q q' g h hLpos)]

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_slice_card
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    ((rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h).card : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_quotient_card X q q' g h hLpos hcompat,
    rawEvenRamanujanGcdClassCompatibleReducedQuotientSet_eq_reducedSlice X q q' g h hLpos]

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_shiftedRange_card
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h)) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    ((((Finset.range
          (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
            - (X ⌈/⌉ Nat.lcm g h))).filter
        (fun t =>
          Nat.Coprime (ramanujanGcdClassJointModulus q q' g h)
            (X ⌈/⌉ Nat.lcm g h + t))).card : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_slice_card X q q' g h hLpos hcompat]
  have hsliceeq :
      rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
        =
      ((Finset.Icc (X ⌈/⌉ Nat.lcm g h)
          ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h)).filter
        (fun m =>
          Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m)) := by
    ext m
    rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_isEven_lcm_ceildiv
      (X := X) (q := q) (q' := q') (g := g) (h := h) (m := m) hLpos hPpos hEvenL]
    simp [Finset.mem_filter, Finset.mem_Icc, and_left_comm, and_assoc]
  rw [hsliceeq]
  rw [card_filter_Icc_eq_card_filter_shiftedRange
    (A := X ⌈/⌉ Nat.lcm g h)
    (B := (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h)
    (p := fun m => Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m)]

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_odd_lcm_shiftedRange_card
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    ((((Finset.range
          (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
            - (X ⌈/⌉ Nat.lcm g h))).filter
        (fun t =>
          Goldbach.Windows.IsEven (X ⌈/⌉ Nat.lcm g h + t)
            ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h)
              (X ⌈/⌉ Nat.lcm g h + t))).card : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_compatible_slice_card X q q' g h hLpos hcompat]
  have hsliceeq :
      rawEvenRamanujanGcdClassCompatibleReducedSlice X q q' g h
        =
      ((Finset.Icc (X ⌈/⌉ Nat.lcm g h)
          ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h)).filter
        (fun m =>
          Goldbach.Windows.IsEven m
            ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m)) := by
    ext m
    rw [mem_rawEvenRamanujanGcdClassCompatibleReducedSlice_iff_of_not_isEven_lcm_ceildiv
      (X := X) (q := q) (q' := q') (g := g) (h := h) (m := m) hLpos hPpos hOddL]
    simp [Finset.mem_filter, Finset.mem_Icc, and_left_comm, and_assoc]
  rw [hsliceeq]
  rw [card_filter_Icc_eq_card_filter_shiftedRange
    (A := X ⌈/⌉ Nat.lcm g h)
    (B := (X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h)
    (p := fun m =>
      Goldbach.Windows.IsEven m
        ∧ Nat.Coprime (ramanujanGcdClassJointModulus q q' g h) m)]

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_fullPeriods_add_remainder
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h))
    (hMpos : 0 < ramanujanGcdClassJointModulus q q' g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    let A := X ⌈/⌉ Nat.lcm g h
    let L :=
      ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    ((((L / M) * (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card)) : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_shiftedRange_card
    X q q' g h hLpos hPpos hcompat hEvenL]
  simpa using
    congrArg (fun n : ℕ => (n : ℝ))
      (coprime_shiftedRange_card_eq_fullPeriods_add_remainder
        (A := X ⌈/⌉ Nat.lcm g h)
        (L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        (M := ramanujanGcdClassJointModulus q q' g h) hMpos)

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_odd_lcm_fullPeriods_add_remainder
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      =
    let A := X ⌈/⌉ Nat.lcm g h
    let L :=
      ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    ((((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card)) : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_odd_lcm_shiftedRange_card
    X q q' g h hLpos hPpos hcompat hOddL]
  simpa using
    congrArg (fun n : ℕ => (n : ℝ))
      (evenCoprime_shiftedRange_card_eq_fullPeriods_add_remainder
        (A := X ⌈/⌉ Nat.lcm g h)
        (L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        (M := ramanujanGcdClassJointModulus q q' g h))

private theorem divisor_pos_of_mem_divisors_of_pos
    {n d : ℕ} (hd : d ∈ n.divisors) (hn : 0 < n) : 0 < d := by
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdnz : d ≠ 0 := by
    intro hd0
    have : n = 0 := by simpa [hd0] using hdvd
    exact (Nat.ne_of_gt hn) this
  exact Nat.pos_of_ne_zero hdnz

private theorem not_isEven_of_not_isEven_lcm_left
    {g h : ℕ} (hLodd : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    ¬ Goldbach.Windows.IsEven g := by
  intro hgEven
  rcases Nat.dvd_lcm_left g h with ⟨m, hm⟩
  apply hLodd
  rw [hm]
  exact isEven_mul_of_isEven_left hgEven

private theorem not_isEven_of_not_isEven_lcm_right
    {g h : ℕ} (hLodd : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    ¬ Goldbach.Windows.IsEven h := by
  intro hhEven
  rcases Nat.dvd_lcm_right g h with ⟨m, hm⟩
  apply hLodd
  rw [hm]
  exact isEven_mul_of_isEven_left hhEven

private theorem isEven_lcm_of_isEven_left
    {g h : ℕ} (hgEven : Goldbach.Windows.IsEven g) :
    Goldbach.Windows.IsEven (Nat.lcm g h) := by
  rcases Nat.dvd_lcm_left g h with ⟨m, hm⟩
  rw [hm]
  exact isEven_mul_of_isEven_left hgEven

private theorem isEven_lcm_of_isEven_right
    {g h : ℕ} (hhEven : Goldbach.Windows.IsEven h) :
    Goldbach.Windows.IsEven (Nat.lcm g h) := by
  rcases Nat.dvd_lcm_right g h with ⟨m, hm⟩
  rw [hm]
  exact isEven_mul_of_isEven_left hhEven

private theorem quotient_pos_of_mem_divisors
    {q g : ℕ} (hq : 1 ≤ q) (hg : g ∈ q.divisors) : 0 < q / g := by
  rcases (Nat.mem_divisors.mp hg).1 with ⟨k, hk⟩
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hkpos : 0 < k := by
    have hknz : k ≠ 0 := by
      intro hk0
      have : q = 0 := by simpa [hk0] using hk
      exact (Nat.ne_of_gt hq) this
    exact Nat.pos_of_ne_zero hknz
  have hdiv : q / g = k := by
    rw [hk, Nat.mul_div_right _ hgpos]
  rw [hdiv]
  exact hkpos

private theorem divisor_dvd_pairBlockPeriod_left
    {q q' g : ℕ} (hg : g ∈ q.divisors) :
    g ∣ centeredRamanujanPairBlockPeriod q q' := by
  have hgdvd : g ∣ q := (Nat.mem_divisors.mp hg).1
  unfold centeredRamanujanPairBlockPeriod
  exact dvd_mul_of_dvd_right (hgdvd.trans (Nat.dvd_lcm_left q q')) 2

private theorem divisor_dvd_pairBlockPeriod_right
    {q q' h : ℕ} (hh : h ∈ q'.divisors) :
    h ∣ centeredRamanujanPairBlockPeriod q q' := by
  have hhdvd : h ∣ q' := (Nat.mem_divisors.mp hh).1
  unfold centeredRamanujanPairBlockPeriod
  exact dvd_mul_of_dvd_right (hhdvd.trans (Nat.dvd_lcm_right q q')) 2

private theorem lcm_divisors_dvd_pairBlockPeriod
    {q q' g h : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.lcm g h ∣ centeredRamanujanPairBlockPeriod q q' := by
  have hgl : g ∣ Nat.lcm q q' := (Nat.mem_divisors.mp hg).1.trans (Nat.dvd_lcm_left q q')
  have hhl : h ∣ Nat.lcm q q' := (Nat.mem_divisors.mp hh).1.trans (Nat.dvd_lcm_right q q')
  have hlcm : Nat.lcm g h ∣ Nat.lcm q q' := Nat.lcm_dvd hgl hhl
  unfold centeredRamanujanPairBlockPeriod
  exact dvd_mul_of_dvd_right hlcm 2

private theorem ceilDiv_eq_predDiv_add_one
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    n ⌈/⌉ d = (n - 1) / d + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hrew : n + d - 1 = (n - 1) + d := by omega
  rw [hrew]
  simpa using (Nat.add_mul_div_right (n - 1) 1 hd)

private theorem ceilDiv_add_mul_right
    {a d b : ℕ} (hd : 0 < d) :
    (a + b * d) ⌈/⌉ d = a ⌈/⌉ d + b := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  have hrew : a + b * d + d - 1 = (a + d - 1) + b * d := by omega
  rw [hrew]
  exact Nat.add_mul_div_right (a + d - 1) b hd

private theorem quotientLength_eq_periodQuotient
    {X P d : ℕ} (hd : 0 < d) (hP : 0 < P) (hdiv : d ∣ P) :
    ((X + P - 1) / d + 1) - (X ⌈/⌉ d) = P / d := by
  have h1 : ((X + P - 1) / d + 1) = (X + P) ⌈/⌉ d := by
    symm
    exact ceilDiv_eq_predDiv_add_one (n := X + P) (Nat.add_pos_right X hP) hd
  rcases hdiv with ⟨u, rfl⟩
  rw [h1]
  have h2 : (X + d * u) ⌈/⌉ d = X ⌈/⌉ d + u := by
    simpa [Nat.mul_comm] using ceilDiv_add_mul_right (a := X) (d := d) (b := u) hd
  rw [h2, Nat.mul_div_right u hd]
  omega

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_rawBlock_decomposition
    {X q q' g h : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    rawEvenRamanujanGcdClassPairBlockSum X q q' g h
      - ramanujanGcdClassWindowAverage X q' h * rawEvenRamanujanGcdClassBlockSum X q q' q g
      - ramanujanGcdClassWindowAverage X q g * rawEvenRamanujanGcdClassBlockSum X q q' q' h
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  unfold centeredRamanujanGcdClassPairFullEvenBlockSum centeredEvenRamanujanGcdClassPairOffset
    centeredRamanujanGcdClassPairKernel rawEvenRamanujanGcdClassPairBlockSum
    rawEvenRamanujanGcdClassBlockSum
  calc
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ite (Goldbach.Windows.IsEven (X + k))
        ((centeredRamanujanGcdClassObservable X q g (X + k))
          * (centeredRamanujanGcdClassObservable X q' h (X + k)))
        0
      =
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ite (Goldbach.Windows.IsEven (X + k))
        ((ramanujanGcdClassCoprimeIndicator q g (X + k) - ramanujanGcdClassWindowAverage X q g)
          * (ramanujanGcdClassCoprimeIndicator q' h (X + k) - ramanujanGcdClassWindowAverage X q' h))
        0 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          by_cases hEven : Goldbach.Windows.IsEven (X + k)
          · rw [if_pos hEven, if_pos hEven]
            rw [centeredRamanujanGcdClassObservable_eq_coprimeIndicator_sub_average_of_mem_divisors
                  (X := X) (q := q) (g := g) (N := X + k) hg]
            rw [centeredRamanujanGcdClassObservable_eq_coprimeIndicator_sub_average_of_mem_divisors
                  (X := X) (q := q') (g := h) (N := X + k) hh]
          · rw [if_neg hEven, if_neg hEven]
    _ =
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ((if Goldbach.Windows.IsEven (X + k) then
          ramanujanGcdClassCoprimeIndicator q g (X + k)
            * ramanujanGcdClassCoprimeIndicator q' h (X + k)
        else 0)
        -
        ramanujanGcdClassWindowAverage X q' h
          * (if Goldbach.Windows.IsEven (X + k) then
              ramanujanGcdClassCoprimeIndicator q g (X + k)
            else 0)
        -
        ramanujanGcdClassWindowAverage X q g
          * (if Goldbach.Windows.IsEven (X + k) then
              ramanujanGcdClassCoprimeIndicator q' h (X + k)
            else 0)
        +
        ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          by_cases hEven : Goldbach.Windows.IsEven (X + k)
          · rw [if_pos hEven, if_pos hEven, if_pos hEven, if_pos hEven, if_pos hEven]
            ring
          · rw [if_neg hEven, if_neg hEven, if_neg hEven, if_neg hEven, if_neg hEven]
            ring
    _ =
      (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        if Goldbach.Windows.IsEven (X + k) then
          ramanujanGcdClassCoprimeIndicator q g (X + k)
            * ramanujanGcdClassCoprimeIndicator q' h (X + k)
        else 0)
      -
      ramanujanGcdClassWindowAverage X q' h
        * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
            if Goldbach.Windows.IsEven (X + k) then
              ramanujanGcdClassCoprimeIndicator q g (X + k)
            else 0)
      -
      ramanujanGcdClassWindowAverage X q g
        * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
            if Goldbach.Windows.IsEven (X + k) then
              ramanujanGcdClassCoprimeIndicator q' h (X + k)
            else 0)
      +
      ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
        * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
            if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0) := by
          calc
            ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
              ((((if Goldbach.Windows.IsEven (X + k) then
                    ramanujanGcdClassCoprimeIndicator q g (X + k)
                      * ramanujanGcdClassCoprimeIndicator q' h (X + k)
                  else 0)
                -
                ramanujanGcdClassWindowAverage X q' h
                  * (if Goldbach.Windows.IsEven (X + k) then
                      ramanujanGcdClassCoprimeIndicator q g (X + k)
                    else 0))
                -
                ramanujanGcdClassWindowAverage X q g
                  * (if Goldbach.Windows.IsEven (X + k) then
                      ramanujanGcdClassCoprimeIndicator q' h (X + k)
                    else 0))
                +
                ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                  * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0))
              =
            (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
              (((if Goldbach.Windows.IsEven (X + k) then
                    ramanujanGcdClassCoprimeIndicator q g (X + k)
                      * ramanujanGcdClassCoprimeIndicator q' h (X + k)
                  else 0)
                -
                ramanujanGcdClassWindowAverage X q' h
                  * (if Goldbach.Windows.IsEven (X + k) then
                      ramanujanGcdClassCoprimeIndicator q g (X + k)
                    else 0))
                -
                ramanujanGcdClassWindowAverage X q g
                  * (if Goldbach.Windows.IsEven (X + k) then
                      ramanujanGcdClassCoprimeIndicator q' h (X + k)
                    else 0)))
              +
            ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
              ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0) := by
                  rw [Finset.sum_add_distrib]
            _ =
            (((∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                (if Goldbach.Windows.IsEven (X + k) then
                  ramanujanGcdClassCoprimeIndicator q g (X + k)
                    * ramanujanGcdClassCoprimeIndicator q' h (X + k)
                else 0))
              -
              ramanujanGcdClassWindowAverage X q' h
                * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                    (if Goldbach.Windows.IsEven (X + k) then
                      ramanujanGcdClassCoprimeIndicator q g (X + k)
                    else 0)))
              -
              ramanujanGcdClassWindowAverage X q g
                * (∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                    (if Goldbach.Windows.IsEven (X + k) then
                      ramanujanGcdClassCoprimeIndicator q' h (X + k)
                    else 0)))
              +
              ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                  * (if Goldbach.Windows.IsEven (X + k) then (1 : ℝ) else 0) := by
                    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
                    rw [Finset.mul_sum, Finset.mul_sum]
            _ = _ := by
                  rw [Finset.mul_sum]
                  have hconst_last :
                      (∑ x ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                          ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                            * (if Goldbach.Windows.IsEven (X + x) then (1 : ℝ) else 0))
                        =
                      ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                        * ∑ x ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
                            (if Goldbach.Windows.IsEven (X + x) then (1 : ℝ) else 0) := by
                              rw [← Finset.mul_sum]
                  rw [hconst_last]
    _ =
      rawEvenRamanujanGcdClassPairBlockSum X q q' g h
      - ramanujanGcdClassWindowAverage X q' h * rawEvenRamanujanGcdClassBlockSum X q q' q g
      - ramanujanGcdClassWindowAverage X q g * rawEvenRamanujanGcdClassBlockSum X q q' q' h
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
            simp [rawEvenRamanujanGcdClassPairBlockSum, rawEvenRamanujanGcdClassBlockSum,
              evenRamanujanBlockCount]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition
    {X q q' g h : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      - ramanujanGcdClassWindowAverage X q' h * rawEvenRamanujanGcdClassBlockCount X q q' q g
      - ramanujanGcdClassWindowAverage X q g * rawEvenRamanujanGcdClassBlockCount X q q' q' h
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_rawBlock_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockSum_eq_count hg hh]
  rw [rawEvenRamanujanGcdClassBlockSum_eq_count (q := q) (q' := q') (q0 := q) (g0 := g) hg]
  rw [rawEvenRamanujanGcdClassBlockSum_eq_count (q := q) (q' := q') (q0 := q') (g0 := h) hh]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_odd_lcm_periodic_comparison
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h)) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    let Pair := by
      let A := X ⌈/⌉ Nat.lcm g h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
      let M := ramanujanGcdClassJointModulus q q' g h
      exact (((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)
    let Left := by
      let A := X ⌈/⌉ g
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - A
      let M := q / g
      exact (((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)
    let Right := by
      let A := X ⌈/⌉ h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - A
      let M := q' / h
      exact (((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)
    Pair
      - ramanujanGcdClassWindowAverage X q' h * Left
      - ramanujanGcdClassWindowAverage X q g * Right
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  have hPairPos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    unfold ramanujanGcdClassJointModulus
    exact Nat.mul_pos (quotient_pos_of_mem_divisors hq hg) (quotient_pos_of_mem_divisors hq' hh)
  have hgOdd : ¬ Goldbach.Windows.IsEven g := not_isEven_of_not_isEven_lcm_left hOddL
  have hhOdd : ¬ Goldbach.Windows.IsEven h := not_isEven_of_not_isEven_lcm_right hOddL
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_odd_lcm_fullPeriods_add_remainder
    X q q' g h (Nat.lcm_pos hgpos hhpos) hPpos hcompat hOddL]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_odd_g_fullPeriods_add_remainder
    X q q' q g hgpos hPpos hgOdd]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_odd_g_fullPeriods_add_remainder
    X q q' q' h hhpos hPpos hhOdd]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_even_lcm_periodic_comparison_of_even_even
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hgEven : Goldbach.Windows.IsEven g) (hhEven : Goldbach.Windows.IsEven h) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    let Pair := by
      let A := X ⌈/⌉ Nat.lcm g h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
      let M := ramanujanGcdClassJointModulus q q' g h
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    let Left := by
      let A := X ⌈/⌉ g
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - A
      let M := q / g
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    let Right := by
      let A := X ⌈/⌉ h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - A
      let M := q' / h
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    Pair
      - ramanujanGcdClassWindowAverage X q' h * Left
      - ramanujanGcdClassWindowAverage X q g * Right
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  have hPairPos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    unfold ramanujanGcdClassJointModulus
    exact Nat.mul_pos (quotient_pos_of_mem_divisors hq hg) (quotient_pos_of_mem_divisors hq' hh)
  have hLeftPos : 0 < q / g := quotient_pos_of_mem_divisors hq hg
  have hRightPos : 0 < q' / h := quotient_pos_of_mem_divisors hq' hh
  have hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h) := isEven_lcm_of_isEven_left hgEven
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_fullPeriods_add_remainder
    X q q' g h (Nat.lcm_pos hgpos hhpos) hPpos hcompat hEvenL hPairPos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_even_g_fullPeriods_add_remainder
    X q q' q g hgpos hPpos hgEven hLeftPos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_even_g_fullPeriods_add_remainder
    X q q' q' h hhpos hPpos hhEven hRightPos]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_even_lcm_periodic_comparison_of_even_odd
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hgEven : Goldbach.Windows.IsEven g) (hhOdd : ¬ Goldbach.Windows.IsEven h) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    let Pair := by
      let A := X ⌈/⌉ Nat.lcm g h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
      let M := ramanujanGcdClassJointModulus q q' g h
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    let Left := by
      let A := X ⌈/⌉ g
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - A
      let M := q / g
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    let Right := by
      let A := X ⌈/⌉ h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - A
      let M := q' / h
      exact (((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)
    Pair
      - ramanujanGcdClassWindowAverage X q' h * Left
      - ramanujanGcdClassWindowAverage X q g * Right
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  have hPairPos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    unfold ramanujanGcdClassJointModulus
    exact Nat.mul_pos (quotient_pos_of_mem_divisors hq hg) (quotient_pos_of_mem_divisors hq' hh)
  have hLeftPos : 0 < q / g := quotient_pos_of_mem_divisors hq hg
  have hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h) := isEven_lcm_of_isEven_left hgEven
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_fullPeriods_add_remainder
    X q q' g h (Nat.lcm_pos hgpos hhpos) hPpos hcompat hEvenL hPairPos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_even_g_fullPeriods_add_remainder
    X q q' q g hgpos hPpos hgEven hLeftPos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_odd_g_fullPeriods_add_remainder
    X q q' q' h hhpos hPpos hhOdd]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_even_lcm_periodic_comparison_of_odd_even
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hgOdd : ¬ Goldbach.Windows.IsEven g) (hhEven : Goldbach.Windows.IsEven h) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    let Pair := by
      let A := X ⌈/⌉ Nat.lcm g h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
      let M := ramanujanGcdClassJointModulus q q' g h
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    let Left := by
      let A := X ⌈/⌉ g
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - A
      let M := q / g
      exact (((L / (2 * M)) * (((Finset.range (2 * M)).filter
          (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)
    let Right := by
      let A := X ⌈/⌉ h
      let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - A
      let M := q' / h
      exact (((L / M) * (((Finset.range M).filter
          (fun t => Nat.Coprime M (A + t))).card)
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
    Pair
      - ramanujanGcdClassWindowAverage X q' h * Left
      - ramanujanGcdClassWindowAverage X q g * Right
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  have hPairPos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    unfold ramanujanGcdClassJointModulus
    exact Nat.mul_pos (quotient_pos_of_mem_divisors hq hg) (quotient_pos_of_mem_divisors hq' hh)
  have hRightPos : 0 < q' / h := quotient_pos_of_mem_divisors hq' hh
  have hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h) := isEven_lcm_of_isEven_right hhEven
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_fullPeriods_add_remainder
    X q q' g h (Nat.lcm_pos hgpos hhpos) hPpos hcompat hEvenL hPairPos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_odd_g_fullPeriods_add_remainder
    X q q' q g hgpos hPpos hgOdd]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_even_g_fullPeriods_add_remainder
    X q q' q' h hhpos hPpos hhEven hRightPos]

noncomputable def rawEvenRamanujanGcdClassBlockPeriodicCount
    (X q q' q0 g0 : ℕ) : ℝ :=
  if Goldbach.Windows.IsEven g0 then
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    (((L / M) * (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card)
      + (((Finset.range (L % M)).filter
          (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
  else
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    (((L / (2 * M)) * (((Finset.range (2 * M)).filter
        (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
      + (((Finset.range (L % (2 * M))).filter
          (fun t =>
            Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
              ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)

noncomputable def rawEvenRamanujanGcdClassPairBlockPeriodicCount
    (X q q' g h : ℕ) : ℝ :=
  if Goldbach.Windows.IsEven (Nat.lcm g h) then
    let A := X ⌈/⌉ Nat.lcm g h
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    (((L / M) * (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card)
      + (((Finset.range (L % M)).filter
          (fun t => Nat.Coprime M (A + (L / M) * M + t))).card) : ℕ) : ℝ)
  else
    let A := X ⌈/⌉ Nat.lcm g h
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    (((L / (2 * M)) * (((Finset.range (2 * M)).filter
        (fun t => Goldbach.Windows.IsEven (A + t) ∧ Nat.Coprime M (A + t))).card)
      + (((Finset.range (L % (2 * M))).filter
          (fun t =>
            Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
              ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card) : ℕ) : ℝ)

noncomputable def rawEvenRamanujanGcdClassPeriodicProductDefect
    (X q q' g h : ℕ) : ℝ :=
  rawEvenRamanujanGcdClassPairBlockPeriodicCount X q q' g h
    - (rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
        * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h)
        / evenRamanujanBlockCount X q q'

theorem rawEvenRamanujanGcdClassBlockPeriodicCount_eq_even_totient_main_add_remainder
    (X q q' q0 g0 : ℕ) (hgEven : Goldbach.Windows.IsEven g0)
    (hMpos : 0 < q0 / g0) :
    rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q0 g0
      =
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    ((((L / M) * Nat.totient M
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card)) : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount, if_pos hgEven]
  dsimp
  rw [card_filter_range_coprime_shift_eq_totient (A := X ⌈/⌉ g0) (M := q0 / g0) hMpos]

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_even_lcm_totient_main_add_remainder
    (X q q' g h : ℕ) (hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h))
    (hMpos : 0 < ramanujanGcdClassJointModulus q q' g h) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCount X q q' g h
      =
    let A := X ⌈/⌉ Nat.lcm g h
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    ((((L / M) * Nat.totient M
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card)) : ℕ) : ℝ) := by
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount, if_pos hEvenL]
  dsimp
  rw [card_filter_range_coprime_shift_eq_totient
    (A := X ⌈/⌉ Nat.lcm g h) (M := ramanujanGcdClassJointModulus q q' g h) hMpos]

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_product_normalized_add_defect
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCount X q q' g h
      =
    (rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
        * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h)
        / evenRamanujanBlockCount X q q'
      + rawEvenRamanujanGcdClassPeriodicProductDefect X q q' g h := by
  unfold rawEvenRamanujanGcdClassPeriodicProductDefect
  ring

theorem totient_product_eq_overlap_factor
    {A B : ℕ} (hA : 0 < A) (_hB : 0 < B) :
    (Nat.totient (A * B) : ℝ)
      =
    (Nat.totient A : ℝ) * (Nat.totient B : ℝ)
      * (Nat.gcd A B : ℝ) / (Nat.totient (Nat.gcd A B) : ℝ) := by
  have hgpos : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left B hA
  have hφg_ne : (Nat.totient (Nat.gcd A B) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hgpos).ne'
  have hnat := Nat.totient_gcd_mul_totient_mul A B
  have hreal' :
      (Nat.totient (Nat.gcd A B) : ℝ) * (Nat.totient (A * B) : ℝ)
        =
      (Nat.totient A : ℝ) * (Nat.totient B : ℝ) * (Nat.gcd A B : ℝ) := by
    exact_mod_cast hnat
  field_simp [hφg_ne]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hreal'

noncomputable def rawEvenRamanujanGcdClassPeriodicTotientComparison
    (X q q' g h : ℕ) : ℝ :=
  let A := q / g
  let B := q' / h
  let PairStart := X ⌈/⌉ Nat.lcm g h
  let PairLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - PairStart
  let PairRem := (((Finset.range (PairLen % (A * B))).filter
      (fun t => Nat.Coprime (A * B) (PairStart + (PairLen / (A * B)) * (A * B) + t))).card : ℕ)
  let LeftStart := X ⌈/⌉ g
  let LeftLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - LeftStart
  let LeftRem := (((Finset.range (LeftLen % A)).filter
      (fun t => Nat.Coprime A (LeftStart + (LeftLen / A) * A + t))).card : ℕ)
  let RightStart := X ⌈/⌉ h
  let RightLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - RightStart
  let RightRem := (((Finset.range (RightLen % B)).filter
      (fun t => Nat.Coprime B (RightStart + (RightLen / B) * B + t))).card : ℕ)
  ((((PairLen / (A * B)) * Nat.totient (A * B) + PairRem : ℕ) : ℝ)
    - ((((((LeftLen / A) * Nat.totient A + LeftRem : ℕ) : ℝ)
          * ((((RightLen / B) * Nat.totient B + RightRem : ℕ) : ℝ)))
        / evenRamanujanBlockCount X q q')))

noncomputable def rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm
    (X q q' g h : ℕ) : ℝ :=
  let A := q / g
  let B := q' / h
  let PairLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
    - (X ⌈/⌉ Nat.lcm g h)
  let LeftLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g)
  let RightLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h)
  ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
    * ((((PairLen / (A * B) : ℕ) : ℝ))
        - ((((LeftLen / A : ℕ) : ℝ) * (((RightLen / B : ℕ) : ℝ)))
            / evenRamanujanBlockCount X q q'))

noncomputable def rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm
    (X q q' g h : ℕ) : ℝ :=
  let A := q / g
  let B := q' / h
  let PairLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
    - (X ⌈/⌉ Nat.lcm g h)
  ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
    * ((((PairLen / (A * B) : ℕ) : ℝ))
        * (((Nat.gcd A B : ℝ) / (Nat.totient (Nat.gcd A B) : ℝ)) - 1))

noncomputable def rawEvenRamanujanGcdClassPeriodicRemainderTerm
    (X q q' g h : ℕ) : ℝ :=
  rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
    - rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
    - rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h

theorem rawEvenRamanujanGcdClassPeriodicProductDefect_eq_even_even_totientComparison
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hgEven : Goldbach.Windows.IsEven g) (hhEven : Goldbach.Windows.IsEven h) :
    rawEvenRamanujanGcdClassPeriodicProductDefect X q q' g h
      = rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h := by
  have hApos : 0 < q / g := quotient_pos_of_mem_divisors hq hg
  have hBpos : 0 < q' / h := quotient_pos_of_mem_divisors hq' hh
  have hPairPos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    unfold ramanujanGcdClassJointModulus
    exact Nat.mul_pos hApos hBpos
  have hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h) := isEven_lcm_of_isEven_left hgEven
  unfold rawEvenRamanujanGcdClassPeriodicProductDefect
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_even_lcm_totient_main_add_remainder
    X q q' g h hEvenL hPairPos]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_even_totient_main_add_remainder
    X q q' q g hgEven hApos]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_even_totient_main_add_remainder
    X q q' q' h hhEven hBpos]
  rfl

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_overlap_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      + rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  unfold rawEvenRamanujanGcdClassPeriodicRemainderTerm
  ring

theorem rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_coprime
    {X q q' g h : ℕ} (hcop : Nat.Coprime (q / g) (q' / h)) :
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h = 0 := by
  rw [rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm]
  have hgcd1 : Nat.gcd (q / g) (q' / h) = 1 := Nat.Coprime.gcd_eq_one hcop
  simp [hgcd1]

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_coprime_coefficientMismatch_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcop : Nat.Coprime (q / g) (q' / h)) :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_overlap_add_remainder hq hq' hg hh,
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_coprime hcop]
  ring

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_explicit_blockDensity
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    let PairLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
      - (X ⌈/⌉ Nat.lcm g h)
    let LeftLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g)
    let RightLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h)
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((((PairLen / (A * B) : ℕ) : ℝ))
          - ((((LeftLen / A : ℕ) : ℝ) * (((RightLen / B : ℕ) : ℝ)))
              / (Nat.lcm q q' : ℝ))) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm, evenRamanujanBlockCount_eq_lcm]

theorem rawEvenRamanujanGcdClassPeriodicLeftLen_eq_blockPeriod_div
    {X q q' g : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hg : g ∈ q.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g))
      =
    centeredRamanujanPairBlockPeriod q q' / g := by
  apply quotientLength_eq_periodQuotient
  · exact divisor_pos_of_mem_divisors_of_pos hg hq
  · dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  · exact divisor_dvd_pairBlockPeriod_left hg

theorem rawEvenRamanujanGcdClassPeriodicRightLen_eq_blockPeriod_div
    {X q q' h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hh : h ∈ q'.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h))
      =
    centeredRamanujanPairBlockPeriod q q' / h := by
  apply quotientLength_eq_periodQuotient
  · exact divisor_pos_of_mem_divisors_of_pos hh hq'
  · dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  · exact divisor_dvd_pairBlockPeriod_right hh

theorem rawEvenRamanujanGcdClassPeriodicPairLen_eq_blockPeriod_div
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
        - (X ⌈/⌉ Nat.lcm g h))
      =
    centeredRamanujanPairBlockPeriod q q' / Nat.lcm g h := by
  apply quotientLength_eq_periodQuotient
  · exact Nat.lcm_pos (divisor_pos_of_mem_divisors_of_pos hg hq)
      (divisor_pos_of_mem_divisors_of_pos hh hq')
  · dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  · exact lcm_divisors_dvd_pairBlockPeriod hg hh

private theorem lcm_div_left_eq_right_div_gcd
    {q q' : ℕ} (hq : 0 < q) :
    Nat.lcm q q' / q = q' / Nat.gcd q q' := by
  let d := Nat.gcd q q'
  rcases Nat.gcd_dvd_left q q' with ⟨a, ha0⟩
  rcases Nat.gcd_dvd_right q q' with ⟨b, hb0⟩
  have ha : q = d * a := by
    simpa [d] using ha0
  have hb : q' = d * b := by
    simpa [d] using hb0
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left q' hq
  have hapos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro haZ
    have : q = 0 := by
      simpa [haZ] using ha
    exact hq.ne' this
  have hcop0 : Nat.Coprime (q / d) (q' / d) := by
    dsimp [d]
    simpa using (Nat.coprime_div_gcd_div_gcd (H := hdpos))
  have hqd : q / d = a := by
    rw [ha]
    simpa [Nat.mul_comm] using (Nat.mul_div_left a hdpos)
  have hq'd : q' / d = b := by
    rw [hb]
    simpa [Nat.mul_comm] using (Nat.mul_div_left b hdpos)
  have hcop : Nat.Coprime a b := by
    simpa [hqd, hq'd] using hcop0
  rw [ha, hb, Nat.lcm_mul_left d a b, hcop.lcm_eq_mul]
  rw [Nat.mul_div_mul_left _ _ hdpos]
  rw [Nat.mul_div_right _ hapos]
  rw [Nat.gcd_mul_left d a b, Nat.Coprime.gcd_eq_one hcop]
  simpa [Nat.mul_comm] using (Nat.mul_div_left b hdpos).symm

private theorem lcm_div_right_eq_left_div_gcd
    {q q' : ℕ} (hq' : 0 < q') :
    Nat.lcm q q' / q' = q / Nat.gcd q q' := by
  simpa [Nat.lcm_comm, Nat.gcd_comm] using
    (lcm_div_left_eq_right_div_gcd (q := q') (q' := q) hq')

private theorem div_gcd_mul_right_eq_lcm
    {q q' : ℕ} (hq : 0 < q) :
    (q / Nat.gcd q q') * q' = Nat.lcm q q' := by
  let d := Nat.gcd q q'
  rcases Nat.gcd_dvd_left q q' with ⟨a, ha0⟩
  rcases Nat.gcd_dvd_right q q' with ⟨b, hb0⟩
  have ha : q = d * a := by
    simpa [d] using ha0
  have hb : q' = d * b := by
    simpa [d] using hb0
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left q' hq
  have hcop0 : Nat.Coprime (q / d) (q' / d) := by
    dsimp [d]
    simpa using (Nat.coprime_div_gcd_div_gcd (H := hdpos))
  have hqd : q / d = a := by
    rw [ha]
    simpa [Nat.mul_comm] using (Nat.mul_div_left a hdpos)
  have hq'd : q' / d = b := by
    rw [hb]
    simpa [Nat.mul_comm] using (Nat.mul_div_left b hdpos)
  have hcop : Nat.Coprime a b := by
    simpa [hqd, hq'd] using hcop0
  rw [ha, hb, Nat.gcd_mul_left d a b, Nat.Coprime.gcd_eq_one hcop,
    Nat.lcm_mul_left d a b, hcop.lcm_eq_mul]
  rw [Nat.mul_div_mul_left a 1 hdpos]
  simp [Nat.mul_assoc, Nat.mul_comm]

private theorem lcm_eq_mul_div_gcd
    {m n : ℕ} (hm : 0 < m) :
    Nat.lcm m n = m * n / Nat.gcd m n := by
  refine (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left n hm) ?_).symm
  rw [Nat.lcm_mul_gcd]

private theorem left_den_eq_qq_div_gcd
    {q q' g h : ℕ}
    (hgdvd : g ∣ q) (hhdvd : h ∣ q')
    (hq : 0 < q) (hq' : 0 < q') :
    (q / g) * (q' / h) * Nat.lcm g h = q * q' / Nat.gcd g h := by
  rcases hgdvd with ⟨a, rfl⟩
  rcases hhdvd with ⟨b, rfl⟩
  have hgpos : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro hg0
    simp [hg0] at hq
  have hhpos : 0 < h := by
    apply Nat.pos_of_ne_zero
    intro hh0
    simp [hh0] at hq'
  rw [lcm_eq_mul_div_gcd hgpos]
  rw [show g * a / g = a by
    simpa [Nat.mul_comm] using (Nat.mul_div_left a hgpos)]
  rw [show h * b / h = b by
    simpa [Nat.mul_comm] using (Nat.mul_div_left b hhpos)]
  have hcdvd : Nat.gcd g h ∣ g * h := dvd_mul_of_dvd_left (Nat.gcd_dvd_left g h) h
  calc
    a * b * (g * h / Nat.gcd g h)
      = (a * b) * (g * h / Nat.gcd g h) := by ring_nf
    _ = ((a * b) * (g * h)) / Nat.gcd g h := by
      symm
      exact Nat.mul_div_assoc (a * b) hcdvd
    _ = g * a * (h * b) / Nat.gcd g h := by ring_nf

private theorem rawEvenRamanujanPairPeriodicFloor_eq_two_mul_gcd_div_gcd
    {q q' g h : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanPairBlockPeriod q q' / Nat.lcm g h / ((q / g) * (q' / h))
      = (2 * Nat.gcd g h) / Nat.gcd q q' := by
  have hgdvd : g ∣ q := (Nat.mem_divisors.mp hg).1
  have hhdvd : h ∣ q' := (Nat.mem_divisors.mp hh).1
  have hqpos : 0 < q := hq
  have hq'pos : 0 < q' := hq'
  have hden1 := left_den_eq_qq_div_gcd hgdvd hhdvd hqpos hq'pos
  have hqq : q * q' = Nat.gcd q q' * Nat.lcm q q' := by
    simpa using (Nat.gcd_mul_lcm q q').symm
  have hcdivd : Nat.gcd g h ∣ Nat.gcd q q' := by
    apply Nat.dvd_gcd
    · exact dvd_trans (Nat.gcd_dvd_left g h) hgdvd
    · exact dvd_trans (Nat.gcd_dvd_right g h) hhdvd
  rcases hcdivd with ⟨k, hk⟩
  have hcpos : 0 < Nat.gcd g h := by
    exact Nat.gcd_pos_of_pos_right g (Nat.pos_of_dvd_of_pos hhdvd hq'pos)
  have hlpos : 0 < Nat.lcm q q' := Nat.lcm_pos hq hq'
  have hcancel : (Nat.gcd g h * Nat.lcm q q') / Nat.gcd g h = Nat.lcm q q' := by
    simpa [Nat.mul_comm] using (Nat.mul_div_left (Nat.lcm q q') hcpos)
  have hden : (q / g) * (q' / h) * Nat.lcm g h = k * Nat.lcm q q' := by
    calc
      (q / g) * (q' / h) * Nat.lcm g h = q * q' / Nat.gcd g h := hden1
      _ = ((Nat.gcd g h) * k * Nat.lcm q q') / Nat.gcd g h := by rw [hqq, hk]
      _ = k * ((Nat.gcd g h * Nat.lcm q q') / Nat.gcd g h) := by
        simpa [Nat.mul_assoc, Nat.mul_comm] using
          (Nat.mul_div_assoc k (dvd_mul_of_dvd_left (dvd_refl (Nat.gcd g h)) (Nat.lcm q q')))
      _ = k * Nat.lcm q q' := by rw [hcancel]
  rw [centeredRamanujanPairBlockPeriod, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm ((q / g) * (q' / h)) (Nat.lcm g h)] at hden
  rw [hden, Nat.mul_comm k (Nat.lcm q q')]
  calc
    2 * Nat.lcm q q' / (Nat.lcm q q' * k) = 2 / k := by
      simpa [Nat.mul_comm] using (Nat.mul_div_mul_right 2 k hlpos)
    _ = (2 * Nat.gcd g h) / Nat.gcd q q' := by
      rw [hk]
      have hrhs : (2 * Nat.gcd g h) / (Nat.gcd g h * k) = 2 / k := by
        simpa [Nat.mul_comm] using (Nat.mul_div_mul_left 2 k hcpos)
      exact hrhs.symm

private theorem div_gcd_mul_left_eq_lcm
    {q q' : ℕ} (hq' : 0 < q') :
    (q' / Nat.gcd q q') * q = Nat.lcm q q' := by
  simpa [Nat.mul_comm, Nat.gcd_comm, Nat.lcm_comm] using
    (div_gcd_mul_right_eq_lcm (q := q') (q' := q) hq')

private theorem rawEvenRamanujanSinglePeriodicDensity_eq_four_div_gcd
    {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    ((((centeredRamanujanPairBlockPeriod q q' / q : ℕ) : ℝ)
        * (((centeredRamanujanPairBlockPeriod q q' / q' : ℕ) : ℝ)))
        / (Nat.lcm q q' : ℝ))
      =
    (4 : ℝ) / (Nat.gcd q q' : ℝ) := by
  have hqpos : 0 < q := hq
  have hq'pos : 0 < q' := hq'
  have hqdvd : q ∣ Nat.lcm q q' := Nat.dvd_lcm_left q q'
  have hq'dvd : q' ∣ Nat.lcm q q' := Nat.dvd_lcm_right q q'
  rw [show centeredRamanujanPairBlockPeriod q q' / q = 2 * (Nat.lcm q q' / q) by
    unfold centeredRamanujanPairBlockPeriod
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (Nat.mul_div_assoc 2 hqdvd)]
  rw [show centeredRamanujanPairBlockPeriod q q' / q' = 2 * (Nat.lcm q q' / q') by
    unfold centeredRamanujanPairBlockPeriod
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (Nat.mul_div_assoc 2 hq'dvd)]
  rw [lcm_div_left_eq_right_div_gcd hqpos, lcm_div_right_eq_left_div_gcd hq'pos]
  have hlcmpos : (Nat.lcm q q' : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos hq hq').ne'
  have hgcdpos : (Nat.gcd q q' : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left q' hqpos).ne'
  have hqdecomp : ((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ) = q := by
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left q q'))
  have hmain : (((q' / Nat.gcd q q' : ℕ) : ℝ)
      * (((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ)))
      = Nat.lcm q q' := by
    rw [hqdecomp]
    exact_mod_cast (div_gcd_mul_left_eq_lcm (q := q) (q' := q') hq'pos)
  have hmain' :
      (((q' / Nat.gcd q q' : ℕ) : ℝ)
          * ((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ))
        = Nat.lcm q q' := by
    calc
      (((q' / Nat.gcd q q' : ℕ) : ℝ)
          * ((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ))
        = (((q' / Nat.gcd q q' : ℕ) : ℝ)
            * (((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ))) := by ring
      _ = Nat.lcm q q' := by rw [hmain]
  field_simp [hlcmpos, hgcdpos]
  calc
    (↑(2 * (q' / Nat.gcd q q')) : ℝ) * ↑(2 * (q / Nat.gcd q q')) * ↑(Nat.gcd q q')
      = (4 : ℝ)
          * ((((q' / Nat.gcd q q' : ℕ) : ℝ)
              * ((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ))) := by
          simp [Nat.cast_mul]
          ring
    _ = (4 : ℝ) * (Nat.lcm q q' : ℝ) := by rw [hmain']
    _ = (Nat.lcm q q' : ℝ) * (4 : ℝ) := by ring

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_blockPeriodSubstituted
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    let P := centeredRamanujanPairBlockPeriod q q'
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((((P / Nat.lcm g h / (A * B) : ℕ) : ℝ))
          - ((((P / q : ℕ) : ℝ) * (((P / q' : ℕ) : ℝ)))
              / (Nat.lcm q q' : ℝ))) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_explicit_blockDensity]
  have hLeft :
      (((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g))
        =
      centeredRamanujanPairBlockPeriod q q' / g := by
    exact rawEvenRamanujanGcdClassPeriodicLeftLen_eq_blockPeriod_div hq hq' hg
  have hRight :
      (((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h))
        =
      centeredRamanujanPairBlockPeriod q q' / h := by
    exact rawEvenRamanujanGcdClassPeriodicRightLen_eq_blockPeriod_div hq hq' hh
  have hPair :
      (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        =
      centeredRamanujanPairBlockPeriod q q' / Nat.lcm g h := by
    exact rawEvenRamanujanGcdClassPeriodicPairLen_eq_blockPeriod_div hq hq' hg hh
  simp_rw [hLeft, hRight, hPair]
  congr 1
  dsimp
  have hgdvd : g ∣ q := (Nat.mem_divisors.mp hg).1
  have hhdvd : h ∣ q' := (Nat.mem_divisors.mp hh).1
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rcases hgdvd with ⟨a, ha⟩
  rcases hhdvd with ⟨b, hb⟩
  rw [ha, hb]
  rw [Nat.div_div_eq_div_mul]
  simp [hgpos, hhpos, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_pairFloor_minus_four_div_gcd
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    let P := centeredRamanujanPairBlockPeriod q q'
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((((P / Nat.lcm g h / (A * B) : ℕ) : ℝ))
          - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_blockPeriodSubstituted
    hq hq' hg hh]
  congr 1
  dsimp
  have hDensity :
      ((((2 * Nat.lcm q q' / q : ℕ) : ℝ) * (((2 * Nat.lcm q q' / q' : ℕ) : ℝ)))
          / (Nat.lcm q q' : ℝ))
        =
      (4 : ℝ) / (Nat.gcd q q' : ℝ) := by
    simpa [centeredRamanujanPairBlockPeriod] using
      (rawEvenRamanujanSinglePeriodicDensity_eq_four_div_gcd (q := q) (q' := q') hq hq')
  rw [hDensity]

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_exact_gcd_floor_overlap
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((((2 * Nat.gcd g h / Nat.gcd q q' : ℕ) : ℝ))
          - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_pairFloor_minus_four_div_gcd
    hq hq' hg hh]
  dsimp
  have hfloor :
      2 * Nat.lcm q q' / Nat.lcm g h / (q / g * (q' / h))
        =
      (2 * Nat.gcd g h) / Nat.gcd q q' := by
    simpa [centeredRamanujanPairBlockPeriod] using
      (rawEvenRamanujanPairPeriodicFloor_eq_two_mul_gcd_div_gcd
        (q := q) (q' := q') (g := g) (h := h) hq hq' hg hh)
  have hcast :
      (((2 * Nat.lcm q q' / Nat.lcm g h / (q / g * (q' / h)) : ℕ) : ℝ)
          - (4 : ℝ) / (Nat.gcd q q' : ℝ))
        =
      ((((2 * Nat.gcd g h / Nat.gcd q q' : ℕ) : ℝ))
          - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
    simpa using
      (congrArg
        (fun n : ℕ => ((n : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
        hfloor)
  rw [hcast]

private theorem gcd_g_h_dvd_gcd_q_q'
    {q q' g h : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.gcd g h ∣ Nat.gcd q q' := by
  have hgdvd : g ∣ q := (Nat.mem_divisors.mp hg).1
  have hhdvd : h ∣ q' := (Nat.mem_divisors.mp hh).1
  apply Nat.dvd_gcd
  · exact dvd_trans (Nat.gcd_dvd_left g h) hgdvd
  · exact dvd_trans (Nat.gcd_dvd_right g h) hhdvd

private theorem rawEvenRamanujanPairPeriodicFloor_eq_zero_of_two_mul_gcd_lt
    {q q' g h : ℕ}
    (hlt : 2 * Nat.gcd g h < Nat.gcd q q') :
    (2 * Nat.gcd g h) / Nat.gcd q q' = 0 := by
  exact Nat.div_eq_of_lt hlt

private theorem rawEvenRamanujanPairPeriodicFloor_eq_one_of_gcd_lt_and_le_two_mul
    {q q' g h : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hle : Nat.gcd q q' ≤ 2 * Nat.gcd g h)
    (hlt : Nat.gcd g h < Nat.gcd q q') :
    (2 * Nat.gcd g h) / Nat.gcd q q' = 1 := by
  let d := Nat.gcd q q'
  let e := Nat.gcd g h
  have hdiv : e ∣ d := gcd_g_h_dvd_gcd_q_q' hg hh
  rcases hdiv with ⟨k, hk⟩
  have hepos : 0 < e := by
    have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
    dsimp [e]
    exact Nat.gcd_pos_of_pos_right g hhpos
  have hk2 : k = 2 := by
    dsimp [d, e] at hk hle hlt
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk0
      simp [hk0] at hk
      omega
    have hk_le_two : k ≤ 2 := by
      have hmul : e * k ≤ e * 2 := by
        simpa [hk, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle
      exact Nat.le_of_mul_le_mul_left hmul hepos
    interval_cases k <;> omega
  have h2epos : 0 < 2 * e := by omega
  dsimp [d, e] at hk ⊢
  rw [hk, hk2, Nat.mul_comm e 2]
  exact Nat.div_self h2epos

private theorem rawEvenRamanujanPairPeriodicFloor_eq_two_of_gcd_eq
    {q q' g h : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (heq : Nat.gcd g h = Nat.gcd q q') :
    (2 * Nat.gcd g h) / Nat.gcd q q' = 2 := by
  have hdpos : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left q' hq
  rw [heq]
  simpa [Nat.mul_comm] using (Nat.mul_div_left 2 hdpos)

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_zero
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hlt : 2 * Nat.gcd g h < Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_exact_gcd_floor_overlap
    hq hq' hg hh]
  dsimp
  have hinner :
      ((((2 * Nat.gcd g h / Nat.gcd q q' : ℕ) : ℝ))
          - (4 : ℝ) / (Nat.gcd q q' : ℝ))
        =
      ((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
    rw [rawEvenRamanujanPairPeriodicFloor_eq_zero_of_two_mul_gcd_lt hlt]
    norm_num
  rw [hinner]

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_one
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hle : Nat.gcd q q' ≤ 2 * Nat.gcd g h)
    (hlt : Nat.gcd g h < Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_exact_gcd_floor_overlap
    hq hq' hg hh]
  dsimp
  have hinner :
      ((((2 * Nat.gcd g h / Nat.gcd q q' : ℕ) : ℝ))
          - (4 : ℝ) / (Nat.gcd q q' : ℝ))
        =
      ((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
    rw [rawEvenRamanujanPairPeriodicFloor_eq_one_of_gcd_lt_and_le_two_mul
      hq hq' hg hh hle hlt]
    norm_num
  rw [hinner]

theorem rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_two
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (heq : Nat.gcd g h = Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h
      =
    let A := q / g
    let B := q' / h
    ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
      * ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_exact_gcd_floor_overlap
    hq hq' hg hh]
  dsimp
  have hinner :
      ((((2 * Nat.gcd g h / Nat.gcd q q' : ℕ) : ℝ))
          - (4 : ℝ) / (Nat.gcd q q' : ℝ))
        =
      ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
    rw [rawEvenRamanujanPairPeriodicFloor_eq_two_of_gcd_eq hq hq' heq]
    norm_num
  rw [hinner]

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_zero_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hlt : 2 * Nat.gcd g h < Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h
      + (((Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ))
          * ((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_overlap_add_remainder hq hq' hg hh,
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_zero hq hq' hg hh hlt]
  ring

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_one_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hle : Nat.gcd q q' ≤ 2 * Nat.gcd g h)
    (hlt : Nat.gcd g h < Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h
      + (((Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ))
          * ((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_overlap_add_remainder hq hq' hg hh,
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_one hq hq' hg hh hle hlt]
  ring

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_two_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (heq : Nat.gcd g h = Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h
      + (((Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ))
          * ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_overlap_add_remainder hq hq' hg hh,
    rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_two hq hq' hg hh heq]
  ring

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_coprime_case_zero_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcop : Nat.Coprime (q / g) (q' / h))
    (hlt : 2 * Nat.gcd g h < Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    (((Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ))
        * ((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_zero_add_remainder
    hq hq' hg hh hlt,
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_coprime hcop]
  ring

theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_coprime_case_two_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcop : Nat.Coprime (q / g) (q' / h))
    (heq : Nat.gcd g h = Nat.gcd q q') :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    (((Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ))
        * ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_two_add_remainder
    hq hq' hg hh heq,
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_coprime hcop]
  ring

noncomputable def centeredRamanujanPairCleanPeriodicDefectTerm
    (X q q' : ℕ) : ℝ :=
  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
    ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
            * rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeTerm
    (X q q' : ℕ) : ℝ :=
  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
    ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
            * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicGcdCorrectionTerm
    (X q q' : ℕ) : ℝ :=
  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
    ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
            * rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicRemainderTerm
    (X q q' : ℕ) : ℝ :=
  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
    ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
            * rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicDefectSummand
    (X q q' g h : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeSummand
    (X q q' g h : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicGcdCorrectionSummand
    (X q q' g h : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm X q q' g h)

noncomputable def centeredRamanujanPairCleanPeriodicRemainderSummand
    (X q q' g h : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h)

private theorem gcd_g_h_le_gcd_q_q'
    {q q' g h : ℕ} (hq' : 1 ≤ q') (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.gcd g h ≤ Nat.gcd q q' := by
  have hdiv : Nat.gcd g h ∣ Nat.gcd q q' := gcd_g_h_dvd_gcd_q_q' hg hh
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right q hq') hdiv

theorem centeredRamanujanPairCleanPeriodicDefectSummand_eq_commonPrime_add_gcdCorrection_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanPairCleanPeriodicDefectSummand X q q' g h
      =
    centeredRamanujanPairCleanPeriodicCommonPrimeSummand X q q' g h
      + centeredRamanujanPairCleanPeriodicGcdCorrectionSummand X q q' g h
      + centeredRamanujanPairCleanPeriodicRemainderSummand X q q' g h := by
  by_cases h0 : 2 * Nat.gcd g h < Nat.gcd q q'
  · rw [centeredRamanujanPairCleanPeriodicDefectSummand,
      centeredRamanujanPairCleanPeriodicCommonPrimeSummand,
      centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
      centeredRamanujanPairCleanPeriodicRemainderSummand]
    rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_zero_add_remainder
      hq hq' hg hh h0]
    rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_zero
      hq hq' hg hh h0]
    ring_nf
  · by_cases h2 : Nat.gcd g h = Nat.gcd q q'
    · rw [centeredRamanujanPairCleanPeriodicDefectSummand,
        centeredRamanujanPairCleanPeriodicCommonPrimeSummand,
        centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
        centeredRamanujanPairCleanPeriodicRemainderSummand]
      rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_two_add_remainder
        hq hq' hg hh h2]
      rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_two
        hq hq' hg hh h2]
      ring_nf
    · have hle : Nat.gcd q q' ≤ 2 * Nat.gcd g h := Nat.le_of_not_gt h0
      have hlt : Nat.gcd g h < Nat.gcd q q' := by
        exact lt_of_le_of_ne (gcd_g_h_le_gcd_q_q' hq' hg hh) h2
      rw [centeredRamanujanPairCleanPeriodicDefectSummand,
        centeredRamanujanPairCleanPeriodicCommonPrimeSummand,
        centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
        centeredRamanujanPairCleanPeriodicRemainderSummand]
      rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_commonPrime_add_case_one_add_remainder
        hq hq' hg hh hle hlt]
      rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_one
        hq hq' hg hh hle hlt]
      ring_nf

theorem centeredRamanujanPairCleanPeriodicDefectTerm_eq_commonPrime_add_gcdCorrection_add_remainder
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicDefectTerm X q q'
      =
    centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'
      + centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      + centeredRamanujanPairCleanPeriodicRemainderTerm X q q' := by
  unfold centeredRamanujanPairCleanPeriodicDefectTerm
    centeredRamanujanPairCleanPeriodicCommonPrimeTerm
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm
    centeredRamanujanPairCleanPeriodicRemainderTerm
  trans
    ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
        (centeredRamanujanPairCleanPeriodicCommonPrimeSummand X q q' g h
          + centeredRamanujanPairCleanPeriodicGcdCorrectionSummand X q q' g h
          + centeredRamanujanPairCleanPeriodicRemainderSummand X q q' g h)
  · refine Finset.sum_congr rfl ?_
    intro g hg
    refine Finset.sum_congr rfl ?_
    intro h hh
    have hg' : g ∈ q.divisors := (Finset.mem_filter.mp hg).1
    have hh' : h ∈ q'.divisors := (Finset.mem_filter.mp hh).1
    simpa [centeredRamanujanPairCleanPeriodicDefectSummand,
      centeredRamanujanPairCleanPeriodicCommonPrimeSummand,
      centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
      centeredRamanujanPairCleanPeriodicRemainderSummand, add_assoc] using
      centeredRamanujanPairCleanPeriodicDefectSummand_eq_commonPrime_add_gcdCorrection_add_remainder
        (X := X) (q := q) (q' := q') (g := g) (h := h) hq hq' hg' hh'
  · calc
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            (centeredRamanujanPairCleanPeriodicCommonPrimeSummand X q q' g h
              + centeredRamanujanPairCleanPeriodicGcdCorrectionSummand X q q' g h
              + centeredRamanujanPairCleanPeriodicRemainderSummand X q q' g h)
          =
        ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ((∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
              centeredRamanujanPairCleanPeriodicCommonPrimeSummand X q q' g h)
            + (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                centeredRamanujanPairCleanPeriodicGcdCorrectionSummand X q q' g h)
            + (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                centeredRamanujanPairCleanPeriodicRemainderSummand X q q' g h)) := by
              refine Finset.sum_congr rfl ?_
              intro g hg
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ =
        centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'
          + centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
          + centeredRamanujanPairCleanPeriodicRemainderTerm X q q' := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            rfl

theorem sum_filter_isEven_divisors_eq_sum_filter_isEven_quotientDivisors
    {β : Type*} [AddCommMonoid β] {q : ℕ} (hq : 1 ≤ q) (f : ℕ → β) :
    ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven, f g
      =
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)), f (q / a) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  refine Finset.sum_nbij' (i := fun g => q / g) (j := fun a => q / a) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rcases Finset.mem_filter.mp hg with ⟨hgdiv, hgeven⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hgdiv).1, hq0⟩
    · simpa [Nat.div_div_self (Nat.mem_divisors.mp hgdiv).1 hq0] using hgeven
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨hadiv, haeven⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hadiv).1, hq0⟩
    · simpa using haeven
  · intro g hg
    rcases Finset.mem_filter.mp hg with ⟨hgdiv, _⟩
    simpa [Nat.div_div_self (Nat.mem_divisors.mp hgdiv).1 hq0]
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨hadiv, _⟩
    exact Nat.div_div_self (Nat.mem_divisors.mp hadiv).1 hq0
  · intro g hg
    rcases Finset.mem_filter.mp hg with ⟨hgdiv, _⟩
    simpa [Nat.div_div_self (Nat.mem_divisors.mp hgdiv).1 hq0]

theorem rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_reindexed_coprime
    {X q q' a b : ℕ} (ha : a ∈ q.divisors) (hb : b ∈ q'.divisors)
    (hcop : Nat.Coprime a b) :
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b) = 0 := by
  apply rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_coprime
  simpa [Nat.div_div_self (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha).2,
    Nat.div_div_self (Nat.mem_divisors.mp hb).1 (Nat.mem_divisors.mp hb).2] using hcop

theorem centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_reindexed_reducedModuli
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'
      =
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        ramanujanGcdClassCoeff q (q / a) * ramanujanGcdClassCoeff q' (q' / b)
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
              * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b)) := by
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeTerm
  rw [sum_filter_isEven_divisors_eq_sum_filter_isEven_quotientDivisors hq
    (fun g =>
      ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
              * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' g h))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [sum_filter_isEven_divisors_eq_sum_filter_isEven_quotientDivisors hq'
    (fun h =>
      ramanujanGcdClassCoeff q (q / a) * ramanujanGcdClassCoeff q' h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
            * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) h))]

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand
    (X q q' a b : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q (q / a) * ramanujanGcdClassCoeff q' (q' / b)
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b))

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant
    (X q q' a b : ℕ) : ℝ :=
  (Nat.totient (q / a) : ℝ) * (Nat.totient (q' / b) : ℝ)
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
    * ((Nat.totient a : ℝ) * (Nat.totient b : ℝ))
    * ((((((X + centeredRamanujanPairBlockPeriod q q' - 1)
          / Nat.lcm (q / a) (q' / b) + 1)
          - (X ⌈/⌉ Nat.lcm (q / a) (q' / b))) / (a * b) : ℕ) : ℝ)
      * (((Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ)) - 1))

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm
    (X q q' : ℕ) : ℝ :=
  ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
    ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
      if Nat.Coprime a b then
        0
      else
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b

theorem centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_supported_reducedModuli
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'
      =
    centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm X q q' := by
  rw [centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_reindexed_reducedModuli hq hq']
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm
    centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand
  refine Finset.sum_congr rfl ?_
  intro a ha
  have ha' : a ∈ q.divisors := (Finset.mem_filter.mp ha).1
  refine Finset.sum_congr rfl ?_
  intro b hb
  have hb' : b ∈ q'.divisors := (Finset.mem_filter.mp hb).1
  by_cases hcop : Nat.Coprime a b
  · rw [if_pos hcop]
    rw [rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_zero_of_reindexed_coprime
      ha' hb' hcop]
    ring
  · rw [if_neg hcop]

theorem rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_reindexed_reducedModuli
    {X q q' a b : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : a ∈ q.divisors) (hb : b ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b)
      =
    ((Nat.totient a : ℝ) * (Nat.totient b : ℝ))
      * ((((((X + centeredRamanujanPairBlockPeriod q q' - 1)
            / Nat.lcm (q / a) (q' / b) + 1)
            - (X ⌈/⌉ Nat.lcm (q / a) (q' / b))) / (a * b) : ℕ) : ℝ)
        * (((Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ)) - 1)) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hq'0 : q' ≠ 0 := Nat.ne_of_gt hq'
  rw [rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm]
  simp [Nat.div_div_self (Nat.mem_divisors.mp ha).1 hq0,
    Nat.div_div_self (Nat.mem_divisors.mp hb).1 hq'0]

theorem abs_ramanujanGcdClassCoeff_reindexed_le_totient
    {q a : ℕ} (hq : 1 ≤ q) (ha : a ∈ q.divisors) :
    |ramanujanGcdClassCoeff q (q / a)| ≤ Nat.totient (q / a) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  rw [ramanujanGcdClassCoeff, Nat.div_div_self (Nat.mem_divisors.mp ha).1 hq0]
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ Nat.totient (q / a) by positivity)]
  have hμ : |(((ArithmeticFunction.moebius : ArithmeticFunction ℤ) a : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
  nlinarith

theorem centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant_nonneg
    {X q q' a b : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : a ∈ q.divisors) (hb : b ∈ q'.divisors) :
    0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b := by
  have ha_pos : 0 < a := divisor_pos_of_mem_divisors_of_pos ha hq
  have hb_pos : 0 < b := divisor_pos_of_mem_divisors_of_pos hb hq'
  have hgcd_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb_pos
  have hφg_pos : (0 : ℝ) < Nat.totient (Nat.gcd a b) := by
    exact_mod_cast Nat.totient_pos.mpr hgcd_pos
  have hoverlap_nonneg : 0 ≤ ((Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ)) - 1 := by
    have hφle : (Nat.totient (Nat.gcd a b) : ℝ) ≤ Nat.gcd a b := by
      exact_mod_cast Nat.totient_le (Nat.gcd a b)
    have hone : (1 : ℝ) ≤ (Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ) := by
      rw [le_div_iff₀ hφg_pos]
      simpa using hφle
    linarith
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant
  positivity

set_option maxHeartbeats 400000 in
theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand_le_majorant
    {X q q' a b : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (ha : a ∈ q.divisors) (hb : b ∈ q'.divisors) :
    |centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b|
      ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b := by
  have hcoeff_left :
      |ramanujanGcdClassCoeff q (q / a)| ≤ Nat.totient (q / a) :=
    abs_ramanujanGcdClassCoeff_reindexed_le_totient (q := q) (a := a) hq ha
  have hcoeff_right :
      |ramanujanGcdClassCoeff q' (q' / b)| ≤ Nat.totient (q' / b) :=
    abs_ramanujanGcdClassCoeff_reindexed_le_totient (q := q') (a := b) hq' hb
  have hscale_nonneg :
      0 ≤ ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)) := by positivity
  have hoverlap_nonneg :
      0 ≤ rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b) := by
    rw [rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_reindexed_reducedModuli
      (X := X) hq hq' ha hb]
    have ha_pos : 0 < a := divisor_pos_of_mem_divisors_of_pos ha hq
    have hb_pos : 0 < b := divisor_pos_of_mem_divisors_of_pos hb hq'
    have hgcd_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb_pos
    have hφg_pos : (0 : ℝ) < Nat.totient (Nat.gcd a b) := by
      exact_mod_cast Nat.totient_pos.mpr hgcd_pos
    have hoverlap_nonneg' : 0 ≤ ((Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ)) - 1 := by
      have hφle : (Nat.totient (Nat.gcd a b) : ℝ) ≤ Nat.gcd a b := by
        exact_mod_cast Nat.totient_le (Nat.gcd a b)
      have hone : (1 : ℝ) ≤ (Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ) := by
        rw [le_div_iff₀ hφg_pos]
        simpa using hφle
      linarith
    positivity
  have hscale_overlap_nonneg :
      0 ≤ (((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
        * rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b)) := by
    exact mul_nonneg hscale_nonneg hoverlap_nonneg
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand
    centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant
  rw [abs_mul, abs_mul,
    abs_of_nonneg hscale_overlap_nonneg]
  have htot_left_nonneg : (0 : ℝ) ≤ Nat.totient (q / a) := by positivity
  have htot_right_nonneg : (0 : ℝ) ≤ Nat.totient (q' / b) := by positivity
  have hoverlap_reindexed :
      rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm X q q' (q / a) (q' / b)
        =
      ((Nat.totient a : ℝ) * (Nat.totient b : ℝ))
        * ((((((X + centeredRamanujanPairBlockPeriod q q' - 1)
              / Nat.lcm (q / a) (q' / b) + 1)
              - (X ⌈/⌉ Nat.lcm (q / a) (q' / b))) / (a * b) : ℕ) : ℝ)
          * (((Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ)) - 1)) :=
    rawEvenRamanujanGcdClassPeriodicCommonPrimeOverlapTerm_eq_reindexed_reducedModuli
      (X := X) hq hq' ha hb
  rw [hoverlap_reindexed]
  have hcoeff_prod :
      |ramanujanGcdClassCoeff q (q / a)| * |ramanujanGcdClassCoeff q' (q' / b)|
        ≤ (Nat.totient (q / a) : ℝ) * (Nat.totient (q' / b) : ℝ) := by
    exact mul_le_mul hcoeff_left hcoeff_right (abs_nonneg _) htot_left_nonneg
  have hmajor_inner_nonneg :
      0 ≤
        ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
          * (((Nat.totient a : ℝ) * (Nat.totient b : ℝ))
            * ((((((X + centeredRamanujanPairBlockPeriod q q' - 1)
                  / Nat.lcm (q / a) (q' / b) + 1)
                  - (X ⌈/⌉ Nat.lcm (q / a) (q' / b))) / (a * b) : ℕ) : ℝ)
              * (((Nat.gcd a b : ℝ) / (Nat.totient (Nat.gcd a b) : ℝ)) - 1)))) := by
    rw [← hoverlap_reindexed]
    exact hscale_overlap_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_right hcoeff_prod hmajor_inner_nonneg)

private theorem reduced_gcd_dvd_gcd_q_q'
    {q q' a b : ℕ} (ha : a ∈ q.divisors) (hb : b ∈ q'.divisors) :
    Nat.gcd a b ∣ Nat.gcd q q' := by
  exact gcd_dvd_gcd (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp hb).1

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd
    (X q q' d : ℕ) : ℝ :=
  ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
    ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
      if Nat.gcd a b = d then
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
      else 0

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_majorant
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        if Nat.gcd a b = d then
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
        else 0 := by
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd
  calc
    |∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
        ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
          if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
          else 0|
      ≤
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      |∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
          if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
          else 0| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun a =>
              ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
                if Nat.gcd a b = d then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
                else 0)
            (q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))))
    _ ≤
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        |if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
          else 0| := by
        refine Finset.sum_le_sum ?_
        intro a ha
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun b =>
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
              else 0)
            (q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b))))
    _ ≤
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        if Nat.gcd a b = d then
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
        else 0 := by
        refine Finset.sum_le_sum ?_
        intro a ha
        have haDiv : a ∈ q.divisors := (Finset.mem_filter.mp ha).1
        refine Finset.sum_le_sum ?_
        intro b hb
        have hbDiv : b ∈ q'.divisors := (Finset.mem_filter.mp hb).1
        by_cases hgd : Nat.gcd a b = d
        · simp [hgd]
          exact abs_centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand_le_majorant
            (X := X) (q := q) (q' := q') (a := a) (b := b) hq hq' haDiv hbDiv
        · simp [hgd]

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_majorant_dvd_support
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    ∑ a ∈ (q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))).filter (fun a => d ∣ a),
      ∑ b ∈ (q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b))).filter (fun b => d ∣ b),
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_majorant
      (X := X) (q := q) (q' := q') (d := d) hq hq') ?_
  show
    (∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        if Nat.gcd a b = d then
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
        else 0)
      ≤
    ∑ a ∈ (q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))).filter (fun a => d ∣ a),
      ∑ b ∈ (q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b))).filter (fun b => d ∣ b),
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
  let S : Finset ℕ := q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))
  let T : Finset ℕ := q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b))
  have hsumall :
      (∑ a ∈ S,
        ∑ b ∈ T,
          (if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
          else (0 : ℝ)))
        ≤
      (∑ a ∈ S,
        ∑ b ∈ T,
          (if d ∣ a ∧ d ∣ b then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
          else (0 : ℝ))) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    have haDiv : a ∈ q.divisors := (Finset.mem_filter.mp ha).1
    refine Finset.sum_le_sum ?_
    intro b hb
    have hbDiv : b ∈ q'.divisors := (Finset.mem_filter.mp hb).1
    by_cases hgd : Nat.gcd a b = d
    · have hda : d ∣ a := by rw [← hgd]; exact Nat.gcd_dvd_left a b
      have hdb : d ∣ b := by rw [← hgd]; exact Nat.gcd_dvd_right a b
      simp [hgd, hda, hdb]
    · by_cases hdiv : d ∣ a ∧ d ∣ b
      · have hnonneg :
          0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b :=
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant_nonneg
              (X := X) (q := q) (q' := q') (a := a) (b := b) hq hq' haDiv hbDiv
        simp [hgd, hdiv, hnonneg]
      · simp [hgd, hdiv]
  have hrhs :
      (∑ a ∈ S,
        ∑ b ∈ T,
          (if d ∣ a ∧ d ∣ b then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
          else (0 : ℝ)))
        =
      ∑ a ∈ S.filter (fun a => d ∣ a),
        ∑ b ∈ T.filter (fun b => d ∣ b),
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b := by
    have houter :
        (∑ a ∈ S,
          ∑ b ∈ T,
            (if d ∣ a ∧ d ∣ b then
              centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
            else (0 : ℝ)))
          =
        ∑ a ∈ S,
          if d ∣ a then
            ∑ b ∈ T.filter (fun b => d ∣ b),
              centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
          else (0 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hda : d ∣ a
      · simp [hda, Finset.sum_filter]
      · simp [hda]
    rw [houter]
    simpa using
      (Finset.sum_filter
        (s := S)
        (p := fun a => d ∣ a)
        (f := fun a =>
          ∑ b ∈ T.filter (fun b => d ∣ b),
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b)).symm
  exact hsumall.trans_eq (by simpa [S, T] using hrhs)

private theorem sum_filter_dvd_reindexed_by_div
    {q d : ℕ} (hq : 1 ≤ q) (hdq : d ∣ q) (f : ℕ → ℝ) :
    (∑ a ∈ (q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))).filter (fun a => d ∣ a), f a)
      =
    ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)), f (d * a1) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hqd0 : q / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos)
  refine Finset.sum_nbij' (i := fun a => a / d) (j := fun a1 => d * a1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha0, hda⟩
    rcases Finset.mem_filter.mp ha0 with ⟨hadiv, haeven⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · rw [Nat.mem_divisors]
      constructor
      · rw [Nat.dvd_div_iff_mul_dvd hdq]
        simpa [Nat.mul_div_cancel' hda] using (Nat.mem_divisors.mp hadiv).1
      · exact hqd0
    · simpa [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hda, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using haeven
  · intro a1 ha1
    rcases Finset.mem_filter.mp ha1 with ⟨ha1div, ha1even⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · refine Finset.mem_filter.mpr ?_
      constructor
      · rw [Nat.mem_divisors]
        constructor
        · rw [← Nat.mul_div_cancel' hdq]
          exact Nat.mul_dvd_mul_left d (Nat.mem_divisors.mp ha1div).1
        · exact hq0
      · simpa [Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ha1even
    · exact dvd_mul_right d a1
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha0, hda⟩
    simpa [Nat.mul_comm] using Nat.mul_div_cancel' hda
  · intro a1 ha1
    simpa [Nat.mul_comm] using Nat.mul_div_right a1 hdpos
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha0, hda⟩
    exact congrArg f (by simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hda).symm)

theorem centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant_dvd_support_eq_reindexed
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    (∑ a ∈ (q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))).filter (fun a => d ∣ a),
      ∑ b ∈ (q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b))).filter (fun b => d ∣ b),
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b)
      =
    ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
      ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1) := by
  rw [sum_filter_dvd_reindexed_by_div (q := q) (d := d) hq hdq]
  refine Finset.sum_congr rfl ?_
  intro a1 ha1
  exact sum_filter_dvd_reindexed_by_div (q := q') (d := d) hq' hdq'
    (fun b => centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) b)

theorem centeredRamanujanPairCleanPeriodicCommonPrimeExactMajorant_eq_coprime_reindexed
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    (∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        if Nat.gcd a b = d then
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
        else 0)
      =
    ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
      ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
        if Nat.Coprime a1 b1 then
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
        else 0 := by
  let S := q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a))
  let T := q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b))
  have hfiltered :
      (∑ a ∈ S,
        ∑ b ∈ T,
          if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
          else 0)
        =
      ∑ a ∈ S.filter (fun a => d ∣ a),
        ∑ b ∈ T.filter (fun b => d ∣ b),
          if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
          else 0 := by
    have houter :
        (∑ a ∈ S,
          ∑ b ∈ T,
            if Nat.gcd a b = d then
              centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
            else 0)
          =
        ∑ a ∈ S,
          if d ∣ a then
            ∑ b ∈ T.filter (fun b => d ∣ b),
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
              else 0
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hda : d ∣ a
      · rw [if_pos hda]
        have hinner :
            (∑ b ∈ T,
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
              else 0)
              =
            ∑ b ∈ T.filter (fun b => d ∣ b),
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
              else 0 := by
          calc
            (∑ b ∈ T,
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
              else 0)
              =
            ∑ b ∈ T,
              if d ∣ b then
                if Nat.gcd a b = d then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
                else 0
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro b hb
                by_cases hdb : d ∣ b
                · simp [hdb]
                · have hneq : Nat.gcd a b ≠ d := by
                    intro hgd
                    exact hdb (by rw [← hgd]; exact Nat.gcd_dvd_right a b)
                  simp [hdb, hneq]
            _ =
            ∑ b ∈ T.filter (fun b => d ∣ b),
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
              else 0 := by
                simp [Finset.sum_filter]
        exact hinner
      · have hzero :
          ∑ b ∈ T,
            (if Nat.gcd a b = d then
              centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
            else 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro b hb
          by_cases hgd : Nat.gcd a b = d
          · exfalso
            exact hda (by rw [← hgd]; exact Nat.gcd_dvd_left a b)
          · simp [hgd]
        simp [hda, hzero]
    rw [houter]
    simpa [S, T] using
      (Finset.sum_filter
        (s := S)
        (p := fun a => d ∣ a)
        (f := fun a =>
          ∑ b ∈ T.filter (fun b => d ∣ b),
            if Nat.gcd a b = d then
              centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' a b
            else 0)).symm
  rw [hfiltered]
  rw [sum_filter_dvd_reindexed_by_div (q := q) (d := d) hq hdq]
  refine Finset.sum_congr rfl ?_
  intro a1 ha1
  rw [sum_filter_dvd_reindexed_by_div (q := q') (d := d) hq' hdq']
  refine Finset.sum_congr rfl ?_
  intro b1 hb1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hcop_iff : Nat.gcd (d * a1) (d * b1) = d ↔ Nat.Coprime a1 b1 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    constructor
    · intro hgd
      have hmul : d * Nat.gcd a1 b1 = d * 1 := by
        simpa [Nat.gcd_mul_left, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hgd
      exact Nat.eq_of_mul_eq_mul_left hdpos hmul
    · intro hcop
      simpa [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.gcd_mul_left,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  by_cases hcop : Nat.Coprime a1 b1
  · simp [hcop, hcop_iff.mpr hcop]
  · have hnotgd : Nat.gcd (d * a1) (d * b1) ≠ d := by
      intro hgd
      exact hcop (hcop_iff.mp hgd)
    simp [hcop, hnotgd]

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_coprime_reindexedMajorant
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
      ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
        if Nat.Coprime a1 b1 then
          centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
        else 0 := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_majorant
      (X := X) (q := q) (q' := q') (d := d) hq hq') ?_
  rw [centeredRamanujanPairCleanPeriodicCommonPrimeExactMajorant_eq_coprime_reindexed
    (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq']

theorem centeredRamanujanPairCleanPeriodicCommonPrimeTranslatedEvenSupport_iff
    {q d a1 : ℕ} (hdq : d ∣ q) :
    Goldbach.Windows.IsEven (q / (d * a1)) ↔ Goldbach.Windows.IsEven ((q / d) / a1) := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor
    (q d a1 : ℕ) : ℝ :=
  (Nat.totient (q / (d * a1)) : ℝ) * (Nat.totient (d * a1) : ℝ)

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor
    (q' d b1 : ℕ) : ℝ :=
  (Nat.totient (q' / (d * b1)) : ℝ) * (Nat.totient (d * b1) : ℝ)

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor
    (X q q' d a1 b1 : ℕ) : ℝ :=
  (((((X + centeredRamanujanPairBlockPeriod q q' - 1)
      / Nat.lcm (q / (d * a1)) (q' / (d * b1)) + 1)
      - (X ⌈/⌉ Nat.lcm (q / (d * a1)) (q' / (d * b1))))
      / ((d * a1) * (d * b1)) : ℕ) : ℝ)

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor
    (d a1 b1 : ℕ) : ℝ :=
  (((Nat.gcd (d * a1) (d * b1) : ℝ) /
    (Nat.totient (Nat.gcd (d * a1) (d * b1)) : ℝ)) - 1)

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor
    (X q q' d a1 b1 : ℕ) : ℝ :=
  ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
    * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1
    * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor d a1 b1

set_option maxHeartbeats 400000 in
theorem centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant_eq_reindexed_factorized
    {X q q' d a1 b1 : ℕ} :
    centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
      =
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
      * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
      * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor X q q' d a1 b1 := by
  dsimp [
    centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant,
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor,
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor,
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor,
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor,
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor
  ]
  ring_nf

private theorem centeredRamanujanPairCleanPeriodicReindexedFullLeft_mem_divisors
    {q d a1 : ℕ} (hq : 1 ≤ q) (hdq : d ∣ q) (ha1 : a1 ∈ (q / d).divisors) :
    d * a1 ∈ q.divisors := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have ha1dvd : a1 ∣ q / d := (Nat.mem_divisors.mp ha1).1
  rw [Nat.mem_divisors]
  constructor
  · rw [← Nat.mul_div_cancel' hdq]
    exact Nat.mul_dvd_mul_left d ha1dvd
  · exact hq0

private theorem centeredRamanujanPairCleanPeriodicReindexedFullRight_mem_divisors
    {q' d b1 : ℕ} (hq' : 1 ≤ q') (hdq' : d ∣ q') (hb1 : b1 ∈ (q' / d).divisors) :
    d * b1 ∈ q'.divisors := by
  have hq'0 : q' ≠ 0 := Nat.ne_of_gt hq'
  have hb1dvd : b1 ∣ q' / d := (Nat.mem_divisors.mp hb1).1
  rw [Nat.mem_divisors]
  constructor
  · rw [← Nat.mul_div_cancel' hdq']
    exact Nat.mul_dvd_mul_left d hb1dvd
  · exact hq'0

private theorem centeredRamanujanPairCleanPeriodicReindexedReducedLeft_mem_divisors
    {q d a1 : ℕ} (hq : 1 ≤ q) (hdq : d ∣ q) (ha1 : a1 ∈ (q / d).divisors) :
    q / (d * a1) ∈ q.divisors := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hfull : d * a1 ∈ q.divisors :=
    centeredRamanujanPairCleanPeriodicReindexedFullLeft_mem_divisors hq hdq ha1
  rw [Nat.mem_divisors]
  exact ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hfull).1, hq0⟩

private theorem centeredRamanujanPairCleanPeriodicReindexedReducedRight_mem_divisors
    {q' d b1 : ℕ} (hq' : 1 ≤ q') (hdq' : d ∣ q') (hb1 : b1 ∈ (q' / d).divisors) :
    q' / (d * b1) ∈ q'.divisors := by
  have hq'0 : q' ≠ 0 := Nat.ne_of_gt hq'
  have hfull : d * b1 ∈ q'.divisors :=
    centeredRamanujanPairCleanPeriodicReindexedFullRight_mem_divisors hq' hdq' hb1
  rw [Nat.mem_divisors]
  exact ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hfull).1, hq'0⟩

private theorem centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor_eq_periodQuotient
    {X q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1
      =
    ((((centeredRamanujanPairBlockPeriod q q'
        / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
        / ((d * a1) * (d * b1)) : ℕ) : ℝ)) := by
  have hleftDiv :
      q / (d * a1) ∈ q.divisors :=
    centeredRamanujanPairCleanPeriodicReindexedReducedLeft_mem_divisors hq hdq ha1
  have hrightDiv :
      q' / (d * b1) ∈ q'.divisors :=
    centeredRamanujanPairCleanPeriodicReindexedReducedRight_mem_divisors hq' hdq' hb1
  have hfullLeft : d * a1 ∈ q.divisors :=
    centeredRamanujanPairCleanPeriodicReindexedFullLeft_mem_divisors hq hdq ha1
  have hfullRight : d * b1 ∈ q'.divisors :=
    centeredRamanujanPairCleanPeriodicReindexedFullRight_mem_divisors hq' hdq' hb1
  have hleftPos : 0 < q / (d * a1) := quotient_pos_of_mem_divisors hq hfullLeft
  have hrightPos : 0 < q' / (d * b1) := quotient_pos_of_mem_divisors hq' hfullRight
  have hPairLen :
      (((X + centeredRamanujanPairBlockPeriod q q' - 1)
          / Nat.lcm (q / (d * a1)) (q' / (d * b1)) + 1)
          - (X ⌈/⌉ Nat.lcm (q / (d * a1)) (q' / (d * b1))))
        =
      centeredRamanujanPairBlockPeriod q q'
        / Nat.lcm (q / (d * a1)) (q' / (d * b1)) := by
    apply quotientLength_eq_periodQuotient
    · exact Nat.lcm_pos hleftPos hrightPos
    · dsimp [centeredRamanujanPairBlockPeriod]
      exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
    · exact lcm_divisors_dvd_pairBlockPeriod hleftDiv hrightDiv
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor
  rw [hPairLen]

private theorem centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor_nonneg
    {X q q' d a1 b1 : ℕ} :
    0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1 := by
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor
  positivity

private theorem centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor_nonneg
    {q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor d a1 b1 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hqd_pos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos
  have hq'd_pos : 0 < q' / d := Nat.div_pos (Nat.le_of_dvd hq' hdq') hdpos
  have ha1_pos : 0 < a1 := divisor_pos_of_mem_divisors_of_pos ha1 (Nat.succ_le_of_lt hqd_pos)
  have hb1_pos : 0 < b1 := divisor_pos_of_mem_divisors_of_pos hb1 (Nat.succ_le_of_lt hq'd_pos)
  have hgcd_pos : 0 < Nat.gcd (d * a1) (d * b1) := Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hdpos hb1_pos)
  have hφg_pos : (0 : ℝ) < Nat.totient (Nat.gcd (d * a1) (d * b1)) := by
    exact_mod_cast Nat.totient_pos.mpr hgcd_pos
  have hφle : (Nat.totient (Nat.gcd (d * a1) (d * b1)) : ℝ)
      ≤ Nat.gcd (d * a1) (d * b1) := by
    exact_mod_cast Nat.totient_le (Nat.gcd (d * a1) (d * b1))
  have hone :
      (1 : ℝ) ≤
        (Nat.gcd (d * a1) (d * b1) : ℝ)
          / (Nat.totient (Nat.gcd (d * a1) (d * b1)) : ℝ) := by
    rw [le_div_iff₀ hφg_pos]
    simpa using hφle
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor
  linarith

private theorem centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor_le_mul
    {q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor d a1 b1
      ≤ ((d * a1 : ℝ) * (d * b1 : ℝ)) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hqd_pos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos
  have hq'd_pos : 0 < q' / d := Nat.div_pos (Nat.le_of_dvd hq' hdq') hdpos
  have ha1_pos : 0 < a1 := divisor_pos_of_mem_divisors_of_pos ha1 (Nat.succ_le_of_lt hqd_pos)
  have hb1_pos : 0 < b1 := divisor_pos_of_mem_divisors_of_pos hb1 (Nat.succ_le_of_lt hq'd_pos)
  have hda1_pos : 0 < d * a1 := Nat.mul_pos hdpos ha1_pos
  have hdb1_pos : 0 < d * b1 := Nat.mul_pos hdpos hb1_pos
  have hgcd_pos : 0 < Nat.gcd (d * a1) (d * b1) := Nat.gcd_pos_of_pos_right _ hdb1_pos
  have hphi_ge_one : (1 : ℝ) ≤ Nat.totient (Nat.gcd (d * a1) (d * b1)) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.totient_pos.mpr hgcd_pos)
  have hoverlap_le_gcd :
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor d a1 b1
        ≤ Nat.gcd (d * a1) (d * b1) := by
    unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor
    have hfrac_le_gcd :
        (Nat.gcd (d * a1) (d * b1) : ℝ)
          / (Nat.totient (Nat.gcd (d * a1) (d * b1)) : ℝ)
          ≤ Nat.gcd (d * a1) (d * b1) := by
      exact div_le_self (by positivity) hphi_ge_one
    linarith
  have hgcd_le_left : (Nat.gcd (d * a1) (d * b1) : ℝ) ≤ (d * a1 : ℝ) := by
    exact_mod_cast Nat.gcd_le_left (m := d * a1) (n := d * b1) hda1_pos
  have hleft_le_mul : (d * a1 : ℝ) ≤ (d * a1 : ℝ) * (d * b1 : ℝ) := by
    have : (1 : ℝ) ≤ (d * b1 : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hdb1_pos
    nlinarith
  exact le_trans hoverlap_le_gcd (le_trans hgcd_le_left hleft_le_mul)

theorem centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor_le_count_mul_mul
    {X q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor X q q' d a1 b1
      ≤
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
      * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1
      * ((d * a1 : ℝ) * (d * b1 : ℝ)) := by
  have hscale_nonneg :
      0 ≤ ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)) := by
    positivity
  have hcount_nonneg :
      0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1 :=
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor_nonneg
  have hfac_nonneg :
      0 ≤ ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
        * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1 := by
    exact mul_nonneg hscale_nonneg hcount_nonneg
  have hoverlap_le :
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor d a1 b1
        ≤ ((d * a1 : ℝ) * (d * b1 : ℝ)) :=
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedOverlapFactor_le_mul
      hq hq' hdq hdq' ha1 hb1
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor
  exact (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hoverlap_le hfac_nonneg))

theorem centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor_le_periodQuotient_mul_mul
    {X q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor X q q' d a1 b1
      ≤
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
      * ((((centeredRamanujanPairBlockPeriod q q'
          / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
          / ((d * a1) * (d * b1)) : ℕ) : ℝ))
      * ((d * a1 : ℝ) * (d * b1 : ℝ)) := by
  calc
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor X q q' d a1 b1
      ≤
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
      * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor X q q' d a1 b1
      * ((d * a1 : ℝ) * (d * b1 : ℝ)) := by
        exact centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor_le_count_mul_mul
          (X := X) (q := q) (q' := q') (d := d) (a1 := a1) (b1 := b1)
          hq hq' hdq hdq' ha1 hb1
    _ =
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
      * ((((centeredRamanujanPairBlockPeriod q q'
          / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
          / ((d * a1) * (d * b1)) : ℕ) : ℝ))
      * ((d * a1 : ℝ) * (d * b1 : ℝ)) := by
        rw [centeredRamanujanPairCleanPeriodicCommonPrimeReindexedCountFactor_eq_periodQuotient
          (X := X) (q := q) (q' := q') (d := d) (a1 := a1) (b1 := b1)
          hq hq' hdq hdq' ha1 hb1]

private theorem centeredRamanujanPairCleanPeriodicReindexedPeriodQuotientMul_le_left
    {q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    ((((centeredRamanujanPairBlockPeriod q q'
        / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
        / ((d * a1) * (d * b1)) : ℕ) : ℝ))
      * ((d * a1 : ℝ) * (d * b1 : ℝ))
      ≤ (2 * (d * a1) * q' : ℝ) := by
  set P := centeredRamanujanPairBlockPeriod q q'
  set A := q / (d * a1)
  set B := q' / (d * b1)
  set G := (d * a1) * (d * b1)
  have hleftDiv :
      A ∈ q.divisors := by
    dsimp [A]
    exact centeredRamanujanPairCleanPeriodicReindexedReducedLeft_mem_divisors hq hdq ha1
  have hrightDiv :
      B ∈ q'.divisors := by
    dsimp [B]
    exact centeredRamanujanPairCleanPeriodicReindexedReducedRight_mem_divisors hq' hdq' hb1
  have hfullLeft :
      d * a1 ∈ q.divisors := by
    exact centeredRamanujanPairCleanPeriodicReindexedFullLeft_mem_divisors hq hdq ha1
  have hfullRight :
      d * b1 ∈ q'.divisors := by
    exact centeredRamanujanPairCleanPeriodicReindexedFullRight_mem_divisors hq' hdq' hb1
  have hA_pos : 0 < A := by
    dsimp [A]
    exact quotient_pos_of_mem_divisors hq hfullLeft
  have hB_pos : 0 < B := by
    dsimp [B]
    exact quotient_pos_of_mem_divisors hq' hfullRight
  have hmul_le_nat :
      ((P / Nat.lcm A B) / G) * G ≤ 2 * (d * a1) * q' := by
    have hdivmul :
        ((P / Nat.lcm A B) / G) * G ≤ P / Nat.lcm A B := by
      exact Nat.div_mul_le_self _ _
    have hdivmono :
        P / Nat.lcm A B ≤ P / A := by
      exact Nat.div_le_div (le_rfl) (Nat.le_lcm_left A hB_pos) (Nat.ne_of_gt hA_pos)
    have hP_le :
        P ≤ 2 * q * q' := by
      dsimp [P, centeredRamanujanPairBlockPeriod]
      have hlcm_dvd : Nat.lcm q q' ∣ q * q' := by
        exact Nat.lcm_dvd (dvd_mul_right q q') (dvd_mul_left q' q)
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_left 2 (Nat.le_of_dvd (Nat.mul_pos hq hq') hlcm_dvd)
    have hPA_le :
        P / A ≤ 2 * (d * a1) * q' := by
      have hq_eq : q = (d * a1) * A := by
        dsimp [A]
        exact (Nat.mul_div_cancel' ((Nat.mem_divisors.mp hfullLeft).1)).symm
      let M := 2 * (d * a1) * q'
      have hM_eq : 2 * ((d * a1) * A) * q' = M * A := by
        dsimp [M]
        ring
      calc
        P / A ≤ (2 * q * q') / A := Nat.div_le_div_right hP_le
        _ = (2 * ((d * a1) * A) * q') / A := by rw [hq_eq]
        _ = (M * A) / A := by rw [hM_eq]
        _ = M := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mul_div_right M hA_pos)
        _ = 2 * (d * a1) * q' := by rfl
    exact le_trans hdivmul (le_trans hdivmono hPA_le)
  exact_mod_cast hmul_le_nat

private theorem centeredRamanujanPairCleanPeriodicReindexedPeriodQuotientMul_le_right
    {q q' d a1 b1 : ℕ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q')
    (ha1 : a1 ∈ (q / d).divisors) (hb1 : b1 ∈ (q' / d).divisors) :
    ((((centeredRamanujanPairBlockPeriod q q'
        / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
        / ((d * a1) * (d * b1)) : ℕ) : ℝ))
      * ((d * a1 : ℝ) * (d * b1 : ℝ))
      ≤ (2 * q * (d * b1) : ℝ) := by
  set P := centeredRamanujanPairBlockPeriod q q'
  set A := q / (d * a1)
  set B := q' / (d * b1)
  set G := (d * a1) * (d * b1)
  have hleftDiv :
      A ∈ q.divisors := by
    dsimp [A]
    exact centeredRamanujanPairCleanPeriodicReindexedReducedLeft_mem_divisors hq hdq ha1
  have hrightDiv :
      B ∈ q'.divisors := by
    dsimp [B]
    exact centeredRamanujanPairCleanPeriodicReindexedReducedRight_mem_divisors hq' hdq' hb1
  have hfullRight :
      d * b1 ∈ q'.divisors := by
    exact centeredRamanujanPairCleanPeriodicReindexedFullRight_mem_divisors hq' hdq' hb1
  have hfullLeft :
      d * a1 ∈ q.divisors := by
    exact centeredRamanujanPairCleanPeriodicReindexedFullLeft_mem_divisors hq hdq ha1
  have hA_pos : 0 < A := by
    dsimp [A]
    exact quotient_pos_of_mem_divisors hq hfullLeft
  have hB_pos : 0 < B := by
    dsimp [B]
    exact quotient_pos_of_mem_divisors hq' hfullRight
  have hmul_le_nat :
      ((P / Nat.lcm A B) / G) * G ≤ 2 * q * (d * b1) := by
    have hdivmul :
        ((P / Nat.lcm A B) / G) * G ≤ P / Nat.lcm A B := by
      exact Nat.div_mul_le_self _ _
    have hdivmono :
        P / Nat.lcm A B ≤ P / B := by
      exact Nat.div_le_div (le_rfl) (Nat.le_lcm_right B hA_pos) (Nat.ne_of_gt hB_pos)
    have hP_le :
        P ≤ 2 * q * q' := by
      dsimp [P, centeredRamanujanPairBlockPeriod]
      have hlcm_dvd : Nat.lcm q q' ∣ q * q' := by
        exact Nat.lcm_dvd (dvd_mul_right q q') (dvd_mul_left q' q)
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_left 2 (Nat.le_of_dvd (Nat.mul_pos hq hq') hlcm_dvd)
    have hPB_le :
        P / B ≤ 2 * q * (d * b1) := by
      have hq'_eq : q' = (d * b1) * B := by
        dsimp [B]
        exact (Nat.mul_div_cancel' ((Nat.mem_divisors.mp hfullRight).1)).symm
      let M := 2 * q * (d * b1)
      have hM_eq : 2 * q * ((d * b1) * B) = M * B := by
        dsimp [M]
        ring
      calc
        P / B ≤ (2 * q * q') / B := Nat.div_le_div_right hP_le
        _ = (2 * q * ((d * b1) * B)) / B := by rw [hq'_eq]
        _ = (M * B) / B := by rw [hM_eq]
        _ = M := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mul_div_right M hB_pos)
        _ = 2 * q * (d * b1) := by rfl
    exact le_trans hdivmul (le_trans hdivmono hPB_le)
  exact_mod_cast hmul_le_nat

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_reindexed_periodQuotient
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
      ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
        centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
          * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
          * ((((centeredRamanujanPairBlockPeriod q q'
              / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
              / ((d * a1) * (d * b1)) : ℕ) : ℝ))
          * ((d * a1 : ℝ) * (d * b1 : ℝ)) := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_majorant_dvd_support
      (X := X) (q := q) (q' := q') (d := d) hq hq') ?_
  rw [centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant_dvd_support_eq_reindexed
    (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq']
  refine Finset.sum_le_sum ?_
  intro a1 ha1
  refine Finset.sum_le_sum ?_
  intro b1 hb1
  have hmajor_eq :
      centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
        =
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
        * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
        * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor X q q' d a1 b1 := by
    exact centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant_eq_reindexed_factorized
      (X := X) (q := q) (q' := q') (d := d) (a1 := a1) (b1 := b1)
  rw [hmajor_eq]
  have hleft_nonneg :
      0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1 := by
    unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor
    positivity
  have hright_nonneg :
      0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1 := by
    unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor
    positivity
  have hmix_le :
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor X q q' d a1 b1
        ≤
      ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
        * ((((centeredRamanujanPairBlockPeriod q q'
            / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
            / ((d * a1) * (d * b1)) : ℕ) : ℝ))
        * ((d * a1 : ℝ) * (d * b1 : ℝ)) :=
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedMixedFactor_le_periodQuotient_mul_mul
      (X := X) (q := q) (q' := q') (d := d) (a1 := a1) (b1 := b1)
      hq hq' hdq hdq' ((Finset.mem_filter.mp ha1).1) ((Finset.mem_filter.mp hb1).1)
  have hmul :=
    mul_le_mul_of_nonneg_left hmix_le (mul_nonneg hleft_nonneg hright_nonneg)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_reindexed_left_product
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    (∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
        * (2 * (d * a1 : ℝ)))
      *
    (∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
        * (q' : ℝ)) := by
  let A :=
    (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1))
  let B :=
    (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1))
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_reindexed_periodQuotient
      (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq') ?_
  change
    (∑ a1 ∈ A,
      ∑ b1 ∈ B,
        centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
          * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
          * ((((centeredRamanujanPairBlockPeriod q q'
              / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
              / ((d * a1) * (d * b1)) : ℕ) : ℝ))
          * ((d * a1 : ℝ) * (d * b1 : ℝ)))
      ≤
    (∑ a1 ∈ A,
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
        * (2 * (d * a1 : ℝ)))
      *
    (∑ b1 ∈ B,
      centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
        * (q' : ℝ))
  have hsum_le :
      (∑ a1 ∈ A,
        ∑ b1 ∈ B,
          centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
            * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
            * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
            * ((((centeredRamanujanPairBlockPeriod q q'
                / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
                / ((d * a1) * (d * b1)) : ℕ) : ℝ))
            * ((d * a1 : ℝ) * (d * b1 : ℝ)))
        ≤
      ∑ a1 ∈ A,
        ∑ b1 ∈ B,
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
            * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
            * (2 * (d * a1 : ℝ)))
            *
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
            * (q' : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro a1 ha1
    refine Finset.sum_le_sum ?_
    intro b1 hb1
    have hleft_nonneg :
        0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1 := by
      unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor
      positivity
    have hright_nonneg :
        0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1 := by
      unfold centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor
      positivity
    have hscale_nonneg :
        0 ≤ ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)) := by
      positivity
    have hcoeff_nonneg :
        0 ≤ centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
          * centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)) := by
      exact mul_nonneg (mul_nonneg hleft_nonneg hright_nonneg) hscale_nonneg
    have hperiod_le :
        ((((centeredRamanujanPairBlockPeriod q q'
            / Nat.lcm (q / (d * a1)) (q' / (d * b1)))
            / ((d * a1) * (d * b1)) : ℕ) : ℝ))
          * ((d * a1 : ℝ) * (d * b1 : ℝ))
          ≤ (2 * (d * a1) * q' : ℝ) :=
      centeredRamanujanPairCleanPeriodicReindexedPeriodQuotientMul_le_left
        (q := q) (q' := q') (d := d) (a1 := a1) (b1 := b1)
        hq hq' hdq hdq' ((Finset.mem_filter.mp ha1).1) ((Finset.mem_filter.mp hb1).1)
    have hmul :=
      mul_le_mul_of_nonneg_left hperiod_le hcoeff_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  refine le_trans hsum_le ?_
  have hprod_eq :
      (∑ a1 ∈ A,
        ∑ b1 ∈ B,
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
            * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
            * (2 * (d * a1 : ℝ)))
            *
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
            * (q' : ℝ)))
        =
      (∑ a1 ∈ A,
        centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
          * (2 * (d * a1 : ℝ)))
        *
      (∑ b1 ∈ B,
        centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
          * (q' : ℝ)) := by
    calc
      (∑ a1 ∈ A,
        ∑ b1 ∈ B,
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
            * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
            * (2 * (d * a1 : ℝ)))
            *
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
            * (q' : ℝ)))
        =
      ∑ a1 ∈ A,
        (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
          * (2 * (d * a1 : ℝ)))
          *
        ∑ b1 ∈ B,
          (centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
            * (q' : ℝ)) := by
          simp_rw [Finset.mul_sum]
      _ =
      (∑ a1 ∈ A,
        centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
          * (2 * (d * a1 : ℝ)))
        *
      (∑ b1 ∈ B,
        centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
          * (q' : ℝ)) := by
          rw [Finset.sum_mul]
  exact le_of_eq hprod_eq

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant
    (q q' d : ℕ) : ℝ :=
  ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedLeftFactor q d a1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
      * (2 * (d * a1 : ℝ))

noncomputable def centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant
    (q' d : ℕ) : ℝ :=
  ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
    centeredRamanujanPairCleanPeriodicCommonPrimeReindexedRightFactor q' d b1
      * (q' : ℝ)

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_productMajorant
    {X q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant q q' d
      * centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant q' d := by
  simpa [centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant,
    centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant] using
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_reindexed_left_product
      (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq')

private theorem centeredRamanujanPairCleanPeriodicCommonPrimeSupportedSummand_eq_sum_reducedGcdDivisors
    {X q q' a b : ℕ} (hq : 1 ≤ q') (ha : a ∈ q.divisors) (hb : b ∈ q'.divisors) :
    (if Nat.Coprime a b then
      0
    else
      centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b)
      =
    ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
      if Nat.gcd a b = d then
        centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
      else 0 := by
  by_cases hcop : Nat.Coprime a b
  · have hgcd1 : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hcop
    rw [if_pos hcop]
    refine (Finset.sum_eq_zero ?_).symm
    intro d hd
    have hdne : d ≠ 1 := (Finset.mem_filter.mp hd).2
    have hneq : ¬ Nat.gcd a b = d := by
      rw [hgcd1]
      exact fun h => hdne h.symm
    simp [hneq]
  · rw [if_neg hcop]
    have hgcd_ne_one : Nat.gcd a b ≠ 1 := by
      intro hgcd1
      exact hcop (Nat.coprime_iff_gcd_eq_one.mpr hgcd1)
    have hG0 : Nat.gcd q q' ≠ 0 := by
      exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_right q hq)
    have hmem : Nat.gcd a b ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1) := by
      refine Finset.mem_filter.mpr ?_
      constructor
      · rw [Nat.mem_divisors]
        exact ⟨reduced_gcd_dvd_gcd_q_q' ha hb, hG0⟩
      · exact hgcd_ne_one
    rw [← Finset.sum_filter]
    have hfilter :
        (((Nat.gcd q q').divisors.filter (fun d => d ≠ 1)).filter
          (fun d => Nat.gcd a b = d)) = {Nat.gcd a b} := by
      ext d
      by_cases hd : d = Nat.gcd a b
      · subst hd
        simp [hmem]
      · simp [hd, eq_comm]
    rw [hfilter]
    simp

theorem centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm_eq_sum_over_reducedGcdDivisors
    {X q q' : ℕ} (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm X q q'
      =
    ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
      centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d := by
  unfold centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm
    centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd
  trans
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
        ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
          if Nat.gcd a b = d then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
          else 0
  · refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr rfl ?_
    intro b hb
    have ha' : a ∈ q.divisors := (Finset.mem_filter.mp ha).1
    have hb' : b ∈ q'.divisors := (Finset.mem_filter.mp hb).1
    exact centeredRamanujanPairCleanPeriodicCommonPrimeSupportedSummand_eq_sum_reducedGcdDivisors
      hq' ha' hb'
  · calc
      (∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
          ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
            ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
              else 0)
          =
      (∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
              else 0) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [Finset.sum_comm]
    _ =
      (∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
          ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
            ∑ b ∈ q'.divisors.filter (fun b => Goldbach.Windows.IsEven (q' / b)),
              if Nat.gcd a b = d then
                centeredRamanujanPairCleanPeriodicCommonPrimeReducedSummand X q q' a b
              else 0) := by
        rw [Finset.sum_comm]

theorem centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_sum_over_nontrivial_reducedGcdDivisors
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'
      =
    ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
      centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d := by
  rw [centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_supported_reducedModuli hq hq']
  exact centeredRamanujanPairCleanPeriodicCommonPrimeSupportedReducedTerm_eq_sum_over_reducedGcdDivisors hq'

theorem centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_zero_of_coprime_moduli
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q') :
    centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q' = 0 := by
  rw [centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_sum_over_nontrivial_reducedGcdDivisors
    hq hq']
  have hgcd1 : Nat.gcd q q' = 1 := Nat.Coprime.gcd_eq_one hcop
  rw [hgcd1]
  have hfilter : (Nat.divisors 1).filter (fun d => d ≠ 1) = ∅ := by
    ext d
    simp
  rw [hfilter]
  simp

noncomputable def centeredRamanujanPairCleanPeriodicGcdBaseWeight
    (q q' g h : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * ((Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ)))

noncomputable def centeredRamanujanPairCleanPeriodicGcdCaseScalar
    (q q' d : ℕ) : ℝ :=
  if 2 * d < Nat.gcd q q' then
    ((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))
  else if d = Nat.gcd q q' then
    ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))
  else
    ((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))

noncomputable def centeredRamanujanPairCleanPeriodicGcdTopHalfScalar
    (q q' d : ℕ) : ℝ :=
  if d = Nat.gcd q q' then
    ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))
  else
    ((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionSummand_eq_baseWeight_mul_caseScalar
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanPairCleanPeriodicGcdCorrectionSummand X q q' g h
      =
    centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
      * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' (Nat.gcd g h) := by
  by_cases h0 : 2 * Nat.gcd g h < Nat.gcd q q'
  · rw [centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
      rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_zero hq hq' hg hh h0,
      centeredRamanujanPairCleanPeriodicGcdBaseWeight,
      centeredRamanujanPairCleanPeriodicGcdCaseScalar]
    simp [h0]
    ring
  · by_cases h2 : Nat.gcd g h = Nat.gcd q q'
    · rw [centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
        rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_two hq hq' hg hh h2,
        centeredRamanujanPairCleanPeriodicGcdBaseWeight,
        centeredRamanujanPairCleanPeriodicGcdCaseScalar]
      have hnot0' : ¬ Nat.gcd q q' * 2 < Nat.gcd q q' := by
        have hge : Nat.gcd q q' ≤ Nat.gcd q q' * 2 := by
          exact Nat.le_mul_of_pos_right (Nat.gcd q q') (by norm_num : 0 < 2)
        exact not_lt_of_ge hge
      simp [h2, centeredRamanujanPairCleanPeriodicGcdCaseScalar, hnot0', Nat.mul_comm]
      ring
    · have hle : Nat.gcd q q' ≤ 2 * Nat.gcd g h := Nat.le_of_not_gt h0
      have hlt : Nat.gcd g h < Nat.gcd q q' := by
        exact lt_of_le_of_ne (gcd_g_h_le_gcd_q_q' hq' hg hh) h2
      rw [centeredRamanujanPairCleanPeriodicGcdCorrectionSummand,
        rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_case_one hq hq' hg hh hle hlt,
        centeredRamanujanPairCleanPeriodicGcdBaseWeight,
        centeredRamanujanPairCleanPeriodicGcdCaseScalar]
      simp [h0, h2]
      ring

noncomputable def centeredRamanujanPairCleanPeriodicGcdWeightAtGcd
    (q q' d : ℕ) : ℝ :=
  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
    ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
      if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0

private theorem sum_filter_even_divisors_dvd_reindexed_by_div
    {q d : ℕ} (hq : 1 ≤ q) (hdq : d ∣ q) (f : ℕ → ℝ) :
    (∑ g ∈ (q.divisors.filter Goldbach.Windows.IsEven).filter (fun g => d ∣ g), f g)
      =
    ∑ a ∈ (q / d).divisors.filter (fun a => Goldbach.Windows.IsEven (d * a)), f (d * a) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hqd0 : q / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos)
  refine Finset.sum_nbij' (i := fun g => g / d) (j := fun a => d * a) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rcases Finset.mem_filter.mp hg with ⟨hg0, hdg⟩
    rcases Finset.mem_filter.mp hg0 with ⟨hgdiv, hgeven⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · rw [Nat.mem_divisors]
      constructor
      · rw [Nat.dvd_div_iff_mul_dvd hdq]
        simpa [Nat.mul_div_cancel' hdg] using (Nat.mem_divisors.mp hgdiv).1
      · exact hqd0
    · have hg_eq : d * (g / d) = g := by
        simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdg)
      simpa [hg_eq] using hgeven
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨hadiv, haeven⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · refine Finset.mem_filter.mpr ?_
      constructor
      · rw [Nat.mem_divisors]
        constructor
        · rw [← Nat.mul_div_cancel' hdq]
          exact Nat.mul_dvd_mul_left d (Nat.mem_divisors.mp hadiv).1
        · exact hq0
      · simpa using haeven
    · exact dvd_mul_right d a
  · intro g hg
    rcases Finset.mem_filter.mp hg with ⟨_, hdg⟩
    simpa [Nat.mul_comm] using Nat.mul_div_cancel' hdg
  · intro a ha
    simpa [Nat.mul_comm] using Nat.mul_div_right a hdpos
  · intro g hg
    rcases Finset.mem_filter.mp hg with ⟨_, hdg⟩
    exact congrArg f (by simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdg).symm)

theorem centeredRamanujanPairCleanPeriodicGcdWeightAtGcd_eq_coprime_reindexed
    {q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hdq : d ∣ q) (hdq' : d ∣ q') :
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
      =
    ∑ a ∈ (q / d).divisors.filter (fun a => Goldbach.Windows.IsEven (d * a)),
      ∑ b ∈ (q' / d).divisors.filter (fun b => Goldbach.Windows.IsEven (d * b)),
        if Nat.Coprime a b then
          centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' (d * a) (d * b)
        else 0 := by
  let S := q.divisors.filter Goldbach.Windows.IsEven
  let T := q'.divisors.filter Goldbach.Windows.IsEven
  have hfiltered :
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        =
      ∑ g ∈ S.filter (fun g => d ∣ g),
        ∑ h ∈ T.filter (fun h => d ∣ h),
          if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0 := by
    unfold centeredRamanujanPairCleanPeriodicGcdWeightAtGcd
    have houter :
        (∑ g ∈ S,
          ∑ h ∈ T,
            if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0)
          =
        ∑ g ∈ S,
          if d ∣ g then
            ∑ h ∈ T.filter (fun h => d ∣ h),
              if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro g hg
      by_cases hdg : d ∣ g
      · rw [if_pos hdg]
        have hinner :
            (∑ h ∈ T,
              if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0)
              =
            ∑ h ∈ T.filter (fun h => d ∣ h),
              if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0 := by
          calc
            (∑ h ∈ T,
              if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0)
              =
            ∑ h ∈ T,
              if d ∣ h then
                if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro h hh
                by_cases hdh : d ∣ h
                · simp [hdh]
                · have hneq : Nat.gcd g h ≠ d := by
                    intro hgd
                    exact hdh (by rw [← hgd]; exact Nat.gcd_dvd_right g h)
                  simp [hdh, hneq]
            _ =
            ∑ h ∈ T.filter (fun h => d ∣ h),
              if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0 := by
                simp [Finset.sum_filter]
        exact hinner
      · have hzero :
          ∑ h ∈ T,
            (if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0)
            = 0 := by
          refine Finset.sum_eq_zero ?_
          intro h hh
          by_cases hgd : Nat.gcd g h = d
          · exfalso
            exact hdg (by rw [← hgd]; exact Nat.gcd_dvd_left g h)
          · simp [hgd]
        simp [hdg, hzero]
    rw [houter]
    simpa [S, T] using
      (Finset.sum_filter
        (s := S)
        (p := fun g => d ∣ g)
        (f := fun g =>
          ∑ h ∈ T.filter (fun h => d ∣ h),
            if Nat.gcd g h = d then centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h else 0)).symm
  rw [hfiltered]
  rw [sum_filter_even_divisors_dvd_reindexed_by_div (q := q) (d := d) hq hdq]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [sum_filter_even_divisors_dvd_reindexed_by_div (q := q') (d := d) hq' hdq']
  refine Finset.sum_congr rfl ?_
  intro b hb
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hcop_iff : Nat.gcd (d * a) (d * b) = d ↔ Nat.Coprime a b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    constructor
    · intro hgd
      have hmul : d * Nat.gcd a b = d * 1 := by
        simpa [Nat.gcd_mul_left, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hgd
      exact Nat.eq_of_mul_eq_mul_left hdpos hmul
    · intro hcop
      simpa [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.gcd_mul_left,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  by_cases hcop : Nat.Coprime a b
  · simp [hcop, hcop_iff.mpr hcop]
  · have hnotgd : Nat.gcd (d * a) (d * b) ≠ d := by
      intro hgd
      exact hcop (hcop_iff.mp hgd)
    simp [hcop, hnotgd]

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_zero
    {q q' d : ℕ} (h0 : 2 * d < Nat.gcd q q') :
    centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
      = ((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  unfold centeredRamanujanPairCleanPeriodicGcdCaseScalar
  simp [h0]

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_two
    {q q' d : ℕ} (h2 : d = Nat.gcd q q') :
    centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
      = ((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  have hnot0' : ¬ 2 * d < Nat.gcd q q' := by
    subst h2
    have hge : Nat.gcd q q' ≤ 2 * Nat.gcd q q' := by
      exact Nat.le_mul_of_pos_left (Nat.gcd q q') (by norm_num : 0 < 2)
    exact not_lt_of_ge hge
  unfold centeredRamanujanPairCleanPeriodicGcdCaseScalar
  rw [if_neg hnot0', if_pos h2]

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_one
    {q q' d : ℕ} (h0 : ¬ 2 * d < Nat.gcd q q') (h2 : d ≠ Nat.gcd q q') :
    centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
      = ((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)) := by
  unfold centeredRamanujanPairCleanPeriodicGcdCaseScalar
  simp [h0, h2]

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_nonpos_of_case_zero
    {q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (h0 : 2 * d < Nat.gcd q q') :
    centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d ≤ 0 := by
  rw [centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_zero h0]
  have hGpos : (0 : ℝ) < Nat.gcd q q' := by
    exact_mod_cast Nat.gcd_pos_of_pos_right q hq'
  nlinarith [div_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (le_of_lt hGpos)]

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_nonneg_of_case_two
    {q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hnotcop : ¬ Nat.Coprime q q')
    (h2 : d = Nat.gcd q q') :
    0 ≤ centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d := by
  rw [centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_two h2]
  have hGtwo_nat : 2 ≤ Nat.gcd q q' := by
    have hgcd_ne_one : Nat.gcd q q' ≠ 1 := by
      intro hgcd1
      exact hnotcop (Nat.coprime_iff_gcd_eq_one.mpr hgcd1)
    have hgcd_pos_nat : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_right q hq'
    have h1le : 1 ≤ Nat.gcd q q' := Nat.succ_le_of_lt hgcd_pos_nat
    exact lt_of_le_of_ne h1le (Ne.symm hgcd_ne_one)
  have hGpos : (0 : ℝ) < Nat.gcd q q' := by
    exact_mod_cast Nat.gcd_pos_of_pos_right q hq'
  have hGtwo : (2 : ℝ) ≤ Nat.gcd q q' := by exact_mod_cast hGtwo_nat
  have := (div_le_iff₀ hGpos).2 (by nlinarith [hGtwo] : (4 : ℝ) ≤ 2 * (Nat.gcd q q' : ℝ))
  nlinarith

private theorem centeredRamanujanPairCleanPeriodicGcdCorrectionSummand_eq_sum_gcdDivisors
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanPairCleanPeriodicGcdCorrectionSummand X q q' g h
      =
    ∑ d ∈ (Nat.gcd q q').divisors,
      if Nat.gcd g h = d then
        centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
          * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
      else 0 := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionSummand_eq_baseWeight_mul_caseScalar hq hq' hg hh]
  have hG0 : Nat.gcd q q' ≠ 0 := by
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_right q hq')
  have hmem : Nat.gcd g h ∈ (Nat.gcd q q').divisors := by
    rw [Nat.mem_divisors]
    exact ⟨gcd_g_h_dvd_gcd_q_q' hg hh, hG0⟩
  rw [← Finset.sum_filter]
  have hfilter :
      ((Nat.gcd q q').divisors.filter fun d => Nat.gcd g h = d) = {Nat.gcd g h} := by
    ext d
    by_cases hd : d = Nat.gcd g h
    · subst hd
      simp [hmem]
    · simp [hd, eq_comm]
  rw [hfilter]
  simp

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_partitionedByGcdDivisors
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          if Nat.gcd g h = d then
            centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
              * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
          else 0 := by
  unfold centeredRamanujanPairCleanPeriodicGcdCorrectionTerm
  trans
    ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
        ∑ d ∈ (Nat.gcd q q').divisors,
          if Nat.gcd g h = d then
            centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
              * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
          else 0
  · refine Finset.sum_congr rfl ?_
    intro g hg
    refine Finset.sum_congr rfl ?_
    intro h hh
    have hg' : g ∈ q.divisors := (Finset.mem_filter.mp hg).1
    have hh' : h ∈ q'.divisors := (Finset.mem_filter.mp hh).1
    exact centeredRamanujanPairCleanPeriodicGcdCorrectionSummand_eq_sum_gcdDivisors hq hq' hg' hh'
  · calc
      (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            ∑ d ∈ (Nat.gcd q q').divisors,
              if Nat.gcd g h = d then
                centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                  * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
              else 0)
          =
      (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
              if Nat.gcd g h = d then
                centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                  * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
              else 0) := by
        refine Finset.sum_congr rfl ?_
        intro g hg
        rw [Finset.sum_comm]
    _ =
      (∑ d ∈ (Nat.gcd q q').divisors,
          ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
            ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
              if Nat.gcd g h = d then
                centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                  * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
              else 0) := by
        rw [Finset.sum_comm]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_sum_weightAtGcd_mul_caseScalar
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    ∑ d ∈ (Nat.gcd q q').divisors,
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_partitionedByGcdDivisors
    (X := X) hq hq']
  refine Finset.sum_congr rfl ?_
  intro d hd
  unfold centeredRamanujanPairCleanPeriodicGcdWeightAtGcd
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro h hh
  by_cases hgd : Nat.gcd g h = d <;> simp [hgd]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_sum_weightAtGcd_mul_caseScalar_splitRegions
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
      +
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => d = Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
      +
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q' ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d) := by
  let G := Nat.gcd q q'
  let D := (Nat.gcd q q').divisors
  let f : ℕ → ℝ := fun d =>
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
      * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_sum_weightAtGcd_mul_caseScalar
    (X := X) hq hq']
  have hEq :
      (D.filter fun d => ¬ 2 * d < G).filter (fun d => d = G) = D.filter (fun d => d = G) := by
    ext d
    by_cases hd : d = G
    · subst hd
      have hle : G ≤ 2 * G := Nat.le_mul_of_pos_left G (by norm_num : 0 < 2)
      simp [hle]
    · simp [hd]
  calc
    ∑ d ∈ D, f d
      =
    (∑ d ∈ D.filter (fun d => 2 * d < G), f d)
      +
    ∑ d ∈ D.filter (fun d => ¬ 2 * d < G), f d := by
        simpa [D, f] using
          (Finset.sum_filter_add_sum_filter_not D (fun d => 2 * d < G) f).symm
    _ =
    (∑ d ∈ D.filter (fun d => 2 * d < G), f d)
      +
    ((∑ d ∈ (D.filter (fun d => ¬ 2 * d < G)).filter (fun d => d = G), f d)
      +
    ∑ d ∈ (D.filter (fun d => ¬ 2 * d < G)).filter (fun d => d ≠ G), f d) := by
        congr 1
        simpa using
          (Finset.sum_filter_add_sum_filter_not
            (D.filter (fun d => ¬ 2 * d < G))
            (fun d => d = G) f).symm
    _ =
    (∑ d ∈ D.filter (fun d => 2 * d < G), f d)
      +
    (∑ d ∈ D.filter (fun d => d = G), f d)
      +
    ∑ d ∈ D.filter (fun d => ¬ 2 * d < G ∧ d ≠ G), f d := by
        rw [hEq]
        simpa [add_assoc, Finset.filter_filter, and_left_comm, and_assoc]
    _ =
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
      +
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => d = Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
      +
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q' ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d) := by
        simpa [D, f, G, add_assoc, not_lt]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_explicitScalar_splitRegions
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      +
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => d = Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      +
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q' ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))) := by
  have hzero :
      (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
        =
      (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_zero]
    exact (Finset.mem_filter.mp hd).2
  have htwo :
      (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => d = Nat.gcd q q'),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
        =
      (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => d = Nat.gcd q q'),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_two]
    exact (Finset.mem_filter.mp hd).2
  have hone :
      (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q' ∧ d ≠ Nat.gcd q q'),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d)
        =
      (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q' ∧ d ≠ Nat.gcd q q'),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_case_one]
    · exact (Finset.mem_filter.mp hd).2.1
    · exact (Finset.mem_filter.mp hd).2.2
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_sum_weightAtGcd_mul_caseScalar_splitRegions
    (X := X) hq hq']
  rw [hzero, htwo, hone]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_smallRegion_add_topHalfSigned
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      +
    ∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d := by
  let G := Nat.gcd q q'
  let D := (Nat.gcd q q').divisors
  let Dtop := D.filter (fun d => ¬ 2 * d < G)
  let topLhs : ℝ :=
    (∑ d ∈ D.filter (fun d => d = G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      +
    ∑ d ∈ D.filter (fun d => ¬ 2 * d < G ∧ d ≠ G),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
  let topRhs : ℝ :=
    ∑ d ∈ Dtop,
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d
  have hEq :
      (Dtop.filter (fun d => d = G)) = D.filter (fun d => d = G) := by
    ext d
    by_cases hd : d = G
    · subst hd
      have hle : G ≤ 2 * G := Nat.le_mul_of_pos_left G (by norm_num : 0 < 2)
      simp [Dtop, D, G, hle]
    · simp [Dtop, D, G, hd]
  have hMidSet :
      (Dtop.filter (fun d => d ≠ G)) = D.filter (fun d => ¬ 2 * d < G ∧ d ≠ G) := by
    ext d
    simp [Dtop, D, G, and_left_comm, and_assoc]
  have hEdge :
      (∑ d ∈ D.filter (fun d => d = G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      =
      ∑ d ∈ Dtop.filter (fun d => d = G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d := by
    rw [hEq]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdEq : d = G := (Finset.mem_filter.mp hd).2
    subst d
    rw [centeredRamanujanPairCleanPeriodicGcdTopHalfScalar]
    simp [G]
  have hMid :
      (∑ d ∈ D.filter (fun d => ¬ 2 * d < G ∧ d ≠ G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      =
      ∑ d ∈ Dtop.filter (fun d => d ≠ G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d := by
    rw [hMidSet]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdNe : d ≠ G := (Finset.mem_filter.mp hd).2.2
    rw [centeredRamanujanPairCleanPeriodicGcdTopHalfScalar]
    have hdNe' : d ≠ Nat.gcd q q' := by simpa [G] using hdNe
    simp [hdNe', G]
  have htop : topLhs = topRhs := by
    let fTop : ℕ → ℝ := fun d =>
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d
    calc
      topLhs
        =
      (∑ d ∈ Dtop.filter (fun d => d = G),
          centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
            * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d)
        +
      ∑ d ∈ Dtop.filter (fun d => d ≠ G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d := by
            simp only [topLhs]
            rw [hEdge, hMid]
      _ = topRhs := by
            simpa [topRhs, fTop] using
              (Finset.sum_filter_add_sum_filter_not Dtop (fun d => d = G) fTop)
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_explicitScalar_splitRegions
    (X := X) hq hq']
  rw [add_assoc]
  change
    (∑ d ∈ D.filter (fun d => 2 * d < G),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      + topLhs
      =
    (∑ d ∈ D.filter (fun d => 2 * d < G),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      + topRhs
  simpa using congrArg
    (fun t =>
      (∑ d ∈ D.filter (fun d => 2 * d < G),
        centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
          * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
        + t) htop

theorem centeredRamanujanPairCleanPeriodicGcdTopHalfSignedSum_eq_edge_add_tail
    {q q' : ℕ} (hq' : 1 ≤ q') :
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d)
      =
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' (Nat.gcd q q')
      * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      +
    ∑ d ∈ ((Nat.gcd q q').divisors.filter
      fun d => Nat.gcd q q' ≤ 2 * d ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))) := by
  let G := Nat.gcd q q'
  let D := (Nat.gcd q q').divisors
  let Dtop := D.filter (fun d => ¬ 2 * d < G)
  let f : ℕ → ℝ := fun d =>
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
      * centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d
  have hG0 : G ≠ 0 := by
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_right q hq')
  have hGmem : G ∈ D := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, hG0⟩
  have hEdgeSet : Dtop.filter (fun d => d = G) = {G} := by
    ext d
    by_cases hd : d = G
    · subst hd
      have hle : G ≤ 2 * G := Nat.le_mul_of_pos_left G (by norm_num : 0 < 2)
      simp [Dtop, D, G, hGmem, hle]
    · simp [Dtop, D, G, hd]
  have hTailSet :
      Dtop.filter (fun d => d ≠ G)
        = D.filter (fun d => G ≤ 2 * d ∧ d ≠ G) := by
    ext d
    simp [Dtop, D, G, and_left_comm, and_assoc, not_lt]
  calc
    (∑ d ∈ Dtop, f d)
      =
    (∑ d ∈ Dtop.filter (fun d => d = G), f d)
      +
    ∑ d ∈ Dtop.filter (fun d => d ≠ G), f d := by
        simpa [f] using (Finset.sum_filter_add_sum_filter_not Dtop (fun d => d = G) f).symm
    _ =
    (∑ d ∈ ({G} : Finset ℕ), f d)
      +
    ∑ d ∈ D.filter (fun d => G ≤ 2 * d ∧ d ≠ G), f d := by
        rw [hEdgeSet, hTailSet]
    _ =
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' G
      * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      +
    ∑ d ∈ D.filter (fun d => G ≤ 2 * d ∧ d ≠ G), f d := by
        simp [f, centeredRamanujanPairCleanPeriodicGcdTopHalfScalar, G]
    _ =
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' (Nat.gcd q q')
      * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      +
    ∑ d ∈ ((Nat.gcd q q').divisors.filter
      fun d => Nat.gcd q q' ≤ 2 * d ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hdNe : d ≠ G := (Finset.mem_filter.mp hd).2.2
        have hdNe' : d ≠ Nat.gcd q q' := by simpa [G] using hdNe
        have hscalar :
            centeredRamanujanPairCleanPeriodicGcdTopHalfScalar q q' d
              = (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))) := by
          unfold centeredRamanujanPairCleanPeriodicGcdTopHalfScalar
          simp [hdNe']
        unfold f
        rw [hscalar]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_smallRegion_add_edge_add_topHalfTail
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      +
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' (Nat.gcd q q')
      * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
      +
    ∑ d ∈ ((Nat.gcd q q').divisors.filter
      fun d => Nat.gcd q q' ≤ 2 * d ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))) := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_smallRegion_add_topHalfSigned
    (X := X) hq hq']
  rw [centeredRamanujanPairCleanPeriodicGcdTopHalfSignedSum_eq_edge_add_tail (q := q) (q' := q') hq']
  simp [add_assoc]

theorem centeredRamanujanPairCleanPeriodicGcdTopHalfTailDivisors_eq_singleton_half_or_empty
    {q q' : ℕ} (hq' : 1 ≤ q') :
    ((Nat.gcd q q').divisors.filter
      fun d => Nat.gcd q q' ≤ 2 * d ∧ d ≠ Nat.gcd q q')
      =
    if 2 ∣ Nat.gcd q q' then {Nat.gcd q q' / 2} else ∅ := by
  let G := Nat.gcd q q'
  have hG0 : G ≠ 0 := by
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_right q hq')
  ext d
  by_cases h2G : 2 ∣ G
  · constructor
    · intro hd
      have hdDiv : d ∈ G.divisors := (Finset.mem_filter.mp hd).1
      have hdCond : G ≤ 2 * d ∧ d ≠ G := (Finset.mem_filter.mp hd).2
      rcases (Nat.mem_divisors.mp hdDiv).1 with ⟨k, hk⟩
      have hdpos : 0 < d := by
        apply Nat.pos_of_ne_zero
        intro hd0
        simp [hd0] at hk
        exact hG0 hk
      have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hk0
        rw [hk0, Nat.mul_zero] at hk
        exact hG0 hk
      have hk_le_two : k ≤ 2 := by
        rw [hk] at hdCond
        rw [Nat.mul_comm 2 d] at hdCond
        exact Nat.le_of_mul_le_mul_left hdCond.1 hdpos
      have hk_ne_one : k ≠ 1 := by
        intro hk1
        apply hdCond.2
        rw [hk, hk1, Nat.mul_one]
      have hk_two : k = 2 := by
        omega
      have hdEq : d = G / 2 := by
        refine (Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2) ?_).symm
        rw [hk, hk_two, Nat.mul_comm]
      rw [if_pos h2G]
      simpa [hdEq, G]
    · intro hd
      rw [if_pos h2G] at hd
      have hdMem : d ∈ ({G / 2} : Finset ℕ) := hd
      have hdEq : d = G / 2 := Finset.mem_singleton.mp hdMem
      rw [hdEq]
      have hGdiv : G / 2 ∣ G := Nat.div_dvd_of_dvd h2G
      have hGhalf_mem : G / 2 ∈ G.divisors := by
        rw [Nat.mem_divisors]
        exact ⟨hGdiv, hG0⟩
      have hGhalf_ne : G / 2 ≠ G := by
        intro hEq
        rcases h2G with ⟨m, hm⟩
        have hm' : G = m * 2 := by simpa [Nat.mul_comm] using hm
        have hmpos : 0 < m := by
          apply Nat.pos_of_ne_zero
          intro hm0
          rw [hm0, Nat.zero_mul] at hm'
          exact hG0 hm'
        have hdiv : G / 2 = m := Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2) hm'
        rw [hdiv, hm'] at hEq
        omega
      have hGhalf_top : G ≤ 2 * (G / 2) := by
        rcases h2G with ⟨m, hm⟩
        have hm' : G = m * 2 := by simpa [Nat.mul_comm] using hm
        rw [hm']
        simpa [Nat.mul_comm] using (le_rfl : m * 2 ≤ m * 2)
      exact Finset.mem_filter.mpr ⟨hGhalf_mem, ⟨hGhalf_top, hGhalf_ne⟩⟩
  · constructor
    · intro hd
      have hdDiv : d ∈ G.divisors := (Finset.mem_filter.mp hd).1
      have hdCond : G ≤ 2 * d ∧ d ≠ G := (Finset.mem_filter.mp hd).2
      rcases (Nat.mem_divisors.mp hdDiv).1 with ⟨k, hk⟩
      have hdpos : 0 < d := by
        apply Nat.pos_of_ne_zero
        intro hd0
        simp [hd0] at hk
        exact hG0 hk
      have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hk0
        rw [hk0, Nat.mul_zero] at hk
        exact hG0 hk
      have hk_le_two : k ≤ 2 := by
        rw [hk] at hdCond
        rw [Nat.mul_comm 2 d] at hdCond
        exact Nat.le_of_mul_le_mul_left hdCond.1 hdpos
      have hk_ne_one : k ≠ 1 := by
        intro hk1
        apply hdCond.2
        rw [hk, hk1, Nat.mul_one]
      have hk_two : k = 2 := by
        omega
      apply False.elim
      exact h2G ⟨d, by rw [hk, hk_two, Nat.mul_comm]⟩
    · intro hd
      rw [if_neg h2G] at hd
      have hempty : d ∈ (∅ : Finset ℕ) := hd
      exact False.elim (by simpa using hempty)

theorem centeredRamanujanPairCleanPeriodicGcdTopHalfTail_eq_half_or_zero
    {q q' : ℕ} (hq' : 1 ≤ q') :
    (∑ d ∈ ((Nat.gcd q q').divisors.filter
      fun d => Nat.gcd q q' ≤ 2 * d ∧ d ≠ Nat.gcd q q'),
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
      =
    if 2 ∣ Nat.gcd q q' then
      centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' (Nat.gcd q q' / 2)
        * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))
    else 0 := by
  rw [centeredRamanujanPairCleanPeriodicGcdTopHalfTailDivisors_eq_singleton_half_or_empty (q := q) (q' := q') hq']
  by_cases h2G : 2 ∣ Nat.gcd q q'
  · simp [h2G]
  · simp [h2G]

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_neg_two_of_coprime_moduli
    {q q' : ℕ} (hcop : Nat.Coprime q q') :
    centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' 1 = (-2 : ℝ) := by
  have hgcd1 : Nat.gcd q q' = 1 := Nat.Coprime.gcd_eq_one hcop
  rw [centeredRamanujanPairCleanPeriodicGcdCaseScalar, hgcd1]
  norm_num

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
        if Nat.gcd g h = 1 then
          centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h * (-2 : ℝ)
        else 0 := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_partitionedByGcdDivisors hq hq']
  have hgcd1 : Nat.gcd q q' = 1 := Nat.Coprime.gcd_eq_one hcop
  rw [hgcd1, Nat.divisors_one]
  simp [centeredRamanujanPairCleanPeriodicGcdCaseScalar_eq_neg_two_of_coprime_moduli hcop]

private theorem gcd_g_h_eq_one_of_coprime_moduli
    {q q' g h : ℕ} (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.gcd g h = 1 := by
  rw [← Nat.coprime_iff_gcd_eq_one]
  exact hcop.coprime_dvd_left (Nat.mem_divisors.mp hg).1 |>.coprime_dvd_right (Nat.mem_divisors.mp hh).1

noncomputable def centeredRamanujanPairCleanPeriodicGcdLeftFactor
    (q q' g : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q g
    * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * (Nat.totient (q / g) : ℝ))

noncomputable def centeredRamanujanPairCleanPeriodicGcdRightFactor
    (q' h : ℕ) : ℝ :=
  ramanujanGcdClassCoeff q' h * (Nat.totient (q' / h) : ℝ)

/-- The one-variable signed divisor sum left by the clean coprime branch.
It is a Möbius-totient convolution restricted to even gcd classes. -/
noncomputable def centeredRamanujanPairCleanPeriodicOneVariableBaseSum
    (q : ℕ) : ℝ :=
  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
    ramanujanGcdClassCoeff q g * (Nat.totient (q / g) : ℝ)

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_explicit
    (q : ℕ) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q
      =
    ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (q / g) : ℤ) : ℝ)
        * (Nat.totient g : ℝ))
        * (Nat.totient (q / g) : ℝ) := by
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum]
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [ramanujanGcdClassCoeff]

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_reducedModuli
    {q : ℕ} (hq : 1 ≤ q) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q
      =
    ∑ a ∈ q.divisors.filter (fun a => Goldbach.Windows.IsEven (q / a)),
      ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) a : ℤ) : ℝ)
        * (Nat.totient (q / a) : ℝ))
        * (Nat.totient a : ℝ) := by
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum]
  rw [sum_filter_isEven_divisors_eq_sum_filter_isEven_quotientDivisors hq
    (f := fun g => ramanujanGcdClassCoeff q g * (Nat.totient (q / g) : ℝ))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have haDiv : a ∈ q.divisors := (Finset.mem_filter.mp ha).1
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  rw [ramanujanGcdClassCoeff]
  rw [Nat.div_div_self (Nat.mem_divisors.mp haDiv).1 hq0]

private theorem not_isEven_divisor_of_not_isEven
    {q g : ℕ} (hqOdd : ¬ Goldbach.Windows.IsEven q) (hg : g ∈ q.divisors) :
    ¬ Goldbach.Windows.IsEven g := by
  intro hgEven
  have hg_dvd_q : g ∣ q := (Nat.mem_divisors.mp hg).1
  have h2g : 2 ∣ g := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hgEven)
  have h2q : 2 ∣ q := dvd_trans h2g hg_dvd_q
  exact hqOdd (Goldbach.Windows.isEven_of_even ((even_iff_two_dvd).2 h2q))

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_isEven
    {q : ℕ} (hqOdd : ¬ Goldbach.Windows.IsEven q) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q = 0 := by
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum]
  refine Finset.sum_eq_zero ?_
  intro g hg
  have hgDiv : g ∈ q.divisors := (Finset.mem_filter.mp hg).1
  have hgEven : Goldbach.Windows.IsEven g := (Finset.mem_filter.mp hg).2
  exact False.elim ((not_isEven_divisor_of_not_isEven hqOdd hgDiv) hgEven)

/-- Odd-part Möbius-totient convolution predicted by the one-variable audit. -/
noncomputable def centeredRamanujanPairCleanPeriodicOddPartBaseSum
    (n : ℕ) : ℝ :=
  ∑ b ∈ n.divisors,
    ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
      * (Nat.totient b : ℝ))
      * (Nat.totient (n / b) : ℝ)

private noncomputable def centeredRamanujanPairCleanPeriodicTotientAF :
    ArithmeticFunction ℝ :=
  ⟨fun n => (Nat.totient n : ℝ), by simp⟩

private noncomputable def centeredRamanujanPairCleanPeriodicOddPartCoeffAF :
    ArithmeticFunction ℝ :=
  (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ).pmul
    centeredRamanujanPairCleanPeriodicTotientAF)

private noncomputable def centeredRamanujanPairCleanPeriodicOddPartBaseAF :
    ArithmeticFunction ℝ :=
  centeredRamanujanPairCleanPeriodicOddPartCoeffAF
    * centeredRamanujanPairCleanPeriodicTotientAF

private theorem centeredRamanujanPairCleanPeriodicTotientAF_isMultiplicative :
    centeredRamanujanPairCleanPeriodicTotientAF.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ?_
  constructor
  · simp [centeredRamanujanPairCleanPeriodicTotientAF]
  · intro m n hm hn hcop
    simp [centeredRamanujanPairCleanPeriodicTotientAF, Nat.totient_mul hcop]

private theorem centeredRamanujanPairCleanPeriodicOddPartCoeffAF_isMultiplicative :
    centeredRamanujanPairCleanPeriodicOddPartCoeffAF.IsMultiplicative := by
  have hmu :
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.intCast ArithmeticFunction.isMultiplicative_moebius
  exact ArithmeticFunction.IsMultiplicative.pmul hmu
    centeredRamanujanPairCleanPeriodicTotientAF_isMultiplicative

private theorem centeredRamanujanPairCleanPeriodicOddPartBaseAF_isMultiplicative :
    centeredRamanujanPairCleanPeriodicOddPartBaseAF.IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.mul
    centeredRamanujanPairCleanPeriodicOddPartCoeffAF_isMultiplicative
    centeredRamanujanPairCleanPeriodicTotientAF_isMultiplicative

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_convolution
    (n : ℕ) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n
      =
    centeredRamanujanPairCleanPeriodicOddPartBaseAF n := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum,
    centeredRamanujanPairCleanPeriodicOddPartBaseAF,
    ArithmeticFunction.mul_apply]
  rw [← Nat.map_div_right_divisors]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro d hd
  simp [centeredRamanujanPairCleanPeriodicOddPartCoeffAF,
    centeredRamanujanPairCleanPeriodicTotientAF]

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_mul_of_coprime
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum (m * n)
      =
    centeredRamanujanPairCleanPeriodicOddPartBaseSum m
      * centeredRamanujanPairCleanPeriodicOddPartBaseSum n := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_convolution,
    centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_convolution,
    centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_convolution]
  exact ArithmeticFunction.IsMultiplicative.iff_ne_zero.mp
    centeredRamanujanPairCleanPeriodicOddPartBaseAF_isMultiplicative |>.2 hm hn hcop

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_factorization_prod
    {n : ℕ} (hn : n ≠ 0) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n
      =
    n.factorization.prod
      (fun p k => centeredRamanujanPairCleanPeriodicOddPartBaseSum (p ^ k)) := by
  calc
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n
      = centeredRamanujanPairCleanPeriodicOddPartBaseAF n := by
          rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_convolution]
    _ = n.factorization.prod
          (fun p k => centeredRamanujanPairCleanPeriodicOddPartBaseAF (p ^ k)) := by
          exact ArithmeticFunction.IsMultiplicative.multiplicative_factorization
            centeredRamanujanPairCleanPeriodicOddPartBaseAF
            centeredRamanujanPairCleanPeriodicOddPartBaseAF_isMultiplicative hn
    _ = n.factorization.prod
          (fun p k => centeredRamanujanPairCleanPeriodicOddPartBaseSum (p ^ k)) := by
          refine Finsupp.prod_congr ?_
          intro p
          intro hp
          rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_convolution]

private theorem div_prime_pow
    {p e i : ℕ} (hp : Nat.Prime p) (hi : i ≤ e) :
    p ^ e / p ^ i = p ^ (e - i) := by
  refine Nat.div_eq_of_eq_mul_left (pow_pos hp.pos i) ?_
  calc
    p ^ e = p ^ ((e - i) + i) := by rw [Nat.sub_add_cancel hi]
    _ = p ^ (e - i) * p ^ i := by rw [pow_add]

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime
    {p : ℕ} (hp : Nat.Prime p) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum p = 0 := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum, show p = p ^ 1 by simp]
  rw [Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have hpPowPos : 0 < p ^ 1 := by simpa using hp.pos
  rw [Nat.div_self hpPowPos]
  norm_num [ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, Nat.totient_one, Nat.totient_prime hp]

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_odd_prime_pow_succ_succ
    {p e : ℕ} (hp : Nat.Prime p) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum (p ^ (e + 2))
      =
    ((p ^ e : ℕ) : ℝ) * (p - 1) := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum, Nat.sum_divisors_prime_pow hp]
  let F : ℕ → ℝ := fun i =>
    ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (p ^ i) : ℤ) : ℝ)
      * (Nat.totient (p ^ i) : ℝ))
      * (Nat.totient (p ^ (e + 2) / p ^ i) : ℝ)
  have hsplit : e + 3 = 2 + (e + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have htail : ∑ x ∈ Finset.range (e + 1), F (2 + x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hmuZ : (ArithmeticFunction.moebius (p ^ (2 + x)) : ℤ) = 0 := by
      have hexp : 2 + x = Nat.succ (Nat.succ x) := by omega
      rw [hexp, ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero _)]
      have : ¬ Nat.succ (Nat.succ x) = 1 := by omega
      simp [this]
    simp [F, hmuZ]
  rw [htail, add_zero]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have hdiv0 : p ^ (e + 2) / p ^ 0 = p ^ (e + 2) := by simp
  have hdiv1 : p ^ (e + 2) / p ^ 1 = p ^ (e + 1) := by
    simpa using div_prime_pow hp (e := e + 2) (i := 1) (by omega)
  rw [hdiv0, hdiv1]
  have hphi_big :
      (Nat.totient (p ^ (e + 2)) : ℝ)
        = ((p ^ (e + 1) : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_prime_pow hp (show 0 < e + 2 by omega)
  have hphi_prev :
      (Nat.totient (p ^ (e + 1)) : ℝ)
        = ((p ^ e : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_prime_pow hp (show 0 < e + 1 by omega)
  have hpow :
      ((p ^ (e + 1) : ℕ) : ℝ) = (p : ℝ) * ((p ^ e : ℕ) : ℝ) := by
    rw [pow_succ]
    norm_num [mul_comm, mul_left_comm, mul_assoc]
  have hpowe : ((p ^ e : ℕ) : ℝ) = (p : ℝ) ^ e := by
    norm_num
  simp [F, ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_one, Nat.totient_prime hp]
  rw [hphi_big, hphi_prev, hpow]
  rw [Nat.cast_sub hp.one_le]
  rw [hpowe]
  ring

private theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime_pow_pos_of_two_le
    {p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k) :
    0 < centeredRamanujanPairCleanPeriodicOddPartBaseSum (p ^ k) := by
  have hk' : k = (k - 2) + 2 := by omega
  rw [hk']
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_odd_prime_pow_succ_succ hp]
  have hpow : 0 < ((p ^ (k - 2) : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hp.pos (k - 2)
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hpm1 : 0 < (p : ℝ) - 1 := by
    linarith
  exact mul_pos hpow hpm1

private theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime_pow_le_pow
    {p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum (p ^ k) ≤ ((p : ℝ) ^ k) := by
  have hk' : k = (k - 2) + 2 := by omega
  rw [hk']
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_odd_prime_pow_succ_succ hp]
  have hpow_cast : ((p ^ (k - 2) : ℕ) : ℝ) = (p : ℝ) ^ (k - 2) := by
    norm_num
  rw [hpow_cast]
  have hstep :
      (p : ℝ) ^ (k - 2) * ((p : ℝ) - 1)
        ≤ (p : ℝ) ^ (k - 2) * (p : ℝ) := by
    have hp_nonneg : 0 ≤ (p : ℝ) ^ (k - 2) := by positivity
    nlinarith
  have hpow_le :
      (p : ℝ) ^ (k - 2) * (p : ℝ) ≤ (p : ℝ) ^ ((k - 2) + 2) := by
    calc
      (p : ℝ) ^ (k - 2) * (p : ℝ)
          = (p : ℝ) ^ ((k - 2) + 1) := by
              rw [pow_succ']
              ring
      _ ≤ (p : ℝ) ^ ((k - 2) + 2) := by
              exact pow_le_pow_right₀ (by exact_mod_cast hp.one_le) (by omega)
  exact hstep.trans hpow_le

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_zero_of_factorization_eq_one
    {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) (hfact : n.factorization p = 1) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n = 0 := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_factorization_prod hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_eq_zero_iff.mpr
  have hdiv : p ∣ n := by
    exact (Nat.Prime.dvd_iff_one_le_factorization hp hn).2 (by simpa [hfact])
  have hp_mem : p ∈ n.primeFactors := by
    exact (Nat.mem_primeFactors).2 ⟨hp, hdiv, hn⟩
  refine ⟨p, hp_mem, ?_⟩
  simpa [hfact] using centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime hp

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_pos_of_factorization_two_le
    {n : ℕ} (hn : n ≠ 0)
    (hpow : ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p) :
    0 < centeredRamanujanPairCleanPeriodicOddPartBaseSum n := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_factorization_prod hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_pos ?_
  intro p hp
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  exact centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime_pow_pos_of_two_le
    hpPrime (hpow p hp)

private theorem totient_two_mul_eq_totient_of_odd
    {d : ℕ} (hdOdd : Odd d) :
    Nat.totient (2 * d) = Nat.totient d := by
  have hcop : Nat.Coprime 2 d := by
    simpa using hdOdd.coprime_two_left
  rw [Nat.totient_mul hcop]
  norm_num

private theorem moebius_two_mul_eq_neg_of_odd
    {d : ℕ} (hdOdd : Odd d) :
    (ArithmeticFunction.moebius (2 * d) : ℤ)
      = -(ArithmeticFunction.moebius d : ℤ) := by
  have hcop : Nat.Coprime 2 d := by
    simpa using hdOdd.coprime_two_left
  have hg : Nat.gcd 2 d = 1 := hcop.gcd_eq_one
  calc
    (ArithmeticFunction.moebius (2 * d) : ℤ)
        =
      (ArithmeticFunction.moebius 2 : ℤ) * (ArithmeticFunction.moebius d : ℤ) := by
        exact
          (ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
            (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))
            ArithmeticFunction.isMultiplicative_moebius hg)
    _ = (-1 : ℤ) * (ArithmeticFunction.moebius d : ℤ) := by
        rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    _ = -(ArithmeticFunction.moebius d : ℤ) := by ring

private theorem totient_four_mul_eq_two_mul_totient_of_odd
    {d : ℕ} (hdOdd : Odd d) :
    Nat.totient (4 * d) = 2 * Nat.totient d := by
  have hcop : Nat.Coprime 4 d := by
    have hcop2 : Nat.Coprime 2 d := by
      simpa using hdOdd.coprime_two_left
    simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow_left 2
  have hphi4 : Nat.totient 4 = 2 := by
    simpa using (Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2))
  rw [Nat.totient_mul hcop, hphi4]

private theorem totient_two_pow_mul_eq_pow_mul_totient_of_odd
    {k d : ℕ} (hk : 1 ≤ k) (hdOdd : Odd d) :
    Nat.totient ((2 ^ k) * d) = 2 ^ (k - 1) * Nat.totient d := by
  have hcop : Nat.Coprime (2 ^ k) d := (hdOdd.coprime_two_left).pow_left k
  have hphi2k : Nat.totient (2 ^ k) = 2 ^ (k - 1) := by
    simpa using (Nat.totient_prime_pow Nat.prime_two hk)
  rw [Nat.totient_mul hcop, hphi2k]

private theorem oneVariable_four_split_pair_summand_eq_oddPart_summand
    {b m : ℕ} (hbOdd : Odd b) (hmOdd : Odd m) :
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
        * (Nat.totient (4 * m) : ℝ))
        * (Nat.totient b : ℝ))
      +
      (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
        * (Nat.totient (2 * m) : ℝ))
        * (Nat.totient (2 * b) : ℝ))
      =
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
        * (Nat.totient b : ℝ))
        * (Nat.totient m : ℝ)) := by
  have hmu2b :
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
        =
      -(((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ) := by
    exact_mod_cast (moebius_two_mul_eq_neg_of_odd hbOdd)
  have hphi4m : (Nat.totient (4 * m) : ℝ) = (2 : ℝ) * (Nat.totient m : ℝ) := by
    norm_num [totient_four_mul_eq_two_mul_totient_of_odd hmOdd]
  have hphi2m : (Nat.totient (2 * m) : ℝ) = (Nat.totient m : ℝ) := by
    norm_num [totient_two_mul_eq_totient_of_odd hmOdd]
  have hphi2b : (Nat.totient (2 * b) : ℝ) = (Nat.totient b : ℝ) := by
    norm_num [totient_two_mul_eq_totient_of_odd hbOdd]
  rw [hmu2b, hphi4m, hphi2m, hphi2b]
  ring

private theorem oneVariable_twoPow_split_pair_summand_doubles
    {k b m : ℕ} (hk : 2 ≤ k) (hbOdd : Odd b) (hmOdd : Odd m) :
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
        * (Nat.totient ((2 ^ (k + 1)) * m) : ℝ))
        * (Nat.totient b : ℝ))
      +
      (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
        * (Nat.totient ((2 ^ k) * m) : ℝ))
        * (Nat.totient (2 * b) : ℝ))
      =
    (2 : ℝ) *
      (((((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
          * (Nat.totient ((2 ^ k) * m) : ℝ))
          * (Nat.totient b : ℝ))
        +
        (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
          * (Nat.totient ((2 ^ (k - 1)) * m) : ℝ))
          * (Nat.totient (2 * b) : ℝ)))) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hkprev : 1 ≤ k - 1 := by omega
  have hmu2b :
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
        =
      -(((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ) := by
    exact_mod_cast (moebius_two_mul_eq_neg_of_odd hbOdd)
  have hphi_k1m :
      (Nat.totient ((2 ^ (k + 1)) * m) : ℝ)
        =
      ((2 ^ k : ℕ) : ℝ) * (Nat.totient m : ℝ) := by
    norm_num [totient_two_pow_mul_eq_pow_mul_totient_of_odd (k := k + 1) (d := m) (by omega) hmOdd]
  have hphi_km :
      (Nat.totient ((2 ^ k) * m) : ℝ)
        =
      ((2 ^ (k - 1) : ℕ) : ℝ) * (Nat.totient m : ℝ) := by
    norm_num [totient_two_pow_mul_eq_pow_mul_totient_of_odd (k := k) (d := m) hk1 hmOdd]
  have hphi_prev_m :
      (Nat.totient ((2 ^ (k - 1)) * m) : ℝ)
        =
      ((2 ^ (k - 2) : ℕ) : ℝ) * (Nat.totient m : ℝ) := by
    have hkcalc : k - 1 - 1 = k - 2 := by omega
    simpa [hkcalc] using
      (show (Nat.totient ((2 ^ (k - 1)) * m) : ℝ)
          = ((2 ^ ((k - 1) - 1) : ℕ) : ℝ) * (Nat.totient m : ℝ) by
            norm_num [totient_two_pow_mul_eq_pow_mul_totient_of_odd (k := k - 1) (d := m) hkprev hmOdd])
  have hphi2b : (Nat.totient (2 * b) : ℝ) = (Nat.totient b : ℝ) := by
    norm_num [totient_two_mul_eq_totient_of_odd hbOdd]
  have hpowk : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) * ((2 ^ (k - 1) : ℕ) : ℝ) := by
    have hkcalc : k = (k - 1) + 1 := by omega
    rw [hkcalc, pow_succ]
    norm_num [mul_comm, mul_left_comm, mul_assoc]
  have hpowprev : ((2 ^ (k - 1) : ℕ) : ℝ) = (2 : ℝ) * ((2 ^ (k - 2) : ℕ) : ℝ) := by
    have hkcalc : k - 1 = (k - 2) + 1 := by omega
    rw [hkcalc, pow_succ]
    norm_num [mul_comm, mul_left_comm, mul_assoc]
  rw [hmu2b, hphi_k1m, hphi_km, hphi_prev_m, hphi2b]
  rw [hpowk, hpowprev]
  ring

private theorem two_pow_mul_eq_two_mul_two_pow_pred
    {k : ℕ} (hk : 1 ≤ k) :
    2 ^ k = 2 * 2 ^ (k - 1) := by
  have hkcalc : k = Nat.succ (k - 1) := by omega
  nth_rw 1 [hkcalc]
  rw [pow_succ]
  simpa [Nat.mul_comm]

private theorem div_two_pow_mul_by_two_mul_of_dvd
    {k n b : ℕ} (hk : 1 ≤ k) (hb : b ∈ n.divisors) :
    ((2 ^ k) * n) / (2 * b) = (2 ^ (k - 1)) * (n / b) := by
  have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := two_pow_mul_eq_two_mul_two_pow_pred hk
  have hbpos : 0 < b := Nat.pos_of_mem_divisors hb
  refine Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 * b) ?_
  calc
    (2 ^ k) * n = (2 * 2 ^ (k - 1)) * n := by rw [hkpow]
    _ = (2 * 2 ^ (k - 1)) * ((n / b) * b) := by rw [Nat.div_mul_cancel hb_dvd_n]
    _ = ((2 ^ (k - 1)) * (n / b)) * (2 * b) := by ring

private theorem moebius_eq_zero_of_four_dvd
    {a : ℕ} (h4 : 4 ∣ a) :
    (ArithmeticFunction.moebius a : ℤ) = 0 := by
  have hnsq : ¬ Squarefree a := by
    intro hsq
    have hsquarefree := Nat.squarefree_iff_prime_squarefree.mp hsq
    exact hsquarefree 2 Nat.prime_two (by simpa using h4)
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq

private theorem mem_two_pow_mul_odd_branch_left
    {k n b : ℕ} (hk : 2 ≤ k) (hnOdd : Odd n) (hb : b ∈ n.divisors) :
    b ∈ ((2 ^ k) * n).divisors.filter
      (fun a => Goldbach.Windows.IsEven (((2 ^ k) * n) / a)) := by
  have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hnOdd
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right hb_dvd_n (2 ^ k), by positivity⟩
  · have hquot : ((2 ^ k) * n) / b = (2 ^ k) * (n / b) := by
      rw [Nat.mul_div_assoc (2 ^ k) hb_dvd_n]
    rw [hquot]
    have hk1 : 1 ≤ k := le_trans (by norm_num) hk
    exact Goldbach.Windows.isEven_of_even <|
      (even_iff_two_dvd).2 (dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.ne_of_gt hk1)) _)

private theorem mem_two_pow_mul_odd_branch_right
    {k n b : ℕ} (hk : 2 ≤ k) (hnOdd : Odd n) (hb : b ∈ n.divisors) :
    2 * b ∈ ((2 ^ k) * n).divisors.filter
      (fun a => Goldbach.Windows.IsEven (((2 ^ k) * n) / a)) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  refine Finset.mem_filter.mpr ?_
  constructor
  · have hb_dvd_rest : b ∣ (2 ^ (k - 1)) * n := dvd_mul_of_dvd_right hb_dvd_n (2 ^ (k - 1))
    have hdiv : 2 * b ∣ 2 * ((2 ^ (k - 1)) * n) := Nat.mul_dvd_mul_left 2 hb_dvd_rest
    have hkpow : (2 ^ k) * n = 2 * ((2 ^ (k - 1)) * n) := by
      rw [two_pow_mul_eq_two_mul_two_pow_pred hk1]
      ring
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by
      intro hn
      subst n
      norm_num at hnOdd)
    exact Nat.mem_divisors.mpr ⟨hkpow ▸ hdiv, by positivity⟩
  · rw [div_two_pow_mul_by_two_mul_of_dvd hk1 hb]
    have hk2 : 1 ≤ k - 1 := by omega
    exact Goldbach.Windows.isEven_of_even <|
      (even_iff_two_dvd).2 (dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.ne_of_gt hk2)) _)

private theorem moebius_eq_zero_of_mem_two_pow_mul_odd_filter_not_branch
    {k n a : ℕ} (hk : 2 ≤ k) (hnOdd : Odd n)
    (ha : a ∈ ((2 ^ k) * n).divisors.filter
      (fun a => Goldbach.Windows.IsEven (((2 ^ k) * n) / a)))
    (hnotLeft : a ∉ n.divisors)
    (hnotRight : ¬ ∃ b, b ∈ n.divisors ∧ a = 2 * b) :
    (ArithmeticFunction.moebius a : ℤ) = 0 := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hkprev : 1 ≤ k - 1 := by omega
  have haDiv : a ∈ ((2 ^ k) * n).divisors := (Finset.mem_filter.mp ha).1
  have ha_dvd_q : a ∣ (2 ^ k) * n := (Nat.mem_divisors.mp haDiv).1
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hnOdd
  rcases Nat.even_or_odd a with haEven | haOdd
  · rcases (even_iff_two_dvd).1 haEven with ⟨c, rfl⟩
    have hc_dvd_qprev : c ∣ (2 ^ (k - 1)) * n := by
      rcases ha_dvd_q with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      apply Nat.mul_left_cancel (by norm_num : 0 < 2)
      calc
        2 * ((2 ^ (k - 1)) * n) = (2 ^ k) * n := by
          rw [two_pow_mul_eq_two_mul_two_pow_pred hk1]
          ring
        _ = (2 * c) * m := hm
        _ = 2 * (c * m) := by ring
    rcases Nat.even_or_odd c with hcEven | hcOdd
    · rcases (even_iff_two_dvd).1 hcEven with ⟨d, hd⟩
      have h4 : 4 ∣ 2 * c := by
        refine ⟨d, ?_⟩
        rw [hd]
        ring
      simpa using moebius_eq_zero_of_four_dvd h4
    · have hcop : Nat.Coprime c (2 ^ (k - 1)) := by
        simpa [Nat.coprime_comm] using (hcOdd.coprime_two_right.pow_right (k - 1))
      have hc_dvd_n : c ∣ n := by
        exact (hcop.dvd_mul_right (m := n)).1 (by simpa [Nat.mul_comm] using hc_dvd_qprev)
      have hc_mem : c ∈ n.divisors := Nat.mem_divisors.mpr ⟨hc_dvd_n, hn0⟩
      exact False.elim (hnotRight ⟨c, hc_mem, rfl⟩)
  · have hcop : Nat.Coprime a (2 ^ k) := by
      simpa [Nat.coprime_comm] using (haOdd.coprime_two_right.pow_right k)
    have ha_dvd_n : a ∣ n := by
      exact (hcop.dvd_mul_right (m := n)).1 (by simpa [Nat.mul_comm] using ha_dvd_q)
    exact False.elim (hnotLeft (Nat.mem_divisors.mpr ⟨ha_dvd_n, hn0⟩))

private theorem odd_div_of_dvd_odd
    {n a : ℕ} (hnOdd : Odd n) (ha : a ∣ n) :
    Odd (n / a) := by
  refine Nat.not_even_iff_odd.mp ?_
  intro hEven
  have h2quot : 2 ∣ n / a := (even_iff_two_dvd).1 hEven
  have hquot_dvd : n / a ∣ n := by
    exact Nat.div_dvd_of_dvd ha
  have h2n : 2 ∣ n := dvd_trans h2quot hquot_dvd
  exact (Nat.not_even_iff_odd.mpr hnOdd) ((even_iff_two_dvd).2 h2n)

private theorem odd_of_mem_divisors_odd
    {n a : ℕ} (hnOdd : Odd n) (ha : a ∈ n.divisors) :
    Odd a := by
  refine Nat.not_even_iff_odd.mp ?_
  intro haEven
  have h2a : 2 ∣ a := (even_iff_two_dvd).1 haEven
  have h2n : 2 ∣ n := dvd_trans h2a (Nat.mem_divisors.mp ha).1
  exact (Nat.not_even_iff_odd.mpr hnOdd) ((even_iff_two_dvd).2 h2n)

private theorem mem_two_mul_odd_divisors_iff
    {n a : ℕ} (hnOdd : Odd n) :
    a ∈ (2 * n).divisors
      ↔ a ∈ n.divisors ∨ ∃ b, b ∈ n.divisors ∧ a = 2 * b := by
  constructor
  · intro ha
    rcases Nat.mem_divisors.mp ha with ⟨ha_dvd_2n, h2n0⟩
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      norm_num at hnOdd
    by_cases haEven : Goldbach.Windows.IsEven a
    · have h2a : 2 ∣ a := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven haEven)
      rcases h2a with ⟨b, hb⟩
      have hb_dvd_n : b ∣ n := by
        rcases ha_dvd_2n with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        apply Nat.mul_left_cancel (by norm_num : 0 < 2)
        calc
          2 * n = a * c := hc
          _ = (2 * b) * c := by rw [hb]
          _ = 2 * (b * c) := by ring
      right
      exact ⟨b, Nat.mem_divisors.mpr ⟨hb_dvd_n, hn0⟩, hb⟩
    · have haOdd : Odd a := by
        refine Nat.not_even_iff_odd.mp ?_
        intro hEven
        exact haEven (Goldbach.Windows.isEven_of_even hEven)
      have hcop : Nat.Coprime a 2 := by
        simpa using haOdd.coprime_two_right
      have ha_dvd_n : a ∣ n := by
        exact (hcop.dvd_mul_right (m := n)).1 (by simpa [mul_comm] using ha_dvd_2n)
      left
      exact Nat.mem_divisors.mpr ⟨ha_dvd_n, hn0⟩
  · intro ha
    rcases ha with ha | ⟨b, hb, rfl⟩
    · rcases Nat.mem_divisors.mp ha with ⟨ha_dvd_n, hn0⟩
      exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right ha_dvd_n 2, by positivity⟩
    · rcases Nat.mem_divisors.mp hb with ⟨hb_dvd_n, hn0⟩
      exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_left 2 hb_dvd_n, by positivity⟩

private theorem mem_two_mul_odd_divisors_filter_even_quotient_iff
    {n a : ℕ} (hnOdd : Odd n) :
    a ∈ (2 * n).divisors.filter (fun a => Goldbach.Windows.IsEven ((2 * n) / a))
      ↔ a ∈ n.divisors := by
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨haDiv2n, hEvenQuot⟩
    rcases Nat.mem_divisors.mp haDiv2n with ⟨ha_dvd_2n, h2n0⟩
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      norm_num at hnOdd
    have h2quot : 2 ∣ (2 * n) / a :=
      (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hEvenQuot)
    rcases h2quot with ⟨m, hm⟩
    have hmul : ((2 * n) / a) * a = 2 * n := Nat.div_mul_cancel ha_dvd_2n
    have hcancel : m * a = n := by
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) <| by
        calc
          2 * (m * a) = (2 * m) * a := by ring
          _ = ((2 * n) / a) * a := by rw [← hm]
          _ = 2 * n := hmul
    refine Nat.mem_divisors.mpr ?_
    exact ⟨⟨m, by rw [mul_comm, hcancel]⟩, hn0⟩
  · intro ha
    rcases Nat.mem_divisors.mp ha with ⟨ha_dvd_n, hn0⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right ha_dvd_n 2, by positivity⟩
    · have hquot : (2 * n) / a = 2 * (n / a) := by
        rw [Nat.mul_div_assoc 2 ha_dvd_n]
      rw [hquot]
      dsimp [Goldbach.Windows.IsEven]
      omega

private theorem div_four_mul_by_two_mul_of_dvd
    {n b : ℕ} (hb : b ∈ n.divisors) :
    (4 * n) / (2 * b) = 2 * (n / b) := by
  have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have hbpos : 0 < b := Nat.pos_of_mem_divisors hb
  refine Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 * b) ?_
  calc
    4 * n = 4 * ((n / b) * b) := by rw [Nat.div_mul_cancel hb_dvd_n]
    _ = (2 * (n / b)) * (2 * b) := by ring

private theorem mem_four_mul_odd_divisors_filter_even_quotient_iff
    {n a : ℕ} (hnOdd : Odd n) :
    a ∈ (4 * n).divisors.filter (fun a => Goldbach.Windows.IsEven ((4 * n) / a))
      ↔ a ∈ n.divisors ∨ ∃ b, b ∈ n.divisors ∧ a = 2 * b := by
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨haDiv4n, hEvenQuot⟩
    rcases Nat.mem_divisors.mp haDiv4n with ⟨ha_dvd_4n, h4n0⟩
    have h2quot : 2 ∣ (4 * n) / a :=
      (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hEvenQuot)
    rcases h2quot with ⟨m, hm⟩
    have hmul : ((4 * n) / a) * a = 4 * n := Nat.div_mul_cancel ha_dvd_4n
    have ha_dvd_2n : a ∣ 2 * n := by
      refine ⟨m, ?_⟩
      apply Nat.mul_left_cancel (by norm_num : 0 < 2)
      calc
        2 * (2 * n) = 4 * n := by ring
        _ = ((4 * n) / a) * a := hmul.symm
        _ = (2 * m) * a := by rw [← hm]
        _ = 2 * (a * m) := by ring
    have h2n0 : 2 * n ≠ 0 := by
      intro h
      exact h4n0 (by nlinarith)
    have ha2 : a ∈ (2 * n).divisors := Nat.mem_divisors.mpr ⟨ha_dvd_2n, h2n0⟩
    exact (mem_two_mul_odd_divisors_iff hnOdd).1 ha2
  · intro ha
    rcases ha with ha | ⟨b, hb, rfl⟩
    · have ha_dvd_n : a ∣ n := (Nat.mem_divisors.mp ha).1
      have hnpos : 0 < n := Nat.pos_of_ne_zero (by
        intro hn
        subst n
        norm_num at hnOdd)
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right ha_dvd_n 4, by nlinarith⟩
      · have hquot : (4 * n) / a = 4 * (n / a) := by
          rw [Nat.mul_div_assoc 4 ha_dvd_n]
        rw [hquot]
        dsimp [Goldbach.Windows.IsEven]
        omega
    · refine Finset.mem_filter.mpr ?_
      constructor
      · have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
        have hnpos : 0 < n := Nat.pos_of_ne_zero (by
          intro hn
          subst n
          norm_num at hnOdd)
        exact Nat.mem_divisors.mpr ⟨by
          rcases hb_dvd_n with ⟨c, hc⟩
          refine ⟨2 * c, ?_⟩
          calc
            4 * n = 4 * (b * c) := by rw [hc]
            _ = (2 * b) * (2 * c) := by ring, by nlinarith⟩
      · rw [div_four_mul_by_two_mul_of_dvd hb]
        dsimp [Goldbach.Windows.IsEven]
        omega

private theorem oneVariableBaseSum_four_mul_odd_eq_branchPairSum
    {n : ℕ} (hnOdd : Odd n) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum (4 * n)
      =
    ∑ b ∈ n.divisors,
      ((((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
          * (Nat.totient ((4 * n) / b) : ℝ))
          * (Nat.totient b : ℝ))
      +
      (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
          * (Nat.totient ((4 * n) / (2 * b)) : ℝ))
          * (Nat.totient (2 * b) : ℝ))) := by
  have hq : 1 ≤ 4 * n := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by
      intro hn
      subst n
      norm_num at hnOdd)
    nlinarith
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_reducedModuli hq]
  let f : ℕ → ℝ := fun a =>
    ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) a : ℤ) : ℝ)
      * (Nat.totient ((4 * n) / a) : ℝ))
      * (Nat.totient a : ℝ)
  have hbij :
      (∑ x ∈ n.divisors.disjSum n.divisors,
        match x with
        | Sum.inl b => f b
        | Sum.inr b => f (2 * b))
        =
      ∑ a ∈ (4 * n).divisors.filter (fun a => Goldbach.Windows.IsEven ((4 * n) / a)),
        f a := by
    refine Finset.sum_bij
      (s := n.divisors.disjSum n.divisors)
      (t := (4 * n).divisors.filter (fun a => Goldbach.Windows.IsEven ((4 * n) / a)))
      (f := fun x : ℕ ⊕ ℕ =>
        match x with
        | Sum.inl b => f b
        | Sum.inr b => f (2 * b))
      (g := f)
      (i := fun x _ => match x with | Sum.inl b => b | Sum.inr b => 2 * b)
      ?_ ?_ ?_ ?_
    · intro x hx
      cases x with
      | inl b =>
          have hb : b ∈ n.divisors := by simpa using (Finset.inl_mem_disjSum.mp hx)
          exact (mem_four_mul_odd_divisors_filter_even_quotient_iff hnOdd).2 (Or.inl hb)
      | inr b =>
          have hb : b ∈ n.divisors := by simpa using (Finset.inr_mem_disjSum.mp hx)
          exact (mem_four_mul_odd_divisors_filter_even_quotient_iff hnOdd).2
            (Or.inr ⟨b, hb, rfl⟩)
    · intro x hx y hy hxy
      cases x
      · rename_i bx
        cases y
        · rename_i byv
          simp at hxy
          simp [hxy]
        · rename_i byv
          have hbx : bx ∈ n.divisors := by simpa using (Finset.inl_mem_disjSum.mp hx)
          have hbxEven : Goldbach.Windows.IsEven bx := by
            simp at hxy
            rw [hxy]
            dsimp [Goldbach.Windows.IsEven]
            omega
          have hnNotEven : ¬ Goldbach.Windows.IsEven n := by
            intro hnEven
            exact (Nat.not_even_iff_odd.mpr hnOdd) (Goldbach.Windows.even_of_isEven hnEven)
          exact False.elim ((not_isEven_divisor_of_not_isEven hnNotEven hbx) hbxEven)
      · rename_i bx
        cases y
        · rename_i byv
          have hby : byv ∈ n.divisors := by simpa using (Finset.inl_mem_disjSum.mp hy)
          have hbyEven : Goldbach.Windows.IsEven byv := by
            simp at hxy
            rw [← hxy]
            dsimp [Goldbach.Windows.IsEven]
            omega
          have hnNotEven : ¬ Goldbach.Windows.IsEven n := by
            intro hnEven
            exact (Nat.not_even_iff_odd.mpr hnOdd) (Goldbach.Windows.even_of_isEven hnEven)
          exact False.elim ((not_isEven_divisor_of_not_isEven hnNotEven hby) hbyEven)
        · rename_i byv
          have h : bx = byv := Nat.mul_left_cancel (by norm_num : 0 < 2) hxy
          simp [h]
    · intro a ha
      rcases (mem_four_mul_odd_divisors_filter_even_quotient_iff hnOdd).1 ha with ha' | ⟨b, hb, hEq⟩
      · refine ⟨Sum.inl a, ?_, rfl⟩
        rw [Finset.inl_mem_disjSum]
        exact ha'
      · refine ⟨Sum.inr b, ?_, hEq.symm⟩
        rw [Finset.inr_mem_disjSum]
        exact hb
    · intro x hx
      cases x <;> rfl
  rw [← hbij, Finset.sum_disjSum, ← Finset.sum_add_distrib]

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_four_mul_odd
    {n : ℕ} (hnOdd : Odd n) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum (4 * n)
      =
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n := by
  rw [oneVariableBaseSum_four_mul_odd_eq_branchPairSum hnOdd]
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum]
  refine Finset.sum_congr rfl ?_
  intro b hb
  have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have hbOdd : Odd b := odd_of_mem_divisors_odd hnOdd hb
  have hquotOdd : Odd (n / b) := odd_div_of_dvd_odd hnOdd hb_dvd_n
  have hquot4 : (4 * n) / b = 4 * (n / b) := by
    rw [Nat.mul_div_assoc 4 hb_dvd_n]
  have hquot2 : (4 * n) / (2 * b) = 2 * (n / b) :=
    div_four_mul_by_two_mul_of_dvd hb
  rw [hquot4, hquot2]
  exact oneVariable_four_split_pair_summand_eq_oddPart_summand hbOdd hquotOdd

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_mul_odd
    {n : ℕ} (hnOdd : Odd n) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum (2 * n)
      =
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n := by
  have hq : 1 ≤ 2 * n := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by
      intro hn
      subst n
      norm_num at hnOdd)
    nlinarith
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_reducedModuli hq]
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum]
  have hset :
      (2 * n).divisors.filter (fun a => Goldbach.Windows.IsEven ((2 * n) / a))
        = n.divisors := by
    ext a
    exact mem_two_mul_odd_divisors_filter_even_quotient_iff hnOdd
  rw [hset]
  apply Finset.sum_congr rfl
  intro a ha
  · have ha_dvd_n : a ∣ n := (Nat.mem_divisors.mp ha).1
    have hquot : (2 * n) / a = 2 * (n / a) := by
      rw [Nat.mul_div_assoc 2 ha_dvd_n]
    have hOddQuot : Odd (n / a) := odd_div_of_dvd_odd hnOdd ha_dvd_n
    rw [hquot, totient_two_mul_eq_totient_of_odd hOddQuot]
    ring

private theorem oneVariableBaseSum_two_pow_mul_odd_eq_branchPairSum
    {k n : ℕ} (hk : 2 ≤ k) (hnOdd : Odd n) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum ((2 ^ k) * n)
      =
    ∑ b ∈ n.divisors,
      ((((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) b : ℤ) : ℝ)
          * (Nat.totient (((2 ^ k) * n) / b) : ℝ))
          * (Nat.totient b : ℝ))
      +
      (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) (2 * b) : ℤ) : ℝ)
          * (Nat.totient (((2 ^ k) * n) / (2 * b)) : ℝ))
          * (Nat.totient (2 * b) : ℝ))) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hq : 1 ≤ (2 ^ k) * n := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by
      intro hn
      subst n
      norm_num at hnOdd)
    have hpowpos : 0 < 2 ^ k := by positivity
    nlinarith
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_reducedModuli hq]
  let f : ℕ → ℝ := fun a =>
    ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) a : ℤ) : ℝ)
      * (Nat.totient (((2 ^ k) * n) / a) : ℝ))
      * (Nat.totient a : ℝ)
  let s :=
    ((2 ^ k) * n).divisors.filter
      (fun a => Goldbach.Windows.IsEven (((2 ^ k) * n) / a))
  let pred : ℕ → Prop := fun a => a ∈ n.divisors ∨ ∃ b, b ∈ n.divisors ∧ a = 2 * b
  have hs :
      (∑ a ∈ s.filter pred, f a) = ∑ a ∈ s, f a := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro a haS haNot
    have hpred : ¬ pred a := by
      intro hp
      exact haNot (Finset.mem_filter.mpr ⟨haS, hp⟩)
    have hnotLeft : a ∉ n.divisors := by
      intro haLeft
      exact hpred (Or.inl haLeft)
    have hnotRight : ¬ ∃ b, b ∈ n.divisors ∧ a = 2 * b := by
      intro haRight
      exact hpred (Or.inr haRight)
    have hmu : (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) a : ℤ) : ℝ) = 0 := by
      exact_mod_cast
        (moebius_eq_zero_of_mem_two_pow_mul_odd_filter_not_branch hk hnOdd haS hnotLeft hnotRight)
    dsimp [f]
    rw [hmu]
    ring
  rw [← hs]
  have hbij :
      (∑ x ∈ n.divisors.disjSum n.divisors,
        match x with
        | Sum.inl b => f b
        | Sum.inr b => f (2 * b))
        =
      ∑ a ∈ s.filter pred, f a := by
    refine Finset.sum_bij
      (s := n.divisors.disjSum n.divisors)
      (t := s.filter pred)
      (f := fun x : ℕ ⊕ ℕ =>
        match x with
        | Sum.inl b => f b
        | Sum.inr b => f (2 * b))
      (g := f)
      (i := fun x _ => match x with | Sum.inl b => b | Sum.inr b => 2 * b)
      ?_ ?_ ?_ ?_
    · intro x hx
      cases x with
      | inl b =>
          have hb : b ∈ n.divisors := by simpa using (Finset.inl_mem_disjSum.mp hx)
          refine Finset.mem_filter.mpr ?_
          constructor
          · exact mem_two_pow_mul_odd_branch_left hk hnOdd hb
          · exact Or.inl hb
      | inr b =>
          have hb : b ∈ n.divisors := by simpa using (Finset.inr_mem_disjSum.mp hx)
          refine Finset.mem_filter.mpr ?_
          constructor
          · exact mem_two_pow_mul_odd_branch_right hk hnOdd hb
          · exact Or.inr ⟨b, hb, rfl⟩
    · intro x hx y hy hxy
      cases x with
      | inl bx =>
          cases y with
          | inl byv =>
              simp at hxy
              simp [hxy]
          | inr byv =>
              have hbx : bx ∈ n.divisors := by simpa using (Finset.inl_mem_disjSum.mp hx)
              have hbxOdd : Odd bx := odd_of_mem_divisors_odd hnOdd hbx
              have hbxEven : Goldbach.Windows.IsEven bx := by
                simp at hxy
                rw [hxy]
                dsimp [Goldbach.Windows.IsEven]
                omega
              exact False.elim ((Nat.not_even_iff_odd.mpr hbxOdd)
                (Goldbach.Windows.even_of_isEven hbxEven))
      | inr bx =>
          cases y with
          | inl byv =>
              have hby : byv ∈ n.divisors := by simpa using (Finset.inl_mem_disjSum.mp hy)
              have hbyOdd : Odd byv := odd_of_mem_divisors_odd hnOdd hby
              have hbyEven : Goldbach.Windows.IsEven byv := by
                simp at hxy
                rw [← hxy]
                dsimp [Goldbach.Windows.IsEven]
                omega
              exact False.elim ((Nat.not_even_iff_odd.mpr hbyOdd)
                (Goldbach.Windows.even_of_isEven hbyEven))
          | inr byv =>
              have h : bx = byv := Nat.mul_left_cancel (by norm_num : 0 < 2) hxy
              simp [h]
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨haS, haPred⟩
      rcases haPred with haLeft | ⟨b, hb, hEq⟩
      · refine ⟨Sum.inl a, ?_, rfl⟩
        rw [Finset.inl_mem_disjSum]
        exact haLeft
      · refine ⟨Sum.inr b, ?_, hEq.symm⟩
        rw [Finset.inr_mem_disjSum]
        exact hb
    · intro x hx
      cases x <;> rfl
  rw [← hbij, Finset.sum_disjSum, ← Finset.sum_add_distrib]

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_pow_succ_mul_odd
    {k n : ℕ} (hk : 2 ≤ k) (hnOdd : Odd n) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum ((2 ^ (k + 1)) * n)
      =
    (2 : ℝ) * centeredRamanujanPairCleanPeriodicOneVariableBaseSum ((2 ^ k) * n) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hk2 : 2 ≤ k + 1 := by omega
  rw [oneVariableBaseSum_two_pow_mul_odd_eq_branchPairSum hk2 hnOdd]
  rw [oneVariableBaseSum_two_pow_mul_odd_eq_branchPairSum hk hnOdd]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b hb
  have hb_dvd_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have hbOdd : Odd b := odd_of_mem_divisors_odd hnOdd hb
  have hmOdd : Odd (n / b) := odd_div_of_dvd_odd hnOdd hb_dvd_n
  have hquot_k1_b : ((2 ^ (k + 1)) * n) / b = (2 ^ (k + 1)) * (n / b) := by
    rw [Nat.mul_div_assoc (2 ^ (k + 1)) hb_dvd_n]
  have hquot_k_2b : ((2 ^ (k + 1)) * n) / (2 * b) = (2 ^ k) * (n / b) := by
    simpa using div_two_pow_mul_by_two_mul_of_dvd (k := k + 1) (n := n) (b := b) (by omega) hb
  have hquot_k_b : ((2 ^ k) * n) / b = (2 ^ k) * (n / b) := by
    rw [Nat.mul_div_assoc (2 ^ k) hb_dvd_n]
  have hquot_prev_2b : ((2 ^ k) * n) / (2 * b) = (2 ^ (k - 1)) * (n / b) := by
    simpa using div_two_pow_mul_by_two_mul_of_dvd (k := k) (n := n) (b := b) hk1 hb
  rw [hquot_k1_b, hquot_k_2b, hquot_k_b, hquot_prev_2b]
  exact oneVariable_twoPow_split_pair_summand_doubles hk hbOdd hmOdd

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_pow_mul_odd
    {k n : ℕ} (hk : 2 ≤ k) (hnOdd : Odd n) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum ((2 ^ k) * n)
      =
    (((2 ^ (k - 2) : ℕ) : ℝ) * centeredRamanujanPairCleanPeriodicOddPartBaseSum n) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero =>
      simpa using centeredRamanujanPairCleanPeriodicOneVariableBaseSum_four_mul_odd hnOdd
  | succ j ih =>
      have hstep :
          centeredRamanujanPairCleanPeriodicOneVariableBaseSum ((2 ^ (2 + (j + 1))) * n)
            =
          (2 : ℝ) *
            centeredRamanujanPairCleanPeriodicOneVariableBaseSum ((2 ^ (2 + j)) * n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_pow_succ_mul_odd
            (k := j + 2) (n := n) (by omega) hnOdd)
      rw [hstep, ih (by omega)]
      have hpow :
          ((2 ^ (j + 1) : ℕ) : ℝ)
            = (2 : ℝ) * ((2 ^ j : ℕ) : ℝ) := by
        rw [pow_succ]
        norm_num [mul_comm, mul_left_comm, mul_assoc]
      have hidxL : 2 + j - 2 = j := by omega
      have hidxR : 2 + (j + 1) - 2 = j + 1 := by omega
      rw [hidxL, hidxR, hpow]
      ring

private theorem ordCompl_two_odd {q : ℕ} (hq : q ≠ 0) :
    Odd (ordCompl[2] q) := by
  refine Nat.not_even_iff_odd.mp ?_
  intro hEven
  have h2 : 2 ∣ ordCompl[2] q := (even_iff_two_dvd).1 hEven
  exact Nat.not_dvd_ordCompl Nat.prime_two hq h2

private theorem factorization_two_pos_of_isEven
    {q : ℕ} (hq : q ≠ 0) (hEven : Goldbach.Windows.IsEven q) :
    1 ≤ q.factorization 2 := by
  refine (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hq).1 ?_
  exact (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hEven)

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_exists_oddPart_factorization_eq_one
    {q p : ℕ} (hq : 1 ≤ q)
    (hp : p ∈ (ordCompl[2] q).primeFactors)
    (hfact : (ordCompl[2] q).factorization p = 1) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q = 0 := by
  by_cases hEven : Goldbach.Windows.IsEven q
  · have hq0 : q ≠ 0 := Nat.ne_of_gt hq
    have hoddPartOdd : Odd (ordCompl[2] q) := ordCompl_two_odd hq0
    have hk1 : 1 ≤ q.factorization 2 := factorization_two_pos_of_isEven hq0 hEven
    by_cases hkEq1 : q.factorization 2 = 1
    · have hdecomp : q = 2 * ordCompl[2] q := by
        calc
          q = (2 ^ q.factorization 2) * ordCompl[2] q := by
                simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
          _ = 2 * ordCompl[2] q := by simp [hkEq1]
      rw [hdecomp]
      rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_mul_odd hoddPartOdd]
      exact centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_zero_of_factorization_eq_one
        (Nat.ordCompl_pos 2 hq0).ne' (Nat.prime_of_mem_primeFactors hp) hfact
    · have hk2 : 2 ≤ q.factorization 2 := by omega
      have hdecomp : q = (2 ^ q.factorization 2) * ordCompl[2] q := by
        simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
      rw [hdecomp]
      rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_pow_mul_odd hk2 hoddPartOdd]
      simp [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_zero_of_factorization_eq_one
        (Nat.ordCompl_pos 2 hq0).ne' (Nat.prime_of_mem_primeFactors hp) hfact]
  · exact centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_isEven hEven

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_pos_of_isEven_and_oddPart_factorization_two_le
    {q : ℕ} (hq : 1 ≤ q) (hEven : Goldbach.Windows.IsEven q)
    (hpow : ∀ p ∈ (ordCompl[2] q).primeFactors, 2 ≤ (ordCompl[2] q).factorization p) :
    0 < centeredRamanujanPairCleanPeriodicOneVariableBaseSum q := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hoddPartOdd : Odd (ordCompl[2] q) := ordCompl_two_odd hq0
  have hk1 : 1 ≤ q.factorization 2 := factorization_two_pos_of_isEven hq0 hEven
  by_cases hkEq1 : q.factorization 2 = 1
  · have hdecomp : q = 2 * ordCompl[2] q := by
      calc
        q = (2 ^ q.factorization 2) * ordCompl[2] q := by
              simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
        _ = 2 * ordCompl[2] q := by simp [hkEq1]
    rw [hdecomp]
    rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_mul_odd hoddPartOdd]
    exact centeredRamanujanPairCleanPeriodicOddPartBaseSum_pos_of_factorization_two_le
      (Nat.ordCompl_pos 2 hq0).ne' hpow
  · have hk2 : 2 ≤ q.factorization 2 := by omega
    have hdecomp : q = (2 ^ q.factorization 2) * ordCompl[2] q := by
      simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
    rw [hdecomp]
    rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_pow_mul_odd hk2 hoddPartOdd]
    have hpow2 : 0 < (((2 ^ (q.factorization 2 - 2) : ℕ) : ℝ)) := by
      exact_mod_cast pow_pos Nat.two_pos (q.factorization 2 - 2)
    exact mul_pos hpow2
      (centeredRamanujanPairCleanPeriodicOddPartBaseSum_pos_of_factorization_two_le
        (Nat.ordCompl_pos 2 hq0).ne' hpow)

/-- The exact support of the one-variable clean coprime factor:
`q` must be even, and every prime in the odd part `ordCompl[2] q` must occur with exponent at least
`2`. -/
def centeredRamanujanPairCleanPeriodicOneVariableSupport (q : ℕ) : Prop :=
  Goldbach.Windows.IsEven q
    ∧ ∀ p ∈ (ordCompl[2] q).primeFactors, 2 ≤ (ordCompl[2] q).factorization p

private instance centeredRamanujanPairCleanPeriodicOneVariableSupportDecidable :
    DecidablePred centeredRamanujanPairCleanPeriodicOneVariableSupport := by
  intro q
  unfold centeredRamanujanPairCleanPeriodicOneVariableSupport
  infer_instance

theorem centeredRamanujanPairCleanPeriodicOneVariableSupport_iff
    {q : ℕ} :
    centeredRamanujanPairCleanPeriodicOneVariableSupport q ↔
      Goldbach.Windows.IsEven q
        ∧ ∀ p ∈ (ordCompl[2] q).primeFactors, 2 ≤ (ordCompl[2] q).factorization p := by
  rfl

theorem centeredRamanujanPairCleanPeriodicOneVariableSupport_has_shape
    {q : ℕ} (hq : 1 ≤ q)
    (hsup : centeredRamanujanPairCleanPeriodicOneVariableSupport q) :
    ∃ k n : ℕ, 1 ≤ k ∧ Odd n
      ∧ q = (2 ^ k) * n
      ∧ ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p := by
  refine ⟨q.factorization 2, ordCompl[2] q, ?_, ordCompl_two_odd (Nat.ne_of_gt hq), ?_, hsup.2⟩
  · exact factorization_two_pos_of_isEven (Nat.ne_of_gt hq) hsup.1
  · simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_support
    {q : ℕ} (hq : 1 ≤ q)
    (hsup : ¬ centeredRamanujanPairCleanPeriodicOneVariableSupport q) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q = 0 := by
  by_cases hEven : Goldbach.Windows.IsEven q
  · have hq0 : q ≠ 0 := Nat.ne_of_gt hq
    have hodd0 : ordCompl[2] q ≠ 0 := (Nat.ordCompl_pos 2 hq0).ne'
    have hnotall :
        ¬ ∀ p ∈ (ordCompl[2] q).primeFactors, 2 ≤ (ordCompl[2] q).factorization p := by
      intro hall
      exact hsup ⟨hEven, hall⟩
    have hex :
        ∃ p ∈ (ordCompl[2] q).primeFactors, (ordCompl[2] q).factorization p = 1 := by
      classical
      by_contra hno
      apply hnotall
      intro p hp
      by_cases hfac2 : 2 ≤ (ordCompl[2] q).factorization p
      · exact hfac2
      · have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hfac1le : 1 ≤ (ordCompl[2] q).factorization p := by
          exact (Nat.Prime.dvd_iff_one_le_factorization hpPrime hodd0).1
            ((Nat.mem_primeFactors.mp hp).2.1)
        have hfact : (ordCompl[2] q).factorization p = 1 := by omega
        exact False.elim (hno ⟨p, hp, hfact⟩)
    rcases hex with ⟨p, hp, hfact⟩
    exact centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_exists_oddPart_factorization_eq_one
      hq hp hfact
  · exact centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_isEven hEven

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_pos_of_support
    {q : ℕ} (hq : 1 ≤ q)
    (hsup : centeredRamanujanPairCleanPeriodicOneVariableSupport q) :
    0 < centeredRamanujanPairCleanPeriodicOneVariableBaseSum q := by
  exact centeredRamanujanPairCleanPeriodicOneVariableBaseSum_pos_of_isEven_and_oddPart_factorization_two_le
    hq hsup.1 hsup.2

theorem centeredRamanujanPairCleanPeriodicOneVariableSupport_not_coprime
    {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hsq : centeredRamanujanPairCleanPeriodicOneVariableSupport q)
    (hsq' : centeredRamanujanPairCleanPeriodicOneVariableSupport q') :
    ¬ Nat.Coprime q q' := by
  intro hcop
  have h2q : 2 ∣ q := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hsq.1)
  have h2q' : 2 ∣ q' := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hsq'.1)
  have h2gcd : 2 ∣ Nat.gcd q q' := Nat.dvd_gcd h2q h2q'
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h2gcd
  norm_num at h2gcd

theorem centeredRamanujanPairCleanPeriodicOddPartBaseSum_le_self_of_factorization_two_le
    {n : ℕ} (hn : n ≠ 0)
    (hpow : ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p) :
    centeredRamanujanPairCleanPeriodicOddPartBaseSum n ≤ (n : ℝ) := by
  rw [centeredRamanujanPairCleanPeriodicOddPartBaseSum_eq_factorization_prod hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  have hle :
      ∏ p ∈ n.primeFactors, centeredRamanujanPairCleanPeriodicOddPartBaseSum (p ^ n.factorization p)
        ≤ ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      exact le_of_lt
        (centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime_pow_pos_of_two_le
          (Nat.prime_of_mem_primeFactors hp) (hpow p hp))
    · intro p hp
      exact centeredRamanujanPairCleanPeriodicOddPartBaseSum_prime_pow_le_pow
        (Nat.prime_of_mem_primeFactors hp) (hpow p hp)
  refine hle.trans ?_
  have hprod_nat : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa using (Nat.prod_pow_primeFactors_factorization hn).symm
  have hprod_real : ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p = (n : ℝ) := by
    exact_mod_cast hprod_nat
  exact hprod_real.le

theorem centeredRamanujanPairCleanPeriodicOneVariableBaseSum_le_self_of_support
    {q : ℕ} (hq : 1 ≤ q)
    (hsup : centeredRamanujanPairCleanPeriodicOneVariableSupport q) :
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q ≤ (q : ℝ) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hoddPartOdd : Odd (ordCompl[2] q) := ordCompl_two_odd hq0
  have hk1 : 1 ≤ q.factorization 2 := factorization_two_pos_of_isEven hq0 hsup.1
  let m := ordCompl[2] q
  by_cases hkEq1 : q.factorization 2 = 1
  · have hdecomp : q = 2 * ordCompl[2] q := by
      calc
        q = (2 ^ q.factorization 2) * ordCompl[2] q := by
              simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
        _ = 2 * ordCompl[2] q := by simp [hkEq1]
    rw [hdecomp]
    rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_mul_odd (by simpa [m] using hoddPartOdd)]
    have hodd_le :
        centeredRamanujanPairCleanPeriodicOddPartBaseSum m ≤ (m : ℝ) := by
      exact centeredRamanujanPairCleanPeriodicOddPartBaseSum_le_self_of_factorization_two_le
        (Nat.ordCompl_pos 2 hq0).ne' hsup.2
    have hdouble :
        (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
      have hnat : m ≤ 2 * m := by
        nlinarith
      exact_mod_cast hnat
    exact hodd_le.trans hdouble
  · have hk2 : 2 ≤ q.factorization 2 := by omega
    have hdecomp : q = (2 ^ q.factorization 2) * ordCompl[2] q := by
      simpa using (Nat.ordProj_mul_ordCompl_eq_self q 2).symm
    rw [hdecomp]
    rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_two_pow_mul_odd hk2
      (by simpa [m] using hoddPartOdd)]
    change (((2 ^ (q.factorization 2 - 2) : ℕ) : ℝ)
      * centeredRamanujanPairCleanPeriodicOddPartBaseSum m)
      ≤ (((2 ^ q.factorization 2) * m : ℕ) : ℝ)
    have hpow_nonneg : 0 ≤ (((2 ^ (q.factorization 2 - 2) : ℕ) : ℝ)) := by positivity
    have hodd_le :
        centeredRamanujanPairCleanPeriodicOddPartBaseSum m ≤ (m : ℝ) := by
      exact centeredRamanujanPairCleanPeriodicOddPartBaseSum_le_self_of_factorization_two_le
        (Nat.ordCompl_pos 2 hq0).ne' hsup.2
    have hmul_le :
        (((2 ^ (q.factorization 2 - 2) : ℕ) : ℝ)
          * centeredRamanujanPairCleanPeriodicOddPartBaseSum m)
          ≤
        (((2 ^ (q.factorization 2 - 2) : ℕ) : ℝ) * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hodd_le hpow_nonneg
    have hpow_le_nat : (2 ^ (q.factorization 2 - 2)) * m ≤ (2 ^ q.factorization 2) * m := by
      exact Nat.mul_le_mul_right m
        (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega))
    have hpow_le :
        (((2 ^ (q.factorization 2 - 2) : ℕ) : ℝ) * (m : ℝ))
          ≤ (((2 ^ q.factorization 2) * m : ℕ) : ℝ) := by
      exact_mod_cast hpow_le_nat
    exact hmul_le.trans hpow_le

/-- Supported one-variable moduli up to the fixed truncation height `Q0 = 30000`. -/
def centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 : Finset ℕ :=
  (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0).filter
    centeredRamanujanPairCleanPeriodicOneVariableSupport

theorem centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0_card :
    centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.card = 291 := by
  native_decide

theorem centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0_sum :
    centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum id = 3008698 := by
  native_decide

theorem centeredRamanujanPairCleanPeriodicGcdLeftFactor_sum_eq_blockCount_mul_oneVariableBaseSum
    (q q' : ℕ) :
    (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g)
      =
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
      * centeredRamanujanPairCleanPeriodicOneVariableBaseSum q) := by
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum]
  calc
    (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g)
      =
    (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
        * (ramanujanGcdClassCoeff q g * (Nat.totient (q / g) : ℝ)))) := by
        refine Finset.sum_congr rfl ?_
        intro g hg
        rw [centeredRamanujanPairCleanPeriodicGcdLeftFactor]
        ring
    _ =
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
      * ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ramanujanGcdClassCoeff q g * (Nat.totient (q / g) : ℝ)) := by
        rw [Finset.mul_sum]

theorem centeredRamanujanPairCleanPeriodicGcdRightFactor_sum_eq_oneVariableBaseSum
    (q' : ℕ) :
    (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
      centeredRamanujanPairCleanPeriodicGcdRightFactor q' h)
      =
    centeredRamanujanPairCleanPeriodicOneVariableBaseSum q' := by
  rw [centeredRamanujanPairCleanPeriodicOneVariableBaseSum]
  refine Finset.sum_congr rfl ?_
  intro h hh
  rw [centeredRamanujanPairCleanPeriodicGcdRightFactor]

theorem centeredRamanujanPairCleanPeriodicGcdBaseWeight_eq_left_mul_right
    (q q' g h : ℕ) :
    centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
      =
    centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
      * centeredRamanujanPairCleanPeriodicGcdRightFactor q' h := by
  rw [centeredRamanujanPairCleanPeriodicGcdBaseWeight,
    centeredRamanujanPairCleanPeriodicGcdLeftFactor,
    centeredRamanujanPairCleanPeriodicGcdRightFactor]
  ring

theorem centeredRamanujanPairCleanPeriodicGcdWeightAtGcd_gcd_eq_factorized
    {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' (Nat.gcd q q')
      =
    (∑ a ∈ (q / Nat.gcd q q').divisors.filter
        (fun a => Goldbach.Windows.IsEven (Nat.gcd q q' * a)),
        centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' (Nat.gcd q q' * a))
      *
    (∑ b ∈ (q' / Nat.gcd q q').divisors.filter
        (fun b => Goldbach.Windows.IsEven (Nat.gcd q q' * b)),
        centeredRamanujanPairCleanPeriodicGcdRightFactor q' (Nat.gcd q q' * b)) := by
  let G := Nat.gcd q q'
  have hGq : G ∣ q := Nat.gcd_dvd_left q q'
  have hGq' : G ∣ q' := Nat.gcd_dvd_right q q'
  have hGpos : 0 < G := by
    dsimp [G]
    exact Nat.gcd_pos_of_pos_right q hq'
  have hcop : Nat.Coprime (q / G) (q' / G) := by
    dsimp [G]
    simpa using (Nat.coprime_div_gcd_div_gcd (H := hGpos))
  rw [centeredRamanujanPairCleanPeriodicGcdWeightAtGcd_eq_coprime_reindexed
    (q := q) (q' := q') (d := G) hq hq' hGq hGq']
  calc
    (∑ a ∈ (q / G).divisors.filter (fun a => Goldbach.Windows.IsEven (G * a)),
      ∑ b ∈ (q' / G).divisors.filter (fun b => Goldbach.Windows.IsEven (G * b)),
        if Nat.Coprime a b then
          centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' (G * a) (G * b)
        else 0)
      =
    (∑ a ∈ (q / G).divisors.filter (fun a => Goldbach.Windows.IsEven (G * a)),
      ∑ b ∈ (q' / G).divisors.filter (fun b => Goldbach.Windows.IsEven (G * b)),
        centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' (G * a) (G * b)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have ha' : a ∈ (q / G).divisors := (Finset.mem_filter.mp ha).1
          refine Finset.sum_congr rfl ?_
          intro b hb
          have hb' : b ∈ (q' / G).divisors := (Finset.mem_filter.mp hb).1
          have hab : Nat.Coprime a b := gcd_g_h_eq_one_of_coprime_moduli hcop ha' hb'
          simp [hab]
    _ =
    (∑ a ∈ (q / G).divisors.filter (fun a => Goldbach.Windows.IsEven (G * a)),
      ∑ b ∈ (q' / G).divisors.filter (fun b => Goldbach.Windows.IsEven (G * b)),
        centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' (G * a)
          * centeredRamanujanPairCleanPeriodicGcdRightFactor q' (G * b)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [centeredRamanujanPairCleanPeriodicGcdBaseWeight_eq_left_mul_right]
    _ =
    (∑ a ∈ (q / G).divisors.filter (fun a => Goldbach.Windows.IsEven (G * a)),
      centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' (G * a)
        * (∑ b ∈ (q' / G).divisors.filter (fun b => Goldbach.Windows.IsEven (G * b)),
            centeredRamanujanPairCleanPeriodicGcdRightFactor q' (G * b))) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.mul_sum]
    _ =
    (∑ a ∈ (q / G).divisors.filter (fun a => Goldbach.Windows.IsEven (G * a)),
      centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' (G * a))
      *
    (∑ b ∈ (q' / G).divisors.filter (fun b => Goldbach.Windows.IsEven (G * b)),
      centeredRamanujanPairCleanPeriodicGcdRightFactor q' (G * b)) := by
          rw [Finset.sum_mul]
    _ =
    (∑ a ∈ (q / Nat.gcd q q').divisors.filter
        (fun a => Goldbach.Windows.IsEven (Nat.gcd q q' * a)),
        centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' (Nat.gcd q q' * a))
      *
    (∑ b ∈ (q' / Nat.gcd q q').divisors.filter
        (fun b => Goldbach.Windows.IsEven (Nat.gcd q q' * b)),
        centeredRamanujanPairCleanPeriodicGcdRightFactor q' (Nat.gcd q q' * b)) := by
          simp [G]

theorem centeredRamanujanPairCleanPeriodicGcdWeightAtGcd_half_gcd_eq_zero_of_not_isEven_half
    {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hhalfDiv : 2 ∣ Nat.gcd q q')
    (hhalfOdd : ¬ Goldbach.Windows.IsEven (Nat.gcd q q' / 2)) :
    centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' (Nat.gcd q q' / 2) = 0 := by
  let d := Nat.gcd q q' / 2
  have hdq : d ∣ q := by
    dsimp [d]
    exact dvd_trans (Nat.div_dvd_of_dvd hhalfDiv) (Nat.gcd_dvd_left q q')
  have hdq' : d ∣ q' := by
    dsimp [d]
    exact dvd_trans (Nat.div_dvd_of_dvd hhalfDiv) (Nat.gcd_dvd_right q q')
  rw [centeredRamanujanPairCleanPeriodicGcdWeightAtGcd_eq_coprime_reindexed
    (q := q) (q' := q') (d := d) hq hq' hdq hdq']
  refine Finset.sum_eq_zero ?_
  intro a ha
  refine Finset.sum_eq_zero ?_
  intro b hb
  have haEvenMul : Goldbach.Windows.IsEven (d * a) := (Finset.mem_filter.mp ha).2
  have hbEvenMul : Goldbach.Windows.IsEven (d * b) := (Finset.mem_filter.mp hb).2
  have haEven : Goldbach.Windows.IsEven a :=
    (isEven_mul_iff_of_not_isEven_left (a := d) (m := a) hhalfOdd).1 haEvenMul
  have hbEven : Goldbach.Windows.IsEven b :=
    (isEven_mul_iff_of_not_isEven_left (a := d) (m := b) hhalfOdd).1 hbEvenMul
  have hnotcop : ¬ Nat.Coprime a b := by
    intro hcop
    have h2a : 2 ∣ a := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven haEven)
    have h2b : 2 ∣ b := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hbEven)
    have h2gcd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2a h2b
    have : 2 ∣ 1 := by simpa [Nat.Coprime.gcd_eq_one hcop] using h2gcd
    norm_num at this
  simp [hnotcop]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_factorized
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (-2 : ℝ)
      * (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g)
      * (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli hq hq' hcop]
  trans
    ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
      ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
        centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h * (-2 : ℝ)
  · refine Finset.sum_congr rfl ?_
    intro g hg
    have hg' : g ∈ q.divisors := (Finset.mem_filter.mp hg).1
    refine Finset.sum_congr rfl ?_
    intro h hh
    have hh' : h ∈ q'.divisors := (Finset.mem_filter.mp hh).1
    have hgh : Nat.gcd g h = 1 := gcd_g_h_eq_one_of_coprime_moduli hcop hg' hh'
    simp [hgh]
  · calc
      (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h * (-2 : ℝ))
        =
      (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            (centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
              * centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) * (-2 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro g hg
            refine Finset.sum_congr rfl ?_
            intro h hh
            rw [centeredRamanujanPairCleanPeriodicGcdBaseWeight_eq_left_mul_right]
      _ =
      (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
            * ((∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) * (-2 : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro g hg
            calc
              (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                  (centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
                    * centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) * (-2 : ℝ))
                =
              (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                  centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
                    * (centeredRamanujanPairCleanPeriodicGcdRightFactor q' h * (-2 : ℝ))) := by
                    refine Finset.sum_congr rfl ?_
                    intro h hh
                    ring
              _ =
              centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
                * (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                    centeredRamanujanPairCleanPeriodicGcdRightFactor q' h * (-2 : ℝ)) := by
                    rw [← Finset.mul_sum]
              _ =
              centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g
                * ((∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                    centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) * (-2 : ℝ)) := by
                    rw [← Finset.sum_mul]
      _ =
      (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g)
        * ((∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) * (-2 : ℝ)) := by
            rw [← Finset.sum_mul]
      _ =
      (-2 : ℝ)
        * (∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
            centeredRamanujanPairCleanPeriodicGcdLeftFactor q q' g)
        * (∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            centeredRamanujanPairCleanPeriodicGcdRightFactor q' h) := by
            ring

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (-2 : ℝ)
      * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
          * centeredRamanujanPairCleanPeriodicOneVariableBaseSum q)
      * centeredRamanujanPairCleanPeriodicOneVariableBaseSum q' := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_factorized hq hq' hcop]
  rw [centeredRamanujanPairCleanPeriodicGcdLeftFactor_sum_eq_blockCount_mul_oneVariableBaseSum]
  rw [centeredRamanujanPairCleanPeriodicGcdRightFactor_sum_eq_oneVariableBaseSum]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_zero_of_coprime_moduli_of_not_isEven
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q')
    (hparity : ¬ Goldbach.Windows.IsEven q ∨ ¬ Goldbach.Windows.IsEven q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q' = 0 := by
  rcases hparity with hqOdd | hq'Odd
  · rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
      hq hq' hcop]
    simp [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_isEven hqOdd]
  · rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
      hq hq' hcop]
    simp [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_isEven hq'Odd]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_zero_of_coprime_moduli_of_support_failure
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q')
    (hbad :
      (∃ p ∈ (ordCompl[2] q).primeFactors, (ordCompl[2] q).factorization p = 1)
        ∨
      (∃ p ∈ (ordCompl[2] q').primeFactors, (ordCompl[2] q').factorization p = 1)
        ∨
      ¬ Goldbach.Windows.IsEven q
        ∨
      ¬ Goldbach.Windows.IsEven q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q' = 0 := by
  rcases hbad with hqBad | hq'Bad | hqOdd | hq'Odd
  · rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
      hq hq' hcop]
    rcases hqBad with ⟨p, hp, hfact⟩
    simp [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_exists_oddPart_factorization_eq_one
      hq hp hfact]
  · rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
      hq hq' hcop]
    rcases hq'Bad with ⟨p, hp, hfact⟩
    simp [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_exists_oddPart_factorization_eq_one
      hq' hp hfact]
  · exact centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_zero_of_coprime_moduli_of_not_isEven
      hq hq' hcop (Or.inl hqOdd)
  · exact centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_zero_of_coprime_moduli_of_not_isEven
      hq hq' hcop (Or.inr hq'Odd)

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_zero_of_coprime_moduli_of_not_support
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q')
    (hbad : ¬ centeredRamanujanPairCleanPeriodicOneVariableSupport q
      ∨ ¬ centeredRamanujanPairCleanPeriodicOneVariableSupport q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q' = 0 := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
    hq hq' hcop]
  rcases hbad with hqBad | hq'Bad
  · simp [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_support hq hqBad]
  · simp [centeredRamanujanPairCleanPeriodicOneVariableBaseSum_eq_zero_of_not_support hq' hq'Bad]

theorem centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_on_support
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q')
    (hs : centeredRamanujanPairCleanPeriodicOneVariableSupport q
      ∧ centeredRamanujanPairCleanPeriodicOneVariableSupport q') :
    centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      =
    (-2 : ℝ)
      * ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)
          * centeredRamanujanPairCleanPeriodicOneVariableBaseSum q)
      * centeredRamanujanPairCleanPeriodicOneVariableBaseSum q' := by
  exact centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_oneVariable
    hq hq' hcop

theorem centeredRamanujanPairCleanPeriodicBlockCount_le
    (q q' : ℕ) :
    ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ)) ≤ (H + 1 : ℝ) := by
  exact_mod_cast Nat.div_le_self (H + 1) (centeredRamanujanPairBlockPeriod q q')

theorem neg_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_two_mul_self_mul_self
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hcop : Nat.Coprime q q')
    (hs : centeredRamanujanPairCleanPeriodicOneVariableSupport q
      ∧ centeredRamanujanPairCleanPeriodicOneVariableSupport q') :
    - centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
      ≤ (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ) * (q' : ℝ) := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_coprime_moduli_on_support
    hq hq' hcop hs]
  set B : ℝ := ((((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℝ))
  set Sq : ℝ := centeredRamanujanPairCleanPeriodicOneVariableBaseSum q
  set Sq' : ℝ := centeredRamanujanPairCleanPeriodicOneVariableBaseSum q'
  have hB_le : B ≤ (H + 1 : ℝ) := by
    simp [B, centeredRamanujanPairBlockPeriod]
    exact_mod_cast Nat.div_le_self (H + 1) (2 * Nat.lcm q q')
  have hSq_le : Sq ≤ (q : ℝ) := by
    simpa [Sq] using centeredRamanujanPairCleanPeriodicOneVariableBaseSum_le_self_of_support hq hs.1
  have hSq'_le : Sq' ≤ (q' : ℝ) := by
    simpa [Sq'] using centeredRamanujanPairCleanPeriodicOneVariableBaseSum_le_self_of_support hq' hs.2
  have hB_nonneg : 0 ≤ B := by
    simp [B]
  have hSq_nonneg : 0 ≤ Sq := by
    exact le_of_lt (by simpa [Sq] using
      centeredRamanujanPairCleanPeriodicOneVariableBaseSum_pos_of_support hq hs.1)
  have hSq'_nonneg : 0 ≤ Sq' := by
    exact le_of_lt (by simpa [Sq'] using
      centeredRamanujanPairCleanPeriodicOneVariableBaseSum_pos_of_support hq' hs.2)
  rw [show (-2 : ℝ) * (B * Sq) * Sq' = (-2 : ℝ) * B * Sq * Sq' by ring]
  have hrewrite :
      -((-2 : ℝ) * B * Sq * Sq') = (2 : ℝ) * B * Sq * Sq' := by ring
  rw [hrewrite]
  have hmul :
      B * Sq * Sq' ≤ ((H + 1 : ℝ) * (q : ℝ)) * (q' : ℝ) := by
    have hBSq :
        B * Sq ≤ (H + 1 : ℝ) * (q : ℝ) := by
      exact mul_le_mul hB_le hSq_le hSq_nonneg (by positivity)
    exact mul_le_mul hBSq hSq'_le hSq'_nonneg (by positivity)
  have hmul2 :
      (2 : ℝ) * (B * Sq * Sq') ≤ (2 : ℝ) * (((H + 1 : ℝ) * (q : ℝ)) * (q' : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hmul (by positivity)
  simpa [mul_assoc] using hmul2

/-- Crude magnitude audit for the clean coprime gcd-correction, restricted to the exact supported
moduli up to `Q0 = 30000`. -/
noncomputable def centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0
    (X : ℕ) : ℝ :=
  Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
    Finset.sum
      (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter (Nat.Coprime q))
      (fun q' => - centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'))

theorem centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0_le
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0 X
      ≤
    (2 : ℝ) * (H + 1 : ℝ)
      * (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum (fun q => q) : ℝ) ^ 2 := by
  unfold centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0
  calc
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
        Finset.sum
          (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter (Nat.Coprime q))
          (fun q' => -centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'))
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
        Finset.sum
          (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter (Nat.Coprime q))
          (fun q' => (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ) * (q' : ℝ))) := by
        refine Finset.sum_le_sum ?_
        intro q hqmem
        have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
          (Finset.mem_filter.mp hqmem).1
        have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
        have hsq : centeredRamanujanPairCleanPeriodicOneVariableSupport q :=
          (Finset.mem_filter.mp hqmem).2
        refine Finset.sum_le_sum ?_
        intro q' hq'mem
        have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
          (Finset.mem_filter.mp hq'mem).1
        have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
          (Finset.mem_filter.mp hq'mem0).1
        have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
        have hsq' : centeredRamanujanPairCleanPeriodicOneVariableSupport q' :=
          (Finset.mem_filter.mp hq'mem0).2
        have hcop : Nat.Coprime q q' := (Finset.mem_filter.mp hq'mem).2
        exact neg_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_two_mul_self_mul_self
          hq hq' hcop ⟨hsq, hsq'⟩
    _ ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
        Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0
          (fun q' => (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ) * (q' : ℝ))) := by
        refine Finset.sum_le_sum ?_
        intro q hqmem
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro q' hq'mem
          exact (Finset.mem_filter.mp hq'mem).1
        · intro q' hq'inq hq'notin
          positivity
    _ =
    (2 : ℝ) * (H + 1 : ℝ)
      * (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q => (q : ℝ)))
      * (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q => (q : ℝ))) := by
        let S := centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0
        let T : ℝ := Finset.sum S (fun q => (q : ℝ))
        calc
          Finset.sum S (fun q =>
              Finset.sum S
                (fun q' => (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ) * (q' : ℝ)))
            =
          Finset.sum S (fun q => ((2 : ℝ) * (H + 1 : ℝ) * (q : ℝ)) * T) := by
                  refine Finset.sum_congr rfl ?_
                  intro q hqmem
                  dsimp [T]
                  calc
                    Finset.sum S (fun q' => (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ) * (q' : ℝ))
                      =
                    Finset.sum S (fun q' => ((2 : ℝ) * (H + 1 : ℝ) * (q : ℝ)) * (q' : ℝ)) := by
                        refine Finset.sum_congr rfl ?_
                        intro q' hq'mem
                        ring
                    _ = ((2 : ℝ) * (H + 1 : ℝ) * (q : ℝ)) * Finset.sum S (fun q' => (q' : ℝ)) := by
                        rw [Finset.mul_sum]
          _ =
          (Finset.sum S (fun q => (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ))) * T := by
              rw [← Finset.sum_mul]
          _ = (((2 : ℝ) * (H + 1 : ℝ)) * Finset.sum S (fun q => (q : ℝ))) * T := by
              congr 1
              calc
                Finset.sum S (fun q => (2 : ℝ) * (H + 1 : ℝ) * (q : ℝ))
                  = Finset.sum S (fun q => ((2 : ℝ) * (H + 1 : ℝ)) * (q : ℝ)) := by
                      refine Finset.sum_congr rfl ?_
                      intro q hqmem
                      ring
                _ = ((2 : ℝ) * (H + 1 : ℝ)) * Finset.sum S (fun q => (q : ℝ)) := by
                      rw [Finset.mul_sum]
          _ =
          (2 : ℝ) * (H + 1 : ℝ) * (Finset.sum S (fun q => (q : ℝ))) * T := by ring
          _ =
          (2 : ℝ) * (H + 1 : ℝ)
            * (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0
                (fun q => (q : ℝ)))
            * (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0
                (fun q' => (q' : ℝ))) := by
              simp [S, T]
    _ =
    (2 : ℝ) * (H + 1 : ℝ)
      * (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum (fun q => q) : ℝ) ^ 2 := by
        have hsum_cast :
            Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q => (q : ℝ))
              = (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum (fun q => q) : ℝ) := by
          simp
        rw [hsum_cast, hsum_cast]
        ring

theorem centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0_le_explicit
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0 X
      ≤ 181063377631390408 := by
  calc
    centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0 X
      ≤
    (2 : ℝ) * (H + 1 : ℝ)
      * (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum (fun q => q) : ℝ) ^ 2 := by
        exact centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0_le X
    _ = 181063377631390408 := by
        have hsum :
            Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q => (q : ℝ))
              = 3008698 := by
          have hsum' :
              ((centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum (fun q => q) : ℕ) : ℝ)
                = 3008698 := by
            exact_mod_cast centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0_sum
          simpa using hsum'
        have hsum_cast :
            (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.sum (fun q => q) : ℝ)
              = 3008698 := by
          simpa using hsum
        rw [hsum_cast]
        norm_num [H]

theorem centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0_eq_zero
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0 X = 0 := by
  unfold centeredRamanujanPairCleanPeriodicCoprimeSupportedMagnitudeUpToQ0
  refine Finset.sum_eq_zero ?_
  intro q hqmem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  have hsq : centeredRamanujanPairCleanPeriodicOneVariableSupport q :=
    (Finset.mem_filter.mp hqmem).2
  have hempty :
      centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter (Nat.Coprime q) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro q' hq'mem
    have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
      (Finset.mem_filter.mp hq'mem).1
    have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
      (Finset.mem_filter.mp hq'mem0).1
    have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
    have hsq' : centeredRamanujanPairCleanPeriodicOneVariableSupport q' :=
      (Finset.mem_filter.mp hq'mem0).2
    exact centeredRamanujanPairCleanPeriodicOneVariableSupport_not_coprime hq hq' hsq hsq'
      ((Finset.mem_filter.mp hq'mem).2)
  simp [hempty]

/-- The clean branch on the exact supported surface, with the coprime part removed from the start. -/
noncomputable def centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0
    (X : ℕ) : ℝ :=
  Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
    Finset.sum
      (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
        (fun q' => ¬ Nat.Coprime q q'))
      (fun q' => centeredRamanujanPairCleanPeriodicDefectTerm X q q'))

noncomputable def centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0
    (X : ℕ) : ℝ :=
  Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
    Finset.sum
      (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
        (fun q' => ¬ Nat.Coprime q q'))
      (fun q' => centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'))

noncomputable def centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0
    (X : ℕ) : ℝ :=
  Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
    Finset.sum
      (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
        (fun q' => ¬ Nat.Coprime q q'))
      (fun q' => centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'))

noncomputable def centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0
    (X : ℕ) : ℝ :=
  Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
    Finset.sum
      (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
        (fun q' => ¬ Nat.Coprime q q'))
      (fun q' => centeredRamanujanPairCleanPeriodicRemainderTerm X q q'))

theorem centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_eq_commonPrime_add_gcdCorrection_add_remainder
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0 X
      =
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
      + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X
      + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X := by
  unfold centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0
  let S := centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0
  change
    Finset.sum S (fun q =>
      Finset.sum
        (S.filter (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicDefectTerm X q q'))
      =
    Finset.sum S (fun q =>
      Finset.sum
        (S.filter (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'))
      +
    Finset.sum S (fun q =>
      Finset.sum
        (S.filter (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'))
      +
    Finset.sum S (fun q =>
      Finset.sum
        (S.filter (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicRemainderTerm X q q'))
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro q hqmem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  calc
    Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicDefectTerm X q q')
      =
    Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'
            + centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'
            + centeredRamanujanPairCleanPeriodicRemainderTerm X q q') := by
          refine Finset.sum_congr rfl ?_
          intro q' hq'mem
          have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
            (Finset.mem_filter.mp hq'mem).1
          have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
            (Finset.mem_filter.mp hq'mem0).1
          have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
          exact centeredRamanujanPairCleanPeriodicDefectTerm_eq_commonPrime_add_gcdCorrection_add_remainder
            (X := X) hq hq'
    _ =
    (Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'))
      +
    (Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'))
      +
    (Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' => centeredRamanujanPairCleanPeriodicRemainderTerm X q q')) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_eq_sum_over_sharedDivisors
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
      =
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d)) := by
  unfold centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0
  refine Finset.sum_congr rfl ?_
  intro q hqmem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  refine Finset.sum_congr rfl ?_
  intro q' hq'mem
  have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
    (Finset.mem_filter.mp hq'mem).1
  have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hq'mem0).1
  have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
  exact centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_sum_over_nontrivial_reducedGcdDivisors
    (X := X) hq hq'

theorem centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_eq_sum_over_sharedDivisors
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X
      =
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                    * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                else 0)) := by
  unfold centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0
  refine Finset.sum_congr rfl ?_
  intro q hqmem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  refine Finset.sum_congr rfl ?_
  intro q' hq'mem
  have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
    (Finset.mem_filter.mp hq'mem).1
  have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hq'mem0).1
  have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
  exact centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_partitionedByGcdDivisors
    (X := X) hq hq'

theorem centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_eq_explicitScalar_splitRegions
    (X : ℕ) :
    centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X
      =
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => 2 * d < Nat.gcd q q'),
            centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
              * (((0 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
            +
          (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => d = Nat.gcd q q'),
            centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
              * (((2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ))))
            +
          (∑ d ∈ ((Nat.gcd q q').divisors.filter fun d => ¬ 2 * d < Nat.gcd q q' ∧ d ≠ Nat.gcd q q'),
            centeredRamanujanPairCleanPeriodicGcdWeightAtGcd q q' d
              * (((1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)))))) := by
  unfold centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0
  refine Finset.sum_congr rfl ?_
  intro q hqmem
  refine Finset.sum_congr rfl ?_
  intro q' hq'mem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
    (Finset.mem_filter.mp hq'mem).1
  have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hq'mem0).1
  have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
  exact centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_explicitScalar_splitRegions
    (X := X) hq hq'

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeTerm_le_sum_abs_weights
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
      |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d| := by
  rw [centeredRamanujanPairCleanPeriodicCommonPrimeTerm_eq_sum_over_nontrivial_reducedGcdDivisors
    (X := X) hq hq']
  simpa using
    (Finset.abs_sum_le_sum_abs
      (fun d => centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d)
      ((Nat.gcd q q').divisors.filter (fun d => d ≠ 1)))

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeTerm_le_sum_productMajorants
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
      centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant q q' d
        * centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant q' d := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeTerm_le_sum_abs_weights
      (X := X) hq hq') ?_
  refine Finset.sum_le_sum ?_
  intro d hd
  have hd_dvd_gcd : d ∣ Nat.gcd q q' := (Nat.mem_divisors.mp ((Finset.mem_filter.mp hd).1)).1
  have hdq : d ∣ q := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_left q q')
  have hdq' : d ∣ q' := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_right q q')
  exact abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_productMajorant
    (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq'

theorem abs_centeredRamanujanPairCleanPeriodicCommonPrimeTerm_le_sum_coprime_reindexedMajorants
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicCommonPrimeTerm X q q'|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
      ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
        ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
          if Nat.Coprime a1 b1 then
            centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
          else 0 := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicCommonPrimeTerm_le_sum_abs_weights
      (X := X) hq hq') ?_
  refine Finset.sum_le_sum ?_
  intro d hd
  have hd_dvd_gcd : d ∣ Nat.gcd q q' := (Nat.mem_divisors.mp ((Finset.mem_filter.mp hd).1)).1
  have hdq : d ∣ q := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_left q q')
  have hdq' : d ∣ q' := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_right q q')
  exact abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_coprime_reindexedMajorant
    (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq'

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_abs_weights
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X|
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|)) := by
  rw [centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_eq_sum_over_sharedDivisors]
  calc
    |∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
        ∑ q' ∈
          centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
            (fun q' => ¬ Nat.Coprime q q'),
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d|
      ≤
    ∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
      |∑ q' ∈
          centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
            (fun q' => ¬ Nat.Coprime q q'),
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun q =>
              ∑ q' ∈
                centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
                  (fun q' => ¬ Nat.Coprime q q'),
                ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
                  centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d)
            centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0)
    _ ≤
    ∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
      ∑ q' ∈
        centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'),
        |∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d| := by
        refine Finset.sum_le_sum ?_
        intro q hqmem
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun q' =>
              ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
                centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d)
            (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
              (fun q' => ¬ Nat.Coprime q q')))
    _ ≤
    ∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
      ∑ q' ∈
        centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'),
        ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
          |centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d| := by
        refine Finset.sum_le_sum ?_
        intro q hqmem
        refine Finset.sum_le_sum ?_
        intro q' hq'mem
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun d => centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd X q q' d)
            ((Nat.gcd q q').divisors.filter (fun d => d ≠ 1)))

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_productMajorants
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X|
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant q q' d
              * centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant q' d)) := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_abs_weights
      (X := X)) ?_
  refine Finset.sum_le_sum ?_
  intro q hqmem
  refine Finset.sum_le_sum ?_
  intro q' hq'mem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
    (Finset.mem_filter.mp hq'mem).1
  have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hq'mem0).1
  have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
  refine Finset.sum_le_sum ?_
  intro d hd
  have hd_dvd_gcd : d ∣ Nat.gcd q q' := (Nat.mem_divisors.mp ((Finset.mem_filter.mp hd).1)).1
  have hdq : d ∣ q := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_left q q')
  have hdq' : d ∣ q' := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_right q q')
  exact abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_productMajorant
    (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq'

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_coprime_reindexedMajorants
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X|
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
              ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
                if Nat.Coprime a1 b1 then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
                else 0)) := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_abs_weights
      (X := X)) ?_
  refine Finset.sum_le_sum ?_
  intro q hqmem
  refine Finset.sum_le_sum ?_
  intro q' hq'mem
  have hqIcc : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hqmem).1
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqIcc).1
  have hq'mem0 : q' ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 :=
    (Finset.mem_filter.mp hq'mem).1
  have hq'Icc : q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 :=
    (Finset.mem_filter.mp hq'mem0).1
  have hq' : 1 ≤ q' := (Finset.mem_Icc.mp hq'Icc).1
  refine Finset.sum_le_sum ?_
  intro d hd
  have hd_dvd_gcd : d ∣ Nat.gcd q q' := (Nat.mem_divisors.mp ((Finset.mem_filter.mp hd).1)).1
  have hdq : d ∣ q := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_left q q')
  have hdq' : d ∣ q' := dvd_trans hd_dvd_gcd (Nat.gcd_dvd_right q q')
  exact abs_centeredRamanujanPairCleanPeriodicCommonPrimeWeightAtReducedGcd_le_coprime_reindexedMajorant
    (X := X) (q := q) (q' := q') (d := d) hq hq' hdq hdq'

theorem centeredRamanujanPairCleanPeriodicGcdCaseScalar_abs_le_two_of_not_coprime
    {q q' d : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hnotcop : ¬ Nat.Coprime q q') :
    |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d| ≤ 2 := by
  have hgcd_ne_one : Nat.gcd q q' ≠ 1 := by
    intro hgcd1
    apply hnotcop
    exact Nat.coprime_iff_gcd_eq_one.mpr hgcd1
  have hgcd_pos_nat : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_right q hq'
  have hgcd_two_nat : 2 ≤ Nat.gcd q q' := by
    have h1le : 1 ≤ Nat.gcd q q' := Nat.succ_le_of_lt hgcd_pos_nat
    exact lt_of_le_of_ne h1le (Ne.symm hgcd_ne_one)
  have hGpos : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by exact_mod_cast hgcd_pos_nat
  have hGtwo : (2 : ℝ) ≤ (Nat.gcd q q' : ℝ) := by exact_mod_cast hgcd_two_nat
  have hfrac_nonneg : 0 ≤ (4 : ℝ) / (Nat.gcd q q' : ℝ) := by positivity
  have hfrac_le_two : (4 : ℝ) / (Nat.gcd q q' : ℝ) ≤ 2 := by
    have := (div_le_iff₀ hGpos).2
      (by nlinarith [hGtwo] : (4 : ℝ) ≤ 2 * (Nat.gcd q q' : ℝ))
    simpa [mul_comm] using this
  unfold centeredRamanujanPairCleanPeriodicGcdCaseScalar
  split_ifs with hlt heq
  · simpa [sub_eq_add_neg, abs_of_nonneg hfrac_nonneg] using hfrac_le_two
  · have hnonneg : 0 ≤ (2 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ) := by
      linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  · have hlow : -1 ≤ (1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ) := by
      linarith
    have hhigh : (1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ) ≤ 1 := by
      linarith
    have habs_le_one : |(1 : ℝ) - (4 : ℝ) / (Nat.gcd q q' : ℝ)| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith, hhigh⟩
    linarith

theorem abs_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_sum_abs_partitioned
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          |if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0| := by
  rw [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_partitionedByGcdDivisors
    (X := X) hq hq']
  calc
    |∑ d ∈ (Nat.gcd q q').divisors,
        ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      |∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
          ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun d =>
              ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
                ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                  if Nat.gcd g h = d then
                    centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                      * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                  else 0)
            (Nat.gcd q q').divisors)
    _ ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        |∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
            if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0| := by
        refine Finset.sum_le_sum ?_
        intro d hd
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun g =>
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                    * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                else 0)
            (q.divisors.filter Goldbach.Windows.IsEven))
    _ ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          |if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0| := by
        refine Finset.sum_le_sum ?_
        intro d hd
        refine Finset.sum_le_sum ?_
        intro g hg
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun h =>
              if Nat.gcd g h = d then
                centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                  * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
              else 0)
            (q'.divisors.filter Goldbach.Windows.IsEven))

theorem centeredRamanujanPairCleanPeriodicGcdAbsPartitioned_le_two_mul_abs_baseWeight_partitioned
    {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hnotcop : ¬ Nat.Coprime q q') :
    (∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          |if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0|)
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          if Nat.gcd g h = d then
            (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
          else 0 := by
  refine Finset.sum_le_sum ?_
  intro d hd
  refine Finset.sum_le_sum ?_
  intro g hg
  refine Finset.sum_le_sum ?_
  intro h hh
  by_cases hgd : Nat.gcd g h = d
  · have hscalar :
        |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d| ≤ 2 :=
      centeredRamanujanPairCleanPeriodicGcdCaseScalar_abs_le_two_of_not_coprime
        (q := q) (q' := q') (d := d) hq hq' hnotcop
    have hbase_nonneg :
        0 ≤ |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h| := abs_nonneg _
    simp [hgd, abs_mul]
    nlinarith
  · simp [hgd]

theorem centeredRamanujanPairCleanPeriodicGcdAbsPartitioned_eq_absBaseWeight_mul_absCaseScalar_partitioned
    {q q' : ℕ} :
    (∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          |if Nat.gcd g h = d then
              centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
            else 0|)
      =
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          if Nat.gcd g h = d then
            |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
              * |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d|
          else 0 := by
  refine Finset.sum_congr rfl ?_
  intro d hd
  refine Finset.sum_congr rfl ?_
  intro g hg
  refine Finset.sum_congr rfl ?_
  intro h hh
  by_cases hgd : Nat.gcd g h = d
  · simp [hgd, abs_mul, mul_comm, mul_left_comm, mul_assoc]
  · simp [hgd]

theorem abs_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_absBaseWeight_mul_absCaseScalar_partitioned
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    |centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          if Nat.gcd g h = d then
            |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
              * |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d|
          else 0 := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_sum_abs_partitioned
      (X := X) hq hq') ?_
  rw [centeredRamanujanPairCleanPeriodicGcdAbsPartitioned_eq_absBaseWeight_mul_absCaseScalar_partitioned]

theorem abs_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_two_mul_abs_baseWeight_partitioned
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hnotcop : ¬ Nat.Coprime q q') :
    |centeredRamanujanPairCleanPeriodicGcdCorrectionTerm X q q'|
      ≤
    ∑ d ∈ (Nat.gcd q q').divisors,
      ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
        ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
          if Nat.gcd g h = d then
            (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
          else 0 := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_sum_abs_partitioned
      (X := X) hq hq') ?_
  exact centeredRamanujanPairCleanPeriodicGcdAbsPartitioned_le_two_mul_abs_baseWeight_partitioned
    (q := q) (q' := q') hq hq' hnotcop

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_sum_abs_partitioned
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                |if Nat.gcd g h = d then
                    centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                      * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                  else 0|)) := by
  rw [centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_eq_sum_over_sharedDivisors]
  calc
    |∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
        ∑ q' ∈
          centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
            (fun q' => ¬ Nat.Coprime q q'),
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                    * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                else 0|
      ≤
    ∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
      |∑ q' ∈
          centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
            (fun q' => ¬ Nat.Coprime q q'),
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                    * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                else 0| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun q =>
              ∑ q' ∈
                centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
                  (fun q' => ¬ Nat.Coprime q q'),
                ∑ d ∈ (Nat.gcd q q').divisors,
                  ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
                    ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                      if Nat.gcd g h = d then
                        centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                          * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                      else 0)
            centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0)
    _ ≤
    ∑ q ∈ centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0,
      ∑ q' ∈
        centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'),
        |∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                    * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                else 0| := by
        refine Finset.sum_le_sum ?_
        intro q hqmem
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun q' =>
              ∑ d ∈ (Nat.gcd q q').divisors,
                ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
                  ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                    if Nat.gcd g h = d then
                      centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                        * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                    else 0)
            (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
              (fun q' => ¬ Nat.Coprime q q')))
    _ ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                |if Nat.gcd g h = d then
                    centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h
                      * centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d
                  else 0|)) := by
        refine Finset.sum_le_sum ?_
        intro q hqmem
        refine Finset.sum_le_sum ?_
        intro q' hq'mem
        have hq : 1 ≤ q := (Finset.mem_Icc.mp ((Finset.mem_filter.mp hqmem).1)).1
        have hq' : 1 ≤ q' :=
          (Finset.mem_Icc.mp ((Finset.mem_filter.mp ((Finset.mem_filter.mp hq'mem).1)).1)).1
        simpa [centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_eq_partitionedByGcdDivisors
          (X := X) hq hq'] using
          (abs_centeredRamanujanPairCleanPeriodicGcdCorrectionTerm_le_sum_abs_partitioned
            (X := X) (q := q) (q' := q') hq hq')

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_two_mul_abs_baseWeight_partitioned
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                else 0)) := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_sum_abs_partitioned
      (X := X)) ?_
  refine Finset.sum_le_sum ?_
  intro q hqmem
  refine Finset.sum_le_sum ?_
  intro q' hq'mem
  have hq : 1 ≤ q := (Finset.mem_Icc.mp ((Finset.mem_filter.mp hqmem).1)).1
  have hq' : 1 ≤ q' :=
    (Finset.mem_Icc.mp ((Finset.mem_filter.mp ((Finset.mem_filter.mp hq'mem).1)).1)).1
  have hnotcop : ¬ Nat.Coprime q q' := (Finset.mem_filter.mp hq'mem).2
  exact centeredRamanujanPairCleanPeriodicGcdAbsPartitioned_le_two_mul_abs_baseWeight_partitioned
    (q := q) (q' := q') hq hq' hnotcop

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_absBaseWeight_mul_absCaseScalar_partitioned
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|
      ≤
    Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                    * |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d|
                else 0)) := by
  refine le_trans
    (abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_sum_abs_partitioned
      (X := X)) ?_
  refine Finset.sum_le_sum ?_
  intro q hqmem
  refine Finset.sum_le_sum ?_
  intro q' hq'mem
  exact le_of_eq
    (centeredRamanujanPairCleanPeriodicGcdAbsPartitioned_eq_absBaseWeight_mul_absCaseScalar_partitioned
      (q := q) (q' := q'))

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_le_commonPrime_productMajorants_add_gcdCorrection_partitioned_add_abs_remainder
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0 X|
      ≤
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant q q' d
              * centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant q' d)))
      +
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                else 0)))
      +
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
  rw [centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_eq_commonPrime_add_gcdCorrection_add_remainder]
  calc
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X|
      ≤
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        simpa [add_assoc] using
          (abs_add_le
            (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
              + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X)
            (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X))
    _ ≤
    (|centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X|
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|)
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        gcongr
        exact abs_add_le
          (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X)
          (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X)
    _ ≤
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            centeredRamanujanPairCleanPeriodicCommonPrimeLeftProductMajorant q q' d
              * centeredRamanujanPairCleanPeriodicCommonPrimeRightProductMajorant q' d)))
      +
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                else 0)))
      +
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        gcongr
        · exact abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_productMajorants X
        · exact abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_two_mul_abs_baseWeight_partitioned X

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_le_commonPrime_coprimeReindexed_add_gcdCorrection_partitioned_add_abs_remainder
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0 X|
      ≤
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
              ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
                if Nat.Coprime a1 b1 then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
                else 0)))
      +
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                else 0)))
      +
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
  rw [centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_eq_commonPrime_add_gcdCorrection_add_remainder]
  calc
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X|
      ≤
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        simpa [add_assoc] using
          (abs_add_le
            (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
              + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X)
            (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X))
    _ ≤
    (|centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X|
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|)
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        gcongr
        exact abs_add_le
          (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X)
          (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X)
    _ ≤
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
              ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
                if Nat.Coprime a1 b1 then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
                else 0)))
      +
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  (2 : ℝ) * |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                else 0)))
      +
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        gcongr
        · exact abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_coprime_reindexedMajorants X
        · exact abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_two_mul_abs_baseWeight_partitioned X

theorem abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_le_commonPrime_coprimeReindexed_add_gcdCorrection_caseSensitive_add_abs_remainder
    (X : ℕ) :
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0 X|
      ≤
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
              ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
                if Nat.Coprime a1 b1 then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
                else 0)))
      +
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                    * |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d|
                else 0)))
      +
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
  rw [centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0_eq_commonPrime_add_gcdCorrection_add_remainder]
  calc
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X|
      ≤
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
        + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        simpa [add_assoc] using
          (abs_add_le
            (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X
              + centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X)
            (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X))
    _ ≤
    (|centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X|
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X|)
      + |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        gcongr
        exact abs_add_le
          (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0 X)
          (centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0 X)
    _ ≤
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors.filter (fun d => d ≠ 1),
            ∑ a1 ∈ (q / d).divisors.filter (fun a1 => Goldbach.Windows.IsEven ((q / d) / a1)),
              ∑ b1 ∈ (q' / d).divisors.filter (fun b1 => Goldbach.Windows.IsEven ((q' / d) / b1)),
                if Nat.Coprime a1 b1 then
                  centeredRamanujanPairCleanPeriodicCommonPrimeReducedMajorant X q q' (d * a1) (d * b1)
                else 0)))
      +
    (Finset.sum centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0 (fun q =>
      Finset.sum
        (centeredRamanujanPairCleanPeriodicOneVariableSupportUpToQ0.filter
          (fun q' => ¬ Nat.Coprime q q'))
        (fun q' =>
          ∑ d ∈ (Nat.gcd q q').divisors,
            ∑ g ∈ q.divisors.filter Goldbach.Windows.IsEven,
              ∑ h ∈ q'.divisors.filter Goldbach.Windows.IsEven,
                if Nat.gcd g h = d then
                  |centeredRamanujanPairCleanPeriodicGcdBaseWeight q q' g h|
                    * |centeredRamanujanPairCleanPeriodicGcdCaseScalar q q' d|
                else 0)))
      +
    |centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0 X| := by
        gcongr
        · exact abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0_le_sum_coprime_reindexedMajorants X
        · exact abs_centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionUpToQ0_le_absBaseWeight_mul_absCaseScalar_partitioned X


theorem rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_coprime_explicitCoefficientMismatch_add_remainder
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcop : Nat.Coprime (q / g) (q' / h)) :
    rawEvenRamanujanGcdClassPeriodicTotientComparison X q q' g h
      =
    (let A := q / g
     let B := q' / h
     let PairLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
       - (X ⌈/⌉ Nat.lcm g h)
     let LeftLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g)
     let RightLen := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h)
     ((Nat.totient A : ℝ) * (Nat.totient B : ℝ))
       * ((((PairLen / (A * B) : ℕ) : ℝ))
           - ((((LeftLen / A : ℕ) : ℝ) * (((RightLen / B : ℕ) : ℝ)))
               / (Nat.lcm q q' : ℝ))))
      + rawEvenRamanujanGcdClassPeriodicRemainderTerm X q q' g h := by
  rw [rawEvenRamanujanGcdClassPeriodicTotientComparison_eq_coprime_coefficientMismatch_add_remainder
    hq hq' hg hh hcop]
  rw [rawEvenRamanujanGcdClassPeriodicCoefficientMismatchTerm_eq_explicit_blockDensity]

theorem rawEvenRamanujanGcdClassBlockCount_eq_periodicCount
    {X q q' q0 g0 : ℕ} (hq0 : 1 ≤ q0) (hg0 : g0 ∈ q0.divisors)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q') :
    rawEvenRamanujanGcdClassBlockCount X q q' q0 g0
      = rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q0 g0 := by
  have hg0pos : 0 < g0 := divisor_pos_of_mem_divisors_of_pos hg0 hq0
  by_cases hgEven : Goldbach.Windows.IsEven g0
  · rw [rawEvenRamanujanGcdClassBlockPeriodicCount, if_pos hgEven]
    have hMpos : 0 < q0 / g0 := quotient_pos_of_mem_divisors hq0 hg0
    rw [rawEvenRamanujanGcdClassBlockCount_eq_even_g_fullPeriods_add_remainder
      X q q' q0 g0 hg0pos hPpos hgEven hMpos]
  · rw [rawEvenRamanujanGcdClassBlockPeriodicCount, if_neg hgEven]
    rw [rawEvenRamanujanGcdClassBlockCount_eq_odd_g_fullPeriods_add_remainder
      X q q' q0 g0 hg0pos hPpos hgEven]

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_periodicCount
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      = rawEvenRamanujanGcdClassPairBlockPeriodicCount X q q' g h := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  by_cases hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h)
  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount, if_pos hEvenL]
    have hMpos : 0 < ramanujanGcdClassJointModulus q q' g h := by
      unfold ramanujanGcdClassJointModulus
      exact Nat.mul_pos (quotient_pos_of_mem_divisors hq hg) (quotient_pos_of_mem_divisors hq' hh)
    rw [rawEvenRamanujanGcdClassPairBlockCount_eq_even_lcm_fullPeriods_add_remainder
      X q q' g h (Nat.lcm_pos hgpos hhpos) hPpos hcompat hEvenL hMpos]
  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount, if_neg hEvenL]
    rw [rawEvenRamanujanGcdClassPairBlockCount_eq_odd_lcm_fullPeriods_add_remainder
      X q q' g h (Nat.lcm_pos hgpos hhpos) hPpos hcompat hEvenL]

noncomputable def rawEvenRamanujanGcdClassPairBlockResolvedCount
    (X q q' g h : ℕ) : ℝ :=
  if ramanujanGcdClassJointCompatibility q q' g h then
    rawEvenRamanujanGcdClassPairBlockPeriodicCount X q q' g h
  else
    0

theorem rawEvenRamanujanGcdClassPairBlockCount_eq_resolvedCount
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPairBlockCount X q q' g h
      = rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h := by
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos hh hq'
  by_cases hcompat : ramanujanGcdClassJointCompatibility q q' g h
  · rw [rawEvenRamanujanGcdClassPairBlockResolvedCount, if_pos hcompat]
    rw [rawEvenRamanujanGcdClassPairBlockCount_eq_periodicCount hq hq' hg hh hcompat]
  · rw [rawEvenRamanujanGcdClassPairBlockResolvedCount, if_neg hcompat]
    rw [rawEvenRamanujanGcdClassPairBlockCount_eq_zero_of_not_compatibility
      X q q' g h (Nat.lcm_pos hgpos hhpos) hcompat]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_periodic_comparison
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    rawEvenRamanujanGcdClassPairBlockPeriodicCount X q q' g h
      - ramanujanGcdClassWindowAverage X q' h
          * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
      - ramanujanGcdClassWindowAverage X q g
          * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_periodicCount hq hq' hg hh hcompat]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_periodicCount hq hg hPpos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_periodicCount hq' hh hPpos]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_resolved_periodic_comparison
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h
      - ramanujanGcdClassWindowAverage X q' h
          * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
      - ramanujanGcdClassWindowAverage X q g
          * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_resolvedCount hq hq' hg hh]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_periodicCount hq hg hPpos]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_periodicCount hq' hh hPpos]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_even_even_productDefect_add_densityMismatch
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hgEven : Goldbach.Windows.IsEven g) (hhEven : Goldbach.Windows.IsEven h) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    rawEvenRamanujanGcdClassPeriodicProductDefect X q q' g h
      + evenRamanujanBlockCount X q q'
          * ((rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
                / evenRamanujanBlockCount X q q'
                - ramanujanGcdClassWindowAverage X q g)
              * (rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
                  / evenRamanujanBlockCount X q q'
                  - ramanujanGcdClassWindowAverage X q' h)) := by
  have _hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h) := isEven_lcm_of_isEven_left hgEven
  have _hhEven : Goldbach.Windows.IsEven h := hhEven
  have hBne : evenRamanujanBlockCount X q q' ≠ 0 := by
    exact ne_of_gt (evenRamanujanBlockCount_pos X q q' hq hq')
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_periodic_comparison hq hq' hg hh hcompat]
  unfold rawEvenRamanujanGcdClassPeriodicProductDefect
  field_simp [hBne]
  ring_nf

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_card_filter_decomposition
    {X q q' g h : ℕ} (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      =
    (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
        (rawEvenRamanujanGcdClassPairBlockHit X q q' g h)).card : ℝ)
      - ramanujanGcdClassWindowAverage X q' h * (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
          (rawEvenRamanujanGcdClassBlockHit X q g)).card : ℝ)
      - ramanujanGcdClassWindowAverage X q g * (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
          (rawEvenRamanujanGcdClassBlockHit X q' h)).card : ℝ)
      + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
          * evenRamanujanBlockCount X q q' := by
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_card_filter]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_card_filter (X := X) (q := q) (q' := q') (q0 := q) (g0 := g)]
  rw [rawEvenRamanujanGcdClassBlockCount_eq_card_filter (X := X) (q := q) (q' := q') (q0 := q') (g0 := h)]

/-- Boundary remainder after extracting all complete `2*lcm(q,q')` even blocks from the gcd-class covariance. -/
noncomputable def centeredRamanujanGcdClassPairBoundaryRemainder
    (X q q' g h : ℕ) : ℝ :=
  let P := centeredRamanujanPairBlockPeriod q q'
  let m := (H + 1) / P
  let r := (H + 1) % P
  ∑ k ∈ Finset.range r, centeredEvenRamanujanGcdClassPairOffset X q q' g h (m * P + k)

theorem centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanGcdClassPairCorrelation X q q' g h
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
      • centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
      + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h := by
  let P := centeredRamanujanPairBlockPeriod q q'
  let m := (H + 1) / P
  let r := (H + 1) % P
  have hP : 0 < P := by
    dsimp [P, centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hper : ∀ k, centeredEvenRamanujanGcdClassPairOffset X q q' g h (k + P) =
      centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
    intro k
    simpa [P] using centeredEvenRamanujanGcdClassPairOffset_add_blockPeriod
      (X := X) (q := q) (q' := q') (g := g) (h := h) (k := k)
  rw [← sum_range_centeredEvenRamanujanGcdClassPairOffset_eq_pairCorrelation]
  calc
    ∑ k ∈ Finset.range (H + 1), centeredEvenRamanujanGcdClassPairOffset X q q' g h k
      =
    ∑ k ∈ Finset.range (m * P + r), centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
      congr 2
      dsimp [m, r]
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod (H + 1) P).symm
    _ =
      m • ∑ k ∈ Finset.range P, centeredEvenRamanujanGcdClassPairOffset X q q' g h k
        + ∑ k ∈ Finset.range r, centeredEvenRamanujanGcdClassPairOffset X q q' g h (m * P + k) := by
          exact periodic_sum_range_blocks_add_remainder
            (f := centeredEvenRamanujanGcdClassPairOffset X q q' g h) hP hper m r
    _ =
      (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
        • centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h
        + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h := by
          simp [centeredRamanujanGcdClassPairFullEvenBlockSum,
            centeredRamanujanGcdClassPairBoundaryRemainder, P, m, r]

theorem centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary_count
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairCorrelation X q q' g h
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
      • (rawEvenRamanujanGcdClassPairBlockCount X q q' g h
          - ramanujanGcdClassWindowAverage X q' h * rawEvenRamanujanGcdClassBlockCount X q q' q g
          - ramanujanGcdClassWindowAverage X q g * rawEvenRamanujanGcdClassBlockCount X q q' q' h
          + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
              * evenRamanujanBlockCount X q q')
      + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h := by
  rw [centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary hq hq']
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_count_decomposition hg hh]

theorem centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary_card
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    centeredRamanujanGcdClassPairCorrelation X q q' g h
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
      • ((((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
            (rawEvenRamanujanGcdClassPairBlockHit X q q' g h)).card : ℝ)
          - ramanujanGcdClassWindowAverage X q' h * (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
              (rawEvenRamanujanGcdClassBlockHit X q g)).card : ℝ)
          - ramanujanGcdClassWindowAverage X q g * (((Finset.range (centeredRamanujanPairBlockPeriod q q')).filter
              (rawEvenRamanujanGcdClassBlockHit X q' h)).card : ℝ)
          + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
              * evenRamanujanBlockCount X q q')
      + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h := by
  rw [centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary hq hq']
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_card_filter_decomposition hg hh]

theorem centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary_periodic
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors)
    :
    centeredRamanujanGcdClassPairCorrelation X q q' g h
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
      • (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h
          - ramanujanGcdClassWindowAverage X q' h
              * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
          - ramanujanGcdClassWindowAverage X q g
              * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
          + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
              * evenRamanujanBlockCount X q q')
      + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h := by
  rw [centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary hq hq']
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_resolved_periodic_comparison hq hq' hg hh]

theorem centeredRamanujanPairCorrelation_eq_sum_gcdClassPeriodicCovariances
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCorrelation X q q'
      =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h
                - ramanujanGcdClassWindowAverage X q' h
                    * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
                - ramanujanGcdClassWindowAverage X q g
                    * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
                + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                    * evenRamanujanBlockCount X q q')
            + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h) := by
  rw [centeredRamanujanPairCorrelation_eq_sum_gcdClassCovariances hq hq']
  refine Finset.sum_congr rfl ?_
  intro g hg
  refine Finset.sum_congr rfl ?_
  intro h hh
  rw [centeredRamanujanGcdClassPairCorrelation_eq_fullBlocks_add_boundary_periodic hq hq' hg hh]

noncomputable def centeredRamanujanPairPeriodicMainTerm
    (X q q' : ℕ) : ℝ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
      * ((((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h
              - ramanujanGcdClassWindowAverage X q' h
                  * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
              - ramanujanGcdClassWindowAverage X q g
                  * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
              + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                  * evenRamanujanBlockCount X q q'))

noncomputable def centeredRamanujanPairPeriodicBoundaryTerm
    (X q q' : ℕ) : ℝ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
      * centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h

theorem centeredRamanujanPairCorrelation_eq_periodicMain_add_boundary
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairCorrelation X q q'
      =
    centeredRamanujanPairPeriodicMainTerm X q q'
      + centeredRamanujanPairPeriodicBoundaryTerm X q q' := by
  rw [centeredRamanujanPairCorrelation_eq_sum_gcdClassPeriodicCovariances hq hq']
  unfold centeredRamanujanPairPeriodicMainTerm centeredRamanujanPairPeriodicBoundaryTerm
  calc
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
          ((((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ) •
              (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h -
                    ramanujanGcdClassWindowAverage X q' h *
                      rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g -
                  ramanujanGcdClassWindowAverage X q g *
                    rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h +
                ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h *
                  evenRamanujanBlockCount X q q')
            + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h)
      =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      (ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
          ((((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ) •
              (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h -
                    ramanujanGcdClassWindowAverage X q' h *
                      rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g -
                  ramanujanGcdClassWindowAverage X q g *
                    rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h +
                ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h *
                  evenRamanujanBlockCount X q q'))
        + ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
            centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h) := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          refine Finset.sum_congr rfl ?_
          intro h hh
          ring
    _ =
      (∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
          ((((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ) •
              (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h -
                    ramanujanGcdClassWindowAverage X q' h *
                      rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g -
                  ramanujanGcdClassWindowAverage X q g *
                    rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h +
                  ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h *
                  evenRamanujanBlockCount X q q'))
      +
      ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
          centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h) := by
            have hsplit_inner :
                (∑ g ∈ q.divisors,
                    ∑ h ∈ q'.divisors,
                      (ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
                          (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ) •
                            (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h -
                                  ramanujanGcdClassWindowAverage X q' h *
                                    rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g -
                                ramanujanGcdClassWindowAverage X q g *
                                  rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h +
                              ramanujanGcdClassWindowAverage X q g *
                                  ramanujanGcdClassWindowAverage X q' h *
                                evenRamanujanBlockCount X q q')
                        +
                        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
                          centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h))
                  =
                ∑ g ∈ q.divisors,
                  ((∑ h ∈ q'.divisors,
                      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
                        (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ) •
                          (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h -
                                ramanujanGcdClassWindowAverage X q' h *
                                  rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g -
                              ramanujanGcdClassWindowAverage X q g *
                                rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h +
                            ramanujanGcdClassWindowAverage X q g *
                                ramanujanGcdClassWindowAverage X q' h *
                              evenRamanujanBlockCount X q q'))
                    +
                    ∑ h ∈ q'.divisors,
                      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h *
                        centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h) := by
                  refine Finset.sum_congr rfl ?_
                  intro g hg
                  rw [Finset.sum_add_distrib]
            rw [hsplit_inner, Finset.sum_add_distrib]
    _ = centeredRamanujanPairPeriodicMainTerm X q q' + centeredRamanujanPairPeriodicBoundaryTerm X q q' := by
      rfl

theorem centeredRamanujanPairCorrelation_eq_closedForm_sum
    (X q q' : ℕ) :
    centeredRamanujanPairCorrelation X q q'
      =
    ∑ N ∈ EvenIn X H,
      ((((((ArithmeticFunction.moebius : ArithmeticFunction ℤ)
            (q / Nat.gcd q N) : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd q N) : ℝ))
          - ramanujanWindowAverage X q)
        *
       (((((ArithmeticFunction.moebius : ArithmeticFunction ℤ)
            (q' / Nat.gcd q' N) : ℤ) : ℝ)
            * (Nat.totient (Nat.gcd q' N) : ℝ))
          - ramanujanWindowAverage X q')) := by
  unfold centeredRamanujanPairCorrelation
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [centeredRamanujanObservable_eq_closedForm_sub_average]
  rw [centeredRamanujanObservable_eq_closedForm_sub_average]

theorem centeredRamanujanPairCorrelation_symm
    (X q q' : ℕ) :
    centeredRamanujanPairCorrelation X q q'
      =
    centeredRamanujanPairCorrelation X q' q := by
  unfold centeredRamanujanPairCorrelation
  refine Finset.sum_congr rfl ?_
  intro N hN
  ring

theorem centeredRamanujanPairCorrelation_sq_le
    (X q q' : ℕ) :
    (centeredRamanujanPairCorrelation X q q') ^ 2
      ≤
    centeredRamanujanWindowEnergy X q * centeredRamanujanWindowEnergy X q' := by
  have hcs :
      (∑ N ∈ EvenIn X H,
          centeredRamanujanObservable X q N * centeredRamanujanObservable X q' N) ^ 2
        ≤
      (∑ N ∈ EvenIn X H, (centeredRamanujanObservable X q N) ^ 2)
        *
      ∑ N ∈ EvenIn X H, (centeredRamanujanObservable X q' N) ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (s := EvenIn X H)
        (f := fun N => centeredRamanujanObservable X q N)
        (g := fun N => centeredRamanujanObservable X q' N))
  unfold centeredRamanujanPairCorrelation centeredRamanujanWindowEnergy
  exact hcs

theorem abs_centeredRamanujanPairCorrelation_le
    (X q q' : ℕ) :
    |centeredRamanujanPairCorrelation X q q'|
      ≤
    Real.sqrt (centeredRamanujanWindowEnergy X q * centeredRamanujanWindowEnergy X q') := by
  have hsquare := centeredRamanujanPairCorrelation_sq_le X q q'
  have hnonneg :
      0 ≤ centeredRamanujanWindowEnergy X q * centeredRamanujanWindowEnergy X q' := by
    unfold centeredRamanujanWindowEnergy
    exact mul_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have habs_sq :
      |centeredRamanujanPairCorrelation X q q'| ^ 2
        ≤
      centeredRamanujanWindowEnergy X q * centeredRamanujanWindowEnergy X q' := by
    simpa [sq_abs] using hsquare
  have hsqrt_sq :
      |centeredRamanujanPairCorrelation X q q'| ^ 2
        ≤
      (Real.sqrt (centeredRamanujanWindowEnergy X q * centeredRamanujanWindowEnergy X q')) ^ 2 := by
    simpa [Real.sq_sqrt hnonneg] using habs_sq
  have habs_le :
      abs (abs (centeredRamanujanPairCorrelation X q q'))
        ≤
      abs (Real.sqrt (centeredRamanujanWindowEnergy X q * centeredRamanujanWindowEnergy X q')) := by
    exact sq_le_sq.mp hsqrt_sq
  simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] using habs_le

theorem normalizedSigmaTruncSummandWindowAverage_re_eq_coeff_mul_ramanujanAverage
    (X q : ℕ) :
    (normalizedSigmaTruncSummandWindowAverage ramanujanSeriesOnWindow X q).re
      =
    normalizedSigmaTruncSummandRealCoeff q * ramanujanWindowAverage X q := by
  unfold normalizedSigmaTruncSummandWindowAverage ramanujanWindowAverage
  rw [Complex.mul_re]
  have hscalar_im : (((↑(EvenIn X H).card : ℂ)⁻¹).im = 0) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  have hterm_im :
      ∀ N : ℕ, (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).im = 0 := by
    intro N
    rw [normalizedSigmaTruncSummand, Complex.ofReal_im]
  have hsum_im :
      (∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).im = 0 := by
    refine Finset.induction_on (EvenIn X H) ?_ ?_
    · simp
    · intro N s hNhs ih
      rw [Finset.sum_insert hNhs, Complex.add_im, hterm_im N, ih]
      norm_num
  have hsum_re :
      (∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re
        =
      ∑ N ∈ EvenIn X H, (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re := by
    refine Finset.induction_on (EvenIn X H) ?_ ?_
    · simp
    · intro N s hNhs ih
      rw [Finset.sum_insert hNhs, Complex.add_re, ih, Finset.sum_insert hNhs]
  have hsum_coeff :
      ∑ N ∈ EvenIn X H, (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re
        =
      ∑ N ∈ EvenIn X H,
        normalizedSigmaTruncSummandRealCoeff q
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [normalizedSigmaTruncSummand_re_eq_coeff_mul_ramanujan]
  calc
    ((↑(EvenIn X H).card : ℂ)⁻¹).re
        * (∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re
        -
      ((↑(EvenIn X H).card : ℂ)⁻¹).im
        * (∑ N ∈ EvenIn X H, normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).im
      =
        (((↑(EvenIn X H).card : ℂ)⁻¹).re) *
          ∑ N ∈ EvenIn X H, (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re := by
            rw [hsum_re, hsum_im, hscalar_im]
            ring
    _ =
        (((EvenIn X H).card : ℝ)⁻¹) *
          ∑ N ∈ EvenIn X H, (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).re := by
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    _ =
        (((EvenIn X H).card : ℝ)⁻¹) *
          ∑ N ∈ EvenIn X H,
            normalizedSigmaTruncSummandRealCoeff q
              * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
                rw [hsum_coeff]
    _ =
        normalizedSigmaTruncSummandRealCoeff q *
          ((((EvenIn X H).card : ℝ)⁻¹) *
            ∑ N ∈ EvenIn X H, Goldbach.AO_OffDiag.TailBlock.ramanujanR q N) := by
              have hfactor :
                  ∑ N ∈ EvenIn X H,
                      normalizedSigmaTruncSummandRealCoeff q
                        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
                    =
                  normalizedSigmaTruncSummandRealCoeff q
                    * ∑ N ∈ EvenIn X H, Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
                      rw [← Finset.mul_sum]
              rw [hfactor]
              ring
    _ = normalizedSigmaTruncSummandRealCoeff q * ramanujanWindowAverage X q := by
          rw [ramanujanWindowAverage]

theorem centeredNormalizedSigmaTruncSummand_re_eq_coeff_mul_centeredRamanujan
    (X q N : ℕ) :
    (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
      =
    normalizedSigmaTruncSummandRealCoeff q * centeredRamanujanObservable X q N := by
  rw [centeredNormalizedSigmaTruncSummand_re_eq_coeff_mul_ramanujan_sub_average]
  rw [normalizedSigmaTruncSummandWindowAverage_re_eq_coeff_mul_ramanujanAverage]
  unfold centeredRamanujanObservable
  ring

private theorem normalizedSigmaTruncSummandWindowAverage_im_eq_zero'
    (X q : ℕ) :
    (normalizedSigmaTruncSummandWindowAverage ramanujanSeriesOnWindow X q).im = 0 := by
  have hterm_im :
      ∀ N : ℕ, (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).im = 0 := by
    intro N
    rw [normalizedSigmaTruncSummand, Complex.ofReal_im]
  unfold normalizedSigmaTruncSummandWindowAverage
  rw [Finset.mul_sum]
  have hscalar_im : (((↑(EvenIn X H).card : ℂ)⁻¹).im = 0) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  refine Finset.induction_on (EvenIn X H) ?_ ?_
  · simp
  · intro N s hNhs ih
    simp [Finset.sum_insert, hNhs, Complex.mul_im, hterm_im]

private theorem centeredNormalizedSigmaTruncSummand_norm_sq_eq_re_sq
    (X q N : ℕ) :
    ‖centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N‖ ^ 2
      =
    (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re ^ 2 := by
  have him :
      (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).im = 0 := by
    have hterm_im :
        (normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N).im = 0 := by
      rw [normalizedSigmaTruncSummand, Complex.ofReal_im]
    unfold centeredNormalizedSigmaTruncSummand
    rw [Complex.sub_im]
    rw [hterm_im, normalizedSigmaTruncSummandWindowAverage_im_eq_zero' X q]
    norm_num
  have hz :
      centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N
        =
      Complex.ofReal
        ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re) := by
    apply Complex.ext
    · change (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
          = (Complex.ofReal
              ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re)).re
      simp
    · change (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).im
          = (Complex.ofReal
              ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re)).im
      simpa using him
  rw [hz, Complex.sq_norm, Complex.normSq_ofReal]
  rw [pow_two]
  rfl

theorem centeredNormalizedSigmaTruncDiagonalEnergy_eq_sum_summandEnergies
    (X : ℕ) :
    centeredNormalizedSigmaTruncDiagonalEnergy X
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q := by
  unfold centeredNormalizedSigmaTruncDiagonalEnergy centeredNormalizedSigmaTruncSummandWindowEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro q hq
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [← centeredNormalizedSigmaTruncSummand_norm_sq_eq_re_sq]

/-- Per-pair centered truncation correlation on the canonical even window. -/
noncomputable def centeredNormalizedSigmaTruncPairCorrelation
    (X q q' : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
      * (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re

theorem centeredNormalizedSigmaTruncPairCorrelation_symm
    (X q q' : ℕ) :
    centeredNormalizedSigmaTruncPairCorrelation X q q'
      =
    centeredNormalizedSigmaTruncPairCorrelation X q' q := by
  unfold centeredNormalizedSigmaTruncPairCorrelation
  refine Finset.sum_congr rfl ?_
  intro N hN
  ring

theorem centeredNormalizedSigmaTruncPairCorrelation_eq_coeffs_mul_centeredRamanujanPairCorrelation
    (X q q' : ℕ) :
    centeredNormalizedSigmaTruncPairCorrelation X q q'
      =
    normalizedSigmaTruncSummandRealCoeff q
      * normalizedSigmaTruncSummandRealCoeff q'
      * centeredRamanujanPairCorrelation X q q' := by
  unfold centeredNormalizedSigmaTruncPairCorrelation centeredRamanujanPairCorrelation
  calc
    ∑ N ∈ EvenIn X H,
        (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re *
          (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re
      =
        ∑ N ∈ EvenIn X H,
          (normalizedSigmaTruncSummandRealCoeff q * centeredRamanujanObservable X q N) *
            (normalizedSigmaTruncSummandRealCoeff q' * centeredRamanujanObservable X q' N) := by
              refine Finset.sum_congr rfl ?_
              intro N hN
              rw [centeredNormalizedSigmaTruncSummand_re_eq_coeff_mul_centeredRamanujan]
              rw [centeredNormalizedSigmaTruncSummand_re_eq_coeff_mul_centeredRamanujan]
    _ =
        ∑ N ∈ EvenIn X H,
          (normalizedSigmaTruncSummandRealCoeff q
            * normalizedSigmaTruncSummandRealCoeff q')
            * (centeredRamanujanObservable X q N * centeredRamanujanObservable X q' N) := by
              refine Finset.sum_congr rfl ?_
              intro N hN
              ring
    _ =
        (normalizedSigmaTruncSummandRealCoeff q
          * normalizedSigmaTruncSummandRealCoeff q')
          * ∑ N ∈ EvenIn X H,
              centeredRamanujanObservable X q N * centeredRamanujanObservable X q' N := by
                rw [Finset.mul_sum]
    _ =
        normalizedSigmaTruncSummandRealCoeff q
          * normalizedSigmaTruncSummandRealCoeff q'
          * centeredRamanujanPairCorrelation X q q' := by
            rw [centeredRamanujanPairCorrelation]

theorem centeredNormalizedSigmaTruncPairCorrelation_eq_periodicGcdClassExpansion
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredNormalizedSigmaTruncPairCorrelation X q q'
      =
    normalizedSigmaTruncSummandRealCoeff q
      * normalizedSigmaTruncSummandRealCoeff q'
      * (∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
          ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
            * ((((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
                • (rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h
                    - ramanujanGcdClassWindowAverage X q' h
                        * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q g
                    - ramanujanGcdClassWindowAverage X q g
                        * rawEvenRamanujanGcdClassBlockPeriodicCount X q q' q' h
                    + ramanujanGcdClassWindowAverage X q g * ramanujanGcdClassWindowAverage X q' h
                        * evenRamanujanBlockCount X q q')
                + centeredRamanujanGcdClassPairBoundaryRemainder X q q' g h)) := by
  rw [centeredNormalizedSigmaTruncPairCorrelation_eq_coeffs_mul_centeredRamanujanPairCorrelation]
  rw [centeredRamanujanPairCorrelation_eq_sum_gcdClassPeriodicCovariances hq hq']

noncomputable def centeredNormalizedSigmaTruncPeriodicMainTerm
    (X q q' : ℕ) : ℝ :=
  normalizedSigmaTruncSummandRealCoeff q
    * normalizedSigmaTruncSummandRealCoeff q'
    * centeredRamanujanPairPeriodicMainTerm X q q'

noncomputable def centeredNormalizedSigmaTruncPeriodicBoundaryTerm
    (X q q' : ℕ) : ℝ :=
  normalizedSigmaTruncSummandRealCoeff q
    * normalizedSigmaTruncSummandRealCoeff q'
    * centeredRamanujanPairPeriodicBoundaryTerm X q q'

theorem centeredNormalizedSigmaTruncPairCorrelation_eq_periodicMain_add_boundary
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredNormalizedSigmaTruncPairCorrelation X q q'
      =
    centeredNormalizedSigmaTruncPeriodicMainTerm X q q'
      + centeredNormalizedSigmaTruncPeriodicBoundaryTerm X q q' := by
  unfold centeredNormalizedSigmaTruncPeriodicMainTerm centeredNormalizedSigmaTruncPeriodicBoundaryTerm
  rw [centeredNormalizedSigmaTruncPairCorrelation_eq_coeffs_mul_centeredRamanujanPairCorrelation]
  rw [centeredRamanujanPairCorrelation_eq_periodicMain_add_boundary hq hq']
  ring

theorem centeredNormalizedSigmaTruncPairCorrelation_sq_le
    (X q q' : ℕ) :
    (centeredNormalizedSigmaTruncPairCorrelation X q q') ^ 2
      ≤
    centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q
      * centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q' := by
  have hcs :
      (∑ N ∈ EvenIn X H,
          (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
            * (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re) ^ 2
        ≤
      (∑ N ∈ EvenIn X H,
          ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re) ^ 2)
        *
      ∑ N ∈ EvenIn X H,
          ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re) ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (s := EvenIn X H)
        (f := fun N => (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re)
        (g := fun N => (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re))
  unfold centeredNormalizedSigmaTruncPairCorrelation
    centeredNormalizedSigmaTruncSummandWindowEnergy
  calc
    (∑ N ∈ EvenIn X H,
        (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re
          * (centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re) ^ 2
        ≤
      (∑ N ∈ EvenIn X H,
          ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N).re) ^ 2)
        *
      ∑ N ∈ EvenIn X H,
          ((centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N).re) ^ 2 := hcs
    _ =
      (∑ N ∈ EvenIn X H,
          ‖centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q N‖ ^ 2)
        *
      ∑ N ∈ EvenIn X H,
          ‖centeredNormalizedSigmaTruncSummand ramanujanSeriesOnWindow X q' N‖ ^ 2 := by
            refine congrArg₂ (· * ·) ?_ ?_
            · refine Finset.sum_congr rfl ?_
              intro N hN
              rw [← centeredNormalizedSigmaTruncSummand_norm_sq_eq_re_sq]
            · refine Finset.sum_congr rfl ?_
              intro N hN
              rw [← centeredNormalizedSigmaTruncSummand_norm_sq_eq_re_sq]

theorem abs_centeredNormalizedSigmaTruncPairCorrelation_le
    (X q q' : ℕ) :
    |centeredNormalizedSigmaTruncPairCorrelation X q q'|
      ≤
    Real.sqrt
      (centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q
        * centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q') := by
  have hsquare := centeredNormalizedSigmaTruncPairCorrelation_sq_le X q q'
  have hnonneg :
      0 ≤
      centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q
        * centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q' := by
    unfold centeredNormalizedSigmaTruncSummandWindowEnergy
    exact mul_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have habs_sq :
      |centeredNormalizedSigmaTruncPairCorrelation X q q'| ^ 2
        ≤
      centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q
        * centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q' := by
    simpa [sq_abs] using hsquare
  have hsqrt_sq :
      |centeredNormalizedSigmaTruncPairCorrelation X q q'| ^ 2
        ≤
      (Real.sqrt
        (centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q
          * centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q')) ^ 2 := by
    simpa [Real.sq_sqrt hnonneg] using habs_sq
  have habs_le :
      abs (abs (centeredNormalizedSigmaTruncPairCorrelation X q q')) ≤
      abs
        (Real.sqrt
          (centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q
            * centeredNormalizedSigmaTruncSummandWindowEnergy ramanujanSeriesOnWindow X q')) :=
    (sq_le_sq.mp hsqrt_sq)
  simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] using habs_le

/-- Squared `ℓ²(EvenIn X H)` energy of the centered raw true-series correction. -/
noncomputable def centeredRawHalfMassTrueSeriesCorrectionWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the centered raw true-tail residual. -/
noncomputable def centeredRawHalfMassTrueTailResidualWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2

/--
Native true-sigma window-energy target for the first centered packet on the direct normalized route.
-/
structure CenteredTrueSigmaWindowEnergyTarget (Cσ : ℝ) : Prop where
  Cσ_nonneg : 0 ≤ Cσ
  bound : ∀ {X : ℕ}, X0 ≤ X → centeredTrueSigmaWindowEnergy X ≤ Cσ

/-- Native truncation window-energy target on the direct normalized route. -/
structure CenteredNormalizedSigmaTruncWindowEnergyTarget (Cτ : ℝ) : Prop where
  Cτ_nonneg : 0 ≤ Cτ
  bound : ∀ {X : ℕ}, X0 ≤ X → centeredNormalizedSigmaTruncWindowEnergy X ≤ Cτ

private lemma normalizedSigmaTruncSummand_norm_le_inv_two_mul_C2
    {q N : ℕ}
    (hq : q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0) :
    ‖normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N‖
      ≤
    (1 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
  have hden_pos : 0 < ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
    nlinarith [ramanujanSeriesOnWindow.C.pos]
  have hterm :
      |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N| ≤ (1 : ℝ) := by
    by_cases hsq : Squarefree q
    · have hq0 : q ≠ 0 := Nat.ne_of_gt ((Finset.mem_Icc.mp hq).1)
      have hEq :
          |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N|
            =
          1 / ((Nat.totient (Nat.gcd q N) : ℝ) * (Nat.totient (q / Nat.gcd q N) : ℝ) ^ 2) := by
        simpa using
          (Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm_abs_eq_split q N hsq hq0)
      have hdpos : 0 < Nat.gcd q N := Nat.gcd_pos_of_pos_left N (Nat.pos_of_ne_zero hq0)
      have hd_le_q : Nat.gcd q N ≤ q := by
        simpa using (Nat.gcd_le_left (m := q) (n := N) (Nat.pos_of_ne_zero hq0))
      have hr0 : q / Nat.gcd q N ≠ 0 := by
        intro hdiv
        have : Nat.gcd q N = 0 ∨ q < Nat.gcd q N := (Nat.div_eq_zero_iff).1 hdiv
        cases this with
        | inl hd0 => exact (Nat.ne_of_gt hdpos) hd0
        | inr hlt => exact (Nat.not_lt_of_ge hd_le_q) hlt
      have hrpos : 0 < q / Nat.gcd q N := Nat.pos_of_ne_zero hr0
      have hd1 : (1 : ℝ) ≤ (Nat.totient (Nat.gcd q N) : ℝ) := by
        have : (1 : ℕ) ≤ Nat.totient (Nat.gcd q N) := Nat.succ_le_of_lt (Nat.totient_pos.mpr hdpos)
        exact_mod_cast this
      have hr1 : (1 : ℝ) ≤ (Nat.totient (q / Nat.gcd q N) : ℝ) := by
        have : (1 : ℕ) ≤ Nat.totient (q / Nat.gcd q N) := Nat.succ_le_of_lt (Nat.totient_pos.mpr hrpos)
        exact_mod_cast this
      have hr_sq1 : (1 : ℝ) ≤ (Nat.totient (q / Nat.gcd q N) : ℝ) ^ 2 := by
        have hnonneg : (0 : ℝ) ≤ (Nat.totient (q / Nat.gcd q N) : ℝ) := le_trans (by norm_num) hr1
        have hmul :
            (1 : ℝ) * (1 : ℝ)
              ≤
            (Nat.totient (q / Nat.gcd q N) : ℝ) * (Nat.totient (q / Nat.gcd q N) : ℝ) :=
          mul_le_mul hr1 hr1 (by norm_num : (0 : ℝ) ≤ 1) hnonneg
        simpa [pow_two] using hmul
      have hden1 :
          (1 : ℝ)
            ≤
          (Nat.totient (Nat.gcd q N) : ℝ) * (Nat.totient (q / Nat.gcd q N) : ℝ) ^ 2 := by
        have hnonneg : (0 : ℝ) ≤ (Nat.totient (Nat.gcd q N) : ℝ) := le_trans (by norm_num) hd1
        have hmul :
            (1 : ℝ) * (1 : ℝ)
              ≤
            (Nat.totient (Nat.gcd q N) : ℝ) * (Nat.totient (q / Nat.gcd q N) : ℝ) ^ 2 :=
          mul_le_mul hd1 hr_sq1 (by norm_num : (0 : ℝ) ≤ 1) hnonneg
        simpa [one_mul] using hmul
      rw [hEq]
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden1)
    · have hsigma0 : Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N = 0 := by
          exact Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm_eq_zero_of_not_squarefree hsq
      have hzero : |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N| ≤ (1 : ℝ) := by
        rw [hsigma0]
        norm_num
      simpa [Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm] using hzero
  change ‖((((Goldbach.AO_OffDiag.TailBlock.muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) *
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q N)
      / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) : ℝ) : ℂ)‖
      ≤ (1 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2)
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [show ((Goldbach.AO_OffDiag.TailBlock.muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) *
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q N) =
      Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N by rfl]
  rw [abs_div, abs_of_nonneg (le_of_lt hden_pos)]
  have hden_nonneg : 0 ≤ ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := le_of_lt hden_pos
  simpa using (div_le_div_of_nonneg_right hterm hden_nonneg)

private lemma normalizedSigmaTruncQ0_norm_le_Q0_div_C2
    (N : ℕ) :
    ‖normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N‖
      ≤
    (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
  have htri :
      ‖∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N‖
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          ‖normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N‖ := by
    simpa using
      (norm_sum_le (s := Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0)
        (f := fun q => normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N))
  have hsum_le :
      ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          ‖normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N‖
        ≤
      ∑ _q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          (1 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
    refine Finset.sum_le_sum ?_
    intro q hq
    exact normalizedSigmaTruncSummand_norm_le_inv_two_mul_C2 hq
  have hQ0card : (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0).card
      = Goldbach.AO_OffDiag.TailBlock.Q0 := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  rw [normalizedSigmaTruncQ0_eq_sum_truncSummand]
  calc
    ‖∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N‖
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        ‖normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N‖ := htri
    _ ≤
      ∑ _q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        (1 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := hsum_le
    _ = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
      rw [Finset.sum_const, nsmul_eq_mul, hQ0card]
      ring

private lemma normalizedSigmaTruncWindowAverage_norm_le_Q0_div_C2
    {X : ℕ} (hX : X0 ≤ X) :
    ‖normalizedSigmaTruncWindowAverage ramanujanSeriesOnWindow X‖
      ≤
    (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := even_window_card_ne_zero hX
  have hsum_le :
      ‖∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N‖
        ≤
      ∑ _N ∈ EvenIn X H, (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
    have htri :
        ‖∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N‖
          ≤
        ∑ N ∈ EvenIn X H, ‖normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N‖ := by
      simpa using
        (norm_sum_le (s := EvenIn X H) (f := fun N => normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N))
    refine le_trans htri ?_
    refine Finset.sum_le_sum ?_
    intro N _hN
    exact normalizedSigmaTruncQ0_norm_le_Q0_div_C2 N
  unfold normalizedSigmaTruncWindowAverage
  rw [norm_mul]
  have hnorm_inv :
      ‖((↑(EvenIn X H).card : ℂ)⁻¹)‖ = (((EvenIn X H).card : ℝ)⁻¹) := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnorm_inv]
  calc
      (((EvenIn X H).card : ℝ)⁻¹) * ‖∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N‖
        ≤
      (((EvenIn X H).card : ℝ)⁻¹)
        * ∑ _N ∈ EvenIn X H, (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
          exact mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (EvenIn X H).card))
    _ = (((EvenIn X H).card : ℝ)⁻¹)
          * (((EvenIn X H).card : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
          have hcard_real_ne : ((EvenIn X H).card : ℝ) ≠ 0 := by
            exact_mod_cast hcard_nat
          rw [← mul_assoc, inv_mul_cancel₀ hcard_real_ne, one_mul]

private lemma centeredNormalizedSigmaTrunc_norm_le_two_mul_Q0_div_C2
    {X N : ℕ} (hX : X0 ≤ X) :
    ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖
      ≤
    2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2) := by
  unfold centeredNormalizedSigmaTrunc
  have h1 := normalizedSigmaTruncQ0_norm_le_Q0_div_C2 N
  have h2 := normalizedSigmaTruncWindowAverage_norm_le_Q0_div_C2 hX
  have htri := norm_sub_le (normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N)
    (normalizedSigmaTruncWindowAverage ramanujanSeriesOnWindow X)
  have hmain :
      ‖normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N
          - normalizedSigmaTruncWindowAverage ramanujanSeriesOnWindow X‖
        ≤
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2)
        + (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := by
    exact le_trans htri (add_le_add h1 h2)
  have hsmall_sub :
      ‖normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N
          - normalizedSigmaTruncWindowAverage ramanujanSeriesOnWindow X‖
        ≤
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2 := by
    have hC2_ne : (ramanujanSeriesOnWindow.C.C2 : ℝ) ≠ 0 := by
      linarith [ramanujanSeriesOnWindow.C.pos]
    calc
      ‖normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N
          - normalizedSigmaTruncWindowAverage ramanujanSeriesOnWindow X‖
          ≤
        (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2)
          + (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 : ℝ) * ramanujanSeriesOnWindow.C.C2) := hmain
      _ = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2 := by
        field_simp [hC2_ne]
        ring
  have hsmall :
      ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖
        ≤
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2 := by
    simpa [centeredNormalizedSigmaTrunc] using hsmall_sub
  have hlarge :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2
        ≤
      2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2) := by
    have hnonneg : 0 ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2 := by
      exact div_nonneg (by positivity) (le_of_lt ramanujanSeriesOnWindow.C.pos)
    nlinarith
  exact le_trans hsmall hlarge

theorem centeredNormalizedSigmaTruncWindowEnergyTarget_coarse :
    CenteredNormalizedSigmaTruncWindowEnergyTarget
      ((((H + 1 : ℕ) : ℝ) * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2)) := by
  refine ⟨by positivity, ?_⟩
  intro X hX
  unfold centeredNormalizedSigmaTruncWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      ∑ _N ∈ EvenIn X H,
        (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro N _hN
          exact pow_le_pow_left₀ (norm_nonneg _)
            (centeredNormalizedSigmaTrunc_norm_le_two_mul_Q0_div_C2 hX) 2
    _ = ((EvenIn X H).card : ℝ)
          * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((H + 1 : ℕ) : ℝ)
          * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2) := by
          have hcard : ((EvenIn X H).card : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by
            exact_mod_cast even_window_card_le_H_add_one X
          exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-- Native centered raw true-series-correction window-energy target. -/
structure CenteredRawHalfMassTrueSeriesCorrectionWindowEnergyTarget (Ccorr : ℝ) : Prop where
  Ccorr_nonneg : 0 ≤ Ccorr
  bound : ∀ {X : ℕ}, X0 ≤ X → centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X ≤ Ccorr

/-- Native centered raw true-tail-residual window-energy target. -/
structure CenteredRawHalfMassTrueTailResidualWindowEnergyTarget (Cres : ℝ) : Prop where
  Cres_nonneg : 0 ≤ Cres
  bound : ∀ {X : ℕ}, X0 ≤ X → centeredRawHalfMassTrueTailResidualWindowEnergy X ≤ Cres

private theorem rawHalfMassTailOnlyWindowAverage_eq_halfMassCanonicalAverageWitness
    {X : ℕ} (hX : X0 ≤ X) :
    ((EvenIn X H).card : ℂ)⁻¹ * (∑ N ∈ EvenIn X H, rawHalfMassTailOnlyObservable X N)
      = halfMassCanonicalAverageWitness X := by
  have hsum :
      ∑ N ∈ EvenIn X H, rawHalfMassTailOnlyObservable X N
        =
      ∑ N ∈ EvenIn X H, halfMassRecenteredZeroModeObservable X N := by
    unfold rawHalfMassTailOnlyObservable
    refine Finset.sum_congr rfl ?_
    intro N hN
    exact (halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window hX hN).symm
  rw [hsum]
  rw [halfMassCanonicalAverageWitness_eq_average]
  exact (halfMassRecenteredWindowAverage_eq_card_inv_mul_rawSum X).symm

theorem centeredRawHalfMassTrueTailResidual_eq_centeredTailOnly_sub_centeredTrueSigmaTail_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N
      =
    halfMassCenteredFluctuation X N - centeredTrueSigmaTail ramanujanSeriesOnWindow X N := by
  have hraw :
      rawHalfMassTailOnlyObservable X N
        = halfMassCanonicalAverageWitness X + halfMassTailOnlyObservable X N := by
    unfold rawHalfMassTailOnlyObservable halfMassTailOnlyObservable
    ring
  rw [halfMassCenteredFluctuation_eq_tailOnly_of_mem_even_window hX hN]
  unfold centeredRawHalfMassTrueTailResidual rawHalfMassTrueTailResidual centeredTrueSigmaTail
  rw [rawHalfMassTrueTailResidualWindowAverage_eq_tailOnlyAverage_sub_trueTailAverage]
  rw [rawHalfMassTailOnlyWindowAverage_eq_halfMassCanonicalAverageWitness hX]
  rw [hraw]
  ring

theorem centeredRawHalfMassTrueTailResidualWindowEnergy_le_two_mul_tailOnly_add_trueTail
    {X : ℕ} (hX : X0 ≤ X) :
    centeredRawHalfMassTrueTailResidualWindowEnergy X
      ≤
    2 * (halfMassTailOnlyWindowEnergy X
          + centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X) := by
  unfold centeredRawHalfMassTrueTailResidualWindowEnergy halfMassTailOnlyWindowEnergy
    centeredTrueSigmaTailWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      ∑ N ∈ EvenIn X H,
        2 * (‖halfMassCenteredFluctuation X N‖ ^ 2
            + ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          rw [centeredRawHalfMassTrueTailResidual_eq_centeredTailOnly_sub_centeredTrueSigmaTail_of_mem_even_window hX hN]
          have hsq :=
            norm_sq_add_le_two_mul_sum_norm_sq
              (halfMassCenteredFluctuation X N)
              (-centeredTrueSigmaTail ramanujanSeriesOnWindow X N)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
    _ =
      2 * (∑ N ∈ EvenIn X H, ‖halfMassCenteredFluctuation X N‖ ^ 2
          + ∑ N ∈ EvenIn X H, ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2) := by
          calc
            ∑ N ∈ EvenIn X H,
                2 * (‖halfMassCenteredFluctuation X N‖ ^ 2
                    + ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2)
                =
              ∑ N ∈ EvenIn X H,
                (2 * ‖halfMassCenteredFluctuation X N‖ ^ 2
                  + 2 * ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro N _hN
                    ring
            _ =
              (∑ N ∈ EvenIn X H, 2 * ‖halfMassCenteredFluctuation X N‖ ^ 2)
                + (∑ N ∈ EvenIn X H, 2 * ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [Finset.sum_add_distrib]
            _ =
              2 * (∑ N ∈ EvenIn X H, ‖halfMassCenteredFluctuation X N‖ ^ 2)
                + 2 * (∑ N ∈ EvenIn X H, ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
            _ =
              2 * (∑ N ∈ EvenIn X H, ‖halfMassCenteredFluctuation X N‖ ^ 2
                + ∑ N ∈ EvenIn X H, ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    ring
    _ =
      2 * (halfMassTailOnlyWindowEnergy X
          + centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X) := by
          rw [← halfMassRecenteredVarianceWindowEnergy_eq_tailOnlyWindowEnergy hX]
          unfold halfMassRecenteredVarianceWindowEnergy centeredTrueSigmaTailWindowEnergy
          rfl

theorem centeredRawHalfMassTrueTailResidualWindowEnergyTarget_of_tailOnly_and_trueTail
    {CtailOnly Ctail : ℝ}
    (htailOnly : HalfMassTailOnlyWindowTarget CtailOnly)
    (htrueTail : CenteredTrueSigmaTailWindowTarget ramanujanSeriesOnWindow Ctail) :
    CenteredRawHalfMassTrueTailResidualWindowEnergyTarget
      (2 * ((CtailOnly + Ctail) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
  refine ⟨?_, ?_⟩
  · have hden_pos : 0 < ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      simp [Goldbach.AO_OffDiag.TailBlock.Q0, H]
    have hnum_nonneg : 0 ≤ CtailOnly + Ctail := add_nonneg htailOnly.C3_nonneg htrueTail.C3_nonneg
    exact mul_nonneg (by norm_num) (div_nonneg hnum_nonneg (le_of_lt hden_pos))
  · intro X hX
    have hmain := centeredRawHalfMassTrueTailResidualWindowEnergy_le_two_mul_tailOnly_add_trueTail hX
    have htailOnly_bound :
        halfMassTailOnlyWindowEnergy X
          ≤
        CtailOnly / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := htailOnly.bound hX
    have htrueTail_bound :
        centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
          ≤
        Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := htrueTail.bound hX
    calc
      centeredRawHalfMassTrueTailResidualWindowEnergy X
          ≤
        2 * (halfMassTailOnlyWindowEnergy X
              + centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X) := hmain
      _ ≤
        2 * ((CtailOnly + Ctail) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
            have hden_pos : 0 < ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
              simp [Goldbach.AO_OffDiag.TailBlock.Q0, H]
            have hadd :
                halfMassTailOnlyWindowEnergy X + centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
                  ≤
                CtailOnly / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
                  + Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) :=
              add_le_add htailOnly_bound htrueTail_bound
            have hcombine :
                CtailOnly / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
                  + Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
                =
                (CtailOnly + Ctail) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
              ring_nf
            calc
              2 * (halfMassTailOnlyWindowEnergy X + centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X)
                  ≤
                2 * (CtailOnly / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
                    + Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
                      exact mul_le_mul_of_nonneg_left hadd (by norm_num)
              _ =
                2 * ((CtailOnly + Ctail) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
                      rw [hcombine]

theorem centeredNormalizedSigmaTrunc_eq_centeredResidual_sub_centeredSeriesCorrection_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N
      =
    centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N
      - centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N := by
  have hmain :=
    halfMassTrueSeriesCorrection_eq_neg_centeredTrunc_add_centeredResidual_of_mem_even_window
      ramanujanSeriesOnWindow hX hN
  rw [halfMassTrueSeriesCorrection_eq_centeredRawSeriesCorrection ramanujanSeriesOnWindow hX] at hmain
  rw [sub_eq_add_neg]
  rw [hmain]
  ring

theorem centeredRawHalfMassTrueSeriesCorrection_eq_centeredResidual_sub_centeredTrunc_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N
      =
    centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N
      - centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N := by
  have hmain :=
    halfMassTrueSeriesCorrection_eq_neg_centeredTrunc_add_centeredResidual_of_mem_even_window
      ramanujanSeriesOnWindow hX hN
  rw [halfMassTrueSeriesCorrection_eq_centeredRawSeriesCorrection ramanujanSeriesOnWindow hX] at hmain
  rw [sub_eq_add_neg]
  rw [hmain]
  ring

theorem centeredNormalizedSigmaTruncWindowEnergy_le_two_mul_seriesCorrection_add_residual
    {X : ℕ} (hX : X0 ≤ X) :
    centeredNormalizedSigmaTruncWindowEnergy X
      ≤
    2 * (centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X
          + centeredRawHalfMassTrueTailResidualWindowEnergy X) := by
  unfold centeredNormalizedSigmaTruncWindowEnergy
    centeredRawHalfMassTrueSeriesCorrectionWindowEnergy
    centeredRawHalfMassTrueTailResidualWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      ∑ N ∈ EvenIn X H,
        2 * (‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2
            + ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          rw [centeredNormalizedSigmaTrunc_eq_centeredResidual_sub_centeredSeriesCorrection_of_mem_even_window hX hN]
          have hsq :=
            norm_sq_add_le_two_mul_sum_norm_sq
              (centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N)
              (-centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
    _ =
      2 * (centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X
          + centeredRawHalfMassTrueTailResidualWindowEnergy X) := by
          calc
            ∑ N ∈ EvenIn X H,
                2 *
                  (‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2
                    + ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2)
                =
              ∑ N ∈ EvenIn X H,
                (2 * ‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2
                  + 2 * ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro N _hN
                    ring
            _ =
              (∑ N ∈ EvenIn X H, 2 * ‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2)
                + (∑ N ∈ EvenIn X H, 2 * ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [Finset.sum_add_distrib]
            _ =
              2 * (∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2)
                + 2 * (∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
            _ =
              2 * (centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X
                + centeredRawHalfMassTrueTailResidualWindowEnergy X) := by
                    unfold centeredRawHalfMassTrueSeriesCorrectionWindowEnergy
                      centeredRawHalfMassTrueTailResidualWindowEnergy
                    ring

theorem centeredRawHalfMassTrueSeriesCorrectionWindowEnergy_le_two_mul_trunc_add_residual
    {X : ℕ} (hX : X0 ≤ X) :
    centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X
      ≤
    2 * (centeredNormalizedSigmaTruncWindowEnergy X
          + centeredRawHalfMassTrueTailResidualWindowEnergy X) := by
  unfold centeredRawHalfMassTrueSeriesCorrectionWindowEnergy
    centeredNormalizedSigmaTruncWindowEnergy
    centeredRawHalfMassTrueTailResidualWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      ∑ N ∈ EvenIn X H,
        2 * (‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2
            + ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          rw [centeredRawHalfMassTrueSeriesCorrection_eq_centeredResidual_sub_centeredTrunc_of_mem_even_window hX hN]
          have hsq :=
            norm_sq_add_le_two_mul_sum_norm_sq
              (centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N)
              (-centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
    _ =
      2 * (centeredNormalizedSigmaTruncWindowEnergy X
          + centeredRawHalfMassTrueTailResidualWindowEnergy X) := by
          calc
            ∑ N ∈ EvenIn X H,
                2 *
                  (‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2
                    + ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2)
                =
              ∑ N ∈ EvenIn X H,
                (2 * ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2
                  + 2 * ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro N _hN
                    ring
            _ =
              (∑ N ∈ EvenIn X H, 2 * ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2)
                + (∑ N ∈ EvenIn X H, 2 * ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [Finset.sum_add_distrib]
            _ =
              2 * (∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2)
                + 2 * (∑ N ∈ EvenIn X H, ‖centeredRawHalfMassTrueTailResidual ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
            _ =
              2 * (centeredNormalizedSigmaTruncWindowEnergy X
                + centeredRawHalfMassTrueTailResidualWindowEnergy X) := by
                    unfold centeredNormalizedSigmaTruncWindowEnergy
                      centeredRawHalfMassTrueTailResidualWindowEnergy
                    ring

theorem centeredRawHalfMassTrueSeriesCorrectionWindowEnergyTarget_of_trunc_and_residual
    {Cτ Cres : ℝ}
    (htrunc : CenteredNormalizedSigmaTruncWindowEnergyTarget Cτ)
    (hres : CenteredRawHalfMassTrueTailResidualWindowEnergyTarget Cres) :
    CenteredRawHalfMassTrueSeriesCorrectionWindowEnergyTarget (2 * (Cτ + Cres)) := by
  refine ⟨by nlinarith [htrunc.Cτ_nonneg, hres.Cres_nonneg], ?_⟩
  intro X hX
  have hmain := centeredRawHalfMassTrueSeriesCorrectionWindowEnergy_le_two_mul_trunc_add_residual hX
  have htrunc_bound : centeredNormalizedSigmaTruncWindowEnergy X ≤ Cτ := htrunc.bound hX
  have hres_bound : centeredRawHalfMassTrueTailResidualWindowEnergy X ≤ Cres := hres.bound hX
  calc
    centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X
        ≤
      2 * (centeredNormalizedSigmaTruncWindowEnergy X
            + centeredRawHalfMassTrueTailResidualWindowEnergy X) := hmain
    _ ≤ 2 * (Cτ + Cres) := by
          exact mul_le_mul_of_nonneg_left (add_le_add htrunc_bound hres_bound) (by norm_num)

theorem centeredNormalizedSigmaTruncWindowEnergyTarget_of_seriesCorrection_and_residual
    {Ccorr Cres : ℝ}
    (hcorr : CenteredRawHalfMassTrueSeriesCorrectionWindowEnergyTarget Ccorr)
    (hres : CenteredRawHalfMassTrueTailResidualWindowEnergyTarget Cres) :
    CenteredNormalizedSigmaTruncWindowEnergyTarget (2 * (Ccorr + Cres)) := by
  refine ⟨by nlinarith [hcorr.Ccorr_nonneg, hres.Cres_nonneg], ?_⟩
  intro X hX
  have hmain := centeredNormalizedSigmaTruncWindowEnergy_le_two_mul_seriesCorrection_add_residual hX
  have hcorr_bound : centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X ≤ Ccorr := hcorr.bound hX
  have hres_bound : centeredRawHalfMassTrueTailResidualWindowEnergy X ≤ Cres := hres.bound hX
  calc
    centeredNormalizedSigmaTruncWindowEnergy X
        ≤
      2 * (centeredRawHalfMassTrueSeriesCorrectionWindowEnergy X
            + centeredRawHalfMassTrueTailResidualWindowEnergy X) := hmain
    _ ≤ 2 * (Ccorr + Cres) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hcorr_bound hres_bound) (by norm_num)

theorem centeredTrueSigmaSeries_eq_centeredTrueSigmaTail_add_centeredTrunc_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
      =
    centeredTrueSigmaTail ramanujanSeriesOnWindow X N
      + centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N := by
  rw [centeredTrueSigmaTail_eq_centeredTrueSigmaSeries_sub_centeredTrunc_of_mem_even_window
    ramanujanSeriesOnWindow hX hN]
  ring

theorem centeredTrueSigmaWindowEnergy_le_two_mul_tail_add_trunc
    {X : ℕ} (hX : X0 ≤ X) :
    centeredTrueSigmaWindowEnergy X
      ≤
    2 * (centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
          + centeredNormalizedSigmaTruncWindowEnergy X) := by
  unfold centeredTrueSigmaWindowEnergy centeredNormalizedSigmaTruncWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      ∑ N ∈ EvenIn X H,
        2 * (‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2
            + ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          rw [centeredTrueSigmaSeries_eq_centeredTrueSigmaTail_add_centeredTrunc_of_mem_even_window hX hN]
          exact norm_sq_add_le_two_mul_sum_norm_sq _ _
    _ =
      2 * (centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
          + centeredNormalizedSigmaTruncWindowEnergy X) := by
          unfold centeredTrueSigmaTailWindowEnergy centeredNormalizedSigmaTruncWindowEnergy
          calc
            ∑ N ∈ EvenIn X H,
                2 *
                  (‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2
                    + ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2)
                =
              ∑ N ∈ EvenIn X H,
                (2 * ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2
                  + 2 * ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro N _hN
                    ring
            _ =
              (∑ N ∈ EvenIn X H, 2 * ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2)
                + (∑ N ∈ EvenIn X H, 2 * ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [Finset.sum_add_distrib]
            _ =
              2 * (∑ N ∈ EvenIn X H, ‖centeredTrueSigmaTail ramanujanSeriesOnWindow X N‖ ^ 2)
                + 2 * (∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2) := by
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
            _ =
              2 * (centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
                + centeredNormalizedSigmaTruncWindowEnergy X) := by
                    unfold centeredTrueSigmaTailWindowEnergy centeredNormalizedSigmaTruncWindowEnergy
                    ring

theorem centeredTrueSigmaWindowEnergyTarget_of_tail_and_trunc
    {Ctail Ctrunc : ℝ}
    (htail : CenteredTrueSigmaTailWindowTarget ramanujanSeriesOnWindow Ctail)
    (htrunc : CenteredNormalizedSigmaTruncWindowEnergyTarget Ctrunc) :
    CenteredTrueSigmaWindowEnergyTarget
      (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) + Ctrunc)) := by
  refine ⟨?_, ?_⟩
  · have hHpos : 0 < (H : ℝ) := by norm_num [H]
    have hQ0pos : 0 < (((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      simp [Goldbach.AO_OffDiag.TailBlock.Q0]
    have hden_pos : 0 < ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      exact mul_pos hHpos hQ0pos
    have htail_nonneg :
        0 ≤ Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      exact div_nonneg htail.C3_nonneg (le_of_lt hden_pos)
    have hsum_nonneg :
        0 ≤ Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) + Ctrunc := by
      exact add_nonneg htail_nonneg htrunc.Cτ_nonneg
    exact mul_nonneg (by norm_num) hsum_nonneg
  intro X hX
  have hmain := centeredTrueSigmaWindowEnergy_le_two_mul_tail_add_trunc hX
  have htail_bound :
      centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
        ≤
      Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := htail.bound hX
  have htrunc_bound :
      centeredNormalizedSigmaTruncWindowEnergy X ≤ Ctrunc := htrunc.bound hX
  calc
    centeredTrueSigmaWindowEnergy X
        ≤
      2 * (centeredTrueSigmaTailWindowEnergy ramanujanSeriesOnWindow X
            + centeredNormalizedSigmaTruncWindowEnergy X) := hmain
    _ ≤
      2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) + Ctrunc) := by
          exact mul_le_mul_of_nonneg_left (add_le_add htail_bound htrunc_bound) (by norm_num)

/-- Coarse native true-sigma energy target obtained from the native true-tail input and the direct
coarse truncation estimate. This is the first fully non-ledger closure for the true-sigma packet. -/
theorem centeredTrueSigmaWindowEnergyTarget_coarse_of_tail
    {Ctail : ℝ}
    (htail : CenteredTrueSigmaTailWindowTarget ramanujanSeriesOnWindow Ctail) :
    CenteredTrueSigmaWindowEnergyTarget
      (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
        + (((H + 1 : ℕ) : ℝ)
            * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2))) := by
  exact centeredTrueSigmaWindowEnergyTarget_of_tail_and_trunc
    htail centeredNormalizedSigmaTruncWindowEnergyTarget_coarse

private theorem norm_sum_mul_sq_le_sum_sq_mul_sum_sq
    {ι : Type} (s : Finset ι) (b w : ι → ℂ) :
    ‖∑ i ∈ s, b i * w i‖ ^ 2 ≤ (∑ i ∈ s, ‖b i‖ ^ 2) * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  classical
  have htri : ‖∑ i ∈ s, b i * w i‖ ≤ ∑ i ∈ s, ‖b i * w i‖ := by
    simpa using (norm_sum_le (s := s) (f := fun i => b i * w i))
  have htri' : ‖∑ i ∈ s, b i * w i‖ ≤ ∑ i ∈ s, ‖b i‖ * ‖w i‖ := by
    simpa [norm_mul] using htri
  have hsq :
      ‖∑ i ∈ s, b i * w i‖ ^ 2 ≤ (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2 := by
    have h0a : 0 ≤ ‖∑ i ∈ s, b i * w i‖ := norm_nonneg _
    have h0b : 0 ≤ ∑ i ∈ s, ‖b i‖ * ‖w i‖ := by
      exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have :
        (‖∑ i ∈ s, b i * w i‖) * (‖∑ i ∈ s, b i * w i‖)
          ≤
        (∑ i ∈ s, ‖b i‖ * ‖w i‖) * (∑ i ∈ s, ‖b i‖ * ‖w i‖) :=
      mul_le_mul htri' htri' h0a h0b
    simpa [pow_two] using this
  have hcs :
      (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2
        ≤
      (∑ i ∈ s, (‖b i‖) ^ 2) * ∑ i ∈ s, (‖w i‖) ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := s) (f := fun i => ‖b i‖) (g := fun i => ‖w i‖))
  exact le_trans hsq hcs

/--
The weighted centered true-sigma packet is exactly a covariance term between the centered explicit
`q0⁻¹` observable and the centered true-sigma series.

This is the exact-zero seam for the first packet on the direct normalized route.
-/
theorem normalizedZeroModeTrueSigmaPacketRawSum_eq_windowScalar_mul_centeredQ0Inv_covariance
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeTrueSigmaPacketRawSum X
      =
    (unscaledGeometricZeroSliceHalfMass
        / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
      * ∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by
  let c : ℂ :=
    unscaledGeometricZeroSliceHalfMass
      / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))
  have hsplit :
      normalizedZeroModeTrueSigmaPacketRawSum X
        =
      c * ∑ N ∈ EvenIn X H,
            (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by
    unfold normalizedZeroModeTrueSigmaPacketRawSum c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [halfMassToNormalizedShapeCorrection_eq_windowScalar_mul_q0NormFactor_inv_of_mem_even_window
      hX hN]
    ring
  have hcenter :
      ∑ N ∈ EvenIn X H,
          (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
        =
      ∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by
    unfold centeredQ0InvExplicitObservable
    calc
      ∑ N ∈ EvenIn X H,
          (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
          =
        ∑ N ∈ EvenIn X H,
          (((Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
              - (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
            + (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by
              refine Finset.sum_congr rfl ?_
              intro N _hN
              ring
      _ =
        ∑ N ∈ EvenIn X H,
          (((Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
              - (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N
            + (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N) := by
              refine Finset.sum_congr rfl ?_
              intro N _hN
              ring
      _ =
        (∑ N ∈ EvenIn X H,
            ((Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
                - (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N)
          +
        (∑ N ∈ EvenIn X H,
            (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N) := by
              rw [Finset.sum_add_distrib]
      _ =
        (∑ N ∈ EvenIn X H,
            ((Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
                - (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N)
          +
        (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)
          * ∑ N ∈ EvenIn X H,
              centeredTrueSigmaSeries ramanujanSeriesOnWindow X N) := by
              rw [← Finset.mul_sum]
      _ =
        (∑ N ∈ EvenIn X H,
            ((Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
                - (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N)
          +
        (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ) * 0) := by
              rw [centeredTrueSigmaSeries_windowRawSum_eq_zero ramanujanSeriesOnWindow hX]
      _ =
        ∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by
              simp [centeredQ0InvExplicitObservable]
  calc
    normalizedZeroModeTrueSigmaPacketRawSum X
        =
      c * ∑ N ∈ EvenIn X H,
            (Q0MinorNormalizationBridge.q0NormFactor N)⁻¹
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := hsplit
    _ =
      c * ∑ N ∈ EvenIn X H,
            centeredQ0InvExplicitObservable X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by rw [hcenter]
    _ =
      (unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
        * ∑ N ∈ EvenIn X H,
            centeredQ0InvExplicitObservable X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N := by
              rfl

theorem normalizedZeroModeTrueSigmaPacketRawSum_norm_le_of_trueSigmaEnergy
    {Cσ : ℝ} (hσ : CenteredTrueSigmaWindowEnergyTarget Cσ)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖normalizedZeroModeTrueSigmaPacketRawSum X‖
      ≤
    ‖unscaledGeometricZeroSliceHalfMass
        / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
      * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
      * Real.sqrt Cσ := by
  have hsquare :
      ‖∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      centeredQ0InvExplicitWindowEnergy X * centeredTrueSigmaWindowEnergy X := by
    simpa [centeredQ0InvExplicitWindowEnergy, centeredTrueSigmaWindowEnergy] using
      norm_sum_mul_sq_le_sum_sq_mul_sum_sq
        (s := EvenIn X H)
        (b := fun N => centeredQ0InvExplicitObservable X N)
        (w := fun N => centeredTrueSigmaSeries ramanujanSeriesOnWindow X N)
  have hq0 :
      centeredQ0InvExplicitWindowEnergy X
        ≤
      ((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2 :=
    centeredQ0InvExplicitWindowEnergy_le_card_mul_span_sq hX
  have hσbound : centeredTrueSigmaWindowEnergy X ≤ Cσ := hσ.bound hX
  have hcard_nonneg : 0 ≤ ((EvenIn X H).card : ℝ) := by
    exact_mod_cast (Nat.zero_le (EvenIn X H).card)
  have hσenergy_nonneg : 0 ≤ centeredTrueSigmaWindowEnergy X := by
    unfold centeredTrueSigmaWindowEnergy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq0_nonneg :
      0 ≤ ((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2 := by
    exact mul_nonneg hcard_nonneg (sq_nonneg _)
  have hsquare' :
      ‖∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ ^ 2
        ≤
      (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ := by
    have hprod :
        centeredQ0InvExplicitWindowEnergy X * centeredTrueSigmaWindowEnergy X
          ≤
        (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ := by
      have hleft :
          centeredQ0InvExplicitWindowEnergy X * centeredTrueSigmaWindowEnergy X
            ≤
          (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
            * centeredTrueSigmaWindowEnergy X :=
        mul_le_mul_of_nonneg_right hq0 hσenergy_nonneg
      have hright :
          (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
              * centeredTrueSigmaWindowEnergy X
            ≤
          (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ :=
        mul_le_mul_of_nonneg_left hσbound hq0_nonneg
      exact le_trans hleft hright
    exact le_trans hsquare hprod
  have hroot :
      ‖∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖
        ≤
      Real.sqrt ((((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ) := by
    have hrad_nonneg :
        0 ≤ (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ := by
      exact mul_nonneg hq0_nonneg hσ.Cσ_nonneg
    have hsqrt_sq :
        ‖∑ N ∈ EvenIn X H,
            centeredQ0InvExplicitObservable X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ ^ 2
          ≤
        (Real.sqrt ((((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ)) ^ 2 := by
      convert hsquare' using 1
      rw [Real.sq_sqrt hrad_nonneg]
    exact le_of_sq_le_sq hsqrt_sq (Real.sqrt_nonneg _)
  calc
    ‖normalizedZeroModeTrueSigmaPacketRawSum X‖
        =
      ‖(unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
        * ∑ N ∈ EvenIn X H,
            centeredQ0InvExplicitObservable X N
              * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ := by
          rw [normalizedZeroModeTrueSigmaPacketRawSum_eq_windowScalar_mul_centeredQ0Inv_covariance hX]
    _ =
      ‖unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
        *
      ‖∑ N ∈ EvenIn X H,
          centeredQ0InvExplicitObservable X N
            * centeredTrueSigmaSeries ramanujanSeriesOnWindow X N‖ := by
          rw [norm_mul]
    _ ≤
      ‖unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
        * Real.sqrt ((((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Cσ) := by
          exact mul_le_mul_of_nonneg_left hroot (norm_nonneg _)
    _ =
      ‖unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
        * (Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2) * Real.sqrt Cσ) := by
          have hA_nonneg : 0 ≤ ((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2 := by
            exact mul_nonneg hcard_nonneg (sq_nonneg _)
          rw [Real.sqrt_mul hA_nonneg]
    _ =
      ‖unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
        * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
        * Real.sqrt Cσ := by
          rw [mul_assoc]

/-- Explicit first-packet audit bound obtained by combining the native true-tail target with the
coarse direct truncation energy estimate. -/
theorem normalizedZeroModeTrueSigmaPacketRawSum_norm_le_of_trueSigmaTail_and_coarseTrunc
    {Ctail : ℝ}
    (htail : CenteredTrueSigmaTailWindowTarget ramanujanSeriesOnWindow Ctail)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖normalizedZeroModeTrueSigmaPacketRawSum X‖
      ≤
    ‖unscaledGeometricZeroSliceHalfMass
        / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
      * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
      * Real.sqrt
          (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
            + (((H + 1 : ℕ) : ℝ)
                * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2))) := by
  exact normalizedZeroModeTrueSigmaPacketRawSum_norm_le_of_trueSigmaEnergy
    (centeredTrueSigmaWindowEnergyTarget_coarse_of_tail htail) hX

/--
The exposed normalized main product is exactly the window cardinality times a native normalized
main scalar built from:

* the unscaled post-`σ` ratio window average;
* the deterministic `q0^{-1}` window average;
* the fixed `X`-normalization factors.

This removes the remaining raw-sum bookkeeping from the main term. What remains is a genuine
weighted short-interval mean problem on the normalized surface.
-/
theorem normalizedZeroModeExposedMainProduct_eq_card_mul_ratioAverageMainScalar
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeExposedMainProduct X
      =
    ((EvenIn X H).card : ℂ)
      * (((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
            * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage X)
          * ((((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
              * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))) := by
  have hγ : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  have hfloor : ((routeVisibleWindowNormFloor X : ℝ) : ℂ) ≠ 0 :=
    routeVisibleWindowNormFloor_ne_zero hX
  have hscalar :
      ((2 : ℂ) * exactGeometricScalar X)
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
        =
      (((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹) := by
    unfold unscaledGeometricZeroSliceHalfMass
    field_simp [hγ, hfloor]
    norm_num
  have hscalar' :
      ((2 : ℂ) * exactGeometricScalar X)
        * Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelIntrinsicMainWitness X
        * (unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
      =
      Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelIntrinsicMainWitness X
        * (((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹) := by
    calc
      ((2 : ℂ) * exactGeometricScalar X)
          * Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelIntrinsicMainWitness X
          * (unscaledGeometricZeroSliceHalfMass
              / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))
          =
        Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelIntrinsicMainWitness X
          * (((2 : ℂ) * exactGeometricScalar X)
              * (unscaledGeometricZeroSliceHalfMass
                  / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)))) := by
            ring
      _ =
        Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelIntrinsicMainWitness X
          * (((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹) := by
            rw [hscalar]
  unfold normalizedZeroModeExposedMainProduct
  rw [halfMassCanonicalAverageWitness_eq_average]
  rw [halfMassRecenteredWindowAverage_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowAverage hX]
  rw [Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelWindowAverage_eq_intrinsicMainWitness hX]
  rw [q0NormFactor_inv_windowRawSum_eq_card_mul_explicitAverage hX]
  rw [hscalar']
  unfold Q0MinorHalfMassArithmeticModelMeanTargets.halfMassArithmeticModelIntrinsicMainWitness
  ring

/--
The main-product defect is exactly the window cardinality times a native weighted-mean defect on
the normalized surface.

So the live arithmetic content of `NormalizedZeroModeWindowRawSumTarget` is no longer a product of
raw sums. It is the defect between the native normalized main scalar and the bookkeeping scalar.
-/
theorem normalizedZeroModeMainProductDefect_eq_card_mul_ratioAverageMainScalarDefect
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeMainProductDefect X
      =
    ((EvenIn X H).card : ℂ)
      * ((((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
              * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage X)
            * ((((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
                * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))))
          - (zeroModeBookkeepingScalarCandidate : ℂ)) := by
  unfold normalizedZeroModeMainProductDefect
  rw [normalizedZeroModeExposedMainProduct_eq_card_mul_ratioAverageMainScalar hX]
  ring

/--
Native normalized main scalar induced by the exact unscaled post-`σ` ratio average.

This is the non-centered scalar that the normalized raw-sum target is really asking to match to the
bookkeeping constant.
-/
noncomputable def normalizedZeroModeRatioAverageMainScalar (X : ℕ) : ℂ :=
  ((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
      * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage X)
    * ((((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
        * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))

/-- Native weighted-mean defect on the normalized surface. -/
noncomputable def normalizedZeroModeRatioAverageMainScalarDefect (X : ℕ) : ℂ :=
  normalizedZeroModeRatioAverageMainScalar X
    - (zeroModeBookkeepingScalarCandidate : ℂ)

/--
Deterministic bookkeeping-image defect obtained by feeding the bookkeeping scalar through the
native normalized main-scalar map.
-/
noncomputable def normalizedZeroModeBookkeepingImageDefect (X : ℕ) : ℂ :=
  (((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
      * (zeroModeBookkeepingScalarCandidate : ℂ))
    * ((((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
        * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))))
  - (zeroModeBookkeepingScalarCandidate : ℂ)

/--
The deterministic normalization factor multiplying the bookkeeping scalar in the native normalized
main-scalar map.

If this factor were identically `1`, the bookkeeping-image defect would vanish by pure
normalization algebra.

Audit note:
- the geometric inverse factor comes from squaring the surrogate interval-window normalization
  `uniformWindowNormalization X = (log X * (2H+1))⁻¹`;
- the route-floor inverse factor comes from dividing the normalized observable by
  `routeVisibleWindowNormFloor X = (1/800) / log(X+H)^2`;
- the `q0` factor comes from the native deterministic average of `q0NormFactor⁻¹`.

So this scalar is an internal image-map normalization, not the paper's displayed Route A
normalization `log^2 X / H` for `\mathcal T(y)`. Any proof attempt that treats it as obviously
equal to `1` must first explain why these internal factors should cancel.
-/
noncomputable def normalizedZeroModeBookkeepingImageScalar (X : ℕ) : ℂ :=
  ((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
      * ((((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
          * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))))

/-- Factor coming from the inverse geometric zero-slice normalization. -/
noncomputable def normalizedZeroModeBookkeepingGeometricFactor (X : ℕ) : ℂ :=
  (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹

/-- Factor coming from the inverse route-floor normalization. -/
noncomputable def normalizedZeroModeBookkeepingRouteFloorFactor (X : ℕ) : ℂ :=
  (((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)

/-- Factor coming from the native deterministic `q0^{-1}` window average. -/
noncomputable def normalizedZeroModeBookkeepingQ0AverageFactor (X : ℕ) : ℂ :=
  (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))

/--
Deterministic scalar mismatch in the bookkeeping image map.

This is the exact normalization seam that must either vanish by identity or be bounded explicitly.
-/
noncomputable def normalizedZeroModeBookkeepingImageScalarMismatch (X : ℕ) : ℂ :=
  normalizedZeroModeBookkeepingImageScalar X - 1

/--
Paper-facing scalar normalization for Route A:
the displayed statistic is normalized by `log^2 X / H`.
-/
noncomputable def routeAPaperDisplayedNormalization (X : ℕ) : ℂ :=
  ((((Real.log (X : ℝ)) ^ 2 / (H : ℝ)) : ℝ) : ℂ)

/--
Explicit correction that strips the repo-internal image factors and reinstalls the paper-facing
Route A normalization.

This is the seam that should be compared to the paper, not the raw internal image scalar.
-/
noncomputable def routeAPaperNormalizationCorrection (X : ℕ) : ℂ :=
  routeAPaperDisplayedNormalization X
    * Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X
    * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)
    * (normalizedZeroModeBookkeepingQ0AverageFactor X)⁻¹

/--
Paper-facing image scalar obtained by renormalizing the internal image map back to the displayed
Route A normalization.
-/
noncomputable def paperZeroModeBookkeepingImageScalar (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeBookkeepingImageScalar X

/--
Deterministic paper-facing image defect. This is the right exact-identity seam for comparing to
the paper's Route A normalization.
-/
noncomputable def paperZeroModeBookkeepingImageDefect (X : ℕ) : ℂ :=
  paperZeroModeBookkeepingImageScalar X - routeAPaperDisplayedNormalization X

theorem normalizedZeroModeBookkeepingImageScalar_eq_factorized
    (X : ℕ) :
    normalizedZeroModeBookkeepingImageScalar X
      =
    normalizedZeroModeBookkeepingGeometricFactor X
      * normalizedZeroModeBookkeepingRouteFloorFactor X
      * normalizedZeroModeBookkeepingQ0AverageFactor X := by
  unfold normalizedZeroModeBookkeepingImageScalar normalizedZeroModeBookkeepingGeometricFactor
    normalizedZeroModeBookkeepingRouteFloorFactor normalizedZeroModeBookkeepingQ0AverageFactor
  ring

private theorem geometricZeroSliceNormalization_inv_eq_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    (Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
      =
    ((((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ) ^ 2) := by
  have hunif : uniformWindowNormalization X ≠ 0 := uniformWindowNormalization_ne_zero hX
  unfold Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization
    Q0MinorZeroModeEnvelope.uniformWindowNormalization
  field_simp [hunif]

private theorem routeVisibleWindowNormFloor_inv_eq_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    (((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
      =
    ((((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) : ℝ) : ℂ) := by
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlog_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hlog_ne : Real.log ((X + H : ℕ) : ℝ) ≠ 0 := by
    linarith
  calc
    (((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
        = (((routeVisibleWindowNormFloor X)⁻¹ : ℝ) : ℂ) := by
            simp
    _ = ((((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) : ℝ) : ℂ) := by
          unfold Q0MinorZeroModeEnvelope.routeVisibleWindowNormFloor
          field_simp [hlog_ne]

theorem normalizedZeroModeBookkeepingImageScalar_eq_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeBookkeepingImageScalar X
      =
    ((((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ) ^ 2)
      * ((((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ))
      * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) := by
  unfold normalizedZeroModeBookkeepingImageScalar
  rw [geometricZeroSliceNormalization_inv_eq_explicit hX]
  rw [routeVisibleWindowNormFloor_inv_eq_explicit hX]
  ring

theorem paperZeroModeBookkeepingImageScalar_eq_displayedNormalization
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeBookkeepingImageScalar X = routeAPaperDisplayedNormalization X := by
  have hgeom : Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X ≠ 0 :=
    geometricZeroSliceNormalization_ne_zero hX
  have hfloor : ((routeVisibleWindowNormFloor X : ℝ) : ℂ) ≠ 0 :=
    routeVisibleWindowNormFloor_ne_zero hX
  have hq0avg : normalizedZeroModeBookkeepingQ0AverageFactor X ≠ 0 := by
    exact q0InvExplicitWindowAverageRe_ne_zero hX
  unfold paperZeroModeBookkeepingImageScalar routeAPaperNormalizationCorrection
    routeAPaperDisplayedNormalization normalizedZeroModeBookkeepingImageScalar
    normalizedZeroModeBookkeepingQ0AverageFactor
  field_simp [hgeom, hfloor, hq0avg]
  have hmain :
      ((((Real.log (X : ℝ)) ^ 2 / (H : ℝ) : ℝ) : ℂ))
        * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
        / (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
        =
      ((((Real.log (X : ℝ)) ^ 2 / (H : ℝ) : ℝ) : ℂ)) := by
    have hq0avg' : (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) ≠ 0 := hq0avg
    rw [mul_div_assoc]
    rw [div_self hq0avg', mul_one]
  calc
    ((((Real.log (X : ℝ)) ^ 2 / (H : ℝ) : ℝ) : ℂ))
        * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
        / (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
        = ((((Real.log (X : ℝ)) ^ 2 / (H : ℝ) : ℝ) : ℂ)) := hmain
    _ = routeAPaperDisplayedNormalization X := by
        simp [routeAPaperDisplayedNormalization]

theorem paperZeroModeBookkeepingImageDefect_eq_zero
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeBookkeepingImageDefect X = 0 := by
  unfold paperZeroModeBookkeepingImageDefect
  rw [paperZeroModeBookkeepingImageScalar_eq_displayedNormalization hX]
  ring

theorem normalizedZeroModeBookkeepingGeometricFactor_eq_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeBookkeepingGeometricFactor X
      =
    ((((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ) ^ 2) := by
  exact geometricZeroSliceNormalization_inv_eq_explicit hX

theorem normalizedZeroModeBookkeepingRouteFloorFactor_eq_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeBookkeepingRouteFloorFactor X
      =
    ((((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2) : ℝ) : ℂ) := by
  exact routeVisibleWindowNormFloor_inv_eq_explicit hX

theorem normalizedZeroModeBookkeepingQ0AverageFactor_eq_rfl
    (X : ℕ) :
    normalizedZeroModeBookkeepingQ0AverageFactor X
      =
    (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)) := by
  rfl

/-- Weighted image of the native unscaled-ratio window-average error at the bookkeeping scalar. -/
noncomputable def normalizedZeroModeWeightedRatioAverageError (X : ℕ) : ℂ :=
  ((Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X)⁻¹
      * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
          zeroModeBookkeepingScalarCandidate X)
    * ((((routeVisibleWindowNormFloor X : ℝ) : ℂ)⁻¹)
        * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ)))

theorem normalizedZeroModeBookkeepingImageDefect_eq_scalar_mul_bookkeeping_minus_bookkeeping
    (X : ℕ) :
    normalizedZeroModeBookkeepingImageDefect X
      =
    normalizedZeroModeBookkeepingImageScalar X
      * (zeroModeBookkeepingScalarCandidate : ℂ)
      - (zeroModeBookkeepingScalarCandidate : ℂ) := by
  unfold normalizedZeroModeBookkeepingImageDefect normalizedZeroModeBookkeepingImageScalar
  ring

theorem normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_scalarDefect
    (X : ℕ) :
    normalizedZeroModeBookkeepingImageDefect X
      =
    (zeroModeBookkeepingScalarCandidate : ℂ)
      * (normalizedZeroModeBookkeepingImageScalar X - 1) := by
  rw [normalizedZeroModeBookkeepingImageDefect_eq_scalar_mul_bookkeeping_minus_bookkeeping]
  ring

theorem normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_scalarMismatch
    (X : ℕ) :
    normalizedZeroModeBookkeepingImageDefect X
      =
    (zeroModeBookkeepingScalarCandidate : ℂ)
      * normalizedZeroModeBookkeepingImageScalarMismatch X := by
  unfold normalizedZeroModeBookkeepingImageScalarMismatch
  exact normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_scalarDefect X

theorem normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_explicitScalarDefect
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeBookkeepingImageDefect X
      =
    (zeroModeBookkeepingScalarCandidate : ℂ)
      * ((((((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ) ^ 2)
          * ((((800 : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ))
          * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))) - 1) := by
  rw [normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_scalarDefect]
  rw [normalizedZeroModeBookkeepingImageScalar_eq_explicit hX]

theorem normalizedZeroModeBookkeepingImageDefect_eq_zero_of_scalar_eq_one
    {X : ℕ} (hscalar : normalizedZeroModeBookkeepingImageScalar X = 1) :
    normalizedZeroModeBookkeepingImageDefect X = 0 := by
  rw [normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_scalarDefect, hscalar]
  ring

theorem normalizedZeroModeBookkeepingImageScalar_eq_one_of_defect_eq_zero
    {X : ℕ} (hdef : normalizedZeroModeBookkeepingImageDefect X = 0) :
    normalizedZeroModeBookkeepingImageScalar X = 1 := by
  rw [normalizedZeroModeBookkeepingImageDefect_eq_bookkeeping_mul_scalarDefect] at hdef
  have hκ : (zeroModeBookkeepingScalarCandidate : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      Q0MinorHalfMassArithmeticModelMeanTargets.zeroModeBookkeepingScalarCandidate_pos)
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp hdef).resolve_left hκ

theorem normalizedZeroModeExposedMainProduct_eq_card_mul_nativeRatioAverageMainScalar
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeExposedMainProduct X
      =
    ((EvenIn X H).card : ℂ) * normalizedZeroModeRatioAverageMainScalar X := by
  rw [normalizedZeroModeExposedMainProduct_eq_card_mul_ratioAverageMainScalar hX]
  rfl

theorem normalizedZeroModeMainProductDefect_eq_card_mul_nativeRatioAverageMainScalarDefect
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeMainProductDefect X
      =
    ((EvenIn X H).card : ℂ) * normalizedZeroModeRatioAverageMainScalarDefect X := by
  unfold normalizedZeroModeMainProductDefect normalizedZeroModeRatioAverageMainScalarDefect
  rw [normalizedZeroModeExposedMainProduct_eq_card_mul_nativeRatioAverageMainScalar hX]
  unfold normalizedZeroModeRatioAverageMainScalar
  ring

/-- Paper-corrected weighted ratio-average error. -/
noncomputable def paperZeroModeWeightedRatioAverageError (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeWeightedRatioAverageError X

/-- Paper-corrected true-sigma centered packet raw sum. -/
noncomputable def paperZeroModeTrueSigmaPacketRawSum (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeTrueSigmaPacketRawSum X

/-- Paper-corrected truncation centered packet raw sum. -/
noncomputable def paperZeroModeTruncPacketRawSum (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeTruncPacketRawSum X

/-- Paper-corrected residual centered packet raw sum. -/
noncomputable def paperZeroModeResidualPacketRawSum (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeResidualPacketRawSum X

theorem routeAPaperDisplayedNormalization_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    routeAPaperDisplayedNormalization X ≠ 0 := by
  unfold routeAPaperDisplayedNormalization
  have hlog_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hlog_ne : Real.log (X : ℝ) ≠ 0 := by
    linarith
  have hlog_sq_ne : (Real.log (X : ℝ)) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hlog_ne
  have hHne : (H : ℝ) ≠ 0 := by
    norm_num [H, Goldbach.BankParams.H]
  have hdiv_ne : (((Real.log (X : ℝ)) ^ 2 / (H : ℝ)) : ℝ) ≠ 0 :=
    div_ne_zero hlog_sq_ne hHne
  intro hzero
  apply hdiv_ne
  exact_mod_cast hzero

theorem paperZeroModeWeightedRatioAverageError_eq_displayedNormalization_mul_ratioErrorAverage
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeWeightedRatioAverageError X
      =
    routeAPaperDisplayedNormalization X
      * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
          zeroModeBookkeepingScalarCandidate X := by
  have hgeom : Q0MinorZeroModeEnvelope.geometricZeroSliceNormalization X ≠ 0 :=
    geometricZeroSliceNormalization_ne_zero hX
  have hfloor : ((routeVisibleWindowNormFloor X : ℝ) : ℂ) ≠ 0 :=
    routeVisibleWindowNormFloor_ne_zero hX
  have hq0avg : normalizedZeroModeBookkeepingQ0AverageFactor X ≠ 0 := by
    exact q0InvExplicitWindowAverageRe_ne_zero hX
  unfold paperZeroModeWeightedRatioAverageError routeAPaperNormalizationCorrection
    normalizedZeroModeWeightedRatioAverageError normalizedZeroModeBookkeepingQ0AverageFactor
  field_simp [hgeom, hfloor, hq0avg]
  have hcancel :
      (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
          * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))⁻¹
        = 1 := by
    exact mul_inv_cancel₀ hq0avg
  calc
    routeAPaperDisplayedNormalization X * ↑(q0InvExplicitWindowAverageRe X) *
          Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
            zeroModeBookkeepingScalarCandidate X *
        (↑(q0InvExplicitWindowAverageRe X))⁻¹
        =
      routeAPaperDisplayedNormalization X
        * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
            zeroModeBookkeepingScalarCandidate X
        * ((((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))
            * (((q0InvExplicitWindowAverageRe X : ℝ) : ℂ))⁻¹) := by
          ring
    _ =
      routeAPaperDisplayedNormalization X
        * Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
            zeroModeBookkeepingScalarCandidate X := by
          rw [hcancel]
          ring

theorem paperZeroModeWeightedRatioAverageError_eq_zero_of_exactRatioAverage
    {X : ℕ} (hX : X0 ≤ X)
    (havg :
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage X
        = (zeroModeBookkeepingScalarCandidate : ℂ)) :
    paperZeroModeWeightedRatioAverageError X = 0 := by
  have herr :
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
        zeroModeBookkeepingScalarCandidate X = 0 := by
    have hsplit :=
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage
        zeroModeBookkeepingScalarCandidate hX
    rw [havg] at hsplit
    have hsub := congrArg (fun z : ℂ => z - (zeroModeBookkeepingScalarCandidate : ℂ)) hsplit
    simpa using hsub.symm
  rw [paperZeroModeWeightedRatioAverageError_eq_displayedNormalization_mul_ratioErrorAverage hX, herr]
  ring

theorem paperZeroModeWeightedRatioAverageError_eq_zero_iff
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeWeightedRatioAverageError X = 0 ↔
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
        zeroModeBookkeepingScalarCandidate X = 0 := by
  rw [paperZeroModeWeightedRatioAverageError_eq_displayedNormalization_mul_ratioErrorAverage hX]
  constructor
  · intro hzero
    have hnorm : routeAPaperDisplayedNormalization X ≠ 0 :=
      routeAPaperDisplayedNormalization_ne_zero hX
    exact (mul_eq_zero.mp hzero).resolve_left hnorm
  · intro herr
    rw [herr]
    ring

theorem paperZeroModeWeightedRatioAverageError_eq_displayedNormalization_mul_exactGeometricScalar_inv_mul_sigmaQuotientCenteredErrorAverage
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeWeightedRatioAverageError X
      =
    routeAPaperDisplayedNormalization X
      * (exactGeometricScalar X)⁻¹
      * Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
          zeroModeBookkeepingScalarCandidate X := by
  have hsig :
      ∀ {N : ℕ}, N ∈ EvenIn X H →
        Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0 := by
    intro N hN
    exact
      Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.sigmaNormalizedSeries_ne_zero_of_mem_even_window
        hX hN
  rw [paperZeroModeWeightedRatioAverageError_eq_displayedNormalization_mul_ratioErrorAverage hX]
  rw [Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage_eq_exactGeometricScalar_inv_mul_sigmaQuotientCenteredErrorAverage
    zeroModeBookkeepingScalarCandidate hX hsig]
  ring

theorem paperZeroModeWeightedRatioAverageError_norm_le_of_unscaledMassShape
    {C2 C3 : ℝ}
    (hshape :
      Q0MinorZeroModeEnvelope.UnscaledZeroModeMassShapeTarget
        zeroModeBookkeepingScalarCandidate C2 C3)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖paperZeroModeWeightedRatioAverageError X‖
      ≤
    ‖routeAPaperDisplayedNormalization X‖
      * (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹
      * (2
          * Real.sqrt
              (((EvenIn X H).card : ℝ)⁻¹
                * (C2 * ((H : ℝ) / (X : ℝ))
                    + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
  have hsplit :=
    paperZeroModeWeightedRatioAverageError_eq_displayedNormalization_mul_exactGeometricScalar_inv_mul_sigmaQuotientCenteredErrorAverage
      hX
  have hγinv :
      ‖(exactGeometricScalar X)⁻¹‖ ≤ (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹ :=
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.norm_inv_exactGeometricScalar_le_inv_Kfull_zero hX
  have hnum :
      ‖Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
          zeroModeBookkeepingScalarCandidate X‖
        ≤
      2
        * Real.sqrt
            (((EvenIn X H).card : ℝ)⁻¹
              * (C2 * ((H : ℝ) / (X : ℝ))
                  + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) :=
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage_norm_le_shapeBound
      hshape hX
  calc
    ‖paperZeroModeWeightedRatioAverageError X‖
        =
      ‖routeAPaperDisplayedNormalization X
          * (exactGeometricScalar X)⁻¹
          * Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
              zeroModeBookkeepingScalarCandidate X‖ := by
          rw [hsplit]
    _ =
      ‖routeAPaperDisplayedNormalization X‖
        * ‖(exactGeometricScalar X)⁻¹‖
        * ‖Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
            zeroModeBookkeepingScalarCandidate X‖ := by
          rw [norm_mul, norm_mul]
    _ ≤
      ‖routeAPaperDisplayedNormalization X‖
        * (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹
        * ‖Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
            zeroModeBookkeepingScalarCandidate X‖ := by
          have hnorm_nonneg : 0 ≤ ‖routeAPaperDisplayedNormalization X‖ := norm_nonneg _
          have hstep :
              ‖(exactGeometricScalar X)⁻¹‖
                * ‖Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
                    zeroModeBookkeepingScalarCandidate X‖
              ≤
              (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹
                * ‖Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeSigmaQuotientCenteredErrorWindowAverage
                    zeroModeBookkeepingScalarCandidate X‖ :=
            mul_le_mul_of_nonneg_right hγinv (norm_nonneg _)
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hstep hnorm_nonneg
    _ ≤
      ‖routeAPaperDisplayedNormalization X‖
        * (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹
        * (2
            * Real.sqrt
                (((EvenIn X H).card : ℝ)⁻¹
                  * (C2 * ((H : ℝ) / (X : ℝ))
                      + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
          have hlead_nonneg :
              0 ≤ ‖routeAPaperDisplayedNormalization X‖ * (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹ := by
            have hKinv_nonneg : 0 ≤ (Goldbach.BG_Identity.K_full (0 : ℤ))⁻¹ := by
              exact inv_nonneg.mpr (le_of_lt Goldbach.BG_Identity.K_full_pos_at_zero)
            apply mul_nonneg
            · exact norm_nonneg _
            · exact hKinv_nonneg
          exact mul_le_mul_of_nonneg_left hnum hlead_nonneg

theorem paperZeroModeTrueSigmaPacketRawSum_norm_le_of_trueSigmaTail_and_coarseTrunc
    {Ctail : ℝ}
    (htail : CenteredTrueSigmaTailWindowTarget ramanujanSeriesOnWindow Ctail)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖paperZeroModeTrueSigmaPacketRawSum X‖
      ≤
    ‖routeAPaperNormalizationCorrection X‖
      * ‖unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
      * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
      * Real.sqrt
          (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
            + (((H + 1 : ℕ) : ℝ)
                * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2))) := by
  unfold paperZeroModeTrueSigmaPacketRawSum
  have hpacket :
      ‖normalizedZeroModeTrueSigmaPacketRawSum X‖
        ≤
      ‖unscaledGeometricZeroSliceHalfMass
          / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
        * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
        * Real.sqrt
            (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
              + (((H + 1 : ℕ) : ℝ)
                  * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2))) :=
    normalizedZeroModeTrueSigmaPacketRawSum_norm_le_of_trueSigmaTail_and_coarseTrunc htail hX
  calc
    ‖routeAPaperNormalizationCorrection X * normalizedZeroModeTrueSigmaPacketRawSum X‖
        = ‖routeAPaperNormalizationCorrection X‖ * ‖normalizedZeroModeTrueSigmaPacketRawSum X‖ := by
            rw [norm_mul]
    _ ≤
      ‖routeAPaperNormalizationCorrection X‖
        * (‖unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
          * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
          * Real.sqrt
              (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
                + (((H + 1 : ℕ) : ℝ)
                    * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2)))) := by
            exact mul_le_mul_of_nonneg_left hpacket (norm_nonneg _)
    _ =
      ‖routeAPaperNormalizationCorrection X‖
        * ‖unscaledGeometricZeroSliceHalfMass
            / (exactGeometricScalar X * ((routeVisibleWindowNormFloor X : ℝ) : ℂ))‖
        * Real.sqrt (((EvenIn X H).card : ℝ) * (q0InvExplicitWindowSpanRe X) ^ 2)
        * Real.sqrt
            (2 * (Ctail / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
              + (((H + 1 : ℕ) : ℝ)
                  * (2 * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ramanujanSeriesOnWindow.C.C2)) ^ 2))) := by
            ring

/-- Paper-corrected main-scalar defect on the normalized route. -/
noncomputable def paperZeroModeRatioAverageMainScalarDefect (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeRatioAverageMainScalar X
    - routeAPaperDisplayedNormalization X * (zeroModeBookkeepingScalarCandidate : ℂ)

/-- Paper-corrected main-product defect. -/
noncomputable def paperZeroModeMainProductDefect (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeExposedMainProduct X
    - ((EvenIn X H).card : ℂ)
        * (routeAPaperDisplayedNormalization X * (zeroModeBookkeepingScalarCandidate : ℂ))

/-- Paper-corrected raw-sum defect for the normalized shape observable. -/
noncomputable def paperZeroModeShapeWindowRawSumDefect (X : ℕ) : ℂ :=
  routeAPaperNormalizationCorrection X * normalizedZeroModeShapeWindowRawSum X
    - ((EvenIn X H).card : ℂ)
        * (routeAPaperDisplayedNormalization X * (zeroModeBookkeepingScalarCandidate : ℂ))

/--
If the unscaled post-`σ` ratio average is written as the bookkeeping scalar plus its native window
average error, then the normalized main-scalar defect is exactly the deterministic weighted image of
that ratio-average error together with the residual scalar mismatch at the bookkeeping value.

This is the sharpest direct mean-theorem surface currently available for the normalized raw-sum
problem.
-/
theorem normalizedZeroModeRatioAverageMainScalarDefect_eq_bookkeepingImage_add_weightedRatioAverageError
    {X : ℕ} (hX : X0 ≤ X) :
    normalizedZeroModeRatioAverageMainScalarDefect X
      =
    normalizedZeroModeBookkeepingImageDefect X
      + normalizedZeroModeWeightedRatioAverageError X := by
  unfold normalizedZeroModeRatioAverageMainScalarDefect normalizedZeroModeRatioAverageMainScalar
    normalizedZeroModeBookkeepingImageDefect normalizedZeroModeWeightedRatioAverageError
  rw [Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage
    zeroModeBookkeepingScalarCandidate hX]
  ring

theorem paperZeroModeRatioAverageMainScalarDefect_eq_paperBookkeepingImage_add_weightedRatioAverageError
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeRatioAverageMainScalarDefect X
      =
    paperZeroModeBookkeepingImageDefect X * (zeroModeBookkeepingScalarCandidate : ℂ)
      + paperZeroModeWeightedRatioAverageError X := by
  unfold paperZeroModeRatioAverageMainScalarDefect paperZeroModeWeightedRatioAverageError
    paperZeroModeBookkeepingImageDefect paperZeroModeBookkeepingImageScalar
    routeAPaperNormalizationCorrection routeAPaperDisplayedNormalization
    normalizedZeroModeRatioAverageMainScalar normalizedZeroModeWeightedRatioAverageError
    normalizedZeroModeBookkeepingImageScalar
  rw [Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage
    zeroModeBookkeepingScalarCandidate hX]
  ring

theorem paperZeroModeRatioAverageMainScalarDefect_eq_weightedRatioAverageError
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeRatioAverageMainScalarDefect X
      =
    paperZeroModeWeightedRatioAverageError X := by
  rw [paperZeroModeRatioAverageMainScalarDefect_eq_paperBookkeepingImage_add_weightedRatioAverageError hX]
  rw [paperZeroModeBookkeepingImageDefect_eq_zero hX]
  ring

/--
If the unscaled ratio window average is exactly the bookkeeping scalar, then the weighted normalized
main-scalar defect reduces to the deterministic bookkeeping-image defect.
-/
theorem normalizedZeroModeRatioAverageMainScalarDefect_eq_bookkeepingImageDefect_of_exactRatioAverage
    {X : ℕ} (hX : X0 ≤ X)
    (havg :
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage X
        = (zeroModeBookkeepingScalarCandidate : ℂ)) :
    normalizedZeroModeRatioAverageMainScalarDefect X
      =
    normalizedZeroModeBookkeepingImageDefect X := by
  have herr :
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioErrorWindowAverage
        zeroModeBookkeepingScalarCandidate X = 0 := by
    have hsplit :=
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage_eq_scalar_add_errorAverage
        zeroModeBookkeepingScalarCandidate hX
    rw [havg] at hsplit
    have hsub := congrArg (fun z : ℂ => z - (zeroModeBookkeepingScalarCandidate : ℂ)) hsplit
    simpa using hsub.symm
  rw [normalizedZeroModeRatioAverageMainScalarDefect_eq_bookkeepingImage_add_weightedRatioAverageError hX]
  unfold normalizedZeroModeWeightedRatioAverageError
  rw [herr]
  simp

/--
Exact native closure criterion for the normalized weighted-mean defect.

If the unscaled ratio average is exactly the bookkeeping scalar and the deterministic bookkeeping
image defect vanishes, then the full normalized main-scalar defect vanishes.
-/
theorem normalizedZeroModeRatioAverageMainScalarDefect_eq_zero_of_exactRatioAverage_and_bookkeepingImage
    {X : ℕ} (hX : X0 ≤ X)
    (havg :
      Q0MinorHalfMassArithmeticModelMeanTargets.unscaledZeroModeMassRatioWindowAverage X
        = (zeroModeBookkeepingScalarCandidate : ℂ))
    (himg : normalizedZeroModeBookkeepingImageDefect X = 0) :
    normalizedZeroModeRatioAverageMainScalarDefect X = 0 := by
  rw [normalizedZeroModeRatioAverageMainScalarDefect_eq_bookkeepingImageDefect_of_exactRatioAverage hX havg]
  exact himg

theorem paperZeroModeMainProductDefect_eq_card_mul_weightedRatioAverageError
    {X : ℕ} (hX : X0 ≤ X) :
    paperZeroModeMainProductDefect X
      =
    ((EvenIn X H).card : ℂ) * paperZeroModeWeightedRatioAverageError X := by
  have hsplit :
      paperZeroModeMainProductDefect X
        =
      ((EvenIn X H).card : ℂ) * paperZeroModeRatioAverageMainScalarDefect X := by
    unfold paperZeroModeMainProductDefect paperZeroModeRatioAverageMainScalarDefect
    rw [normalizedZeroModeExposedMainProduct_eq_card_mul_nativeRatioAverageMainScalar hX]
    ring
  rw [hsplit, paperZeroModeRatioAverageMainScalarDefect_eq_weightedRatioAverageError hX]

theorem paperZeroModeShapeWindowRawSumDefect_eq_mainProductDefect_add_centeredPackets
    {X : ℕ}
    (hX : X0 ≤ X)
    (hq0 : ∀ {N : ℕ}, N ∈ EvenIn X H → Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : ∀ {N : ℕ}, N ∈ EvenIn X H → unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    paperZeroModeShapeWindowRawSumDefect X
      =
    paperZeroModeMainProductDefect X
      + paperZeroModeTrueSigmaPacketRawSum X
      - paperZeroModeTruncPacketRawSum X
      + paperZeroModeResidualPacketRawSum X := by
  unfold paperZeroModeShapeWindowRawSumDefect paperZeroModeMainProductDefect
    paperZeroModeTrueSigmaPacketRawSum paperZeroModeTruncPacketRawSum paperZeroModeResidualPacketRawSum
  rw [normalizedZeroModeShapeWindowRawSum_eq_exposedMainProduct_add_centeredPackets
    hX hq0 hw0 hunscaled hgeom hsig hfloor]
  ring

theorem paperZeroModeShapeWindowRawSumDefect_eq_weightedRatioAverageError_add_centeredPackets
    {X : ℕ}
    (hX : X0 ≤ X)
    (hq0 : ∀ {N : ℕ}, N ∈ EvenIn X H → Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra.minorArcWeightFourier
      X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : ∀ {N : ℕ}, N ∈ EvenIn X H → unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : ∀ {N : ℕ}, N ∈ EvenIn X H →
      Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    paperZeroModeShapeWindowRawSumDefect X
      =
    ((EvenIn X H).card : ℂ) * paperZeroModeWeightedRatioAverageError X
      + paperZeroModeTrueSigmaPacketRawSum X
      - paperZeroModeTruncPacketRawSum X
      + paperZeroModeResidualPacketRawSum X := by
  rw [paperZeroModeShapeWindowRawSumDefect_eq_mainProductDefect_add_centeredPackets
    hX hq0 hw0 hunscaled hgeom hsig hfloor]
  rw [paperZeroModeMainProductDefect_eq_card_mul_weightedRatioAverageError hX]

end

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
