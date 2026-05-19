import Goldbach.Cert.MajorArcModules.Q0MinorRouteADenseGridTargets
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaClosure
import Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
import Goldbach.Cert.MajorArcModules.Q0MajorTailConstModeBound
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
import Goldbach.BG_Identity

/-!
# Route A mean / variance source targets

This file records the missing PSB-facing arithmetic source layer for Route A.

The positive observable is the actual normalized band-limited Route-A statistic, not the geometric
surrogate. The main deterministic result here is the finite-grid Chebyshev step:

mean lower bound + centered-quadratic upper bound
  ⇒ dense good grid for the actual normalized statistic.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
open Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
open Goldbach.Cert.MajorArcModules.Q0MinorRouteADenseGridTargets
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

/-- PSB-facing Route-A mean input on the actual normalized band-limited statistic. -/
abbrev RouteABandLimitedGridMeanLowerBound
    (K : ℤ → ℝ) (C0 : ℕ) (μ : ℕ → ℝ) : Prop :=
  RouteAGridMeanLowerBound K C0 μ

/-- PSB-facing Route-A variance input on the actual normalized band-limited statistic. -/
abbrev RouteABandLimitedGridVarianceUpperBound
    (K : ℤ → ℝ) (C0 : ℕ) (V : ℕ → ℝ) : Prop :=
  RouteAGridVarianceUpperBound K C0 V

/--
PSB-facing dyadic mean input on the exact route-visible scalar.

This is the closest arithmetic proxy to the paper's positive-mean statement before the Route-A
kernel is averaged over the grid.
-/
structure RouteAVisibleDyadicMeanLowerBound
    (M : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      M X ≤ Finset.sum (EvenIn X H) (fun N => (routeVisibleScalar X N).re)

/--
Raw PSB-facing dyadic mean input on the normalized minor residual `minorResidual`.

This is the paper-nearest source theorem before transferring to the exact route-visible scalar.
-/
structure RouteAPSBMinorResidualDyadicMeanLowerBound
    (M : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      M X ≤
        Finset.sum (EvenIn X H) (fun N =>
          (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
            Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re)

/-- The raw dyadic mean sum of the normalized minor residual used by the PSB source theorem. -/
noncomputable def routeAPSBMinorResidualDyadicMeanSum (X : ℕ) : ℝ :=
  Finset.sum (EvenIn X H) (fun N =>
    (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
      Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re)

/-- Dyadic real-part sum of the singular-series-style Route-A candidate main term `SS_formula`. -/
noncomputable def routeAPSBSSMainContributionSum (X : ℕ) : ℝ :=
  Finset.sum (EvenIn X H) (fun N => (SS_formula X N).re)

/-- Dyadic real-part sum of the zero-mode sigma baseline under `SS_formula`. -/
noncomputable def routeAPSBZeroModeSigmaBaselineSum (X : ℕ) : ℝ :=
  Finset.sum (EvenIn X H) (fun N => (zeroModeSigmaBaseline X N).re)

/-- Dyadic real-part sum of the geometric part of the zero-mode sigma baseline. -/
noncomputable def routeAPSBZeroModeGeometricBaselineSum (X : ℕ) : ℝ :=
  Finset.sum (EvenIn X H) (fun N => (zeroModeGeometricBaseline X N).re)

/--
Window-stable scalar part of the geometric zero-mode baseline on `EvenIn X H`.

On the canonical even window, the unscaled geometric zero slice is exactly constant, so the only
`N`-dependence left in `zeroModeGeometricBaseline` comes from the explicit `q0` normalization.
-/
noncomputable def routeAPSBZeroModeGeometricWindowScalar (X : ℕ) : ℂ :=
  Q0MinorTTStarAlgebra.minorArcWeightFourier X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0
    * geometricZeroSliceNormalization X
    * exactGeometricScalar X

/-- Route-A scalar factor relating `SS_formula` to the zero-mode sigma baseline on the window. -/
noncomputable def routeAPSBSSMainScale (X : ℕ) : ℝ :=
  zeroModeBookkeepingScalarCandidate * routeVisibleWindowNormFloor X

/--
Dyadic absolute real-part sum of the remaining Route-A scalar contribution `G_formula + R_formula`.

This is the most conservative mean-error object attached to the exact decomposition
`routeVisibleScalar = G_formula + SS_formula + R_formula`.
-/
noncomputable def routeAPSBVisibleMeanErrorAbsSum (X : ℕ) : ℝ :=
  Finset.sum (EvenIn X H) (fun N => |(G_formula X N + R_formula X N).re|)

/-- Lower-bound target for the `SS_formula` dyadic mean contribution. -/
structure RouteAPSBSSMainContributionLowerBound
    (Mmain : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X → Mmain X ≤ routeAPSBSSMainContributionSum X

/-- Lower-bound target for the dyadic mean of the zero-mode sigma baseline. -/
structure RouteAPSBZeroModeSigmaBaselineLowerBound
    (Mbase : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X → Mbase X ≤ routeAPSBZeroModeSigmaBaselineSum X

/-- Lower-bound target for the dyadic mean of the geometric part of the zero-mode sigma baseline. -/
structure RouteAPSBZeroModeGeometricBaselineLowerBound
    (Mgeom : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X → Mgeom X ≤ routeAPSBZeroModeGeometricBaselineSum X

/-- Pointwise nonnegativity target for the real part of the geometric zero-mode baseline. -/
structure RouteAPSBZeroModeGeometricBaselineReNonneg : Prop where
  nonneg :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 0 ≤ (zeroModeGeometricBaseline X N).re

/-- Lower-bound target for the real part of the window-stable geometric baseline scalar. -/
structure RouteAPSBZeroModeGeometricWindowScalarReLowerBound
    (W : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X → W X ≤ (routeAPSBZeroModeGeometricWindowScalar X).re

/-- Nonnegativity target for the real part of the window-stable geometric baseline scalar. -/
structure RouteAPSBZeroModeGeometricWindowScalarReNonneg : Prop where
  nonneg :
    ∀ {X : ℕ}, X0 ≤ X → 0 ≤ (routeAPSBZeroModeGeometricWindowScalar X).re

/-- Lower-bound target for the real part of the exact geometric scalar on the even window. -/
structure RouteAPSBExactGeometricScalarReLowerBound
    (E : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X → E X ≤ (exactGeometricScalar X).re

/-- Nonnegativity target for the real part of the exact geometric scalar. -/
structure RouteAPSBExactGeometricScalarReNonneg : Prop where
  nonneg :
    ∀ {X : ℕ}, X0 ≤ X → 0 ≤ (exactGeometricScalar X).re

/-- Explicit lower profile coming from the diagonal `n = N / 2` contribution. -/
def routeAPSBExactGeometricScalarLowerProfile (_X : ℕ) : ℝ :=
  Goldbach.BG_Identity.K_full (0 : ℤ)

/-- Explicit lower profile for the fixed zero-mode geometric window scalar. -/
def routeAPSBZeroModeGeometricWindowScalarLowerProfile (X : ℕ) : ℝ :=
  ((47 : ℝ) / 50)
    * (((2 * H + 1 : ℕ) : ℝ)⁻¹ * (Real.log (X : ℝ))⁻¹) ^ 2
    * routeAPSBExactGeometricScalarLowerProfile X

/-- Explicit lower profile for the dyadic geometric baseline sum. -/
def routeAPSBZeroModeGeometricBaselineLowerProfile (X : ℕ) : ℝ :=
  ((EvenIn X H).card : ℝ)
    * (routeVisibleWindowNormFloor X ^ 2
        * routeAPSBZeroModeGeometricWindowScalarLowerProfile X)

/-- Explicit lower profile for the dyadic sigma baseline sum. -/
def routeAPSBZeroModeSigmaBaselineLowerProfile (X : ℕ) : ℝ :=
  routeAPSBZeroModeGeometricBaselineLowerProfile X

/-- Explicit lower profile for the `SS_formula` dyadic main contribution. -/
def routeAPSBSSMainLowerProfile (X : ℕ) : ℝ :=
  routeAPSBSSMainScale X * routeAPSBZeroModeSigmaBaselineLowerProfile X

/-- Public lower norm bound for the exact recentered geometric scalar. -/
lemma exactGeometricScalar_norm_lower
    {X : ℕ} (hX : X0 ≤ X) :
    Goldbach.BG_Identity.K_full (0 : ℤ) ≤ ‖exactGeometricScalar X‖ := by
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := by
    simpa [N] using (canonicalEvenWindowPoint_mem_even_window (X := X))
  let hT :=
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise.unscaledGeometricZeroSliceMassWindowNormTarget_explicit
  have hlower := hT.lower hX hN
  simpa [N, exactGeometricScalar] using hlower

/-- Public upper norm bound for the exact recentered geometric scalar. -/
lemma exactGeometricScalar_norm_le_two
    {X : ℕ} (hX : X0 ≤ X) :
    ‖exactGeometricScalar X‖ ≤ 2 := by
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := by
    simpa [N] using (canonicalEvenWindowPoint_mem_even_window (X := X))
  let hT :=
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise.unscaledGeometricZeroSliceMassWindowNormTarget_explicit
  have hupper := hT.upper hX hN
  simpa [N, exactGeometricScalar] using hupper

/-- The exact recentered geometric scalar has nonnegative real part. -/
theorem routeAPSBExactGeometricScalarReNonneg_explicit :
    RouteAPSBExactGeometricScalarReNonneg := by
  refine ⟨?_⟩
  intro X hX
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := by
    simpa [N] using (canonicalEvenWindowPoint_mem_even_window (X := X))
  have hnonneg := unscaledGeometricZeroSliceMass_re_nonneg_of_mem_even_window hX hN
  simpa [N, exactGeometricScalar] using hnonneg

/-- The diagonal contribution gives a uniform real-part lower floor for the exact geometric scalar. -/
theorem routeAPSBExactGeometricScalarReLowerBound_explicit :
    RouteAPSBExactGeometricScalarReLowerBound routeAPSBExactGeometricScalarLowerProfile := by
  refine ⟨?_⟩
  intro X hX
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := by
    simpa [N] using (canonicalEvenWindowPoint_mem_even_window (X := X))
  have hlower := unscaledGeometricZeroSliceMass_re_lower_of_mem_even_window hX hN
  simpa [routeAPSBExactGeometricScalarLowerProfile, N, exactGeometricScalar] using hlower

/--
Pointwise lower-floor target for `zeroModeGeometricBaseline` on the canonical even window.

This is the smallest pointwise input needed to package the geometric-baseline dyadic mean lower
bound.
-/
structure RouteAPSBZeroModeGeometricBaselinePointwiseLowerBound
    (m : ℕ → ℝ) : Prop where
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → m X ≤ (zeroModeGeometricBaseline X N).re

/-- The singular-series factor in `zeroModeSigmaBaseline` is a real scalar. -/
lemma sigmaNormalizedSeries_re_eq_real (N : ℕ) :
    (sigmaNormalizedSeries N).re
      =
    Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
      / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) := by
  simpa [sigmaNormalizedSeries] using
    (Complex.ofReal_re
      (Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)))

lemma sigmaNormalizedSeries_im_eq_zero (N : ℕ) :
    (sigmaNormalizedSeries N).im = 0 := by
  simpa [sigmaNormalizedSeries] using
    (Complex.ofReal_im
      (Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)))

/-- On the working even window, the normalized singular series is at least `1` in real part. -/
lemma one_le_sigmaNormalizedSeries_re_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    1 ≤ (sigmaNormalizedSeries N).re := by
  rw [sigmaNormalizedSeries_re_eq_real]
  have hσ := Goldbach.Analytic.SigmaLowerOn_working.bound hX hN
  have hden_pos : 0 < ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) := by
    nlinarith [Goldbach.Analytic.C2_numeric.pos]
  have hden_le :
      ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)
        ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N := by
    simpa [Goldbach.Analytic.σmin_working] using hσ
  have hquot :
      ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)
        / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)
        ≤
      Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) := by
    exact div_le_div_of_nonneg_right hden_le (le_of_lt hden_pos)
  simpa [hden_pos.ne'] using hquot

/--
Exact real-part factorization of the zero-mode sigma baseline into the geometric baseline and the
real normalized singular-series multiplier.
-/
lemma zeroModeSigmaBaseline_re_eq_sigma_mul_geometricBaseline_re
    (X N : ℕ) :
    (zeroModeSigmaBaseline X N).re
      =
    (sigmaNormalizedSeries N).re * (zeroModeGeometricBaseline X N).re := by
  unfold zeroModeSigmaBaseline
  rw [Complex.mul_re]
  rw [sigmaNormalizedSeries_im_eq_zero, sigmaNormalizedSeries_re_eq_real]
  ring

/--
Reduce the primitive lower bound on the dyadic zero-mode sigma baseline to the geometric baseline,
provided the geometric baseline has nonnegative real part on the working even window.

This isolates the only remaining sign issue on the Route-A mean side: the singular-series factor is
already positive on the window, so the arithmetic lower bound lives on `zeroModeGeometricBaseline`.
-/
theorem routeAPSBZeroModeSigmaBaselineLowerBound_of_geometricBaseline
    (Mgeom : ℕ → ℝ)
    (hgeom : RouteAPSBZeroModeGeometricBaselineLowerBound Mgeom)
    (hgeom_nonneg : RouteAPSBZeroModeGeometricBaselineReNonneg) :
    RouteAPSBZeroModeSigmaBaselineLowerBound Mgeom := by
  refine ⟨?_⟩
  intro X hX
  have hsum_ge :
      routeAPSBZeroModeGeometricBaselineSum X ≤ routeAPSBZeroModeSigmaBaselineSum X := by
    unfold routeAPSBZeroModeGeometricBaselineSum routeAPSBZeroModeSigmaBaselineSum
    refine Finset.sum_le_sum ?_
    intro N hN
    rw [zeroModeSigmaBaseline_re_eq_sigma_mul_geometricBaseline_re]
    have hsigma_one : 1 ≤ (sigmaNormalizedSeries N).re :=
      one_le_sigmaNormalizedSeries_re_of_mem_even_window hX hN
    have hgeom_re_nonneg : 0 ≤ (zeroModeGeometricBaseline X N).re :=
      hgeom_nonneg.nonneg hX hN
    calc
      (zeroModeGeometricBaseline X N).re
          ≤ 1 * (zeroModeGeometricBaseline X N).re := by simpa using le_rfl
      _ ≤ (sigmaNormalizedSeries N).re * (zeroModeGeometricBaseline X N).re := by
          exact mul_le_mul_of_nonneg_right hsigma_one hgeom_re_nonneg
  exact le_trans (hgeom.bound hX) hsum_ge

/--
Exact factorization of the geometric zero-mode baseline into the square of the `q0`-normalization
and a window-stable scalar part on `EvenIn X H`.
-/
theorem zeroModeGeometricBaseline_eq_q0NormFactor_sq_mul_windowScalar_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    zeroModeGeometricBaseline X N
      =
    (Q0MinorNormalizationBridge.q0NormFactor N ^ 2)
      * routeAPSBZeroModeGeometricWindowScalar X := by
  unfold zeroModeGeometricBaseline routeAPSBZeroModeGeometricWindowScalar
  rw [geometricWeightedMinorCoeff_zero_eq_q0_weight0_mul_rawGeometricZeroSliceMass]
  rw [rawGeometricZeroSliceMass_eq_geometricZeroSliceNormalization_mul_unscaled]
  rw [unscaledGeometricZeroSliceMass_eq_exactGeometricScalar hX hN]
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

/--
On the canonical even window, the real part of `zeroModeGeometricBaseline` is the square of the
real `q0`-normalization times the real part of the window-stable scalar factor.
-/
theorem zeroModeGeometricBaseline_re_eq_q0NormFactor_sq_mul_windowScalar_re_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (zeroModeGeometricBaseline X N).re
      =
    (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) ^ 2)
      * (routeAPSBZeroModeGeometricWindowScalar X).re := by
  rw [zeroModeGeometricBaseline_eq_q0NormFactor_sq_mul_windowScalar_of_mem_even_window hX hN]
  let r : ℝ := (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
  have hr : Q0MinorNormalizationBridge.q0NormFactor N = (r : ℂ) := by
    simp [Q0MinorNormalizationBridge.q0NormFactor, r]
  rw [hr]
  change ((((r : ℂ) ^ 2) * routeAPSBZeroModeGeometricWindowScalar X).re
      = r ^ 2 * (routeAPSBZeroModeGeometricWindowScalar X).re)
  rw [Complex.mul_re]
  simp [pow_two]

/--
Package a pointwise lower floor on `zeroModeGeometricBaseline` into the dyadic lower-bound target.
-/
theorem routeAPSBZeroModeGeometricBaselineLowerBound_of_pointwise
    (m : ℕ → ℝ)
    (hpoint : RouteAPSBZeroModeGeometricBaselinePointwiseLowerBound m) :
    RouteAPSBZeroModeGeometricBaselineLowerBound (fun X => ((EvenIn X H).card : ℝ) * m X) := by
  refine ⟨?_⟩
  intro X hX
  unfold routeAPSBZeroModeGeometricBaselineSum
  calc
    ((EvenIn X H).card : ℝ) * m X
        = Finset.sum (EvenIn X H) (fun _ => m X) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Finset.sum (EvenIn X H) (fun N => (zeroModeGeometricBaseline X N).re) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact hpoint.bound hX hN

/--
Any nonnegative pointwise lower floor on `zeroModeGeometricBaseline` yields the sign packet needed
to lift the geometric baseline lower bound through the sigma factor.
-/
theorem routeAPSBZeroModeGeometricBaselineReNonneg_of_pointwise
    (m : ℕ → ℝ)
    (hm_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ m X)
    (hpoint : RouteAPSBZeroModeGeometricBaselinePointwiseLowerBound m) :
    RouteAPSBZeroModeGeometricBaselineReNonneg := by
  refine ⟨?_⟩
  intro X N hX hN
  exact le_trans (hm_nonneg hX) (hpoint.bound hX hN)

/--
Reduce the dyadic geometric-baseline lower bound to a lower bound for the window-stable scalar.

This is the current Route-A mean bottleneck in its cleanest form: once the fixed window scalar has
a positive real lower floor, the `q0`-normalization lower bound upgrades it to the geometric
baseline dyadic mean on `EvenIn X H`.
-/
theorem routeAPSBZeroModeGeometricBaselineLowerBound_of_windowScalar
    (W : ℕ → ℝ)
    (hW : RouteAPSBZeroModeGeometricWindowScalarReLowerBound W)
    (hW_nonneg : RouteAPSBZeroModeGeometricWindowScalarReNonneg) :
    RouteAPSBZeroModeGeometricBaselineLowerBound
      (fun X => ((EvenIn X H).card : ℝ) * (routeVisibleWindowNormFloor X ^ 2 * W X)) := by
  apply routeAPSBZeroModeGeometricBaselineLowerBound_of_pointwise
  refine ⟨?_⟩
  intro X N hX hN
  rw [zeroModeGeometricBaseline_re_eq_q0NormFactor_sq_mul_windowScalar_re_of_mem_even_window hX hN]
  have hq0_lower :
      routeVisibleWindowNormFloor X ^ 2
        ≤
      (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) ^ 2) := by
    have h := Q0MinorNormalizedEnergy.q0NormFactor_lower_on_window (X := X) (N := N) hX hN
    rw [Q0MinorNormalizedEnergy.norm_q0NormFactor] at h
    have hnonneg : 0 ≤ routeVisibleWindowNormFloor X := by
      unfold routeVisibleWindowNormFloor
      positivity
    have hq0_nonneg : 0 ≤ (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := by
      positivity
    have hsq :
        routeVisibleWindowNormFloor X * routeVisibleWindowNormFloor X
          ≤
        ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2))
          * ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) := by
      exact mul_le_mul h h hnonneg hq0_nonneg
    simpa [pow_two] using hsq
  have hW_le : W X ≤ (routeAPSBZeroModeGeometricWindowScalar X).re := hW.bound hX
  have hW_nonnegX : 0 ≤ (routeAPSBZeroModeGeometricWindowScalar X).re := hW_nonneg.nonneg hX
  calc
    routeVisibleWindowNormFloor X ^ 2 * W X
        ≤ routeVisibleWindowNormFloor X ^ 2 * (routeAPSBZeroModeGeometricWindowScalar X).re := by
            exact mul_le_mul_of_nonneg_left hW_le (sq_nonneg _)
    _ ≤ (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) ^ 2)
          * (routeAPSBZeroModeGeometricWindowScalar X).re := by
            exact mul_le_mul_of_nonneg_right hq0_lower hW_nonnegX

/-- Nonnegativity of the geometric baseline follows from nonnegative fixed window-scalar input. -/
theorem routeAPSBZeroModeGeometricBaselineReNonneg_of_windowScalar
    (hW_nonneg : RouteAPSBZeroModeGeometricWindowScalarReNonneg) :
    RouteAPSBZeroModeGeometricBaselineReNonneg := by
  refine ⟨?_⟩
  intro X N hX hN
  rw [zeroModeGeometricBaseline_re_eq_q0NormFactor_sq_mul_windowScalar_re_of_mem_even_window hX hN]
  exact mul_nonneg (sq_nonneg _) (hW_nonneg.nonneg hX)

/-- The constant Fourier mode of the major-arc weight is exactly the real major-arc mass. -/
theorem majorArcWeightFourier_zero_eq_majorArcConstMode
    (X : ℕ) (Δ : ℝ) :
    Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0
      =
    ((Q0MajorTailMeanZero.majorArcConstMode X Δ : ℝ) : ℂ) := by
  have h0 :
      Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0
        =
      ∫ α in (0 : ℝ)..(1 : ℝ), Q0MajorTailTTStarAlgebra.majorArcWeightC X Δ α := by
    simp [Q0MajorTailTTStarAlgebra.majorArcWeightFourier, fourier_zero, mul_assoc]
  calc
    Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0
        =
      ∫ α in (0 : ℝ)..(1 : ℝ), Q0MajorTailTTStarAlgebra.majorArcWeightC X Δ α := h0
    _ =
      ∫ α in (0 : ℝ)..(1 : ℝ), ((Q0MajorTailMeanZero.majorArcWeight X Δ α : ℝ) : ℂ) := by
        refine intervalIntegral.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro α
        by_cases hα :
            α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
        · simp [Q0MajorTailTTStarAlgebra.majorArcWeightC, Q0MajorTailMeanZero.majorArcWeight, hα]
        · simp [Q0MajorTailTTStarAlgebra.majorArcWeightC, Q0MajorTailMeanZero.majorArcWeight, hα]
    _ = ((∫ α in (0 : ℝ)..(1 : ℝ), Q0MajorTailMeanZero.majorArcWeight X Δ α : ℝ) : ℂ) := by
      simpa using
        (intervalIntegral.integral_ofReal
          (f := fun α : ℝ => Q0MajorTailMeanZero.majorArcWeight X Δ α))
    _ = ((Q0MajorTailMeanZero.majorArcConstMode X Δ : ℝ) : ℂ) := by
      simp [Q0MajorTailMeanZero.majorArcConstMode]

/-- The zero-frequency minor-arc Fourier weight is the real complement of the major-arc mass. -/
theorem minorArcWeightFourier_zero_eq_one_sub_majorArcConstMode
    (X : ℕ) (Δ : ℝ) :
    Q0MinorTTStarAlgebra.minorArcWeightFourier X Δ 0
      =
    (((1 - Q0MajorTailMeanZero.majorArcConstMode X Δ) : ℝ) : ℂ) := by
  rw [Q0MinorTTStarAlgebra.minorArcWeightFourier_zero, majorArcWeightFourier_zero_eq_majorArcConstMode]
  simp

lemma minorArcWeightFourier_zero_re_eq_one_sub_majorArcConstMode
    (X : ℕ) (Δ : ℝ) :
    (Q0MinorTTStarAlgebra.minorArcWeightFourier X Δ 0).re
      =
    1 - Q0MajorTailMeanZero.majorArcConstMode X Δ := by
  rw [minorArcWeightFourier_zero_eq_one_sub_majorArcConstMode]
  simp

lemma minorArcWeightFourier_zero_im_eq_zero
    (X : ℕ) (Δ : ℝ) :
    (Q0MinorTTStarAlgebra.minorArcWeightFourier X Δ 0).im = 0 := by
  rw [minorArcWeightFourier_zero_eq_one_sub_majorArcConstMode]
  simp

/-- Explicit lower bound for the real zero-frequency minor-arc weight on the working window. -/
lemma minorArcWeightFourier_zero_re_lower_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    (47 : ℝ) / 50
      ≤
    (Q0MinorTTStarAlgebra.minorArcWeightFourier X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re := by
  rw [minorArcWeightFourier_zero_re_eq_one_sub_majorArcConstMode]
  have hXpos : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hmaj :
      Q0MajorTailMeanZero.majorArcConstMode X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon
        ≤ (60000 : ℝ) / (X : ℝ) := by
    have h := Q0MajorTailMeanZero.majorArcConstMode_le
      (X := X) (Δ := (1 : ℝ)) (by norm_num) hXpos
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0] at h ⊢
    exact h
  have hsmall : (60000 : ℝ) / (X : ℝ) ≤ (3 : ℝ) / 50 := by
    have hXr : (1000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hXposR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
    rw [div_le_iff₀ hXposR]
    nlinarith
  linarith

/-- The geometric zero-slice normalization is a positive real scalar. -/
lemma geometricZeroSliceNormalization_re_eq_explicit
    (X : ℕ) :
    (geometricZeroSliceNormalization X).re
      =
    ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2 := by
  have hre : (Complex.log (X : ℂ)).re = Real.log (X : ℝ) := by
    simpa using Complex.log_ofReal_re (X : ℝ)
  have him : (Complex.log (X : ℂ)).im = 0 := by
    rw [Complex.log_im]
    simpa using Complex.arg_ofReal_of_nonneg (show 0 ≤ (X : ℝ) by positivity)
  unfold geometricZeroSliceNormalization uniformWindowNormalization
  simpa [pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq, hre, him, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
    using rfl

lemma geometricZeroSliceNormalization_im_eq_zero
    (X : ℕ) :
    (geometricZeroSliceNormalization X).im = 0 := by
  have hre : (Complex.log (X : ℂ)).re = Real.log (X : ℝ) := by
    simpa using Complex.log_ofReal_re (X : ℝ)
  have him : (Complex.log (X : ℂ)).im = 0 := by
    rw [Complex.log_im]
    simpa using Complex.arg_ofReal_of_nonneg (show 0 ≤ (X : ℝ) by positivity)
  unfold geometricZeroSliceNormalization uniformWindowNormalization
  simpa [pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq, hre, him, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
    using rfl

lemma geometricZeroSliceNormalization_re_nonneg
    (X : ℕ) :
    0 ≤ (geometricZeroSliceNormalization X).re := by
  rw [geometricZeroSliceNormalization_re_eq_explicit]
  positivity

/--
Real-part factorization of the window-stable geometric scalar: the minor-arc zero mode and the
geometric normalization are real scalars, so only the real part of `exactGeometricScalar` enters.
-/
lemma routeAPSBZeroModeGeometricWindowScalar_re_eq_components
    (X : ℕ) :
    (routeAPSBZeroModeGeometricWindowScalar X).re
      =
    (Q0MinorTTStarAlgebra.minorArcWeightFourier X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re
      * (geometricZeroSliceNormalization X).re
      * (exactGeometricScalar X).re := by
  unfold routeAPSBZeroModeGeometricWindowScalar
  have hpair_im :
      (Q0MinorTTStarAlgebra.minorArcWeightFourier X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0
        * geometricZeroSliceNormalization X).im = 0 := by
    rw [Complex.mul_im, minorArcWeightFourier_zero_im_eq_zero, geometricZeroSliceNormalization_im_eq_zero]
    ring
  have hpair_re :
      (Q0MinorTTStarAlgebra.minorArcWeightFourier X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0
        * geometricZeroSliceNormalization X).re
        =
      (Q0MinorTTStarAlgebra.minorArcWeightFourier X Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re
        * (geometricZeroSliceNormalization X).re := by
    rw [Complex.mul_re, minorArcWeightFourier_zero_im_eq_zero, geometricZeroSliceNormalization_im_eq_zero]
    ring
  rw [Complex.mul_re, hpair_im, hpair_re]
  ring

/--
Build the fixed window-scalar lower bound from explicit control of the zero-frequency minor weight,
the geometric normalization, and the exact geometric scalar.
-/
theorem routeAPSBZeroModeGeometricWindowScalarReLowerBound_of_exactGeometricScalar
    (E : ℕ → ℝ)
    (hexact : RouteAPSBExactGeometricScalarReLowerBound E)
    (hexact_nonneg : RouteAPSBExactGeometricScalarReNonneg) :
    RouteAPSBZeroModeGeometricWindowScalarReLowerBound
      (fun X =>
        ((47 : ℝ) / 50)
          * ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2
          * E X) := by
  refine ⟨?_⟩
  intro X hX
  rw [routeAPSBZeroModeGeometricWindowScalar_re_eq_components]
  have hminor :
      (47 : ℝ) / 50
        ≤
      (Q0MinorTTStarAlgebra.minorArcWeightFourier X
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re :=
    minorArcWeightFourier_zero_re_lower_explicit hX
  have hgeom_eq :
      (geometricZeroSliceNormalization X).re
        =
      ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2 :=
    geometricZeroSliceNormalization_re_eq_explicit X
  have hgeom_nonneg :
      0 ≤ ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2 := by
    positivity
  have hexactX : E X ≤ (exactGeometricScalar X).re := hexact.bound hX
  have hexact_nonnegX : 0 ≤ (exactGeometricScalar X).re := hexact_nonneg.nonneg hX
  have hscale_nonneg :
      0 ≤
        ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2
          * (exactGeometricScalar X).re := by
    exact mul_nonneg hgeom_nonneg hexact_nonnegX
  have hminor_scaled :
      (47 : ℝ) / 50
        * (((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2
            * (exactGeometricScalar X).re)
      ≤
      (Q0MinorTTStarAlgebra.minorArcWeightFourier X
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re
        * (((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2
            * (exactGeometricScalar X).re) := by
    exact mul_le_mul_of_nonneg_right hminor hscale_nonneg
  calc
    (47 : ℝ) / 50 * ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2 * E X
        ≤
    (47 : ℝ) / 50 * ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2
      * (exactGeometricScalar X).re := by
          exact mul_le_mul_of_nonneg_left hexactX
            (mul_nonneg (by positivity) hgeom_nonneg)
    _ ≤
    (Q0MinorTTStarAlgebra.minorArcWeightFourier X
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re
      * ((Real.log (X : ℝ) * (((2 * H + 1 : ℕ) : ℝ)))⁻¹) ^ 2
      * (exactGeometricScalar X).re := by
          simpa [mul_assoc] using hminor_scaled
    _ =
    (Q0MinorTTStarAlgebra.minorArcWeightFourier X
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re
      * (geometricZeroSliceNormalization X).re
      * (exactGeometricScalar X).re := by
          rw [hgeom_eq]

/-- The fixed window scalar is nonnegative once the exact geometric scalar has nonnegative real part. -/
theorem routeAPSBZeroModeGeometricWindowScalarReNonneg_of_exactGeometricScalar
    (hexact : RouteAPSBExactGeometricScalarReNonneg) :
    RouteAPSBZeroModeGeometricWindowScalarReNonneg := by
  refine ⟨?_⟩
  intro X hX
  rw [routeAPSBZeroModeGeometricWindowScalar_re_eq_components]
  have hminor : 0 ≤
      (Q0MinorTTStarAlgebra.minorArcWeightFourier X
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 0).re := by
    exact le_trans (by positivity : 0 ≤ (47 : ℝ) / 50)
      (minorArcWeightFourier_zero_re_lower_explicit hX)
  exact mul_nonneg (mul_nonneg hminor (geometricZeroSliceNormalization_re_nonneg X))
    (hexact.nonneg hX)

/-- Explicit lower bound for the fixed zero-mode geometric window scalar. -/
theorem routeAPSBZeroModeGeometricWindowScalarReLowerBound_explicit :
    RouteAPSBZeroModeGeometricWindowScalarReLowerBound
      routeAPSBZeroModeGeometricWindowScalarLowerProfile := by
  refine ⟨?_⟩
  intro X hX
  have h :=
    (routeAPSBZeroModeGeometricWindowScalarReLowerBound_of_exactGeometricScalar
      routeAPSBExactGeometricScalarLowerProfile
      routeAPSBExactGeometricScalarReLowerBound_explicit
      routeAPSBExactGeometricScalarReNonneg_explicit).bound hX
  simpa [routeAPSBZeroModeGeometricWindowScalarLowerProfile]
    using h

/-- The fixed zero-mode geometric window scalar is nonnegative. -/
theorem routeAPSBZeroModeGeometricWindowScalarReNonneg_explicit :
    RouteAPSBZeroModeGeometricWindowScalarReNonneg := by
  exact routeAPSBZeroModeGeometricWindowScalarReNonneg_of_exactGeometricScalar
    routeAPSBExactGeometricScalarReNonneg_explicit

/-- Explicit lower bound for the dyadic geometric baseline sum. -/
theorem routeAPSBZeroModeGeometricBaselineLowerBound_explicit :
    RouteAPSBZeroModeGeometricBaselineLowerBound
      routeAPSBZeroModeGeometricBaselineLowerProfile := by
  exact routeAPSBZeroModeGeometricBaselineLowerBound_of_windowScalar
    routeAPSBZeroModeGeometricWindowScalarLowerProfile
    routeAPSBZeroModeGeometricWindowScalarReLowerBound_explicit
    routeAPSBZeroModeGeometricWindowScalarReNonneg_explicit

/-- The geometric baseline has nonnegative real part on the working even window. -/
theorem routeAPSBZeroModeGeometricBaselineReNonneg_explicit :
    RouteAPSBZeroModeGeometricBaselineReNonneg := by
  exact routeAPSBZeroModeGeometricBaselineReNonneg_of_windowScalar
    routeAPSBZeroModeGeometricWindowScalarReNonneg_explicit

/-- Explicit lower bound for the dyadic zero-mode sigma baseline sum. -/
theorem routeAPSBZeroModeSigmaBaselineLowerBound_explicit :
    RouteAPSBZeroModeSigmaBaselineLowerBound
      routeAPSBZeroModeSigmaBaselineLowerProfile := by
  simpa [routeAPSBZeroModeSigmaBaselineLowerProfile]
    using routeAPSBZeroModeSigmaBaselineLowerBound_of_geometricBaseline
      routeAPSBZeroModeGeometricBaselineLowerProfile
      routeAPSBZeroModeGeometricBaselineLowerBound_explicit
      routeAPSBZeroModeGeometricBaselineReNonneg_explicit

lemma routeAPSBSSMainScale_nonneg {X : ℕ} (hX : X0 ≤ X) : 0 ≤ routeAPSBSSMainScale X := by
  unfold routeAPSBSSMainScale zeroModeBookkeepingScalarCandidate
  unfold routeVisibleWindowNormFloor
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlog_ge : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := by
    exact Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hlog_nonneg : 0 ≤ Real.log ((X + H : ℕ) : ℝ) := by
    linarith
  have hscalar_nonneg : 0 ≤ ((800 : ℝ) * sigmaEnvelopeKappa) := by
    norm_num [sigmaEnvelopeKappa]
  have hinv_nonneg : 0 ≤ (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) := by
    exact one_div_nonneg.mpr (sq_nonneg _)
  have hfloor_nonneg :
      0 ≤ (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
    exact mul_nonneg (by norm_num) hinv_nonneg
  exact mul_nonneg hscalar_nonneg hfloor_nonneg

/--
Exact scalar-factor identity for the dyadic `SS_formula` mean contribution.

This isolates the arithmetic core of the PSB main term: after pulling out the positive
`X`-dependent scalar `zeroModeBookkeepingScalarCandidate * routeVisibleWindowNormFloor X`, the
remaining dyadic sum is the real-part sum of `zeroModeSigmaBaseline`.
-/
theorem routeAPSBSSMainContributionSum_eq_scale_mul_zeroModeSigmaBaselineSum
    (X : ℕ) :
    routeAPSBSSMainContributionSum X
      = routeAPSBSSMainScale X * routeAPSBZeroModeSigmaBaselineSum X := by
  unfold routeAPSBSSMainContributionSum routeAPSBSSMainScale routeAPSBZeroModeSigmaBaselineSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [Q0MinorZeroModeEnvelope.SS_formula_eq_zeroModeSigmaBaseline_mul_routeVisibleWindowNormFloor]
  have hreal :
      ((((zeroModeBookkeepingScalarCandidate * routeVisibleWindowNormFloor X : ℝ) : ℂ)
          * zeroModeSigmaBaseline X N).re)
        =
      (zeroModeBookkeepingScalarCandidate * routeVisibleWindowNormFloor X)
        * (zeroModeSigmaBaseline X N).re := by
    simp [Complex.mul_re]
  simpa [mul_comm, mul_assoc] using hreal

/--
Package a lower bound for the dyadic zero-mode sigma baseline sum into the Route-A `SS_formula`
main-contribution lower bound.
-/
theorem routeAPSBSSMainContributionLowerBound_of_zeroModeSigmaBaseline
    (Mbase : ℕ → ℝ)
    (hbase : RouteAPSBZeroModeSigmaBaselineLowerBound Mbase) :
    RouteAPSBSSMainContributionLowerBound (fun X => routeAPSBSSMainScale X * Mbase X) := by
  refine ⟨?_⟩
  intro X hX
  rw [routeAPSBSSMainContributionSum_eq_scale_mul_zeroModeSigmaBaselineSum]
  exact mul_le_mul_of_nonneg_left (hbase.bound hX) (routeAPSBSSMainScale_nonneg hX)

/-- Explicit lower bound for the `SS_formula` dyadic main contribution on the Route-A mean side. -/
theorem routeAPSBSSMainContributionLowerBound_explicit :
    RouteAPSBSSMainContributionLowerBound routeAPSBSSMainLowerProfile := by
  simpa [routeAPSBSSMainLowerProfile]
    using routeAPSBSSMainContributionLowerBound_of_zeroModeSigmaBaseline
      routeAPSBZeroModeSigmaBaselineLowerProfile
      routeAPSBZeroModeSigmaBaselineLowerBound_explicit

/-- Normalized window-energy budget profile in the standard Route-A shape. -/
def routeAPSBWindowEnergyProfile (C2 C3 : ℝ) (X : ℕ) : ℝ :=
  routeVisibleWindowNormFloorSq X
    * (C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

/-- Dyadic absolute-error profile built from separate `L²` controls on `G_formula` and `R_formula`. -/
def routeAPSBVisibleMeanErrorProfile (C2g C3g C2r C3r : ℝ) (X : ℕ) : ℝ :=
  Real.sqrt (((EvenIn X H).card : ℝ) * routeAPSBWindowEnergyProfile C2g C3g X)
    + Real.sqrt (((EvenIn X H).card : ℝ) * routeAPSBWindowEnergyProfile C2r C3r X)

lemma routeAPSBWindowEnergyProfile_nonneg
    {C2 C3 : ℝ} {X : ℕ} (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    0 ≤ routeAPSBWindowEnergyProfile C2 C3 X := by
  unfold routeAPSBWindowEnergyProfile
  refine mul_nonneg (routeVisibleWindowNormFloorSq_nonneg _) ?_
  refine add_nonneg ?_ ?_
  · exact mul_nonneg hC2 (by positivity)
  · exact div_nonneg hC3 (by positivity)

lemma routeAPSBSum_norm_le_sqrt_card_mul_sum_norm_sq
    (X : ℕ) (f : ℕ → ℂ) :
    Finset.sum (EvenIn X H) (fun N => ‖f N‖)
      ≤
    Real.sqrt
      ((((EvenIn X H).card : ℝ))
        * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2)) := by
  have hsq :
      (Finset.sum (EvenIn X H) (fun N => ‖f N‖)) ^ 2
        ≤
      (((EvenIn X H).card : ℝ))
        * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2) := by
    exact
      (sq_sum_le_card_mul_sum_sq (s := EvenIn X H) (f := fun N => ‖f N‖) :
        (Finset.sum (EvenIn X H) (fun N => ‖f N‖)) ^ 2
          ≤
        (((EvenIn X H).card : ℝ))
          * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2))
  have hsum_nonneg : 0 ≤ Finset.sum (EvenIn X H) (fun N => ‖f N‖) := by
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hrhs_nonneg :
      0 ≤
        (((EvenIn X H).card : ℝ))
          * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2) := by
    refine mul_nonneg (by exact_mod_cast Nat.zero_le (EvenIn X H).card) ?_
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsqrt_sq :
      (Real.sqrt
        ((((EvenIn X H).card : ℝ))
          * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2))) ^ 2
        =
      (((EvenIn X H).card : ℝ))
        * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2) := by
    exact Real.sq_sqrt hrhs_nonneg
  have hsqrt_nonneg :
      0 ≤
        Real.sqrt
          ((((EvenIn X H).card : ℝ))
            * Finset.sum (EvenIn X H) (fun N => ‖f N‖ ^ 2)) := by
    exact Real.sqrt_nonneg _
  nlinarith [hsq, hsqrt_sq, hsum_nonneg, hsqrt_nonneg]

lemma routeAPSBVisibleMeanErrorAbsSum_le_sum_norm_G_add_sum_norm_R
    (X : ℕ) :
    routeAPSBVisibleMeanErrorAbsSum X
      ≤
    Finset.sum (EvenIn X H) (fun N => ‖G_formula X N‖)
      + Finset.sum (EvenIn X H) (fun N => ‖R_formula X N‖) := by
  unfold routeAPSBVisibleMeanErrorAbsSum
  calc
    Finset.sum (EvenIn X H) (fun N => |(G_formula X N + R_formula X N).re|)
      ≤
    Finset.sum (EvenIn X H) (fun N => ‖G_formula X N + R_formula X N‖) := by
        refine Finset.sum_le_sum ?_
        intro N hN
        simpa using Complex.abs_re_le_norm (G_formula X N + R_formula X N)
    _ ≤
    Finset.sum (EvenIn X H) (fun N => (‖G_formula X N‖ + ‖R_formula X N‖)) := by
        refine Finset.sum_le_sum ?_
        intro N hN
        exact norm_add_le (G_formula X N) (R_formula X N)
    _ =
    Finset.sum (EvenIn X H) (fun N => ‖G_formula X N‖)
      + Finset.sum (EvenIn X H) (fun N => ‖R_formula X N‖) := by
        rw [Finset.sum_add_distrib]

/-- Upper-bound target for the absolute dyadic mean error carried by `G_formula + R_formula`. -/
structure RouteAPSBVisibleMeanErrorAbsUpperBound
    (Merr : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X → routeAPSBVisibleMeanErrorAbsSum X ≤ Merr X

/--
Deterministic `L² → L¹` transport for the dyadic visible error.

This separates the paper arithmetic from the bookkeeping: any window-energy bounds for
`G_formula` and `R_formula` immediately control the conservative absolute error
`G_formula + R_formula`.
-/
theorem routeAPSBVisibleMeanErrorAbsUpperBound_of_windowEnergyBounds
    (EG ER : ℕ → ℝ)
    (hG :
      ∀ {X : ℕ}, X0 ≤ X →
        Finset.sum (EvenIn X H) (fun N => ‖G_formula X N‖ ^ 2) ≤ EG X)
    (hR :
      ∀ {X : ℕ}, X0 ≤ X →
        routeVisibleResidualWindowEnergy X ≤ ER X) :
    RouteAPSBVisibleMeanErrorAbsUpperBound
      (fun X =>
        Real.sqrt (((EvenIn X H).card : ℝ) * EG X)
          + Real.sqrt (((EvenIn X H).card : ℝ) * ER X)) := by
  refine ⟨?_⟩
  intro X hX
  have hsplit := routeAPSBVisibleMeanErrorAbsSum_le_sum_norm_G_add_sum_norm_R X
  have hG_l1 :=
    routeAPSBSum_norm_le_sqrt_card_mul_sum_norm_sq X (fun N => G_formula X N)
  have hR_l1 :=
    routeAPSBSum_norm_le_sqrt_card_mul_sum_norm_sq X (fun N => R_formula X N)
  have hG_sq :
      Finset.sum (EvenIn X H) (fun N => ‖G_formula X N‖ ^ 2) ≤ EG X :=
    hG hX
  have hR_sq :
      Finset.sum (EvenIn X H) (fun N => ‖R_formula X N‖ ^ 2) ≤ ER X := by
    simpa [routeVisibleResidualWindowEnergy] using hR hX
  have hcard_nonneg : 0 ≤ (((EvenIn X H).card : ℝ)) := by
    exact_mod_cast Nat.zero_le (EvenIn X H).card
  have hG_sqrt :
      Real.sqrt
          ((((EvenIn X H).card : ℝ))
            * Finset.sum (EvenIn X H) (fun N => ‖G_formula X N‖ ^ 2))
        ≤ Real.sqrt ((((EvenIn X H).card : ℝ)) * EG X) := by
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hG_sq hcard_nonneg)
  have hR_sqrt :
      Real.sqrt
          ((((EvenIn X H).card : ℝ))
            * Finset.sum (EvenIn X H) (fun N => ‖R_formula X N‖ ^ 2))
        ≤ Real.sqrt ((((EvenIn X H).card : ℝ)) * ER X) := by
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hR_sq hcard_nonneg)
  exact le_trans hsplit
    (add_le_add (le_trans hG_l1 hG_sqrt) (le_trans hR_l1 hR_sqrt))

/--
Energy-target form of the dyadic visible-error bound.

The `G_formula` side is supplied by `GFormulaEnergyTarget`; the remaining live arithmetic input is
the route-visible residual target for `R_formula`.
-/
theorem routeAPSBVisibleMeanErrorAbsUpperBound_of_energyTargets
    {C2g C3g C2r C3r : ℝ}
    (hG : Q0MinorGFormulaRouteA.GFormulaEnergyTarget C2g C3g)
    (hR : RouteVisibleResidualTarget C2r C3r) :
    RouteAPSBVisibleMeanErrorAbsUpperBound
      (routeAPSBVisibleMeanErrorProfile C2g C3g C2r C3r) := by
  exact
    routeAPSBVisibleMeanErrorAbsUpperBound_of_windowEnergyBounds
      (EG := routeAPSBWindowEnergyProfile C2g C3g)
      (ER := routeAPSBWindowEnergyProfile C2r C3r)
      (hG := by
        intro X hX
        exact hG.bound (X := X) hX)
      (hR := by
        intro X hX
        exact hR.bound (X := X) hX)

/--
Explicit `G_formula` closure plus a residual-energy target gives the full visible-error upper
bound. Thus the Route-A mean subtractive side is reduced to the residual theorem for `R_formula`.
-/
theorem routeAPSBVisibleMeanErrorAbsUpperBound_of_explicitG_and_residualTarget
    {C2r C3r : ℝ}
    (hR : RouteVisibleResidualTarget C2r C3r) :
    RouteAPSBVisibleMeanErrorAbsUpperBound
      (routeAPSBVisibleMeanErrorProfile
        ((((14 : ℝ) / 13) ^ 4)
          * Q0MinorGFormulaRouteA.gFormulaCoreBudgetConst)
        0 C2r C3r) := by
  exact routeAPSBVisibleMeanErrorAbsUpperBound_of_energyTargets
    Q0MinorGFormulaClosure.gFormulaEnergyTarget_explicit hR

/--
Exact dyadic-sum inequality underlying the PSB `main contribution - error` packet.

This is the deterministic statement that the singular-series-style sum `SS_formula` is controlled
from below by the exact raw dyadic mean of `minorResidual`, up to the absolute contribution of the
remaining terms `G_formula + R_formula`.
-/
theorem routeAPSBSSMainContribution_le_minorResidual_plus_errorAbs
    {X : ℕ} (hX : X0 ≤ X) :
    routeAPSBSSMainContributionSum X
      ≤ routeAPSBMinorResidualDyadicMeanSum X + routeAPSBVisibleMeanErrorAbsSum X := by
  have hpoint :
      ∀ N ∈ EvenIn X H,
        (SS_formula X N).re
          ≤
        (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
            Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re
          + |(G_formula X N + R_formula X N).re| := by
    intro N hN
    have hdecomp :
        routeVisibleScalar X N = G_formula X N + SS_formula X N + R_formula X N := by
      exact routeVisibleScalar_eq_G_formula_add_SS_formula_add_R_formula (X := X) (N := N)
    have hminor :
        routeVisibleScalar X N
          =
        Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
          Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon := by
      exact routeVisibleScalar_eq_minorResidual hX hN
    have hscalar :
        (SS_formula X N).re
          =
        (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
            Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re
          - (G_formula X N + R_formula X N).re := by
      rw [← hminor, hdecomp]
      simp only [Complex.add_re, sub_eq_add_neg]
      ring_nf
    rw [hscalar]
    linarith [neg_abs_le ((G_formula X N + R_formula X N).re)]
  calc
    routeAPSBSSMainContributionSum X
      = Finset.sum (EvenIn X H) (fun N => (SS_formula X N).re) := by
          rfl
    _ ≤ Finset.sum (EvenIn X H) (fun N =>
          (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
              Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re
            + |(G_formula X N + R_formula X N).re|) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact hpoint N hN
    _ =
      routeAPSBMinorResidualDyadicMeanSum X + routeAPSBVisibleMeanErrorAbsSum X := by
        simp [routeAPSBMinorResidualDyadicMeanSum, routeAPSBVisibleMeanErrorAbsSum,
          Finset.sum_add_distrib]

/--
PSB main-contribution lower bound on the raw dyadic mean of `minorResidual`.

This is the machine-facing form of the positive part of the paper's PSB argument. It is stated
against the exact raw dyadic mean sum, with any subtractive loss carried separately by `Merr`.
-/
structure RouteAPSBMinorResidualMainContributionLowerBound
    (Mmain Merr : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      Mmain X ≤ routeAPSBMinorResidualDyadicMeanSum X + Merr X

/--
PSB error upper bound on the raw dyadic mean of `minorResidual`.

This is intentionally minimal: at the current Route-A mean stage we only need the subtractive error
to be nonnegative so it can be peeled off from the main contribution lower bound.
-/
structure RouteAPSBMinorResidualMeanErrorUpperBound
    (Merr : ℕ → ℝ) : Prop where
  nonneg :
    ∀ {X : ℕ}, X0 ≤ X → 0 ≤ Merr X

/--
The visible absolute-error upper bound already forces the PSB mean-error profile to be nonnegative.

So `RouteAPSBMinorResidualMeanErrorUpperBound` is bookkeeping only unless the paper introduces an
additional mean-loss term distinct from the visible dyadic error.
-/
theorem routeAPSBMinorResidualMeanErrorUpperBound_of_visibleErrorAbs
    (Merr : ℕ → ℝ)
    (herr : RouteAPSBVisibleMeanErrorAbsUpperBound Merr) :
    RouteAPSBMinorResidualMeanErrorUpperBound Merr := by
  refine ⟨?_⟩
  intro X hX
  have hsum_nonneg : 0 ≤ routeAPSBVisibleMeanErrorAbsSum X := by
    unfold routeAPSBVisibleMeanErrorAbsSum
    refine Finset.sum_nonneg ?_
    intro N hN
    exact abs_nonneg ((G_formula X N + R_formula X N).re)
  have hupper : routeAPSBVisibleMeanErrorAbsSum X ≤ Merr X := herr.bound hX
  linarith

/--
Build the PSB main-contribution packet from a lower bound on `SS_formula` and an upper bound on
the absolute dyadic error carried by `G_formula + R_formula`.
-/
theorem routeAPSBMinorResidualMainContributionLowerBound_of_SS_main_and_errorAbs
    (Mmain Merr : ℕ → ℝ)
    (hmain : RouteAPSBSSMainContributionLowerBound Mmain)
    (herr : RouteAPSBVisibleMeanErrorAbsUpperBound Merr) :
    RouteAPSBMinorResidualMainContributionLowerBound Mmain Merr := by
  refine ⟨?_⟩
  intro X hX
  have hmainX : Mmain X ≤ routeAPSBSSMainContributionSum X := hmain.bound hX
  have htransfer :
      routeAPSBSSMainContributionSum X
        ≤ routeAPSBMinorResidualDyadicMeanSum X + routeAPSBVisibleMeanErrorAbsSum X := by
    exact routeAPSBSSMainContribution_le_minorResidual_plus_errorAbs hX
  have herrX : routeAPSBVisibleMeanErrorAbsSum X ≤ Merr X := herr.bound hX
  linarith

/--
Direct PSB dyadic mean lower bound from the current repo-level main/error model:
`SS_formula` as the positive main term and `G_formula + R_formula` as conservative error.
-/
theorem routeAPSBMinorResidualDyadicMeanLowerBound_of_SS_main_and_errorAbs
    (Mmain Merr : ℕ → ℝ)
    (hmain : RouteAPSBSSMainContributionLowerBound Mmain)
    (herr : RouteAPSBVisibleMeanErrorAbsUpperBound Merr) :
    RouteAPSBMinorResidualDyadicMeanLowerBound (fun X => Mmain X - Merr X) := by
  refine ⟨?_⟩
  intro X hX
  have hmain' :
      RouteAPSBMinorResidualMainContributionLowerBound Mmain Merr :=
    routeAPSBMinorResidualMainContributionLowerBound_of_SS_main_and_errorAbs
      (Mmain := Mmain) (Merr := Merr) hmain herr
  have herr' :
      RouteAPSBMinorResidualMeanErrorUpperBound Merr :=
    routeAPSBMinorResidualMeanErrorUpperBound_of_visibleErrorAbs (Merr := Merr) herr
  have hmainX :
      Mmain X ≤ routeAPSBMinorResidualDyadicMeanSum X + Merr X := hmain'.bound hX
  have herrX : 0 ≤ Merr X := herr'.nonneg hX
  have hmainX' :
      Mmain X ≤
        Finset.sum (EvenIn X H) (fun N =>
          (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
            Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re) + Merr X := by
    simpa [routeAPSBMinorResidualDyadicMeanSum] using hmainX
  change Mmain X - Merr X ≤
    Finset.sum (EvenIn X H) (fun N =>
      (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re)
  linarith

/--
Route-A PSB dyadic mean lower bound with the positive `SS_formula` main term already explicit.

After this theorem, the mean-side arithmetic still needed upstream is exactly the residual-energy
target for `R_formula`; the `G_formula` contribution is handled by its explicit closure theorem.
-/
theorem routeAPSBMinorResidualDyadicMeanLowerBound_of_explicitSSMain_and_residualTarget
    {C2r C3r : ℝ}
    (hR : RouteVisibleResidualTarget C2r C3r) :
    RouteAPSBMinorResidualDyadicMeanLowerBound
      (fun X =>
        routeAPSBSSMainLowerProfile X
          - routeAPSBVisibleMeanErrorProfile
              ((((14 : ℝ) / 13) ^ 4)
                * Q0MinorGFormulaRouteA.gFormulaCoreBudgetConst)
              0 C2r C3r X) := by
  exact routeAPSBMinorResidualDyadicMeanLowerBound_of_SS_main_and_errorAbs
    routeAPSBSSMainLowerProfile
    (routeAPSBVisibleMeanErrorProfile
      ((((14 : ℝ) / 13) ^ 4)
        * Q0MinorGFormulaRouteA.gFormulaCoreBudgetConst)
      0 C2r C3r)
    routeAPSBSSMainContributionLowerBound_explicit
    (routeAPSBVisibleMeanErrorAbsUpperBound_of_explicitG_and_residualTarget hR)

/--
Assemble the raw PSB dyadic mean lower bound from a `main contribution - error` estimate.

This is the intended machine-facing form of the paper's PSB mean argument when the proof naturally
splits into a positive main contribution and a controlled subtractive error.
-/
theorem routeAPSBMinorResidualDyadicMeanLowerBound_of_main_minus_error
    (Mmain Merr : ℕ → ℝ)
    (hmain :
      ∀ {X : ℕ}, X0 ≤ X → Mmain X ≤ routeAPSBMinorResidualDyadicMeanSum X + Merr X)
    (herr_nonneg :
      ∀ {X : ℕ}, X0 ≤ X → 0 ≤ Merr X) :
    RouteAPSBMinorResidualDyadicMeanLowerBound (fun X => Mmain X - Merr X) := by
  refine ⟨?_⟩
  intro X hX
  have hmainX : Mmain X ≤ routeAPSBMinorResidualDyadicMeanSum X + Merr X := hmain hX
  have herrX : 0 ≤ Merr X := herr_nonneg hX
  have hmainX' :
      Mmain X ≤
        Finset.sum (EvenIn X H) (fun N =>
          (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
            Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re) + Merr X := by
    simpa [routeAPSBMinorResidualDyadicMeanSum] using hmainX
  change Mmain X - Merr X ≤
    Finset.sum (EvenIn X H) (fun N =>
      (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re)
  linarith

/--
Assemble the raw PSB dyadic mean lower bound from named main-contribution and error packets.

This is the preferred theorem surface for the PSB source: future arithmetic work should target the
two named input structures rather than rebuilding the raw lower bound directly.
-/
theorem routeAPSBMinorResidualDyadicMeanLowerBound_of_mainContribution_and_error
    (Mmain Merr : ℕ → ℝ)
    (hmain :
      RouteAPSBMinorResidualMainContributionLowerBound Mmain Merr)
    (herr :
      RouteAPSBMinorResidualMeanErrorUpperBound Merr) :
    RouteAPSBMinorResidualDyadicMeanLowerBound (fun X => Mmain X - Merr X) := by
  exact routeAPSBMinorResidualDyadicMeanLowerBound_of_main_minus_error
    (Mmain := Mmain) (Merr := Merr) hmain.bound herr.nonneg

/--
Machine-facing Route-A kernel package abstracting the paper's band-limited majorant `K_H`.

At the current stage we record only the properties needed for the bulk kernel-geometry argument.
Further band-limiting / mass fields can be added later when the Sampling/Bernstein layer is wired
to a concrete kernel model.
-/
structure RouteAKernelData where
  K : ℤ → ℝ
  even : ∀ t : ℤ, K (-t) = K t
  nonneg : ∀ t : ℤ, 0 ≤ K t
  centralWidth : ℕ
  centralValue : ℝ
  centralValue_nonneg : 0 ≤ centralValue
  centralLower : ∀ {t : ℤ}, Int.natAbs t < centralWidth → centralValue ≤ K t

/-- Bulk lower-bound profile extracted from a central-positive Route-A kernel. -/
noncomputable def routeAKernelBulkWeightLower
    (kernel : RouteAKernelData) (C0 X : ℕ) : ℝ :=
  routeAStatisticNormalization X
    * ((((routeADenseGrid X C0).card : ℝ)⁻¹) * kernel.centralValue)

/--
The formal Route-A kernel.

We use the repo's explicit Fejér/tent coefficient kernel, scaled by `H` so its discrete mass is on
the same `\asymp H` scale as the paper's positive low-pass `K_H`.
-/
noncomputable def routeAPaperKernel (t : ℤ) : ℝ :=
  (H : ℝ) * Goldbach.BG_Identity.K_full t

/-- Constant near-origin lower value used by the explicit paper-kernel geometry. -/
noncomputable def routeAPaperKernelExplicitNearOriginValue : ℝ :=
  (H : ℝ) / (2 * (Goldbach.BG_Identity.Ucut : ℝ))

/-- Explicit bulk lower profile induced by the concrete paper-kernel model. -/
noncomputable def routeAPaperKernelExplicitBulkProfile (C0 X : ℕ) : ℝ :=
  routeAStatisticNormalization X
    * ((((routeADenseGrid X C0).card : ℝ)⁻¹) * routeAPaperKernelExplicitNearOriginValue)

/-- Explicit pointwise boundary profile induced by the concrete paper-kernel model. -/
noncomputable def routeAPaperKernelExplicitBoundaryProfile (X : ℕ) : ℝ :=
  routeAStatisticNormalization X * ((H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))

/--
Concrete kernel-data target for the paper kernel.

This is a stronger optional interface: it upgrades the paper kernel all the way to the generic
`RouteAKernelData` package. Route A no longer needs this full pointwise package for the mean
theorem, but it remains available when a stronger explicit kernel model is desirable.
-/
structure RouteAPaperKernelDataTarget where
  data : RouteAKernelData
  kernel_eq : data.K = routeAPaperKernel

/-- Evenness target for the abstract paper kernel. -/
structure RouteAPaperKernelEvenTarget : Prop where
  even : ∀ t : ℤ, routeAPaperKernel (-t) = routeAPaperKernel t

/-- Nonnegativity target for the abstract paper kernel. -/
structure RouteAPaperKernelNonnegTarget : Prop where
  nonneg : ∀ t : ℤ, 0 ≤ routeAPaperKernel t

/--
Optional strong central positivity target for the abstract paper kernel.

This is stronger than the current Route-A mean theorem needs. It is retained only as a route to the
generic `RouteAKernelData` package when one wants a pointwise central profile.
-/
structure RouteAPaperKernelCentralLowerTarget : Type where
  centralWidth : ℕ
  centralValue : ℝ
  centralValue_nonneg : 0 ≤ centralValue
  centralLower : ∀ {t : ℤ}, Int.natAbs t < centralWidth → centralValue ≤ routeAPaperKernel t

def routeAPaperKernelDataTarget_of_components
    (heven : RouteAPaperKernelEvenTarget)
    (hnonneg : RouteAPaperKernelNonnegTarget)
    (hcentral : RouteAPaperKernelCentralLowerTarget) :
    RouteAPaperKernelDataTarget := by
  refine ⟨{
    K := routeAPaperKernel
    even := heven.even
    nonneg := hnonneg.nonneg
    centralWidth := hcentral.centralWidth
    centralValue := hcentral.centralValue
    centralValue_nonneg := hcentral.centralValue_nonneg
    centralLower := hcentral.centralLower
  }, rfl⟩

theorem routeAPaperKernelEvenTarget_explicit :
    RouteAPaperKernelEvenTarget := by
  refine ⟨?_⟩
  intro t
  unfold routeAPaperKernel
  simpa using congrArg (fun x : ℝ => (H : ℝ) * x) (Goldbach.BG_Identity.K_full_neg (k := t))

theorem routeAPaperKernelNonnegTarget_explicit :
    RouteAPaperKernelNonnegTarget := by
  refine ⟨?_⟩
  intro t
  unfold routeAPaperKernel
  exact mul_nonneg (by positivity) (Goldbach.BG_Identity.K_full_nonneg t)

lemma routeADenseGridStep_two_mul_le_Ucut_of_two_le
    {C0 : ℕ} (hC0 : 2 ≤ C0) :
    2 * routeADenseGridStep C0 ≤ Goldbach.BG_Identity.Ucut := by
  unfold routeADenseGridStep
  have hd : max 1 C0 = C0 := by
    omega
  rw [hd]
  have hdiv : (H + C0 - 1) / C0 ≤ 5050 := by
    norm_num [Goldbach.BankParams.H]
    apply Nat.div_le_of_le_mul
    omega
  norm_num [Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H] at hdiv ⊢
  omega

/--
Grid-averaged kernel weight seen by the actual normalized Route-A statistic.

This is the deterministic weight with which the arithmetic mass at `N` contributes to the grid
average of the normalized band-limited statistic.
-/
noncomputable def routeABandLimitedGridKernelAverageWeight
    (K : ℤ → ℝ) (C0 X N : ℕ) : ℝ :=
  routeAStatisticNormalization X
    * routeAGridAverage C0 (fun y => K ((N : ℤ) - (y : ℤ))) X

/-- Weighted arithmetic sum attached to the grid-averaged Route-A kernel. -/
noncomputable def routeABandLimitedGridWeightedVisibleSum
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  Finset.sum (EvenIn X H) (fun N =>
    routeABandLimitedGridKernelAverageWeight K C0 X N * (routeVisibleScalar X N).re)

axiom routeAGridAverageNormalizedStatistic_eq_weighted_sum
    (K : ℤ → ℝ) (C0 X : ℕ) :
    routeAGridAverageNormalizedStatistic K C0 X
      =
    routeABandLimitedGridWeightedVisibleSum K C0 X

lemma routeABandLimitedGridKernelAverageWeight_nonneg
    (kernel : RouteAKernelData) (C0 X N : ℕ) :
    0 ≤ routeABandLimitedGridKernelAverageWeight kernel.K C0 X N := by
  unfold routeABandLimitedGridKernelAverageWeight routeAGridAverage
  have hnorm : 0 ≤ routeAStatisticNormalization X := by
    unfold routeAStatisticNormalization
    positivity
  have havg : 0 ≤
      (((routeADenseGrid X C0).card : ℝ)⁻¹
        * Finset.sum (routeADenseGrid X C0) (fun y => kernel.K ((N : ℤ) - (y : ℤ)))) := by
    have hsum_nonneg :
        0 ≤ Finset.sum (routeADenseGrid X C0) (fun y => kernel.K ((N : ℤ) - (y : ℤ))) := by
      refine Finset.sum_nonneg ?_
      intro y hy
      exact kernel.nonneg ((N : ℤ) - (y : ℤ))
    positivity
  positivity

lemma routeADenseGrid_exists_mem_sub_lt_step
    {X C0 N : ℕ} (hX : X ≤ N) (hN : N ≤ 2 * X) :
    ∃ y ∈ routeADenseGrid X C0, y ≤ N ∧ N - y < routeADenseGridStep C0 := by
  let d := routeADenseGridStep C0
  let k := (N - X) / d
  let y := X + d * k
  have hdpos : 0 < d := by
    unfold d
    exact routeADenseGridStep_pos C0
  have hy_mem : y ∈ routeADenseGrid X C0 := by
    rw [mem_routeADenseGrid_iff]
    constructor
    · refine Finset.mem_Icc.mpr ?_
      constructor
      · exact Nat.le_add_right _ _
      · calc
          y ≤ X + (N - X) := by
            have hdecomp : d * k + (N - X) % d = N - X := by
              unfold k d
              exact Nat.div_add_mod (N - X) (routeADenseGridStep C0)
            unfold y
            omega
          _ = N := Nat.add_sub_of_le hX
          _ ≤ 2 * X := hN
    · unfold y
      rw [Nat.add_sub_cancel_left]
      exact Nat.mul_mod_right _ _
  refine ⟨y, hy_mem, ?_, ?_⟩
  · calc
      y ≤ X + (N - X) := by
        have hdecomp : d * k + (N - X) % d = N - X := by
          unfold k d
          exact Nat.div_add_mod (N - X) (routeADenseGridStep C0)
        unfold y
        omega
      _ = N := Nat.add_sub_of_le hX
  · have hmodlt : (N - X) % d < d := Nat.mod_lt _ hdpos
    have hdecomp : N - y = (N - X) % d := by
      unfold y k d
      have hdiv : routeADenseGridStep C0 * ((N - X) / routeADenseGridStep C0)
          + (N - X) % routeADenseGridStep C0 = N - X := by
        exact Nat.div_add_mod (N - X) (routeADenseGridStep C0)
      omega
    rw [hdecomp]
    exact hmodlt

/--
Bulk window on which the grid-averaged kernel weight is expected to be uniformly positive.

This is a deterministic Route-A geometry object; the exact bulk choice can be sharpened later.
-/
def routeABandLimitedGridKernelBulk (X C0 : ℕ) : Finset ℕ :=
  Finset.Icc (X + routeADenseGridStep C0) (2 * X - routeADenseGridStep C0)

/--
Deterministic bulk lower bound target for the grid-averaged Route-A kernel weight.

This is the geometry input that should eventually combine with the PSB mean to produce the Route-A
main-term positivity.
-/
structure RouteABandLimitedGridKernelAverageWeightBulkLowerBound
    (K : ℤ → ℝ) (C0 : ℕ) (cK : ℕ → ℝ) : Prop where
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ routeABandLimitedGridKernelBulk X C0 →
      cK X ≤ routeABandLimitedGridKernelAverageWeight K C0 X N

theorem routeABandLimitedGridKernelAverageWeightBulkLowerBound_of_kernelData
    (kernel : RouteAKernelData) (C0 : ℕ)
    (hstep : routeADenseGridStep C0 ≤ kernel.centralWidth) :
    RouteABandLimitedGridKernelAverageWeightBulkLowerBound
      kernel.K C0 (routeAKernelBulkWeightLower kernel C0) := by
  refine ⟨?_⟩
  intro X N hX hN
  rcases Finset.mem_Icc.mp hN with ⟨hNX, hN2X⟩
  have hXleN : X ≤ N := le_trans (Nat.le_add_right X (routeADenseGridStep C0)) hNX
  have hNwin : N ≤ 2 * X := le_trans hN2X (Nat.sub_le _ _)
  rcases routeADenseGrid_exists_mem_sub_lt_step (X := X) (C0 := C0) hXleN hNwin with
    ⟨y, hy, hyN, hdist⟩
  have hpoint :
      kernel.centralValue ≤ kernel.K ((N : ℤ) - (y : ℤ)) := by
    apply kernel.centralLower
    have hsub :
        Int.natAbs ((N : ℤ) - (y : ℤ)) = N - y := by
      calc
        Int.natAbs ((N : ℤ) - (y : ℤ))
            = Int.natAbs (((N - y : ℕ) : ℤ)) := by
                rw [Int.ofNat_sub hyN]
        _ = N - y := by
            simp
    rw [hsub]
    exact lt_of_lt_of_le hdist hstep
  have hsum_ge :
      kernel.centralValue
        ≤
      Finset.sum (routeADenseGrid X C0) (fun z => kernel.K ((N : ℤ) - (z : ℤ))) := by
    calc
      kernel.centralValue ≤ kernel.K ((N : ℤ) - (y : ℤ)) := hpoint
      _ ≤ Finset.sum (routeADenseGrid X C0) (fun z => kernel.K ((N : ℤ) - (z : ℤ))) := by
          exact Finset.single_le_sum
            (by
              intro z hz
              exact kernel.nonneg ((N : ℤ) - (z : ℤ)))
            hy
  have havg_ge :
      (((routeADenseGrid X C0).card : ℝ)⁻¹ * kernel.centralValue)
        ≤
      routeAGridAverage C0 (fun z => kernel.K ((N : ℤ) - (z : ℤ))) X := by
    unfold routeAGridAverage
    have hcard_nonneg : 0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹) := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hsum_ge hcard_nonneg
    simpa [mul_assoc] using hscaled
  have hnorm_nonneg : 0 ≤ routeAStatisticNormalization X := by
    unfold routeAStatisticNormalization
    positivity
  have hscaled := mul_le_mul_of_nonneg_left havg_ge hnorm_nonneg
  simpa [routeAKernelBulkWeightLower, routeABandLimitedGridKernelAverageWeight] using hscaled

/--
Deterministic boundary leakage upper bound target for the grid-averaged Route-A kernel weight.

This isolates the off-bulk contribution that must be paired with the arithmetic mean theorem.
-/
structure RouteABandLimitedGridKernelAverageWeightBoundaryUpperBound
    (K : ℤ → ℝ) (C0 : ℕ) (B : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      Finset.sum ((EvenIn X H).filter (fun N => N ∉ routeABandLimitedGridKernelBulk X C0)) (fun N =>
        |routeABandLimitedGridKernelAverageWeight K C0 X N| * |(routeVisibleScalar X N).re|)
        ≤ B X

/--
Pointwise boundary upper bound for the grid-averaged Route-A kernel weight.

This is the deterministic kernel side of the boundary leakage estimate; the arithmetic side is a
boundary absolute-mass bound for the route-visible scalar.
-/
structure RouteABandLimitedGridKernelAverageWeightBoundaryPointwiseUpperBound
    (K : ℤ → ℝ) (C0 : ℕ) (wB : ℕ → ℝ) : Prop where
  nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ wB X
  bound :
    ∀ {X N : ℕ}, X0 ≤ X →
      N ∈ ((EvenIn X H).filter (fun n => n ∉ routeABandLimitedGridKernelBulk X C0)) →
        |routeABandLimitedGridKernelAverageWeight K C0 X N| ≤ wB X

/--
Arithmetic boundary absolute-mass input for the route-visible scalar.

This is the minimal arithmetic datum needed to turn a pointwise kernel boundary bound into a
boundary leakage bound for the weighted visible sum.
-/
structure RouteABandLimitedBoundaryVisibleAbsMassUpperBound
    (C0 : ℕ) (MB : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      Finset.sum ((EvenIn X H).filter (fun N => N ∉ routeABandLimitedGridKernelBulk X C0)) (fun N =>
        |(routeVisibleScalar X N).re|)
        ≤ MB X

theorem routeABandLimitedGridKernelAverageWeightBoundaryUpperBound_of_pointwise_and_visibleMass
    (K : ℤ → ℝ) (C0 : ℕ) (wB MB : ℕ → ℝ)
    (hkernel :
      RouteABandLimitedGridKernelAverageWeightBoundaryPointwiseUpperBound K C0 wB)
    (hvisible :
      RouteABandLimitedBoundaryVisibleAbsMassUpperBound C0 MB) :
    RouteABandLimitedGridKernelAverageWeightBoundaryUpperBound K C0
      (fun X => wB X * MB X) := by
  refine ⟨?_⟩
  intro X hX
  let boundary : Finset ℕ := (EvenIn X H).filter (fun N => N ∉ routeABandLimitedGridKernelBulk X C0)
  calc
    Finset.sum boundary (fun N =>
      |routeABandLimitedGridKernelAverageWeight K C0 X N| * |(routeVisibleScalar X N).re|)
        ≤
    Finset.sum boundary (fun N => wB X * |(routeVisibleScalar X N).re|) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact mul_le_mul_of_nonneg_right (hkernel.bound hX hN) (abs_nonneg _)
    _ = wB X * Finset.sum boundary (fun N => |(routeVisibleScalar X N).re|) := by
          rw [Finset.mul_sum]
    _ ≤ wB X * MB X := by
          exact mul_le_mul_of_nonneg_left (by simpa [boundary] using hvisible.bound hX)
            (hkernel.nonneg hX)

/--
Arithmetic bulk lower bound for the route-visible scalar on the Route-A bulk window.

This is the PSB-facing input before the deterministic kernel weight is applied.
-/
structure RouteABandLimitedBulkVisibleMassLowerBound
    (C0 : ℕ) (M : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      M X ≤
        Finset.sum ((EvenIn X H).filter (fun N => N ∈ routeABandLimitedGridKernelBulk X C0)) (fun N =>
          (routeVisibleScalar X N).re)

/--
Pointwise nonnegativity of the route-visible scalar on the Route-A bulk window.

This is the sign input needed to convert a bulk scalar-mass lower bound into a weighted bulk lower
bound using the positive kernel geometry.
-/
structure RouteABandLimitedBulkVisibleNonneg
    (C0 : ℕ) : Prop where
  bound :
    ∀ {X N : ℕ}, X0 ≤ X →
      N ∈ ((EvenIn X H).filter (fun n => n ∈ routeABandLimitedGridKernelBulk X C0)) →
        0 ≤ (routeVisibleScalar X N).re

/--
PSB-style bulk visible-mass lower bound specialized to the actual paper Route-A kernel geometry.
-/
abbrev RouteAPaperKernelBulkVisibleMassLowerBound
    (C0 : ℕ) (M : ℕ → ℝ) : Prop :=
  RouteABandLimitedBulkVisibleMassLowerBound C0 M

/--
Bulk sign control specialized to the actual paper Route-A kernel geometry.
-/
abbrev RouteAPaperKernelBulkVisibleNonneg
    (C0 : ℕ) : Prop :=
  RouteABandLimitedBulkVisibleNonneg C0

/--
Boundary absolute visible-mass control specialized to the actual paper Route-A kernel geometry.
-/
abbrev RouteAPaperKernelBoundaryVisibleAbsMassUpperBound
    (C0 : ℕ) (MB : ℕ → ℝ) : Prop :=
  RouteABandLimitedBoundaryVisibleAbsMassUpperBound C0 MB

theorem routeABandLimitedBulkVisibleMassLowerBound_of_total_and_boundary
    (C0 : ℕ) (Mtot MB : ℕ → ℝ)
    (htotal : RouteAVisibleDyadicMeanLowerBound Mtot)
    (hboundary : RouteABandLimitedBoundaryVisibleAbsMassUpperBound C0 MB) :
    RouteABandLimitedBulkVisibleMassLowerBound C0 (fun X => Mtot X - MB X) := by
  refine ⟨?_⟩
  intro X hX
  let bulk : Finset ℕ := (EvenIn X H).filter (fun N => N ∈ routeABandLimitedGridKernelBulk X C0)
  let boundary : Finset ℕ := (EvenIn X H).filter (fun N => N ∉ routeABandLimitedGridKernelBulk X C0)
  let visibleRe : ℕ → ℝ := fun N => (routeVisibleScalar X N).re
  have hsplit :
      Finset.sum (EvenIn X H) visibleRe
        = Finset.sum bulk visibleRe + Finset.sum boundary visibleRe := by
    unfold bulk boundary visibleRe
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := EvenIn X H)
        (p := fun N => N ∈ routeABandLimitedGridKernelBulk X C0)
        (f := fun N => (routeVisibleScalar X N).re)).symm
  have hboundary_upper :
      Finset.sum boundary visibleRe ≤ MB X := by
    have hreal_le_abs :
        Finset.sum boundary visibleRe
          ≤
        Finset.sum boundary (fun N => |visibleRe N|) := by
      refine Finset.sum_le_sum ?_
      intro N hN
      exact le_abs_self (visibleRe N)
    have habs_bound :
        Finset.sum boundary (fun N => |visibleRe N|) ≤ MB X := by
      simpa [boundary, visibleRe] using hboundary.bound hX
    exact hreal_le_abs.trans habs_bound
  have htotalX : Mtot X ≤ Finset.sum (EvenIn X H) visibleRe := by
    simpa [visibleRe] using htotal.bound hX
  rw [hsplit] at htotalX
  have hbulk :
      Mtot X - MB X ≤ Finset.sum bulk visibleRe := by
    linarith
  simpa [bulk, visibleRe]
    using hbulk

theorem routeAPaperKernelBulkVisibleMassLowerBound_of_total_and_boundary
    (C0 : ℕ) (Mtot MB : ℕ → ℝ)
    (htotal : RouteAVisibleDyadicMeanLowerBound Mtot)
    (hboundary : RouteAPaperKernelBoundaryVisibleAbsMassUpperBound C0 MB) :
    RouteAPaperKernelBulkVisibleMassLowerBound C0 (fun X => Mtot X - MB X) := by
  exact routeABandLimitedBulkVisibleMassLowerBound_of_total_and_boundary
    (C0 := C0) (Mtot := Mtot) (MB := MB) htotal hboundary

/-- Pointwise boundary kernel control specialized to the actual paper Route-A kernel. -/
abbrev RouteAPaperKernelBoundaryPointwiseUpperBound
    (C0 : ℕ) (wB : ℕ → ℝ) : Prop :=
  RouteABandLimitedGridKernelAverageWeightBoundaryPointwiseUpperBound routeAPaperKernel C0 wB

/--
Near-origin lower bound for the sampled paper kernel.

This is weaker and more natural than a full pointwise central profile on all integers: it only asks
for a positive lower bound on the offsets `0 ≤ t < routeADenseGridStep C0` that arise from the
nearest-gridpoint argument in the bulk geometry theorem.
-/
structure RouteAPaperKernelNearOriginLowerBound
    (C0 : ℕ) (k0 : ℕ → ℝ) : Prop where
  nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ k0 X
  bound :
    ∀ {X t : ℕ}, X0 ≤ X → t < routeADenseGridStep C0 →
      k0 X ≤ routeAPaperKernel t

/-- Bulk lower profile induced by a near-origin lower bound for the paper kernel. -/
noncomputable def routeAPaperKernelGridAverageBulkLowerProfile
    (C0 : ℕ) (k0 : ℕ → ℝ) (X : ℕ) : ℝ :=
  routeAStatisticNormalization X
    * ((((routeADenseGrid X C0).card : ℝ)⁻¹) * k0 X)

/--
Direct bulk lower bound for the grid-averaged paper-kernel weight.

This is the actual deterministic positivity input consumed by the Route-A mean theorem.
-/
abbrev RouteAPaperKernelGridAverageBulkLowerBound
    (C0 : ℕ) (cK : ℕ → ℝ) : Prop :=
  RouteABandLimitedGridKernelAverageWeightBulkLowerBound routeAPaperKernel C0 cK

theorem routeAPaperKernelGridAverageBulkLowerBound_of_nearOrigin
    (C0 : ℕ) (k0 : ℕ → ℝ)
    (hnonneg : RouteAPaperKernelNonnegTarget)
    (hnear : RouteAPaperKernelNearOriginLowerBound C0 k0) :
    RouteAPaperKernelGridAverageBulkLowerBound C0
      (routeAPaperKernelGridAverageBulkLowerProfile C0 k0) := by
  refine ⟨?_⟩
  intro X N hX hN
  rcases Finset.mem_Icc.mp hN with ⟨hNX, hN2X⟩
  have hXleN : X ≤ N := le_trans (Nat.le_add_right X (routeADenseGridStep C0)) hNX
  have hNwin : N ≤ 2 * X := le_trans hN2X (Nat.sub_le _ _)
  rcases routeADenseGrid_exists_mem_sub_lt_step (X := X) (C0 := C0) hXleN hNwin with
    ⟨y, hy, hyN, hdist⟩
  have hpoint :
      k0 X ≤ routeAPaperKernel ((N - y : ℕ) : ℤ) := by
    simpa using hnear.bound hX hdist
  have hsum_ge :
      k0 X
        ≤
      Finset.sum (routeADenseGrid X C0) (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ))) := by
    calc
      k0 X ≤ routeAPaperKernel ((N - y : ℕ) : ℤ) := hpoint
      _ = routeAPaperKernel ((N : ℤ) - (y : ℤ)) := by
          rw [Int.ofNat_sub hyN]
      _ ≤ Finset.sum (routeADenseGrid X C0) (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ))) := by
          exact Finset.single_le_sum
            (by
              intro z hz
              exact hnonneg.nonneg ((N : ℤ) - (z : ℤ)))
            hy
  have havg_ge :
      (((routeADenseGrid X C0).card : ℝ)⁻¹ * k0 X)
        ≤
      routeAGridAverage C0 (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ))) X := by
    unfold routeAGridAverage
    have hcard_nonneg : 0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hsum_ge hcard_nonneg
    simpa [mul_assoc] using hscaled
  have hnorm_nonneg : 0 ≤ routeAStatisticNormalization X := by
    unfold routeAStatisticNormalization
    positivity
  have hscaled := mul_le_mul_of_nonneg_left havg_ge hnorm_nonneg
  simpa [routeAPaperKernelGridAverageBulkLowerProfile, routeABandLimitedGridKernelAverageWeight] using hscaled

/--
Deterministic Route-A paper-kernel geometry packet.

This records exactly the kernel-side inputs needed before any PSB arithmetic is used:
1. the grid-averaged paper-kernel weight is uniformly positive on the bulk,
2. the boundary part of the grid-averaged kernel weight has a pointwise upper bound.
-/
structure RouteAPaperKernelGeometryTarget
    (C0 : ℕ) (cK wB : ℕ → ℝ) where
  bulkLower : RouteAPaperKernelGridAverageBulkLowerBound C0 cK
  boundaryPointwise : RouteAPaperKernelBoundaryPointwiseUpperBound C0 wB

theorem routeAPaperKernelGeometryTarget_of_nearOrigin_and_boundary
    (C0 : ℕ) (k0 wB : ℕ → ℝ)
    (hnonneg : RouteAPaperKernelNonnegTarget)
    (hnear : RouteAPaperKernelNearOriginLowerBound C0 k0)
    (hboundary : RouteAPaperKernelBoundaryPointwiseUpperBound C0 wB) :
    RouteAPaperKernelGeometryTarget C0
      (routeAPaperKernelGridAverageBulkLowerProfile C0 k0) wB := by
  refine ⟨?_, hboundary⟩
  exact routeAPaperKernelGridAverageBulkLowerBound_of_nearOrigin
    (C0 := C0) (k0 := k0) hnonneg hnear

theorem routeAPaperKernelNearOriginLowerBound_explicit
    (C0 : ℕ)
    (hstep : 2 * routeADenseGridStep C0 ≤ Goldbach.BG_Identity.Ucut) :
    RouteAPaperKernelNearOriginLowerBound C0
      (fun _ => (H : ℝ) / (2 * (Goldbach.BG_Identity.Ucut : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    positivity
  · intro X t hX ht
    have hUpos : 0 < (Goldbach.BG_Identity.Ucut : ℝ) := Goldbach.BG_Identity.Ucut_pos_real
    have htwo_t : 2 * t ≤ Goldbach.BG_Identity.Ucut := by
      omega
    have htU : t ≤ Goldbach.BG_Identity.Ucut := by
      omega
    have hK := Goldbach.BG_Identity.K_full_ofNat_le (m := t) htU
    have hk_eq :
        routeAPaperKernel t
          = (H : ℝ) * (((1 : ℝ) - (t : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
              / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      unfold routeAPaperKernel
      simpa using congrArg (fun x : ℝ => (H : ℝ) * x) hK
    have ht_half : (t : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) ≤ (1 : ℝ) / 2 := by
      have h2tR : (2 * t : ℝ) ≤ (Goldbach.BG_Identity.Ucut : ℝ) := by
        exact_mod_cast htwo_t
      exact (div_le_iff₀ hUpos).2 (by nlinarith)
    have hfactor :
        ((1 : ℝ) / 2) / (Goldbach.BG_Identity.Ucut : ℝ)
          ≤
        ((1 : ℝ) - (t : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
          / (Goldbach.BG_Identity.Ucut : ℝ) := by
      have hhalf : (1 : ℝ) / 2 ≤ 1 - (t : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
        nlinarith
      have hinv_nonneg : 0 ≤ ((Goldbach.BG_Identity.Ucut : ℝ)⁻¹) := by
        exact inv_nonneg.mpr (le_of_lt hUpos)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hhalf hinv_nonneg)
    have hscaled :
        (H : ℝ) * (((1 : ℝ) / 2) / (Goldbach.BG_Identity.Ucut : ℝ))
          ≤
        (H : ℝ) * (((1 : ℝ) - (t : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
          / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ (H : ℝ))
    calc
      (H : ℝ) / (2 * (Goldbach.BG_Identity.Ucut : ℝ))
          = (H : ℝ) * (((1 : ℝ) / 2) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
              field_simp [Goldbach.BG_Identity.Ucut_ne_zero_real]
      _ ≤ (H : ℝ) * (((1 : ℝ) - (t : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
            / (Goldbach.BG_Identity.Ucut : ℝ)) := hscaled
      _ = routeAPaperKernel t := by rw [hk_eq]

theorem routeAPaperKernelBoundaryPointwiseUpperBound_explicit
    (C0 : ℕ) :
    RouteAPaperKernelBoundaryPointwiseUpperBound C0
      (fun X => routeAStatisticNormalization X * ((H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact mul_nonneg
      (by
        unfold routeAStatisticNormalization
        positivity)
      (div_nonneg (by positivity : 0 ≤ (H : ℝ)) (by positivity : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ)))
  · intro X N hX hN
    have hterm_le :
        ∀ z : ℕ,
          routeAPaperKernel ((N : ℤ) - (z : ℤ)) ≤ (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
      intro z
      have hnonnegK : 0 ≤ Goldbach.BG_Identity.K_full ((N : ℤ) - (z : ℤ)) :=
        Goldbach.BG_Identity.K_full_nonneg _
      have hpeak :
          Goldbach.BG_Identity.K_full ((N : ℤ) - (z : ℤ))
            ≤
          (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
        have hpeakAbs :=
          Goldbach.BG_Identity.K_full_peak_le
            (U := Goldbach.BG_Identity.Ucut) (k := (N : ℤ) - (z : ℤ))
        have hnonnegRaw :
            0 ≤ Goldbach.BG_Identity.K_full_raw Goldbach.BG_Identity.Ucut ((N : ℤ) - (z : ℤ)) := by
          simpa [Goldbach.BG_Identity.K_full] using hnonnegK
        have hpeakRaw :
            Goldbach.BG_Identity.K_full_raw Goldbach.BG_Identity.Ucut ((N : ℤ) - (z : ℤ))
              ≤
            (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
          rw [abs_of_nonneg hnonnegRaw] at hpeakAbs
          exact hpeakAbs
        simpa [Goldbach.BG_Identity.K_full] using hpeakRaw
      unfold routeAPaperKernel
      simpa [one_div] using
        (mul_le_mul_of_nonneg_left hpeak (by positivity : 0 ≤ (H : ℝ)))
    have havg_le :
        routeAGridAverage C0 (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ))) X
          ≤
        (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
      unfold routeAGridAverage
      have hcard_nonneg : 0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹) := by positivity
      have hsum_le :
          Finset.sum (routeADenseGrid X C0) (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ)))
            ≤
          Finset.sum (routeADenseGrid X C0) (fun _ => (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        exact hterm_le z
      have hscaled := mul_le_mul_of_nonneg_left hsum_le hcard_nonneg
      have hconst :
          (((routeADenseGrid X C0).card : ℝ)⁻¹)
              * Finset.sum (routeADenseGrid X C0) (fun _ => (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
            =
          (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
        have hcard_pos : 0 < ((routeADenseGrid X C0).card : ℝ) := by
          exact_mod_cast routeADenseGrid_card_pos X C0
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp [hcard_pos.ne']
      calc
        (((routeADenseGrid X C0).card : ℝ)⁻¹)
            * Finset.sum (routeADenseGrid X C0) (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ)))
          ≤
        (((routeADenseGrid X C0).card : ℝ)⁻¹)
            * Finset.sum (routeADenseGrid X C0) (fun _ => (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := hscaled
        _ = (H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := hconst
    have hweight_nonneg :
        0 ≤ routeABandLimitedGridKernelAverageWeight routeAPaperKernel C0 X N := by
      unfold routeABandLimitedGridKernelAverageWeight routeAGridAverage
      have hnorm : 0 ≤ routeAStatisticNormalization X := by
        unfold routeAStatisticNormalization
        positivity
      have hsum_nonneg :
          0 ≤ Finset.sum (routeADenseGrid X C0) (fun z => routeAPaperKernel ((N : ℤ) - (z : ℤ))) := by
        refine Finset.sum_nonneg ?_
        intro z hz
        exact routeAPaperKernelNonnegTarget_explicit.nonneg ((N : ℤ) - (z : ℤ))
      positivity
    have hnorm_nonneg : 0 ≤ routeAStatisticNormalization X := by
      unfold routeAStatisticNormalization
      positivity
    have hscaled :=
      mul_le_mul_of_nonneg_left havg_le hnorm_nonneg
    have hraw :
        routeABandLimitedGridKernelAverageWeight routeAPaperKernel C0 X N
          ≤
        routeAStatisticNormalization X * ((H : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      simpa [routeABandLimitedGridKernelAverageWeight] using hscaled
    simpa [abs_of_nonneg hweight_nonneg] using hraw

theorem routeAPaperKernelGeometryTarget_explicit
    (C0 : ℕ)
    (hstep : 2 * routeADenseGridStep C0 ≤ Goldbach.BG_Identity.Ucut) :
    RouteAPaperKernelGeometryTarget C0
      (routeAPaperKernelExplicitBulkProfile C0)
      routeAPaperKernelExplicitBoundaryProfile := by
  exact routeAPaperKernelGeometryTarget_of_nearOrigin_and_boundary
    (C0 := C0)
    (k0 := fun _ => routeAPaperKernelExplicitNearOriginValue)
    (wB := routeAPaperKernelExplicitBoundaryProfile)
    routeAPaperKernelNonnegTarget_explicit
    (routeAPaperKernelNearOriginLowerBound_explicit (C0 := C0) hstep)
    (routeAPaperKernelBoundaryPointwiseUpperBound_explicit (C0 := C0))

theorem routeAPaperKernelGeometryTarget_explicit_of_two_le
    (C0 : ℕ) (hC0 : 2 ≤ C0) :
    RouteAPaperKernelGeometryTarget C0
      (routeAPaperKernelExplicitBulkProfile C0)
      routeAPaperKernelExplicitBoundaryProfile := by
  exact routeAPaperKernelGeometryTarget_explicit
    (C0 := C0) (routeADenseGridStep_two_mul_le_Ucut_of_two_le hC0)

lemma routeAPaperKernelExplicitBulkProfile_nonneg
    (C0 : ℕ) {X : ℕ} (_hX : X0 ≤ X) :
    0 ≤ routeAPaperKernelExplicitBulkProfile C0 X := by
  unfold routeAPaperKernelExplicitBulkProfile routeAPaperKernelExplicitNearOriginValue
  have hnorm : 0 ≤ routeAStatisticNormalization X := by
    unfold routeAStatisticNormalization
    positivity
  have hcard : 0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹) := by
    positivity
  have hinner :
      0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹)
        * ((H : ℝ) / (2 * (Goldbach.BG_Identity.Ucut : ℝ))) := by
    apply mul_nonneg hcard
    positivity
  exact mul_nonneg hnorm hinner

/-- Route-A dense-good threshold extracted from a positive mean lower bound. -/
def routeABandLimitedDenseGoodThreshold (μ : ℕ → ℝ) : ℕ → ℝ :=
  fun X => μ X / 2

/--
Route-A dense-good density loss extracted from mean and variance.

This is the finite-grid Chebyshev loss `4 V / (μ² * #grid)`.
-/
def routeABandLimitedDenseGoodDensityLoss
    (C0 : ℕ) (μ V : ℕ → ℝ) : ℕ → ℝ :=
  fun X => (4 * V X) / ((μ X) ^ 2 * (((routeADenseGrid X C0).card : ℝ)))

theorem routeABandLimitedGridMeanLowerBound_of_PSBMean_and_kernelWeight
    (K : ℤ → ℝ) (C0 : ℕ) (cK M B : ℕ → ℝ)
    (hweighted : ∀ X, routeAGridAverageNormalizedStatistic K C0 X
      = routeABandLimitedGridWeightedVisibleSum K C0 X)
    (hcK_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ cK X)
    (hkernel :
      RouteABandLimitedGridKernelAverageWeightBulkLowerBound K C0 cK)
    (hboundary :
      RouteABandLimitedGridKernelAverageWeightBoundaryUpperBound K C0 B)
    (hbulkMass :
      RouteABandLimitedBulkVisibleMassLowerBound C0 M)
    (hbulkNonneg :
      RouteABandLimitedBulkVisibleNonneg C0) :
    RouteABandLimitedGridMeanLowerBound K C0 (fun X => cK X * M X - B X) := by
  refine ⟨?_⟩
  intro X hX
  let bulk : Finset ℕ := (EvenIn X H).filter (fun N => N ∈ routeABandLimitedGridKernelBulk X C0)
  let boundary : Finset ℕ := (EvenIn X H).filter (fun N => N ∉ routeABandLimitedGridKernelBulk X C0)
  let weightedTerm : ℕ → ℝ := fun N =>
    routeABandLimitedGridKernelAverageWeight K C0 X N * (routeVisibleScalar X N).re
  have hsplit :
      routeABandLimitedGridWeightedVisibleSum K C0 X
        =
      Finset.sum bulk weightedTerm + Finset.sum boundary weightedTerm := by
    unfold routeABandLimitedGridWeightedVisibleSum bulk boundary weightedTerm
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := EvenIn X H)
        (p := fun N => N ∈ routeABandLimitedGridKernelBulk X C0)
        (f := fun N =>
          routeABandLimitedGridKernelAverageWeight K C0 X N * (routeVisibleScalar X N).re)).symm
  have hbulk_weighted_ge :
      cK X * Finset.sum bulk (fun N => (routeVisibleScalar X N).re)
        ≤
      Finset.sum bulk weightedTerm := by
    calc
      cK X * Finset.sum bulk (fun N => (routeVisibleScalar X N).re)
          = Finset.sum bulk (fun N => cK X * (routeVisibleScalar X N).re) := by
              rw [Finset.mul_sum]
      _ ≤ Finset.sum bulk weightedTerm := by
          refine Finset.sum_le_sum ?_
          intro N hN
          have hweight : cK X ≤ routeABandLimitedGridKernelAverageWeight K C0 X N := by
            exact hkernel.bound hX (Finset.mem_filter.mp hN).2
          have hnonneg : 0 ≤ (routeVisibleScalar X N).re := by
            exact hbulkNonneg.bound hX hN
          exact mul_le_mul_of_nonneg_right hweight hnonneg
  have hbulk_main_ge :
      cK X * M X ≤ Finset.sum bulk weightedTerm := by
    have hmass : M X ≤ Finset.sum bulk (fun N => (routeVisibleScalar X N).re) := by
      simpa [bulk] using hbulkMass.bound hX
    have hscaled : cK X * M X ≤ cK X * Finset.sum bulk (fun N => (routeVisibleScalar X N).re) := by
      exact mul_le_mul_of_nonneg_left hmass (hcK_nonneg hX)
    exact hscaled.trans hbulk_weighted_ge
  have hboundary_lower :
      - B X ≤ Finset.sum boundary weightedTerm := by
    have habs_bound :
        Finset.sum boundary (fun N =>
          |routeABandLimitedGridKernelAverageWeight K C0 X N| * |(routeVisibleScalar X N).re|)
          ≤ B X := by
      simpa [boundary] using hboundary.bound hX
    have hneg_abs :
        - Finset.sum boundary (fun N =>
          |routeABandLimitedGridKernelAverageWeight K C0 X N| * |(routeVisibleScalar X N).re|)
          ≤
        Finset.sum boundary weightedTerm := by
      calc
        - Finset.sum boundary (fun N =>
            |routeABandLimitedGridKernelAverageWeight K C0 X N| * |(routeVisibleScalar X N).re|)
            =
          Finset.sum boundary (fun N =>
            - (|routeABandLimitedGridKernelAverageWeight K C0 X N|
                * |(routeVisibleScalar X N).re|)) := by
                  rw [Finset.sum_neg_distrib]
        _ ≤ Finset.sum boundary weightedTerm := by
            refine Finset.sum_le_sum ?_
            intro N hN
            simpa [weightedTerm, abs_mul] using
              (neg_abs_le
                (routeABandLimitedGridKernelAverageWeight K C0 X N * (routeVisibleScalar X N).re))
    linarith
  have hmain :
      cK X * M X - B X ≤ routeABandLimitedGridWeightedVisibleSum K C0 X := by
    rw [hsplit]
    linarith
  change cK X * M X - B X ≤ routeAGridAverageNormalizedStatistic K C0 X
  rw [hweighted X]
  exact hmain

lemma routeAKernelBulkWeightLower_nonneg
    (kernel : RouteAKernelData) (C0 : ℕ) {X : ℕ} (_hX : X0 ≤ X) :
    0 ≤ routeAKernelBulkWeightLower kernel C0 X := by
  unfold routeAKernelBulkWeightLower
  have hnorm : 0 ≤ routeAStatisticNormalization X := by
    unfold routeAStatisticNormalization
    positivity
  have hcard : 0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹) := by
    positivity
  have hinner : 0 ≤ (((routeADenseGrid X C0).card : ℝ)⁻¹ * kernel.centralValue) := by
    exact mul_nonneg hcard kernel.centralValue_nonneg
  nlinarith

theorem routeABandLimitedGridMeanLowerBound_of_PSBMean_and_kernelData
    (kernel : RouteAKernelData) (C0 : ℕ) (M B : ℕ → ℝ)
    (hstep : routeADenseGridStep C0 ≤ kernel.centralWidth)
    (hweighted : ∀ X, routeAGridAverageNormalizedStatistic kernel.K C0 X
      = routeABandLimitedGridWeightedVisibleSum kernel.K C0 X)
    (hboundary :
      RouteABandLimitedGridKernelAverageWeightBoundaryUpperBound kernel.K C0 B)
    (hbulkMass :
      RouteABandLimitedBulkVisibleMassLowerBound C0 M)
    (hbulkNonneg :
      RouteABandLimitedBulkVisibleNonneg C0) :
    RouteABandLimitedGridMeanLowerBound kernel.K C0
      (fun X => routeAKernelBulkWeightLower kernel C0 X * M X - B X) := by
  apply routeABandLimitedGridMeanLowerBound_of_PSBMean_and_kernelWeight
    (K := kernel.K) (C0 := C0) (cK := routeAKernelBulkWeightLower kernel C0)
    (M := M) (B := B)
  · exact hweighted
  · exact routeAKernelBulkWeightLower_nonneg kernel C0
  · exact routeABandLimitedGridKernelAverageWeightBulkLowerBound_of_kernelData kernel C0 hstep
  · exact hboundary
  · exact hbulkMass
  · exact hbulkNonneg

/--
Paper-kernel Route-A mean theorem.

Once the explicit paper kernel has been upgraded to `RouteAKernelData`, and the PSB-style bulk
visible-mass / boundary inputs are available, the actual Route-A grid mean follows immediately.
-/
theorem routeABandLimitedGridMeanLowerBound_of_paperKernel_and_PSB
    (C0 : ℕ) (cK Mbulk wB Mboundary : ℕ → ℝ)
    (hweighted :
      ∀ X, routeAGridAverageNormalizedStatistic routeAPaperKernel C0 X
        = routeABandLimitedGridWeightedVisibleSum routeAPaperKernel C0 X)
    (hcK_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ cK X)
    (hbulkKernel :
      RouteAPaperKernelGridAverageBulkLowerBound C0 cK)
    (hboundaryKernel :
      RouteAPaperKernelBoundaryPointwiseUpperBound C0 wB)
    (hboundaryMass :
      RouteAPaperKernelBoundaryVisibleAbsMassUpperBound C0 Mboundary)
    (hbulkMass :
      RouteAPaperKernelBulkVisibleMassLowerBound C0 Mbulk)
    (hbulkNonneg :
      RouteAPaperKernelBulkVisibleNonneg C0) :
    RouteABandLimitedGridMeanLowerBound routeAPaperKernel C0
      (fun X => cK X * Mbulk X - wB X * Mboundary X) := by
  have hboundary :
      RouteABandLimitedGridKernelAverageWeightBoundaryUpperBound routeAPaperKernel C0
        (fun X => wB X * Mboundary X) := by
    exact routeABandLimitedGridKernelAverageWeightBoundaryUpperBound_of_pointwise_and_visibleMass
      (K := routeAPaperKernel) (C0 := C0) (wB := wB) (MB := Mboundary)
      hboundaryKernel hboundaryMass
  exact routeABandLimitedGridMeanLowerBound_of_PSBMean_and_kernelWeight
    (K := routeAPaperKernel) (C0 := C0) (cK := cK) (M := Mbulk) (B := fun X => wB X * Mboundary X)
    hweighted hcK_nonneg hbulkKernel hboundary hbulkMass hbulkNonneg

theorem routeAPaperKernelBoundaryUpperBound_of_geometry_and_visibleMass
    (C0 : ℕ) (cK wB Mboundary : ℕ → ℝ)
    (hgeom : RouteAPaperKernelGeometryTarget C0 cK wB)
    (hboundaryMass :
      RouteAPaperKernelBoundaryVisibleAbsMassUpperBound C0 Mboundary) :
    RouteABandLimitedGridKernelAverageWeightBoundaryUpperBound routeAPaperKernel C0
      (fun X => wB X * Mboundary X) := by
  exact routeABandLimitedGridKernelAverageWeightBoundaryUpperBound_of_pointwise_and_visibleMass
    (K := routeAPaperKernel) (C0 := C0) (wB := wB) (MB := Mboundary)
    hgeom.boundaryPointwise hboundaryMass

theorem routeABandLimitedGridMeanLowerBound_of_paperKernelGeometry_and_PSB
    (C0 : ℕ) (cK Mbulk wB Mboundary : ℕ → ℝ)
    (hgeom : RouteAPaperKernelGeometryTarget C0 cK wB)
    (hweighted :
      ∀ X, routeAGridAverageNormalizedStatistic routeAPaperKernel C0 X
        = routeABandLimitedGridWeightedVisibleSum routeAPaperKernel C0 X)
    (hcK_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ cK X)
    (hboundaryMass :
      RouteAPaperKernelBoundaryVisibleAbsMassUpperBound C0 Mboundary)
    (hbulkMass :
      RouteAPaperKernelBulkVisibleMassLowerBound C0 Mbulk)
    (hbulkNonneg :
      RouteAPaperKernelBulkVisibleNonneg C0) :
    RouteABandLimitedGridMeanLowerBound routeAPaperKernel C0
      (fun X => cK X * Mbulk X - wB X * Mboundary X) := by
  exact routeABandLimitedGridMeanLowerBound_of_paperKernel_and_PSB
    (C0 := C0) (cK := cK) (Mbulk := Mbulk) (wB := wB) (Mboundary := Mboundary)
    hweighted hcK_nonneg hgeom.bulkLower hgeom.boundaryPointwise hboundaryMass hbulkMass hbulkNonneg

/--
Explicit Route-A mean theorem for the concrete paper-kernel model.

Under the mild grid hypothesis `2 ≤ C0`, the remaining inputs are purely arithmetic:
bulk visible mass, boundary absolute mass, and bulk nonnegativity.
-/
theorem routeABandLimitedGridMeanLowerBound_of_explicitPaperKernelGeometry_and_PSB
    (C0 : ℕ) (hC0 : 2 ≤ C0) (Mbulk Mboundary : ℕ → ℝ)
    (hboundaryMass :
      RouteAPaperKernelBoundaryVisibleAbsMassUpperBound C0 Mboundary)
    (hbulkMass :
      RouteAPaperKernelBulkVisibleMassLowerBound C0 Mbulk)
    (hbulkNonneg :
      RouteAPaperKernelBulkVisibleNonneg C0) :
    RouteABandLimitedGridMeanLowerBound routeAPaperKernel C0
      (fun X =>
        routeAPaperKernelExplicitBulkProfile C0 X * Mbulk X
          - routeAPaperKernelExplicitBoundaryProfile X * Mboundary X) := by
  apply routeABandLimitedGridMeanLowerBound_of_paperKernelGeometry_and_PSB
    (C0 := C0)
    (cK := routeAPaperKernelExplicitBulkProfile C0)
    (Mbulk := Mbulk)
    (wB := routeAPaperKernelExplicitBoundaryProfile)
    (Mboundary := Mboundary)
  · exact routeAPaperKernelGeometryTarget_explicit_of_two_le C0 hC0
  · intro X
    exact routeAGridAverageNormalizedStatistic_eq_weighted_sum routeAPaperKernel C0 X
  · exact routeAPaperKernelExplicitBulkProfile_nonneg C0
  · exact hboundaryMass
  · exact hbulkMass
  · exact hbulkNonneg

/--
Explicit Route-A mean theorem sourced from a dyadic mean plus a boundary absolute-mass bound.

This is the direct PSB-facing entry point: once the exact route-visible scalar has a positive total
dyadic mean and the boundary strip carries small absolute mass, the explicit paper-kernel geometry
converts those arithmetic inputs into the Route-A grid-mean lower bound.
-/
theorem routeABandLimitedGridMeanLowerBound_of_explicitPaperKernelGeometry_and_total_boundary
    (C0 : ℕ) (hC0 : 2 ≤ C0) (Mtot Mboundary : ℕ → ℝ)
    (htotal : RouteAVisibleDyadicMeanLowerBound Mtot)
    (hboundaryMass :
      RouteAPaperKernelBoundaryVisibleAbsMassUpperBound C0 Mboundary)
    (hbulkNonneg :
      RouteAPaperKernelBulkVisibleNonneg C0) :
    RouteABandLimitedGridMeanLowerBound routeAPaperKernel C0
      (fun X =>
        routeAPaperKernelExplicitBulkProfile C0 X * (Mtot X - Mboundary X)
          - routeAPaperKernelExplicitBoundaryProfile X * Mboundary X) := by
  apply routeABandLimitedGridMeanLowerBound_of_explicitPaperKernelGeometry_and_PSB
    (C0 := C0) (hC0 := hC0)
    (Mbulk := fun X => Mtot X - Mboundary X)
    (Mboundary := Mboundary)
  · exact hboundaryMass
  · exact routeAPaperKernelBulkVisibleMassLowerBound_of_total_and_boundary
      (C0 := C0) (Mtot := Mtot) (MB := Mboundary) htotal hboundaryMass
  · exact hbulkNonneg

lemma routeVisibleScalar_eq_minorResidual_on_EvenIn
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    routeVisibleScalar X N
      =
    Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
      Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon := by
  simpa [routeVisibleScalar] using
    (Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleAnalysis.routeVisibleValue_eq_minorResidual
      (X := X) (N := N) hX hN)

/--
Transfer the raw PSB dyadic mean theorem on `minorResidual` to the exact route-visible scalar.
-/
theorem routeAVisibleDyadicMeanLowerBound_of_minorResidual
    {M : ℕ → ℝ}
    (hpsb : RouteAPSBMinorResidualDyadicMeanLowerBound M) :
    RouteAVisibleDyadicMeanLowerBound M := by
  refine ⟨?_⟩
  intro X hX
  have hraw : M X ≤
      Finset.sum (EvenIn X H) (fun N =>
        (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
          Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re) := by
    exact hpsb.bound hX
  have hsum_eq :
      Finset.sum (EvenIn X H) (fun N =>
        (Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy.minorResidual X N
          Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon).re)
        =
      Finset.sum (EvenIn X H) (fun N => (routeVisibleScalar X N).re) := by
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [← routeVisibleScalar_eq_minorResidual_on_EvenIn hX hN]
  rw [← hsum_eq]
  exact hraw

/--
Package the exact visible-scalar dyadic mean lower bound directly from PSB main-contribution and
error packets on `minorResidual`.

This is the preferred Route-A entry point for future PSB work: prove the paper's positive mean as
`main contribution - error` on the raw `minorResidual`, and this theorem upgrades it to the exact
route-visible scalar consumed by the Route-A mean assembly.
-/
theorem routeAVisibleDyadicMeanLowerBound_of_minorResidual_mainContribution_and_error
    (Mmain Merr : ℕ → ℝ)
    (hmain :
      RouteAPSBMinorResidualMainContributionLowerBound Mmain Merr)
    (herr :
      RouteAPSBMinorResidualMeanErrorUpperBound Merr) :
    RouteAVisibleDyadicMeanLowerBound (fun X => Mmain X - Merr X) := by
  apply routeAVisibleDyadicMeanLowerBound_of_minorResidual
  exact routeAPSBMinorResidualDyadicMeanLowerBound_of_mainContribution_and_error
    (Mmain := Mmain) (Merr := Merr) hmain herr

/--
Direct Route-A visible dyadic mean lower bound from the current repo-level PSB model:
positive `SS_formula` bulk contribution minus conservative visible absolute error.
-/
theorem routeAVisibleDyadicMeanLowerBound_of_SS_main_and_errorAbs
    (Mmain Merr : ℕ → ℝ)
    (hmain : RouteAPSBSSMainContributionLowerBound Mmain)
    (herr : RouteAPSBVisibleMeanErrorAbsUpperBound Merr) :
    RouteAVisibleDyadicMeanLowerBound (fun X => Mmain X - Merr X) := by
  apply routeAVisibleDyadicMeanLowerBound_of_minorResidual
  exact routeAPSBMinorResidualDyadicMeanLowerBound_of_SS_main_and_errorAbs
    (Mmain := Mmain) (Merr := Merr) hmain herr

theorem routeADenseGoodGridTarget_of_mean_and_variance
    (K : ℤ → ℝ) (C0 : ℕ) (μ V : ℕ → ℝ)
    (hmean : RouteABandLimitedGridMeanLowerBound K C0 μ)
    (hvar : RouteABandLimitedGridVarianceUpperBound K C0 V)
    (hμpos : ∀ {X : ℕ}, X0 ≤ X → 0 < μ X) :
    RouteADenseGoodGridTarget K C0
      (routeABandLimitedDenseGoodThreshold μ)
      (routeABandLimitedDenseGoodDensityLoss C0 μ V) := by
  refine ⟨?_⟩
  intro X hX
  let s := routeADenseGrid X C0
  let avg : ℝ :=
    (((s.card : ℝ))⁻¹ * Finset.sum s (fun y => routeABandLimitedStatisticNormalizedRe K X y))
  let good : Finset ℕ :=
    s.filter (fun y => μ X / 2 ≤ routeABandLimitedStatisticNormalizedRe K X y)
  let bad : Finset ℕ :=
    s.filter (fun y => routeABandLimitedStatisticNormalizedRe K X y < μ X / 2)
  have hmeanX : μ X ≤ avg := by
    simpa [s, avg] using hmean.bound hX
  have hvarX :
      Finset.sum s (fun y => (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2) ≤ V X := by
    simpa [s, avg] using hvar.bound hX
  have hbad_term :
      ∀ y ∈ bad, (μ X / 2) ^ 2 ≤ (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2 := by
    intro y hy
    have hybad : routeABandLimitedStatisticNormalizedRe K X y < μ X / 2 := by
      exact (Finset.mem_filter.mp hy).2
    have hsub : μ X / 2 ≤ avg - routeABandLimitedStatisticNormalizedRe K X y := by
      linarith
    have hμhalf_nonneg : 0 ≤ μ X / 2 := by
      have := hμpos hX
      positivity
    calc
      (μ X / 2) ^ 2 ≤ (avg - routeABandLimitedStatisticNormalizedRe K X y) ^ 2 := by
        nlinarith
      _ = (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2 := by
        ring
  have hbad_mass_lower :
      ((bad.card : ℝ) * (μ X / 2) ^ 2)
        ≤
      Finset.sum bad (fun y => (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2) := by
    calc
      ((bad.card : ℝ) * (μ X / 2) ^ 2)
          = Finset.sum bad (fun _ => (μ X / 2) ^ 2) := by
              simp
      _ ≤ Finset.sum bad (fun y => (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2) := by
        refine Finset.sum_le_sum ?_
        intro y hy
        exact hbad_term y hy
  have hbad_subset : bad ⊆ s := by
    exact Finset.filter_subset _ s
  have hbad_mass_upper :
      Finset.sum bad (fun y => (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2)
        ≤
      Finset.sum s (fun y => (routeABandLimitedStatisticNormalizedRe K X y - avg) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hbad_subset
      (by
        intro y hy hsbad
        positivity)
  have hbad_count_bound :
      ((bad.card : ℝ) * (μ X / 2) ^ 2) ≤ V X := by
    exact hbad_mass_lower.trans (hbad_mass_upper.trans hvarX)
  have hμsq_pos : 0 < (μ X / 2) ^ 2 := by
    have hμhalf_pos : 0 < μ X / 2 := by
      have := hμpos hX
      positivity
    positivity
  have hbad_card_le :
      (bad.card : ℝ) ≤ (4 * V X) / (μ X) ^ 2 := by
    have htmp : (bad.card : ℝ) ≤ V X / ((μ X / 2) ^ 2) := by
      have := (le_div_iff₀ hμsq_pos).2 hbad_count_bound
      simpa [div_eq_mul_inv] using this
    have hrewrite : V X / ((μ X / 2) ^ 2) = (4 * V X) / (μ X) ^ 2 := by
      field_simp [hμpos hX]
      ring
    rw [hrewrite] at htmp
    exact htmp
  have hs_card_pos : 0 < ((s.card : ℝ)) := by
    exact_mod_cast routeADenseGrid_card_pos X C0
  have hbad_card_scaled :
      (bad.card : ℝ)
        ≤
      routeABandLimitedDenseGoodDensityLoss C0 μ V X * (s.card : ℝ) := by
    have hs_card_ne : (s.card : ℝ) ≠ 0 := by positivity
    have hscale :
        (4 * V X) / (μ X) ^ 2
          =
        routeABandLimitedDenseGoodDensityLoss C0 μ V X * (s.card : ℝ) := by
      unfold routeABandLimitedDenseGoodDensityLoss
      rw [show (((routeADenseGrid X C0).card : ℝ)) = (s.card : ℝ) by simp [s]]
      field_simp [hμpos hX, hs_card_ne]
    calc
      (bad.card : ℝ) ≤ (4 * V X) / (μ X) ^ 2 := hbad_card_le
      _ = routeABandLimitedDenseGoodDensityLoss C0 μ V X * (s.card : ℝ) := hscale
  have hcard_split_nat :
      good.card + bad.card = s.card := by
    simpa [good, bad] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := s) (fun y => μ X / 2 ≤ routeABandLimitedStatisticNormalizedRe K X y))
  have hcard_split :
      (good.card : ℝ) + (bad.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast hcard_split_nat
  have hgood_lower :
      (1 - routeABandLimitedDenseGoodDensityLoss C0 μ V X) * (s.card : ℝ)
        ≤
      (good.card : ℝ) := by
    linarith
  simpa [routeABandLimitedDenseGoodThreshold, s, good] using hgood_lower

theorem routeADenseGridClosureTarget_of_mean_and_variance_and_sampling
    (K : ℤ → ℝ) (C0 : ℕ) (μ V : ℕ → ℝ)
    (hmean : RouteABandLimitedGridMeanLowerBound K C0 μ)
    (hvar : RouteABandLimitedGridVarianceUpperBound K C0 V)
    (hμpos : ∀ {X : ℕ}, X0 ≤ X → 0 < μ X)
    (hsampling :
      RouteASamplingBernsteinTarget K C0 (routeABandLimitedDenseGoodThreshold μ)) :
    RouteADenseGridClosureTarget K C0 μ V
      (routeABandLimitedDenseGoodThreshold μ)
      (routeABandLimitedDenseGoodDensityLoss C0 μ V) := by
  refine ⟨hmean, hvar, ?_, hsampling⟩
  exact routeADenseGoodGridTarget_of_mean_and_variance K C0 μ V hmean hvar hμpos

end
