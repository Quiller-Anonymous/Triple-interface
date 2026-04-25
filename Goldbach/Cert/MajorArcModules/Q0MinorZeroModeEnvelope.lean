import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeAnalysis
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy

/-!
`Q0MinorZeroModeEnvelope` packages the current zero-mode envelope seam behind the frozen
route-visible bridge witness.

The key point is that the promoted empirical envelope

`sigmaEnvelopeFormula(X) = κ / log(X + H)^2`

is not an unrelated extra factor: it uses exactly the same `log(X + H)^(-2)` normalization seam
already present in the canonical route floor `c_X`.  This file isolates that relationship and
defines the normalized zero-mode ratio whose eventual analytic explanation is now the main
frontier.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeAnalysis

noncomputable section

/-- The canonical route-normalization floor `c_X = (1/800) / log(X + H)^2`. -/
def routeVisibleWindowNormFloor (X : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2)

theorem routeVisibleWindowNormFloor_sq (X : ℕ) :
    routeVisibleWindowNormFloor X ^ 2 = routeVisibleWindowNormFloorSq X := by
  simp [routeVisibleWindowNormFloor, routeVisibleWindowNormFloorSq]

/--
The promoted zero-mode envelope uses the same `log(X + H)^(-2)` seam as the route-normalization
floor, up to the fixed scalar multiplier `800 * κ`.
-/
theorem sigmaEnvelopeFormula_eq_routeVisibleWindowNormFloor_mul
    (X : ℕ) :
    sigmaEnvelopeFormula X = ((800 : ℝ) * sigmaEnvelopeKappa) * routeVisibleWindowNormFloor X := by
  simp [sigmaEnvelopeFormula, routeVisibleWindowNormFloor, mul_assoc, mul_comm]
  ring

/--
Current scalar candidate for the normalized zero-mode shape observable.

This is the scalar that remains after factoring the frozen envelope through the canonical route
floor `c_X`.
-/
def zeroModeBookkeepingScalarCandidate : ℝ :=
  (800 : ℝ) * sigmaEnvelopeKappa

/-- Geometric zero-mode baseline before singular-series modulation. -/
noncomputable def zeroModeGeometricBaseline (X N : ℕ) : ℂ :=
  Q0MinorNormalizationBridge.q0NormFactor N * geometricWeightedMinorCoeff X N 0

/-- The constant uniform scalar weight carried by the interval-window surrogate. -/
noncomputable def uniformWindowNormalization (X : ℕ) : ℂ :=
  (((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ)⁻¹

/-- The raw indicator of membership in the surrogate interval window. -/
noncomputable def uniformWindowSupportIndicator (X n : ℕ) : ℂ :=
  if n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) then 1 else 0

/--
The frozen surrogate weight is a constant normalization times the bare interval support indicator.
-/
theorem uniformWindowScalarWeight_eq_normalization_mul_indicator
    (X n : ℕ) :
    uniformWindowScalarWeight X n
      = uniformWindowNormalization X * uniformWindowSupportIndicator X n := by
  unfold uniformWindowScalarWeight uniformWindowNormalization uniformWindowSupportIndicator
  by_cases hn : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  · simp [hn]
  · simp [hn]

/--
Raw exact zero-mode mass before the common `q0` and `t = 0` minor weight are reinstated.

This is the exact `nmSupportOfT N 0` sum with the hard arithmetic `aTerm` coefficients and the
BG/TT* kernel `KHatH`, but with the common `minorArcWeightFourier X Δ_canon 0` factored out.
-/
noncomputable def rawExactZeroModeMass (X N : ℕ) : ℂ :=
  ∑ nm ∈ nmSupportOfT N 0,
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.1
        * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.2
        * KHatH (kFn nm)

/--
Raw geometric zero-slice mass before the common `q0` and `t = 0` minor weight are reinstated.

This is the interval-convolution surrogate analogue of `rawExactZeroModeMass`.
-/
noncomputable def rawGeometricZeroSliceMass (X N : ℕ) : ℂ :=
  ∑ nm ∈ nmSupportOfT N 0,
      uniformWindowScalarWeight X nm.1
        * uniformWindowScalarWeight X nm.2
        * KHatH (kFn nm)

/--
Unscaled geometric zero-slice mass: the same zero slice with only the bare interval support and
the TT*/BG kernel, before the built-in uniform-window normalization is applied.
-/
noncomputable def unscaledGeometricZeroSliceMass (X N : ℕ) : ℂ :=
  ∑ nm ∈ nmSupportOfT N 0,
      uniformWindowSupportIndicator X nm.1
        * uniformWindowSupportIndicator X nm.2
        * KHatH (kFn nm)

/--
The raw geometric zero slice is the unscaled surrogate zero slice times the square of the uniform
window normalization.
-/
theorem rawGeometricZeroSliceMass_eq_uniformWindowNormalization_sq_mul_unscaled
    (X N : ℕ) :
    rawGeometricZeroSliceMass X N
      =
    uniformWindowNormalization X ^ 2 * unscaledGeometricZeroSliceMass X N := by
  unfold rawGeometricZeroSliceMass unscaledGeometricZeroSliceMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro nm hnm
  rw [uniformWindowScalarWeight_eq_normalization_mul_indicator]
  rw [uniformWindowScalarWeight_eq_normalization_mul_indicator]
  ring

/-- The intrinsic normalization carried by the geometric zero-slice surrogate. -/
noncomputable def geometricZeroSliceNormalization (X : ℕ) : ℂ :=
  uniformWindowNormalization X ^ 2

/-- Heuristic fixed half-mass baseline for the unscaled geometric zero slice. -/
def unscaledGeometricZeroSliceHalfMass : ℂ :=
  (1 / 2 : ℝ)

/--
Named-factor version of the raw geometric zero-slice normalization identity.
-/
theorem rawGeometricZeroSliceMass_eq_geometricZeroSliceNormalization_mul_unscaled
    (X N : ℕ) :
    rawGeometricZeroSliceMass X N
      =
    geometricZeroSliceNormalization X * unscaledGeometricZeroSliceMass X N := by
  simpa [geometricZeroSliceNormalization] using
    rawGeometricZeroSliceMass_eq_uniformWindowNormalization_sq_mul_unscaled (X := X) (N := N)

/-- Exact deviation of the unscaled geometric zero slice from the half-mass baseline. -/
noncomputable def unscaledGeometricZeroSliceHalfMassError (X N : ℕ) : ℂ :=
  unscaledGeometricZeroSliceMass X N - unscaledGeometricZeroSliceHalfMass

/--
Exact decomposition of the unscaled geometric zero slice into the fixed half-mass baseline plus
an explicit error term.
-/
theorem unscaledGeometricZeroSliceMass_eq_halfMass_add_error
    (X N : ℕ) :
    unscaledGeometricZeroSliceMass X N
      = unscaledGeometricZeroSliceHalfMass + unscaledGeometricZeroSliceHalfMassError X N := by
  unfold unscaledGeometricZeroSliceHalfMassError
  ring

/--
The exact zero mode is `q0NormFactor * weight0 * rawExactZeroModeMass`.
-/
theorem zeroModeScalar_eq_q0_weight0_mul_rawExactZeroModeMass
    (X N : ℕ) :
    zeroModeScalar X N
      =
    Q0MinorNormalizationBridge.q0NormFactor N
      * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
      * rawExactZeroModeMass X N := by
  calc
    zeroModeScalar X N = weightedMinorCoeff X N 0 := by
      symm
      exact routeZeroMode_eq_weightedMinorCoeff_zero X N
    _ =
      Q0MinorNormalizationBridge.q0NormFactor N
        * ∑ nm ∈ nmSupportOfT N 0,
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.1
              * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.2
              * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
              * KHatH (kFn nm) := by
        simpa using weightedMinorCoeff_zero_eq_q0NormFactor_mul_sum_nmSupport0 X N
    _ =
      Q0MinorNormalizationBridge.q0NormFactor N
        * (minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
            * rawExactZeroModeMass X N) := by
        simp [rawExactZeroModeMass, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      Q0MinorNormalizationBridge.q0NormFactor N
        * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
        * rawExactZeroModeMass X N := by ring

/--
The geometric zero slice is `q0NormFactor * weight0 * rawGeometricZeroSliceMass`.
-/
theorem geometricWeightedMinorCoeff_zero_eq_q0_weight0_mul_rawGeometricZeroSliceMass
    (X N : ℕ) :
    geometricWeightedMinorCoeff X N 0
      =
    Q0MinorNormalizationBridge.q0NormFactor N
      * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
      * rawGeometricZeroSliceMass X N := by
  unfold geometricWeightedMinorCoeff rawGeometricZeroSliceMass
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Singular-series geometric zero-mode baseline before the final `X`-envelope is applied. -/
noncomputable def zeroModeSigmaBaseline (X N : ℕ) : ℂ :=
  zeroModeGeometricBaseline X N * sigmaNormalizedSeries N

/--
The zero-mode envelope observable:

`zeroModeScalar / (q0NormFactor(N) * geometricWeightedMinorCoeff(X,N,0) * sigmaNormalizedSeries(N))`.

This is the quantity whose near-constancy in `N` motivated the frozen `sigmaEnvelopeFormula`.
-/
noncomputable def zeroModeEnvelopeObservable (X N : ℕ) : ℂ :=
  zeroModeScalar X N / zeroModeSigmaBaseline X N

/--
Raw post-`σ` zero-mode mass ratio observable.

This is the upstream ratio that current diagnostics show is already nearly scalar before the later
route-floor `c_X` normalization is reinstated.
-/
noncomputable def rawZeroModeMassRatioObservable (X N : ℕ) : ℂ :=
  rawExactZeroModeMass X N / (rawGeometricZeroSliceMass X N * sigmaNormalizedSeries N)

/--
Unscaled post-`σ` zero-mode mass ratio observable.

This is the same upstream ratio, but with the intrinsic surrogate zero-slice normalization peeled
off. Current diagnostics suggest this is the first layer whose scalar content is genuinely order
one.
-/
noncomputable def unscaledZeroModeMassRatioObservable (X N : ℕ) : ℂ :=
  rawExactZeroModeMass X N / (unscaledGeometricZeroSliceMass X N * sigmaNormalizedSeries N)

/--
Recentered raw post-`σ` observable using the fixed half-mass baseline together with the intrinsic
surrogate zero-slice normalization.
-/
noncomputable def halfMassRecenteredZeroModeObservable (X N : ℕ) : ℂ :=
  rawExactZeroModeMass X N
    / (geometricZeroSliceNormalization X * unscaledGeometricZeroSliceHalfMass * sigmaNormalizedSeries N)

/-- Exact raw-mass residual after subtracting an abstract geometric baseline scalar. -/
noncomputable def rawZeroModeMassRatioError (κ : ℝ) (X N : ℕ) : ℂ :=
  rawZeroModeMassRatioObservable X N - (κ : ℂ)

/-- Exact unscaled raw-mass residual after subtracting an abstract intrinsic geometric scalar. -/
noncomputable def unscaledZeroModeMassRatioError (κ : ℝ) (X N : ℕ) : ℂ :=
  unscaledZeroModeMassRatioObservable X N - (κ : ℂ)

/-- Exact residual after subtracting an abstract scalar from the half-mass-recentered observable. -/
noncomputable def halfMassRecenteredZeroModeError (κ : ℝ) (X N : ℕ) : ℂ :=
  halfMassRecenteredZeroModeObservable X N - (κ : ℂ)

/--
The raw post-`σ` ratio is the inverse geometric zero-slice normalization times the unscaled ratio.
-/
theorem rawZeroModeMassRatioObservable_eq_geometricZeroSliceNormalization_inv_mul_unscaled
    (X N : ℕ) (hgeom : geometricZeroSliceNormalization X ≠ 0) :
    rawZeroModeMassRatioObservable X N
      =
    (geometricZeroSliceNormalization X)⁻¹ * unscaledZeroModeMassRatioObservable X N := by
  unfold rawZeroModeMassRatioObservable unscaledZeroModeMassRatioObservable
  rw [rawGeometricZeroSliceMass_eq_geometricZeroSliceNormalization_mul_unscaled]
  field_simp [hgeom]

/--
Exact decomposition of the unscaled post-`σ` mass ratio into an abstract intrinsic geometric
scalar plus error.
-/
theorem unscaledZeroModeMassRatioObservable_eq_scalar_add_error
    (κ : ℝ) (X N : ℕ) :
    unscaledZeroModeMassRatioObservable X N = (κ : ℂ) + unscaledZeroModeMassRatioError κ X N := by
  unfold unscaledZeroModeMassRatioError
  ring

/--
The zero-mode envelope observable is the half-mass-recentered observable times one explicit
normalization correction: the fixed half mass divided by `q0NormFactor * unscaledZeroModeMass`.
-/
noncomputable def halfMassToZeroModeEnvelopeCorrection (X N : ℕ) : ℂ :=
  unscaledGeometricZeroSliceHalfMass
    / (Q0MinorNormalizationBridge.q0NormFactor N * unscaledGeometricZeroSliceMass X N)

theorem zeroModeEnvelopeObservable_eq_halfMassToCorrection_mul_halfMassRecentered
    (X N : ℕ)
    (hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : sigmaNormalizedSeries N ≠ 0) :
    zeroModeEnvelopeObservable X N
      =
    halfMassToZeroModeEnvelopeCorrection X N * halfMassRecenteredZeroModeObservable X N := by
  unfold zeroModeEnvelopeObservable zeroModeSigmaBaseline zeroModeGeometricBaseline
    halfMassToZeroModeEnvelopeCorrection halfMassRecenteredZeroModeObservable
  rw [zeroModeScalar_eq_q0_weight0_mul_rawExactZeroModeMass]
  rw [geometricWeightedMinorCoeff_zero_eq_q0_weight0_mul_rawGeometricZeroSliceMass]
  rw [rawGeometricZeroSliceMass_eq_geometricZeroSliceNormalization_mul_unscaled]
  field_simp [hq0, hw0, hunscaled, hgeom, hsig]
  have hhalf : unscaledGeometricZeroSliceHalfMass ≠ 0 := by
    norm_num [unscaledGeometricZeroSliceHalfMass]
  calc
    rawExactZeroModeMass X N = rawExactZeroModeMass X N * 1 := by ring
    _ =
        rawExactZeroModeMass X N
          * (unscaledGeometricZeroSliceHalfMass * unscaledGeometricZeroSliceHalfMass⁻¹) := by
            rw [mul_inv_cancel₀ hhalf]
    _ =
        rawExactZeroModeMass X N
          * unscaledGeometricZeroSliceHalfMass
          * unscaledGeometricZeroSliceHalfMass⁻¹ := by
            ring

/--
The normalized zero-mode shape observable is the same half-mass-recentered observable multiplied
by the explicit normalization correction and one further division by the route floor `c_X`.
-/
noncomputable def normalizedZeroModeShapeObservable (X N : ℕ) : ℂ :=
  zeroModeEnvelopeObservable X N / ((routeVisibleWindowNormFloor X : ℝ) : ℂ)

noncomputable def halfMassToNormalizedShapeCorrection (X N : ℕ) : ℂ :=
  halfMassToZeroModeEnvelopeCorrection X N / ((routeVisibleWindowNormFloor X : ℝ) : ℂ)

/--
Deviation of the half-mass-to-normalized-shape correction from the ideal bookkeeping value `1`.
-/
noncomputable def normalizedZeroModeShapeCorrectionError (X N : ℕ) : ℂ :=
  halfMassToNormalizedShapeCorrection X N - 1

theorem normalizedZeroModeShapeObservable_eq_halfMassToCorrection_mul_halfMassRecentered
    (X N : ℕ)
    (hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hunscaled : unscaledGeometricZeroSliceMass X N ≠ 0)
    (hgeom : geometricZeroSliceNormalization X ≠ 0)
    (hsig : sigmaNormalizedSeries N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    normalizedZeroModeShapeObservable X N
      =
    halfMassToNormalizedShapeCorrection X N * halfMassRecenteredZeroModeObservable X N := by
  unfold halfMassToNormalizedShapeCorrection normalizedZeroModeShapeObservable
  rw [zeroModeEnvelopeObservable_eq_halfMassToCorrection_mul_halfMassRecentered X N hq0 hw0 hunscaled hgeom hsig]
  field_simp [hfloor]

/--
Exact decomposition of the half-mass-recentered unscaled observable into an abstract intrinsic
scalar plus error.
-/
theorem halfMassRecenteredZeroModeObservable_eq_scalar_add_error
    (κ : ℝ) (X N : ℕ) :
    halfMassRecenteredZeroModeObservable X N
      = (κ : ℂ) + halfMassRecenteredZeroModeError κ X N := by
  unfold halfMassRecenteredZeroModeError
  ring

/--
The raw post-`σ` mass ratio differs from the route-facing zero-mode envelope observable by exactly
one `q0NormFactor`.

So the raw ratio is not yet scalar in the theorem-facing sense; it still carries the same `q0`
normalization layer that the route-visible object later removes.
-/
theorem rawZeroModeMassRatioObservable_eq_q0_mul_zeroModeEnvelopeObservable
    (X N : ℕ)
    (hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 ≠ 0) :
    rawZeroModeMassRatioObservable X N
      =
    Q0MinorNormalizationBridge.q0NormFactor N * zeroModeEnvelopeObservable X N := by
  unfold rawZeroModeMassRatioObservable zeroModeEnvelopeObservable zeroModeSigmaBaseline
    zeroModeGeometricBaseline
  rw [zeroModeScalar_eq_q0_weight0_mul_rawExactZeroModeMass]
  rw [geometricWeightedMinorCoeff_zero_eq_q0_weight0_mul_rawGeometricZeroSliceMass]
  field_simp [hq0, hw0]

/--
Exact decomposition of the raw post-`σ` zero-mode mass ratio into an abstract scalar plus error.
-/
theorem rawZeroModeMassRatioObservable_eq_scalar_add_error
    (κ : ℝ) (X N : ℕ) :
    rawZeroModeMassRatioObservable X N = (κ : ℂ) + rawZeroModeMassRatioError κ X N := by
  unfold rawZeroModeMassRatioError
  ring

/--
Equivalently, the raw post-`σ` mass ratio is `q0NormFactor * c_X * normalizedZeroModeShapeObservable`.
-/
theorem rawZeroModeMassRatioObservable_eq_q0_mul_floor_mul_normalized
    (X N : ℕ)
    (hq0 : Q0MinorNormalizationBridge.q0NormFactor N ≠ 0)
    (hw0 : minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    rawZeroModeMassRatioObservable X N
      =
    Q0MinorNormalizationBridge.q0NormFactor N
      * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)
      * normalizedZeroModeShapeObservable X N := by
  rw [rawZeroModeMassRatioObservable_eq_q0_mul_zeroModeEnvelopeObservable X N hq0 hw0]
  unfold normalizedZeroModeShapeObservable
  field_simp [hfloor]

/-- Exact scalar residual after subtracting an abstract bookkeeping constant from the normalized observable. -/
noncomputable def normalizedZeroModeShapeError (κ : ℝ) (X N : ℕ) : ℂ :=
  normalizedZeroModeShapeObservable X N - (κ : ℂ)

/--
Exact decomposition of the normalized zero-mode shape observable into an abstract bookkeeping
constant plus residual.
-/
theorem normalizedZeroModeShapeObservable_eq_scalar_add_error
    (κ : ℝ) (X N : ℕ) :
    normalizedZeroModeShapeObservable X N = (κ : ℂ) + normalizedZeroModeShapeError κ X N := by
  unfold normalizedZeroModeShapeError
  ring

/-- The frozen zero-mode formula is the singular-series geometric baseline times the `X`-envelope. -/
theorem SS_formula_eq_zeroModeSigmaBaseline_mul_sigmaEnvelopeFormula
    (X N : ℕ) :
    SS_formula X N = zeroModeSigmaBaseline X N * ((sigmaEnvelopeFormula X : ℝ) : ℂ) := by
  unfold SS_formula zeroModeSigmaBaseline zeroModeGeometricBaseline
  ring

/--
Route-facing reformulation of the frozen zero-mode formula through the canonical route floor.

This isolates the current heuristic provenance claim:
the promoted zero-mode envelope is the same `log(X + H)^(-2)` seam as the route floor, with one
extra scalar multiplier `800 * κ`.
-/
theorem SS_formula_eq_zeroModeSigmaBaseline_mul_routeVisibleWindowNormFloor
    (X N : ℕ) :
    SS_formula X N
      =
    zeroModeSigmaBaseline X N
      * (((zeroModeBookkeepingScalarCandidate * routeVisibleWindowNormFloor X : ℝ) : ℂ)) := by
  rw [SS_formula_eq_zeroModeSigmaBaseline_mul_sigmaEnvelopeFormula]
  congr 1
  exact congrArg (fun r : ℝ => (r : ℂ)) <|
    by simpa [zeroModeBookkeepingScalarCandidate] using
      (sigmaEnvelopeFormula_eq_routeVisibleWindowNormFloor_mul X)

/-- Exact zero-mode error after subtracting the abstract shape `κ * c_X * sigma` from the baseline. -/
noncomputable def zeroModeEnvelopeError (κ : ℝ) (X N : ℕ) : ℂ :=
  zeroModeScalar X N
    - zeroModeSigmaBaseline X N
        * (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)

/--
Exact zero-mode shape decomposition with abstract scalar `κ`.

This is the natural first theorem target: explain the zero mode by the singular-series baseline
times the shared route-normalization seam, leaving only one scalar constant and one residual.
-/
theorem zeroModeScalar_eq_kappa_times_sigmaFloor_plus_error
    (κ : ℝ) (X N : ℕ) :
    zeroModeScalar X N
      =
    zeroModeSigmaBaseline X N * (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)
      + zeroModeEnvelopeError κ X N := by
  unfold zeroModeEnvelopeError
  ring

/--
Exact pointwise normalization identity behind the zero-mode shape transfer.

When the defining denominators are nonzero, the route-facing envelope error is precisely the
normalized shape error multiplied back by `zeroModeSigmaBaseline` and the route floor. The
inequality packaged by `ZeroModeEnvelopeNormalizationTransferTarget` is therefore a pure
normalization-size question, not new half-mass arithmetic.
-/
theorem zeroModeEnvelopeError_eq_sigma_floor_mul_normalizedShapeError
    (κ : ℝ) (X N : ℕ)
    (hsigma : zeroModeSigmaBaseline X N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    zeroModeEnvelopeError κ X N
      =
    zeroModeSigmaBaseline X N
      * ((routeVisibleWindowNormFloor X : ℝ) : ℂ)
      * normalizedZeroModeShapeError κ X N := by
  unfold zeroModeEnvelopeError normalizedZeroModeShapeError normalizedZeroModeShapeObservable
    zeroModeEnvelopeObservable
  field_simp [hsigma, hfloor]
  have hcast :
      (((κ * routeVisibleWindowNormFloor X : ℝ) : ℂ))
        =
      (((routeVisibleWindowNormFloor X : ℝ) : ℂ) * (κ : ℂ)) := by
    simp [Complex.ofReal_mul, mul_comm]
  rw [hcast]
  ring_nf

/-- Squared `ℓ²(EvenIn X H)` energy of the zero-mode envelope error. -/
noncomputable def zeroModeEnvelopeErrorWindowEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖zeroModeEnvelopeError κ X N‖ ^ 2

/--
Route-facing zero-mode shape target with abstract scalar `κ`.

This is the current proof-oriented frontier: the `N`-shape and the shared `c_X` seam are fixed,
and only the scalar bookkeeping and residual estimate remain.
-/
structure ZeroModeEnvelopeShapeTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      zeroModeEnvelopeErrorWindowEnergy κ X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

/-- Squared `ℓ²(EvenIn X H)` energy of the normalized-observable error after subtracting `κ`. -/
noncomputable def normalizedZeroModeShapeErrorWindowEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖normalizedZeroModeShapeError κ X N‖ ^ 2

/-- Raw sum of the normalized zero-mode shape observable on the canonical even window. -/
noncomputable def normalizedZeroModeShapeWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, normalizedZeroModeShapeObservable X N

/-- Canonical even-window average of the normalized zero-mode shape observable. -/
noncomputable def normalizedZeroModeShapeWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * normalizedZeroModeShapeWindowRawSum X

/-- Centered `ℓ²(EvenIn X H)` energy of the normalized zero-mode shape observable. -/
noncomputable def normalizedZeroModeShapeVarianceWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖normalizedZeroModeShapeObservable X N - normalizedZeroModeShapeWindowAverage X‖ ^ 2

/-- Window-scale average defect of the normalized zero-mode shape observable relative to `κ`. -/
noncomputable def normalizedZeroModeShapeWindowAverageStabilityEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ((EvenIn X H).card : ℝ) * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2

/--
The normalized-observable form of the zero-mode target:

`normalizedZeroModeShapeObservable = κ + error`

with the error controlled on the canonical route window.

This is the live arithmetic frontier for the numerically viable normalized route. A proof that is
meant to preserve that route should hit this target directly, or through a theorem that stays on
the normalized shape surface. In particular, the fallback path through
`normalizedZeroModeBookkeepingTarget_of_halfMass_and_correction` imports
`HalfMassRecenteredZeroModeTarget`; combined with the current half-mass variance seam downstream of
`Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute.rawLedger_canon_one_one_axiom`, that
fallback path inherits the raw-ledger `C2 * (H / X)` profile with `C2 = 1`, which is numerically
incompatible with the calibrated admissibility cap for the bookkeeping comparison theorem.
-/
structure NormalizedZeroModeBookkeepingTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      normalizedZeroModeShapeErrorWindowEnergy κ X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Named direct-frontier alias for the normalized zero-mode bookkeeping problem.

This alias is intentionally non-innovative mathematically: it records that the next viable theorem
must be a direct proof on the normalized observable itself, rather than a reduction through the
older half-mass variance route.
-/
abbrev DirectNormalizedZeroModeBookkeepingTarget (κ C2 C3 : ℝ) : Prop :=
  NormalizedZeroModeBookkeepingTarget κ C2 C3

/--
Direct arithmetic average target for the normalized zero-mode shape observable.

This is the normalized-surface analogue of the half-mass average witness, but it lives directly on
the Route-A bookkeeping observable rather than the half-mass-recentered proxy.
-/
structure NormalizedZeroModeWindowAverageTarget (κ : ℝ) : Prop where
  average_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      normalizedZeroModeShapeWindowAverage X = (κ : ℂ)

/--
Raw-sum form of the normalized window-average target.

This is the smallest honest arithmetic source theorem for the direct normalized Route-A branch:
identify the canonical even-window raw sum of the normalized shape observable with
`|EvenIn(X,H)| * κ`.
-/
structure NormalizedZeroModeWindowRawSumTarget (κ : ℝ) : Prop where
  sum_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      normalizedZeroModeShapeWindowRawSum X = ((EvenIn X H).card : ℂ) * (κ : ℂ)

/--
Direct centered-variance target for the normalized zero-mode shape observable.

This is the route-preserving replacement for proving a variance theorem only after dropping back to
the half-mass endpoint.
-/
structure NormalizedZeroModeArithmeticVarianceTarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      normalizedZeroModeShapeVarianceWindowEnergy X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Average-stability target for the normalized zero-mode shape observable.

This lets the direct normalized route separate centered fluctuation from the question of whether
the canonical window average stabilizes to a single bookkeeping scalar `κ`.
-/
structure NormalizedZeroModeWindowAverageStabilityTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      normalizedZeroModeShapeWindowAverageStabilityEnergy κ X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Pointwise transfer from the normalized zero-mode shape error back to the route-facing envelope
error.

This is the normalization seam in the zero-mode shape problem. It is deliberately separated from
the arithmetic bookkeeping target: proving this target should be a deterministic comparison of the
`zeroModeSigmaBaseline` and route-floor normalizations, while `NormalizedZeroModeBookkeepingTarget`
contains the actual scalar/half-mass arithmetic.
-/
structure ZeroModeEnvelopeNormalizationTransferTarget (κ : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      ‖zeroModeEnvelopeError κ X N‖ ^ 2
        ≤
      routeVisibleWindowNormFloorSq X * ‖normalizedZeroModeShapeError κ X N‖ ^ 2

/--
Assemble the route-facing zero-mode envelope shape target from two smaller inputs:

* a deterministic normalization transfer from the normalized shape error to the envelope error;
* the normalized bookkeeping/half-mass arithmetic bound.

This exposes the real obstruction: after this reduction, `ZeroModeEnvelopeShapeTarget` no longer
hides whether the hard work is arithmetic or normalization bookkeeping.
-/
theorem zeroModeEnvelopeShapeTarget_of_normalizedBookkeeping_and_transfer
    {κ C2 C3 : ℝ}
    (htransfer : ZeroModeEnvelopeNormalizationTransferTarget κ)
    (hbook : NormalizedZeroModeBookkeepingTarget κ C2 C3) :
    ZeroModeEnvelopeShapeTarget κ C2 C3 := by
  refine ⟨hbook.C2_nonneg, hbook.C3_nonneg, ?_⟩
  intro X hX
  unfold zeroModeEnvelopeErrorWindowEnergy
  calc
    Finset.sum (EvenIn X H) (fun N => ‖zeroModeEnvelopeError κ X N‖ ^ 2)
        ≤
      Finset.sum (EvenIn X H) (fun N =>
        routeVisibleWindowNormFloorSq X * ‖normalizedZeroModeShapeError κ X N‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact htransfer.bound hX hN
    _ =
      routeVisibleWindowNormFloorSq X *
        Finset.sum (EvenIn X H) (fun N => ‖normalizedZeroModeShapeError κ X N‖ ^ 2) := by
          rw [Finset.mul_sum]
    _ ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [normalizedZeroModeShapeErrorWindowEnergy] using hbook.bound hX)
            (routeVisibleWindowNormFloorSq_nonneg X)

/-- Squared `ℓ²(EvenIn X H)` energy of the raw post-`σ` mass-ratio error. -/
noncomputable def rawZeroModeMassRatioErrorWindowEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖rawZeroModeMassRatioError κ X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the unscaled post-`σ` mass-ratio error. -/
noncomputable def unscaledZeroModeMassRatioErrorWindowEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖unscaledZeroModeMassRatioError κ X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the unscaled geometric half-mass error. -/
noncomputable def unscaledGeometricZeroSliceHalfMassErrorWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the half-mass-recentered observable error. -/
noncomputable def halfMassRecenteredZeroModeErrorWindowEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2

/--
The raw-mass version of the zero-mode scalar target:

`rawExactZeroModeMass = rawGeometricZeroSliceMass * sigma * κ + error`.
-/
structure RawZeroModeMassShapeTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      rawZeroModeMassRatioErrorWindowEnergy κ X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
The unscaled raw-mass version of the zero-mode scalar target.

This is the first layer where the constant appears empirically to be order one.
-/
structure UnscaledZeroModeMassShapeTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      unscaledZeroModeMassRatioErrorWindowEnergy κ X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Target asserting that the unscaled geometric zero slice is itself a half-mass object up to a small
window error.
-/
structure UnscaledGeometricZeroSliceHalfMassTarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      unscaledGeometricZeroSliceHalfMassErrorWindowEnergy X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Target for the recentered intrinsic constant after replacing the moving unscaled surrogate slice by
the fixed half-mass baseline.
-/
structure HalfMassRecenteredZeroModeTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassRecenteredZeroModeErrorWindowEnergy κ X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Window-local factorization surface for the normalized zero-mode shape observable.

This keeps denominator nonvanishing and exact algebra separate from the arithmetic target. If a
future proof of `NormalizedZeroModeBookkeepingTarget` uses this surface, then the proof route has
explicitly passed back through the half-mass-recentered observable.
-/
structure NormalizedZeroModeHalfMassFactorizationTarget : Prop where
  eq_factor :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      normalizedZeroModeShapeObservable X N
        =
      halfMassToNormalizedShapeCorrection X N * halfMassRecenteredZeroModeObservable X N

/--
Stability package for the correction factor relating the half-mass-recentered observable to the
normalized shape observable.

The first field bounds the multiplicative amplification of half-mass error. The second bounds the
additive scalar drift caused by the correction factor not being exactly `1`.
-/
structure NormalizedZeroModeShapeCorrectionStabilityTarget
    (κ A C2 C3 : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  correction_norm :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      ‖halfMassToNormalizedShapeCorrection X N‖ ^ 2 ≤ A
  correction_error_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H,
          ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2)
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Canonical abstract endpoint for the zero-mode provenance ladder.

This packages the scalar `κ_hm` and the window-scale target controlling the half-mass-recentered
observable, without committing to any specific candidate value such as `4/3`.
-/
structure HalfMassRecenteredEndpoint where
  κ : ℝ
  C2 : ℝ
  C3 : ℝ
  target : HalfMassRecenteredZeroModeTarget κ C2 C3
  shape_target : ZeroModeEnvelopeShapeTarget κ C2 C3

theorem HalfMassRecenteredEndpoint.to_target (e : HalfMassRecenteredEndpoint) :
    HalfMassRecenteredZeroModeTarget e.κ e.C2 e.C3 :=
  e.target

theorem HalfMassRecenteredEndpoint.to_shape_target (e : HalfMassRecenteredEndpoint) :
    ZeroModeEnvelopeShapeTarget e.κ e.C2 e.C3 :=
  e.shape_target

theorem HalfMassRecenteredEndpoint.halfMass_decomposition
    (e : HalfMassRecenteredEndpoint) (X N : ℕ) :
    halfMassRecenteredZeroModeObservable X N
      = (e.κ : ℂ) + halfMassRecenteredZeroModeError e.κ X N := by
  exact halfMassRecenteredZeroModeObservable_eq_scalar_add_error e.κ X N

/--
Exact route-visible residual associated to an abstract half-mass-recentered scalar and the frozen
mean-channel witness.
-/
noncomputable def routeVisibleResidualOfHalfMassScalar (κ : ℝ) (X N : ℕ) : ℂ :=
  (meanChannelScalar X N - G_formula X N) + zeroModeEnvelopeError κ X N

/-- Squared `ℓ²(EvenIn X H)` energy of the exact route-visible residual at an abstract scalar `κ`. -/
noncomputable def routeVisibleResidualOfHalfMassScalarWindowEnergy (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖routeVisibleResidualOfHalfMassScalar κ X N‖ ^ 2

theorem routeVisibleScalar_eq_frozenGeometric_plus_zeroModeShape_plus_residual
    (κ : ℝ) (X N : ℕ) :
    routeVisibleScalar X N
      =
    G_formula X N
      + zeroModeSigmaBaseline X N * (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)
      + routeVisibleResidualOfHalfMassScalar κ X N := by
  rw [routeVisibleScalar_eq_zeroModeScalar_add_meanChannelScalar]
  have hmean : meanChannelScalar X N = G_formula X N + (meanChannelScalar X N - G_formula X N) := by
    ring
  rw [hmean]
  rw [zeroModeScalar_eq_kappa_times_sigmaFloor_plus_error]
  unfold routeVisibleResidualOfHalfMassScalar
  ring

theorem HalfMassRecenteredEndpoint.routeVisible_decomposition
    (e : HalfMassRecenteredEndpoint) (X N : ℕ) :
    routeVisibleScalar X N
      =
    G_formula X N
      + zeroModeSigmaBaseline X N * (((e.κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)
      + routeVisibleResidualOfHalfMassScalar e.κ X N := by
  exact routeVisibleScalar_eq_frozenGeometric_plus_zeroModeShape_plus_residual e.κ X N

/--
Legacy scalar clue inherited from the fully normalized zero-mode observable.

This is intentionally *not* asserted to be the raw post-`σ` mass scalar. The raw-mass diagnostics
show that the raw observable still carries additional normalization layers.
-/
def normalizedZeroModeScalarClue : ℝ :=
  (1 / 374400 : ℝ)

/--
Heuristic first rational candidate for the intrinsic unscaled geometric zero-slice mass scalar.

This is intentionally a diagnostic clue, not a proved constant.
-/
def unscaledGeometricZeroSliceMassScalarCandidate : ℝ :=
  (4 / 3 : ℝ)

/--
Heuristic first rational candidate for the half-mass-recentered intrinsic scalar.

This is retained only as a diagnostic clue.
-/
def halfMassRecenteredScalarCandidate : ℝ :=
  (4 / 3 : ℝ)

/--
The theorem-facing reformulation of the shape target as an explicit exact decomposition plus
window-norm control of the error.
-/
structure NormalizedZeroModeEnvelopeTarget (κ C2 C3 : ℝ) : Prop where
  shape_target : ZeroModeEnvelopeShapeTarget κ C2 C3

theorem normalizedZeroModeEnvelopeTarget_of_shape
    {κ C2 C3 : ℝ} (hT : ZeroModeEnvelopeShapeTarget κ C2 C3) :
    NormalizedZeroModeEnvelopeTarget κ C2 C3 :=
  ⟨hT⟩

theorem HalfMassRecenteredEndpoint.to_normalized_target (e : HalfMassRecenteredEndpoint) :
    NormalizedZeroModeEnvelopeTarget e.κ e.C2 e.C3 :=
  normalizedZeroModeEnvelopeTarget_of_shape e.to_shape_target

theorem normalizedZeroModeError_window_bound
    {κ C2 C3 : ℝ} (hT : NormalizedZeroModeEnvelopeTarget κ C2 C3) :
    ∀ {X : ℕ}, X0 ≤ X →
      zeroModeEnvelopeErrorWindowEnergy κ X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
  exact hT.shape_target.bound

/--
Route-facing approximation target at an abstract zero-mode scalar `κ`.

This is the scalar-parameterized version of the frozen route-visible approximation target. It is
the correct assembly surface for the arithmetic endpoint before one identifies `κ` with a
particular frozen candidate.
-/
structure RouteVisibleApproximationTargetAtScalar (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      routeVisibleResidualOfHalfMassScalarWindowEnergy κ X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

theorem routeVisibleApproximationTargetAtScalar_eq_window_bound
    {κ C2 C3 : ℝ} (hT : RouteVisibleApproximationTargetAtScalar κ C2 C3) :
    ∀ {X : ℕ}, X0 ≤ X →
      routeVisibleResidualOfHalfMassScalarWindowEnergy κ X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) :=
  hT.bound

/--
The theorem-facing zero-mode envelope target.

This is deliberately weak: it records the exact object whose future analytic control should explain
why the frozen scalar envelope is the right route-facing witness.
-/
structure ZeroModeEnvelopeTarget (E : ℕ → ℝ) : Prop where
  relation :
    ∀ X N, zeroModeScalar X N
      = zeroModeSigmaBaseline X N * ((E X : ℝ) : ℂ)
        + (zeroModeScalar X N - zeroModeSigmaBaseline X N * ((E X : ℝ) : ℂ))

/-- The current frozen envelope is the first theorem-facing candidate for `ZeroModeEnvelopeTarget`. -/
theorem sigmaEnvelopeFormula_is_zeroModeEnvelopeTarget :
    ZeroModeEnvelopeTarget sigmaEnvelopeFormula := by
  refine ⟨?_⟩
  intro X N
  ring

theorem zeroModeEnvelopeError_candidate_eq_zeroModeScalar_sub_SS_formula
    (X N : ℕ) :
    zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N
      = zeroModeScalar X N - SS_formula X N := by
  unfold zeroModeEnvelopeError
  rw [SS_formula_eq_zeroModeSigmaBaseline_mul_routeVisibleWindowNormFloor]

theorem routeVisibleResidualOfCandidate_eq_R_formula
    (X N : ℕ) :
    routeVisibleResidualOfHalfMassScalar zeroModeBookkeepingScalarCandidate X N = R_formula X N := by
  unfold routeVisibleResidualOfHalfMassScalar R_formula
  rw [routeVisibleScalar_eq_zeroModeScalar_add_meanChannelScalar]
  rw [zeroModeEnvelopeError_candidate_eq_zeroModeScalar_sub_SS_formula]
  ring

lemma norm_sq_add_le_two_mul_sum_norm_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h_add : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h_sq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    have h_nonneg_left : 0 ≤ ‖a + b‖ := norm_nonneg _
    have h_nonneg_right : 0 ≤ ‖a‖ + ‖b‖ := by positivity
    have h_mul := mul_le_mul h_add h_add h_nonneg_left h_nonneg_right
    simpa [pow_two] using h_mul
  have h_expand : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact le_trans h_sq h_expand

lemma norm_sub_sq_le_two_mul_norm_sub_sq_add_two_mul_norm_sub_sq
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
Direct normalized-surface reduction from a fixed average witness and a centered variance bound.

This is the first theorem in the Route-A-native bookkeeping route: it closes the normalized target
without passing through `HalfMassRecenteredZeroModeTarget`.
-/
theorem normalizedZeroModeBookkeepingTarget_of_average_and_variance
    {κ C2 C3 : ℝ}
    (hAvg : NormalizedZeroModeWindowAverageTarget κ)
    (hVar : NormalizedZeroModeArithmeticVarianceTarget C2 C3) :
    NormalizedZeroModeBookkeepingTarget κ C2 C3 := by
  refine ⟨hVar.C2_nonneg, hVar.C3_nonneg, ?_⟩
  intro X hX
  have hEq :
      normalizedZeroModeShapeErrorWindowEnergy κ X
        =
      normalizedZeroModeShapeVarianceWindowEnergy X := by
    unfold normalizedZeroModeShapeErrorWindowEnergy normalizedZeroModeShapeVarianceWindowEnergy
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [show normalizedZeroModeShapeError κ X N
        = normalizedZeroModeShapeObservable X N - (κ : ℂ) by rfl]
    rw [hAvg.average_eq hX]
  rw [hEq]
  exact hVar.bound hX

/--
Direct-frontier packaging of the normalized bookkeeping target from native average and variance
inputs.

This is the preferred closure theorem for the numerically viable Route-A branch: it stays entirely
on `normalizedZeroModeShapeObservable` and its window operators.
-/
theorem directNormalizedZeroModeBookkeepingTarget_of_average_and_variance
    {κ C2 C3 : ℝ}
    (hAvg : NormalizedZeroModeWindowAverageTarget κ)
    (hVar : NormalizedZeroModeArithmeticVarianceTarget C2 C3) :
    DirectNormalizedZeroModeBookkeepingTarget κ C2 C3 := by
  exact normalizedZeroModeBookkeepingTarget_of_average_and_variance hAvg hVar

/--
Upgrade a raw normalized window-sum identity to the corresponding normalized window-average target.

This isolates the remaining arithmetic content in the average step: once the raw sum is identified,
no further Route-A bookkeeping is needed to recover the exact average.
-/
theorem normalizedZeroModeWindowAverageTarget_of_rawSum
    {κ : ℝ}
    (hSum : NormalizedZeroModeWindowRawSumTarget κ) :
    NormalizedZeroModeWindowAverageTarget κ := by
  refine ⟨?_⟩
  intro X hX
  unfold normalizedZeroModeShapeWindowAverage
  rw [hSum.sum_eq hX]
  have hcard_nat : (EvenIn X H).card ≠ 0 := by
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
  have hcardC : (((EvenIn X H).card : ℂ)) ≠ 0 := by
    exact_mod_cast hcard_nat
  rw [← mul_assoc, inv_mul_cancel₀ hcardC, one_mul]

/--
Direct-frontier packaging from the raw normalized window sum and native normalized variance.

This theorem isolates the remaining arithmetic source theorem for the direct normalized route:
prove the exact raw sum on the normalized observable and a native variance bound, and the
bookkeeping target follows without any half-mass reduction.
-/
theorem directNormalizedZeroModeBookkeepingTarget_of_rawSum_and_variance
    {κ C2 C3 : ℝ}
    (hSum : NormalizedZeroModeWindowRawSumTarget κ)
    (hVar : NormalizedZeroModeArithmeticVarianceTarget C2 C3) :
    DirectNormalizedZeroModeBookkeepingTarget κ C2 C3 := by
  exact
    directNormalizedZeroModeBookkeepingTarget_of_average_and_variance
      (normalizedZeroModeWindowAverageTarget_of_rawSum hSum)
      hVar

/--
An exact average witness gives zero average-stability energy on the normalized surface.
-/
theorem normalizedZeroModeWindowAverageStabilityTarget_of_averageTarget
    {κ : ℝ} (hAvg : NormalizedZeroModeWindowAverageTarget κ) :
    NormalizedZeroModeWindowAverageStabilityTarget κ 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro X hX
  unfold normalizedZeroModeShapeWindowAverageStabilityEnergy
  rw [hAvg.average_eq hX, sub_self, norm_zero, pow_two]
  have hleft : (((EvenIn X H).card : ℝ) * ((0 : ℝ) * 0)) = 0 := by ring
  have hright :
      (0 : ℝ) * ((H : ℝ) / (X : ℝ))
        + (0 : ℝ) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) = 0 := by
    ring
  rw [hleft, hright]

/--
Direct normalized-surface reduction from centered variance plus scale-by-scale average stability.

This is the honest Route-A version of the projection-to-constants step: keep the whole argument on
`normalizedZeroModeShapeObservable` until a direct proof either succeeds or visibly collapses.
-/
theorem normalizedZeroModeBookkeepingTarget_of_variance_and_averageStability
    {κ C2v C3v C2a C3a : ℝ}
    (hVar : NormalizedZeroModeArithmeticVarianceTarget C2v C3v)
    (hAvg : NormalizedZeroModeWindowAverageStabilityTarget κ C2a C3a) :
    NormalizedZeroModeBookkeepingTarget κ
      (2 * C2v + 2 * C2a)
      (2 * C3v + 2 * C3a) := by
  refine ⟨by nlinarith [hVar.C2_nonneg, hAvg.C2_nonneg],
    by nlinarith [hVar.C3_nonneg, hAvg.C3_nonneg], ?_⟩
  intro X hX
  have hterm :
      ∀ N ∈ EvenIn X H,
        ‖normalizedZeroModeShapeError κ X N‖ ^ 2
          ≤
        2 * ‖normalizedZeroModeShapeObservable X N - normalizedZeroModeShapeWindowAverage X‖ ^ 2
          + 2 * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2 := by
    intro N hN
    simpa [normalizedZeroModeShapeError] using
      norm_sub_sq_le_two_mul_norm_sub_sq_add_two_mul_norm_sub_sq
        (normalizedZeroModeShapeObservable X N) (normalizedZeroModeShapeWindowAverage X) (κ : ℂ)
  have hsum :
      (∑ N ∈ EvenIn X H, ‖normalizedZeroModeShapeError κ X N‖ ^ 2)
        ≤
      ∑ N ∈ EvenIn X H,
        (2 * ‖normalizedZeroModeShapeObservable X N - normalizedZeroModeShapeWindowAverage X‖ ^ 2
          + 2 * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2) := by
    exact Finset.sum_le_sum (fun N hN => hterm N hN)
  have hsplit :
      ∑ N ∈ EvenIn X H,
        (2 * ‖normalizedZeroModeShapeObservable X N - normalizedZeroModeShapeWindowAverage X‖ ^ 2
          + 2 * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2)
        =
      2 * normalizedZeroModeShapeVarianceWindowEnergy X
        + 2 * normalizedZeroModeShapeWindowAverageStabilityEnergy κ X := by
    unfold normalizedZeroModeShapeVarianceWindowEnergy normalizedZeroModeShapeWindowAverageStabilityEnergy
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    have hconst :
        ∑ _N ∈ EvenIn X H, 2 * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2
          =
        ((EvenIn X H).card : ℝ) * (2 * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    ring
  have hVarBound := hVar.bound (X := X) hX
  have hAvgBound := hAvg.bound (X := X) hX
  calc
    normalizedZeroModeShapeErrorWindowEnergy κ X
        = ∑ N ∈ EvenIn X H, ‖normalizedZeroModeShapeError κ X N‖ ^ 2 := by
            rfl
    _ ≤
      ∑ N ∈ EvenIn X H,
        (2 * ‖normalizedZeroModeShapeObservable X N - normalizedZeroModeShapeWindowAverage X‖ ^ 2
          + 2 * ‖normalizedZeroModeShapeWindowAverage X - (κ : ℂ)‖ ^ 2) := hsum
    _ =
      2 * normalizedZeroModeShapeVarianceWindowEnergy X
        + 2 * normalizedZeroModeShapeWindowAverageStabilityEnergy κ X := hsplit
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

/--
Reduction from the normalized bookkeeping target to the older half-mass-recentered target plus a
separate correction-factor stability package.

This theorem is intentionally diagnostic. If the only available proof of
`NormalizedZeroModeBookkeepingTarget` goes through this lemma and then through
`HalfMassRecenteredZeroModeTarget`, the Route A zero-mode residual has inherited the old half-mass
arithmetic burden. If the normalized target is proved directly, it is genuinely weaker than that
old endpoint. Under the current repo seam, the downstream fallback path eventually reaches
`Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute.rawLedger_canon_one_one_axiom`, so this
reduction should be treated as structurally informative but numerically dead for the calibrated
bookkeeping comparison problem.
-/
theorem normalizedZeroModeBookkeepingTarget_of_halfMass_and_correction
    {κ A C2h C3h C2c C3c : ℝ}
    (hfactor : NormalizedZeroModeHalfMassFactorizationTarget)
    (hhalf : HalfMassRecenteredZeroModeTarget κ C2h C3h)
    (hcorr : NormalizedZeroModeShapeCorrectionStabilityTarget κ A C2c C3c) :
    NormalizedZeroModeBookkeepingTarget κ
      (2 * A * C2h + 2 * C2c)
      (2 * A * C3h + 2 * C3c) := by
  refine ⟨?_, ?_, ?_⟩
  · have hmain : 0 ≤ 2 * A * C2h := by
      exact mul_nonneg (mul_nonneg (by norm_num) hcorr.A_nonneg) hhalf.C2_nonneg
    have hcorrC : 0 ≤ 2 * C2c := by
      exact mul_nonneg (by norm_num) hcorr.C2_nonneg
    nlinarith
  · have hmain : 0 ≤ 2 * A * C3h := by
      exact mul_nonneg (mul_nonneg (by norm_num) hcorr.A_nonneg) hhalf.C3_nonneg
    have hcorrC : 0 ≤ 2 * C3c := by
      exact mul_nonneg (by norm_num) hcorr.C3_nonneg
    nlinarith
  · intro X hX
    let denom : ℝ := (H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2
    let halfBudget : ℝ := C2h * ((H : ℝ) / (X : ℝ)) + C3h / denom
    let corrBudget : ℝ := C2c * ((H : ℝ) / (X : ℝ)) + C3c / denom
    have hpoint :
        ∀ N ∈ EvenIn X H,
          ‖normalizedZeroModeShapeError κ X N‖ ^ 2
            ≤
          2 * A * ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2
            + 2 * ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2 := by
      intro N hN
      have herr :
          normalizedZeroModeShapeError κ X N
            =
          halfMassToNormalizedShapeCorrection X N
              * halfMassRecenteredZeroModeError κ X N
            + normalizedZeroModeShapeCorrectionError X N * (κ : ℂ) := by
        unfold normalizedZeroModeShapeError halfMassRecenteredZeroModeError
          normalizedZeroModeShapeCorrectionError
        rw [hfactor.eq_factor hX hN]
        ring
      have hsplit :
          ‖normalizedZeroModeShapeError κ X N‖ ^ 2
            ≤
          2 *
            (‖halfMassToNormalizedShapeCorrection X N
                * halfMassRecenteredZeroModeError κ X N‖ ^ 2
              + ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2) := by
        rw [herr]
        exact norm_sq_add_le_two_mul_sum_norm_sq _ _
      have hmul_exact :
          ‖halfMassToNormalizedShapeCorrection X N
              * halfMassRecenteredZeroModeError κ X N‖ ^ 2
            =
          ‖halfMassToNormalizedShapeCorrection X N‖ ^ 2
            * ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2 := by
        rw [norm_mul, mul_pow]
      have hmul_bound :
          ‖halfMassToNormalizedShapeCorrection X N
              * halfMassRecenteredZeroModeError κ X N‖ ^ 2
            ≤
          A * ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2 := by
        rw [hmul_exact]
        exact mul_le_mul_of_nonneg_right
          (hcorr.correction_norm hX hN)
          (sq_nonneg ‖halfMassRecenteredZeroModeError κ X N‖)
      nlinarith [
        hsplit,
        hmul_bound,
        sq_nonneg ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖,
        sq_nonneg ‖halfMassRecenteredZeroModeError κ X N‖,
        hcorr.A_nonneg]
    have hsum_point :
        (∑ N ∈ EvenIn X H, ‖normalizedZeroModeShapeError κ X N‖ ^ 2)
          ≤
        ∑ N ∈ EvenIn X H,
          (2 * A * ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2
            + 2 * ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2) := by
      exact Finset.sum_le_sum (fun N hN => hpoint N hN)
    have hsplit_sum :
        (∑ N ∈ EvenIn X H,
          (2 * A * ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2
            + 2 * ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2))
          =
        2 * A * halfMassRecenteredZeroModeErrorWindowEnergy κ X
          +
        2 * (∑ N ∈ EvenIn X H,
          ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2) := by
      unfold halfMassRecenteredZeroModeErrorWindowEnergy
      rw [Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
    have hhalf_bound :
        halfMassRecenteredZeroModeErrorWindowEnergy κ X ≤ halfBudget := by
      simpa [halfBudget, denom] using hhalf.bound (X := X) hX
    have hcorr_bound :
        (∑ N ∈ EvenIn X H,
          ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2) ≤ corrBudget := by
      simpa [corrBudget, denom] using hcorr.correction_error_bound (X := X) hX
    have hcombined :
        2 * A * halfMassRecenteredZeroModeErrorWindowEnergy κ X
          +
        2 * (∑ N ∈ EvenIn X H,
          ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2)
          ≤
        2 * A * halfBudget + 2 * corrBudget := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hhalf_bound
          (mul_nonneg (by norm_num) hcorr.A_nonneg))
        (mul_le_mul_of_nonneg_left hcorr_bound (by norm_num))
    calc
      normalizedZeroModeShapeErrorWindowEnergy κ X
          =
        ∑ N ∈ EvenIn X H, ‖normalizedZeroModeShapeError κ X N‖ ^ 2 := by
          rfl
      _ ≤
        ∑ N ∈ EvenIn X H,
          (2 * A * ‖halfMassRecenteredZeroModeError κ X N‖ ^ 2
            + 2 * ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2) := hsum_point
      _ =
        2 * A * halfMassRecenteredZeroModeErrorWindowEnergy κ X
          +
        2 * (∑ N ∈ EvenIn X H,
          ‖normalizedZeroModeShapeCorrectionError X N * (κ : ℂ)‖ ^ 2) := hsplit_sum
      _ ≤
        2 * A * halfBudget + 2 * corrBudget := hcombined
      _ =
        (2 * A * C2h + 2 * C2c) * ((H : ℝ) / (X : ℝ))
          + (2 * A * C3h + 2 * C3c)
              / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
          simp [halfBudget, corrBudget, denom]
          ring

theorem routeVisibleResidualOfHalfMassScalarWindowEnergy_le_two_mul_zeroMode_mean
    (κ : ℝ) (X : ℕ) :
    routeVisibleResidualOfHalfMassScalarWindowEnergy κ X
      ≤
    2 * (zeroModeEnvelopeErrorWindowEnergy κ X + meanChannelApproxErrorWindowEnergy X) := by
  unfold routeVisibleResidualOfHalfMassScalarWindowEnergy
  unfold zeroModeEnvelopeErrorWindowEnergy meanChannelApproxErrorWindowEnergy
  have hzsum :
      (∑ N ∈ EvenIn X H, 2 * ‖zeroModeEnvelopeError κ X N‖ ^ 2)
        =
      2 * (∑ N ∈ EvenIn X H, ‖zeroModeEnvelopeError κ X N‖ ^ 2) := by
    rw [← Finset.mul_sum]
  have hmsum :
      (∑ N ∈ EvenIn X H, 2 * ‖meanChannelApproxError X N‖ ^ 2)
        =
      2 * (∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2) := by
    rw [← Finset.mul_sum]
  calc
    ∑ N ∈ EvenIn X H, ‖routeVisibleResidualOfHalfMassScalar κ X N‖ ^ 2
      ≤
    ∑ N ∈ EvenIn X H,
      2 * (‖zeroModeEnvelopeError κ X N‖ ^ 2 + ‖meanChannelApproxError X N‖ ^ 2) := by
        refine Finset.sum_le_sum ?_
        intro N hN
        simpa [routeVisibleResidualOfHalfMassScalar, meanChannelApproxError, two_mul, add_assoc,
          add_left_comm, add_comm] using
          (norm_sq_add_le_two_mul_sum_norm_sq
            (meanChannelScalar X N - G_formula X N)
            (zeroModeEnvelopeError κ X N))
    _ =
      ∑ N ∈ EvenIn X H,
        (2 * ‖zeroModeEnvelopeError κ X N‖ ^ 2 + 2 * ‖meanChannelApproxError X N‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          ring
    _ =
      (∑ N ∈ EvenIn X H, 2 * ‖zeroModeEnvelopeError κ X N‖ ^ 2)
        +
      ∑ N ∈ EvenIn X H, 2 * ‖meanChannelApproxError X N‖ ^ 2 := by
        rw [Finset.sum_add_distrib]
    _ =
      2 * (∑ N ∈ EvenIn X H, ‖zeroModeEnvelopeError κ X N‖ ^ 2)
        +
      2 * (∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2) := by
        rw [hzsum, hmsum]
    _ =
      2 *
        (∑ N ∈ EvenIn X H, ‖zeroModeEnvelopeError κ X N‖ ^ 2
          + ∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2) := by
        ring

theorem routeVisibleResidualWindowEnergy_le_two_mul_zeroMode_mean
    (X : ℕ) :
    routeVisibleResidualWindowEnergy X
      ≤
    2 * (zeroModeEnvelopeErrorWindowEnergy zeroModeBookkeepingScalarCandidate X
      + meanChannelApproxErrorWindowEnergy X) := by
  calc
    routeVisibleResidualWindowEnergy X
      = ∑ N ∈ EvenIn X H, ‖R_formula X N‖ ^ 2 := by
          rfl
    _ ≤ ∑ N ∈ EvenIn X H,
          2 *
            (‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2
              + ‖meanChannelApproxError X N‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro N hN
          rw [← routeVisibleResidualOfCandidate_eq_R_formula X N]
          simpa [routeVisibleResidualOfHalfMassScalar, meanChannelApproxError, two_mul, add_assoc,
            add_left_comm, add_comm] using
            (norm_sq_add_le_two_mul_sum_norm_sq
              (meanChannelScalar X N - G_formula X N)
              (zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N))
    _ = 2 * (zeroModeEnvelopeErrorWindowEnergy zeroModeBookkeepingScalarCandidate X
          + meanChannelApproxErrorWindowEnergy X) := by
          unfold zeroModeEnvelopeErrorWindowEnergy meanChannelApproxErrorWindowEnergy
          have hzsum :
              (∑ N ∈ EvenIn X H,
                  2 * ‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2)
                =
              2 * (∑ N ∈ EvenIn X H,
                  ‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2) := by
            rw [← Finset.mul_sum]
          have hmsum :
              (∑ N ∈ EvenIn X H, 2 * ‖meanChannelApproxError X N‖ ^ 2)
                =
              2 * (∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2) := by
            rw [← Finset.mul_sum]
          calc
            ∑ N ∈ EvenIn X H,
                2 *
                  (‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2
                    + ‖meanChannelApproxError X N‖ ^ 2)
                =
              ∑ N ∈ EvenIn X H,
                (2 * ‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2
                  + 2 * ‖meanChannelApproxError X N‖ ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro N hN
                    ring
            _ =
              (∑ N ∈ EvenIn X H, 2 * ‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2)
                +
              ∑ N ∈ EvenIn X H, 2 * ‖meanChannelApproxError X N‖ ^ 2 := by
                rw [Finset.sum_add_distrib]
            _ =
              2 * (∑ N ∈ EvenIn X H, ‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2)
                +
              2 * (∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2) := by
                rw [hzsum, hmsum]
            _ =
              2 *
                (∑ N ∈ EvenIn X H, ‖zeroModeEnvelopeError zeroModeBookkeepingScalarCandidate X N‖ ^ 2
                  + ∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2) := by
                ring

theorem normalizedZeroModeEnvelopeTarget_of_halfMassEndpoint
    (e : HalfMassRecenteredEndpoint) :
    NormalizedZeroModeEnvelopeTarget e.κ e.C2 e.C3 :=
  e.to_normalized_target

theorem routeVisibleApproximationTargetAtScalar_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    RouteVisibleApproximationTargetAtScalar e.κ
      (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) := by
  refine ⟨by nlinarith [e.target.C2_nonneg, hm.C2_nonneg], by nlinarith [e.target.C3_nonneg, hm.C3_nonneg], ?_⟩
  intro X hX
  have hres :=
    routeVisibleResidualOfHalfMassScalarWindowEnergy_le_two_mul_zeroMode_mean e.κ X
  have hz' :
      zeroModeEnvelopeErrorWindowEnergy e.κ X ≤
        routeVisibleWindowNormFloorSq X *
          (e.C2 * ((H : ℝ) / (X : ℝ))
            + e.C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
    exact e.to_shape_target.bound (X := X) hX
  have hm' := hm.bound (X := X) hX
  let F : ℝ := routeVisibleWindowNormFloorSq X
  let Az : ℝ := e.C2 * ((H : ℝ) / (X : ℝ))
      + e.C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  let Am : ℝ := C2m * ((H : ℝ) / (X : ℝ))
      + C3m / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  have hsum : zeroModeEnvelopeErrorWindowEnergy e.κ X
      + meanChannelApproxErrorWindowEnergy X ≤ F * (Az + Am) := by
    have hadd : zeroModeEnvelopeErrorWindowEnergy e.κ X
        + meanChannelApproxErrorWindowEnergy X ≤ F * Az + F * Am := by
      exact add_le_add hz' hm'
    simpa [F, Az, Am, left_distrib, mul_add] using hadd
  have htwo :
      2 * (zeroModeEnvelopeErrorWindowEnergy e.κ X
        + meanChannelApproxErrorWindowEnergy X)
        ≤
      F *
        (2 * (e.C2 + C2m) * ((H : ℝ) / (X : ℝ))
          + 2 * (e.C3 + C3m) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2 : ℝ))
    have hcombine :
        2 * (F * (Az + Am))
          =
        F *
          (2 * (e.C2 + C2m) * ((H : ℝ) / (X : ℝ))
            + 2 * (e.C3 + C3m) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
      dsimp [F, Az, Am]
      ring
    exact hmul.trans_eq hcombine
  exact le_trans hres htwo

theorem frozenRouteVisibleApproximationTarget_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    (hκ : e.κ = zeroModeBookkeepingScalarCandidate)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    FrozenRouteVisibleApproximationTarget (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) := by
  refine ⟨?_⟩
  refine ⟨by nlinarith [e.target.C2_nonneg, hm.C2_nonneg], by nlinarith [e.target.C3_nonneg, hm.C3_nonneg], ?_⟩
  intro X hX
  have habs := routeVisibleApproximationTargetAtScalar_of_endpoint_and_meanApprox e hm
  have hbound := habs.bound (X := X) hX
  have hEq :
      routeVisibleResidualOfHalfMassScalarWindowEnergy e.κ X = routeVisibleResidualWindowEnergy X := by
    rw [hκ]
    unfold routeVisibleResidualOfHalfMassScalarWindowEnergy routeVisibleResidualWindowEnergy
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [routeVisibleResidualOfCandidate_eq_R_formula]
  rw [hEq] at hbound
  exact hbound

/--
The structured route-handled model associated to an abstract zero-mode scalar.

This is the part that should be consumed by the downstream route logic as main term, rather than
being thrown back into an error ledger.
-/
noncomputable def routeHandledModelAtScalar (κ : ℝ) (X N : ℕ) : ℂ :=
  G_formula X N
    + zeroModeSigmaBaseline X N * (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)

/-- The geometric component of the structured route-handled model. -/
noncomputable def routeHandledGeometricPart (X N : ℕ) : ℂ :=
  G_formula X N

/-- The zero-mode shape component of the structured route-handled model. -/
noncomputable def routeHandledZeroModeShapePart (κ : ℝ) (X N : ℕ) : ℂ :=
  zeroModeSigmaBaseline X N * (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)

theorem routeHandledModelAtScalar_eq_geometric_plus_zeroModeShape
    (κ : ℝ) (X N : ℕ) :
    routeHandledModelAtScalar κ X N
      =
    routeHandledGeometricPart X N + routeHandledZeroModeShapePart κ X N := by
  simp [routeHandledModelAtScalar, routeHandledGeometricPart, routeHandledZeroModeShapePart]

/--
Exact route-level target asserting that the structured model is the part handled elsewhere in the
route, with the remaining discrepancy isolated in `routeVisibleResidualOfHalfMassScalar`.
-/
structure RouteHandledModelTarget (κ : ℝ) : Prop where
  decomposition :
    ∀ X N,
      routeVisibleScalar X N
        =
      routeHandledModelAtScalar κ X N
        + routeVisibleResidualOfHalfMassScalar κ X N

theorem routeHandledModelTarget_of_halfMassEndpoint
    (e : HalfMassRecenteredEndpoint) :
    RouteHandledModelTarget e.κ := by
  refine ⟨?_⟩
  intro X N
  simpa [routeHandledModelAtScalar] using e.routeVisible_decomposition X N

/--
Exact split of the canonical minor residual into the structured route-handled model and the
post-model residual.

This is the honest compatibility surface with downstream Route A/B bookkeeping: the model is
kept as main term, while the residual is the only part intended for error-ledger treatment.
-/
structure ModelResidualSplit (κ : ℝ) : Prop where
  split_eq :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N TurnkeyRouteQ0.Δ_canon
          =
        routeHandledModelAtScalar κ X N + routeVisibleResidualOfHalfMassScalar κ X N

theorem modelResidualSplit_of_halfMassEndpoint
    (e : HalfMassRecenteredEndpoint) :
    ModelResidualSplit e.κ := by
  refine ⟨?_⟩
  intro X N hX hN
  rw [← routeVisibleScalar_eq_minorResidual hX hN]
  simpa [routeHandledModelAtScalar] using e.routeVisible_decomposition X N

/--
Downstream Route A/B main-term target: the canonical minor residual splits into a structured
model plus residual, and the structured model itself is already separated into its geometric and
zero-mode-shape pieces.
-/
structure RouteABMainTermTarget (κ : ℝ) : Prop where
  residual_split : ModelResidualSplit κ
  handled_split :
    ∀ X N,
      routeHandledModelAtScalar κ X N
        =
      routeHandledGeometricPart X N + routeHandledZeroModeShapePart κ X N

theorem routeABMainTermTarget_of_halfMassEndpoint
    (e : HalfMassRecenteredEndpoint) :
    RouteABMainTermTarget e.κ := by
  refine ⟨modelResidualSplit_of_halfMassEndpoint e, ?_⟩
  intro X N
  exact routeHandledModelAtScalar_eq_geometric_plus_zeroModeShape e.κ X N

/--
Explicit downstream boundary for Route A/B consumption.

This packages exactly the promise the downstream route should consume from Vaughan's bridge:
the canonical minor residual splits into the geometric handled term, the zero-mode-shape handled
term, and the post-model residual.
-/
structure RouteABConsumptionTarget (κ : ℝ) : Prop where
  decompose :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N TurnkeyRouteQ0.Δ_canon
          =
        routeHandledGeometricPart X N
          + routeHandledZeroModeShapePart κ X N
          + routeVisibleResidualOfHalfMassScalar κ X N

theorem routeABConsumptionTarget_of_mainTermTarget
    {κ : ℝ} (h : RouteABMainTermTarget κ) :
    RouteABConsumptionTarget κ := by
  refine ⟨?_⟩
  intro X N hX hN
  have hsplit := h.residual_split.split_eq hX hN
  have hhandled := h.handled_split X N
  rw [hhandled] at hsplit
  simpa [add_assoc] using hsplit

/--
Residual-only extraction from the frozen route-visible approximation target.

This is the piece that should later feed any normalized-energy or raw-energy ledger machinery.
The structured model itself is deliberately not pushed into that ledger.
-/
theorem routeVisibleResidualTarget_of_frozenRouteVisibleApproximationTarget
    {C2 C3 : ℝ} (h : FrozenRouteVisibleApproximationTarget C2 C3) :
    RouteVisibleResidualTarget C2 C3 :=
  h.residual_target

/--
Residual-only ledger target for the post-model route-visible error.

This is the object that should be fed into any future energy-ledger machinery for the leftover
error term, rather than trying to bound the full structured model as if it were noise.
-/
structure RouteVisibleResidualEnergyTarget (κ C2 C3 : ℝ) : Prop where
  residual_bound : RouteVisibleApproximationTargetAtScalar κ C2 C3

theorem routeVisibleResidualEnergyTarget_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    RouteVisibleResidualEnergyTarget e.κ
      (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) :=
  ⟨routeVisibleApproximationTargetAtScalar_of_endpoint_and_meanApprox e hm⟩

theorem routeHandledModel_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (_hm : MeanChannelApproxTarget C2m C3m) :
    RouteHandledModelTarget e.κ :=
  routeHandledModelTarget_of_halfMassEndpoint e

/--
Combined closure target for the Vaughan bridge architecture:
the structured model is handled elsewhere in the route, while the residual is controlled in the
route-visible window norm.
-/
structure FinalRouteClosureTarget (κ C2 C3 : ℝ) : Prop where
  model_target : RouteHandledModelTarget κ
  residual_target : RouteVisibleApproximationTargetAtScalar κ C2 C3

theorem routeClosure_of_model_and_residual
    {κ C2 C3 : ℝ}
    (hModel : RouteHandledModelTarget κ)
    (hErr : RouteVisibleApproximationTargetAtScalar κ C2 C3) :
    FinalRouteClosureTarget κ C2 C3 :=
  ⟨hModel, hErr⟩

theorem FinalRouteClosureTarget.to_routeABMainTermTarget
    {κ C2 C3 : ℝ} (h : FinalRouteClosureTarget κ C2 C3) :
    RouteABMainTermTarget κ := by
  refine ⟨?_ , ?_⟩
  · refine ⟨?_⟩
    intro X N hX hN
    rw [← routeVisibleScalar_eq_minorResidual hX hN]
    exact h.model_target.decomposition X N
  · intro X N
    exact routeHandledModelAtScalar_eq_geometric_plus_zeroModeShape κ X N

theorem FinalRouteClosureTarget.to_residualEnergyTarget
    {κ C2 C3 : ℝ} (h : FinalRouteClosureTarget κ C2 C3) :
    RouteVisibleResidualEnergyTarget κ C2 C3 :=
  ⟨h.residual_target⟩

theorem FinalRouteClosureTarget.to_routeABConsumptionTarget
    {κ C2 C3 : ℝ} (h : FinalRouteClosureTarget κ C2 C3) :
    RouteABConsumptionTarget κ :=
  routeABConsumptionTarget_of_mainTermTarget h.to_routeABMainTermTarget

/--
Downstream Route A/B closure packet: the route consumes the structured handled model through the
explicit Route A/B contract, while the post-model residual is controlled separately in the
route-visible energy norm.
-/
structure RouteABClosureTarget (κ C2 C3 : ℝ) : Prop where
  main_target : RouteABConsumptionTarget κ
  residual_target : RouteVisibleResidualEnergyTarget κ C2 C3

theorem FinalRouteClosureTarget.to_routeABClosureTarget
    {κ C2 C3 : ℝ}
    (h : FinalRouteClosureTarget κ C2 C3) :
    RouteABClosureTarget κ C2 C3 :=
  ⟨h.to_routeABConsumptionTarget, h.to_residualEnergyTarget⟩

theorem routeABClosure_of_mainTerm_and_residual
    {κ C2 C3 : ℝ}
    (hMain : RouteABConsumptionTarget κ)
    (hErr : RouteVisibleResidualEnergyTarget κ C2 C3) :
    RouteABClosureTarget κ C2 C3 :=
  ⟨hMain, hErr⟩

/--
Abstract completion theorem for Vaughan's bridge:
an arithmetic endpoint plus a geometric mean-channel approximation yield the final split between
structured route-handled model and controlled residual.
-/
theorem finalRouteClosureTarget_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    FinalRouteClosureTarget e.κ
      (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) := by
  exact
    routeClosure_of_model_and_residual
      (routeHandledModelTarget_of_halfMassEndpoint e)
      (routeVisibleApproximationTargetAtScalar_of_endpoint_and_meanApprox e hm)

/--
Arithmetic-side frontier for Vaughan's bridge: produce the abstract half-mass-recentered endpoint.

This is intentionally explicit. The zero-mode provenance ladder below this endpoint is now
stabilized, so the remaining arithmetic task is exactly to instantiate this interface.
-/
axiom vaughanHalfMassRecenteredEndpoint : HalfMassRecenteredEndpoint

/--
Geometric-side frontier for Vaughan's bridge: prove the frozen mean-channel approximation target.

This is the second remaining mathematical input after the zero-mode endpoint.
-/
axiom vaughanMeanChannelApproxTarget :
  ∃ C2 C3 : ℝ, MeanChannelApproxTarget C2 C3

theorem frozenRouteVisibleApproximationTarget_of_zeroModeShape_and_meanApprox
    {C2z C3z C2m C3m : ℝ}
    (hz : ZeroModeEnvelopeShapeTarget zeroModeBookkeepingScalarCandidate C2z C3z)
    (hm : MeanChannelApproxTarget C2m C3m) :
    FrozenRouteVisibleApproximationTarget (2 * (C2z + C2m)) (2 * (C3z + C3m)) := by
  refine ⟨?_⟩
  refine ⟨by nlinarith [hz.C2_nonneg, hm.C2_nonneg], by nlinarith [hz.C3_nonneg, hm.C3_nonneg], ?_⟩
  intro X hX
  have hres :=
    routeVisibleResidualWindowEnergy_le_two_mul_zeroMode_mean X
  have hz' := hz.bound (X := X) hX
  have hm' := hm.bound (X := X) hX
  let F : ℝ := routeVisibleWindowNormFloorSq X
  let Az : ℝ := C2z * ((H : ℝ) / (X : ℝ))
      + C3z / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  let Am : ℝ := C2m * ((H : ℝ) / (X : ℝ))
      + C3m / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)
  have hsum : zeroModeEnvelopeErrorWindowEnergy zeroModeBookkeepingScalarCandidate X
      + meanChannelApproxErrorWindowEnergy X ≤ F * (Az + Am) := by
    have hadd : zeroModeEnvelopeErrorWindowEnergy zeroModeBookkeepingScalarCandidate X
        + meanChannelApproxErrorWindowEnergy X ≤ F * Az + F * Am := by
      exact add_le_add hz' hm'
    simpa [F, Az, Am, left_distrib, mul_add] using hadd
  have htwo :
      2 * (zeroModeEnvelopeErrorWindowEnergy zeroModeBookkeepingScalarCandidate X
        + meanChannelApproxErrorWindowEnergy X)
        ≤
      F *
        (2 * (C2z + C2m) * ((H : ℝ) / (X : ℝ))
          + 2 * (C3z + C3m) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2 : ℝ))
    have hcombine :
        2 * (F * (Az + Am))
          =
        F *
          (2 * (C2z + C2m) * ((H : ℝ) / (X : ℝ))
            + 2 * (C3z + C3m) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
      dsimp [F, Az, Am]
      ring
    exact hmul.trans_eq hcombine
  exact le_trans hres htwo

end

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
