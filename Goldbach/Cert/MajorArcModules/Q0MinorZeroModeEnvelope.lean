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

/--
The normalized-observable form of the zero-mode target:

`normalizedZeroModeShapeObservable = κ + error`

with the error controlled on the canonical route window.
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
