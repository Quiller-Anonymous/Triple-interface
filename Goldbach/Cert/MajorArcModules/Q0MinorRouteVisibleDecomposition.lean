import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleAnalysis
import Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Analytic.NumericSigma
import Goldbach.SingularSeries

/-!
`Q0MinorRouteVisibleDecomposition` separates three roles that should no longer be conflated:

1. the exact route-visible witness consumed by the current route operator,
2. candidate bridge models built to explain that witness,
3. the residual left after subtracting a chosen bridge model.

This file is intentionally algebraic. It does not define a specific geometric or
singular-series model. Instead it provides the exact route-visible scalar pieces
and the residual bookkeeping surface that a future bridge theorem should use.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleAnalysis
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition

noncomputable section

set_option maxRecDepth 4096

/-- Exact scalar value of the route-visible minor object at `(X,N)`. -/
noncomputable def routeVisibleScalar (X N : ℕ) : ℂ :=
  routeVisibleValue X N

/-- Exact scalar contribution of the zero mode at `(X,N)`. -/
noncomputable def zeroModeScalar (X N : ℕ) : ℂ :=
  routeVisibleZeroCoeff X N

/-- Exact scalar contribution of the mean channel after the current slice-sum operator. -/
noncomputable def meanChannelScalar (X N : ℕ) : ℂ :=
  Q0MinorSingularityShadowBridge.familySliceSumOn
    (Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N

theorem routeVisibleScalar_eq_zeroModeScalar_add_meanChannelScalar
    (X N : ℕ) :
    routeVisibleScalar X N = zeroModeScalar X N + meanChannelScalar X N := by
  unfold routeVisibleScalar zeroModeScalar meanChannelScalar routeVisibleValue routeVisibleZeroCoeff
  rfl

/--
A candidate bridge model for the exact route-visible scalar.

The point of this structure is to keep the witness roles separate:
`routeVisibleScalar` is exact; a `RouteVisibleScalarModel` is explanatory.
-/
structure RouteVisibleScalarModel where
  geometricRouteVisible : ℕ → ℕ → ℂ
  singularSeriesZeroModeCorrection : ℕ → ℕ → ℂ

/-- Uniform interval-window scalar weight used by the frozen geometric formula. -/
noncomputable def uniformWindowScalarWeight (X n : ℕ) : ℂ :=
  if n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) then
    (((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℂ)⁻¹
  else
    0

/--
Exact weighted minor coefficient built from the frozen interval-window surrogate, i.e. with the
prime/arithmetic coefficient replaced by a uniform window weight.
-/
noncomputable def geometricWeightedMinorCoeff (X N : ℕ) (t : ℤ) : ℂ :=
  Q0MinorNormalizationBridge.q0NormFactor N
    * ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t,
        uniformWindowScalarWeight X nm.1
          * uniformWindowScalarWeight X nm.2
          * Q0MinorTTStarAlgebra.minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon t
          * Q0MinorTTStarAlgebra.KHatH (Q0MinorTTStarFrequencyExpansion.kFn nm)

/-- Scalar mean-channel contribution of the frozen geometric surrogate. -/
noncomputable def geometricMeanChannelScalar (X N : ℕ) : ℂ :=
  Q0MinorSingularityShadowBridge.familySliceSumOn
    (Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
    (fun _ t =>
      meanChannelOn
        (Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
        (geometricWeightedMinorCoeff X N) t) N

/--
Normalized singular-series modulation around the baseline value `1`.

This uses the exact in-repo singular series `σ(n) = 2*C2*∏ oddFactor`, normalized by `2*C2`.
-/
noncomputable def sigmaNormalizedSeries (N : ℕ) : ℂ :=
  (((Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
      / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2)) : ℝ) : ℂ)

/--
Normalized singular-series modulation around the baseline value `1`.

This is retained as a diagnostic auxiliary, but the main fixed formula witness now uses the full
normalized singular series in `SS_formula`.
-/
noncomputable def sigmaNormalizedModulation (N : ℕ) : ℂ :=
  sigmaNormalizedSeries N - 1

/--
Fixed singular-series zero-mode formula: the geometric zero-mode scalar multiplied by the full
normalized singular series.
-/
def sigmaEnvelopeKappa : ℝ := 4.089173283623e-04

/--
Frozen `X`-envelope for the singular-series zero-mode witness.

This is the route-aligned `κ / log(X + H)^2` envelope selected by the first explicit sweep on the
exact route scalar residual norm.
-/
def sigmaEnvelopeFormula (X : ℕ) : ℝ :=
  sigmaEnvelopeKappa / (Real.log ((X + H : ℕ) : ℝ)) ^ 2

/--
Fixed singular-series zero-mode formula: the geometric zero-mode scalar multiplied by the
route-aligned envelope and the full normalized singular series.
-/
noncomputable def SS_formula (X N : ℕ) : ℂ :=
  Q0MinorNormalizationBridge.q0NormFactor N
    * geometricWeightedMinorCoeff X N 0
    * ((sigmaEnvelopeFormula X : ℝ) : ℂ)
    * sigmaNormalizedSeries N

/-- Residual left after subtracting the chosen candidate bridge model. -/
noncomputable def routeVisibleResidual
    (M : RouteVisibleScalarModel) (X N : ℕ) : ℂ :=
  routeVisibleScalar X N
    - M.geometricRouteVisible X N
    - M.singularSeriesZeroModeCorrection X N

theorem routeVisibleScalar_eq_model_add_residual
    (M : RouteVisibleScalarModel) (X N : ℕ) :
    routeVisibleScalar X N
      =
    M.geometricRouteVisible X N
      + M.singularSeriesZeroModeCorrection X N
      + routeVisibleResidual M X N := by
  unfold routeVisibleResidual routeVisibleScalar
  ring

/--
Fixed geometric route-visible scalar formula.

At the route-facing scalar level, the current geometric witness is taken to be the mean-channel
surrogate alone with the extra `q0NormFactor` envelope suggested by the normalization seam; the
zero-mode baseline is bundled into `SS_formula`.
-/
noncomputable def G_formula (X N : ℕ) : ℂ :=
  Q0MinorNormalizationBridge.q0NormFactor N * geometricMeanChannelScalar X N

/-- Exact residual left after subtracting the frozen `G + SS` formula pair. -/
noncomputable def R_formula (X N : ℕ) : ℂ :=
  routeVisibleScalar X N - G_formula X N - SS_formula X N

theorem routeVisibleScalar_eq_G_formula_add_SS_formula_add_R_formula
    (X N : ℕ) :
    routeVisibleScalar X N = G_formula X N + SS_formula X N + R_formula X N := by
  unfold R_formula
  ring

/-- The current frozen bridge witness packaged as a route-visible scalar model. -/
noncomputable def frozenRouteVisibleModel : RouteVisibleScalarModel where
  geometricRouteVisible := G_formula
  singularSeriesZeroModeCorrection := SS_formula

theorem routeVisibleScalar_eq_frozenModel_add_residual
    (X N : ℕ) :
    routeVisibleScalar X N
      =
    frozenRouteVisibleModel.geometricRouteVisible X N
      + frozenRouteVisibleModel.singularSeriesZeroModeCorrection X N
      + routeVisibleResidual frozenRouteVisibleModel X N := by
  simpa [frozenRouteVisibleModel, G_formula, SS_formula, R_formula, routeVisibleResidual] using
    routeVisibleScalar_eq_G_formula_add_SS_formula_add_R_formula (X := X) (N := N)

/-- Squared `ℓ²(EvenIn X H)` energy of the exact route-visible residual `R_formula`. -/
noncomputable def routeVisibleResidualWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖R_formula X N‖ ^ 2

/--
The normalization floor carried by `q0NormFactor` uniformly on the canonical window.

This is the exact `c_X^2` shape used by `Q0MinorNormalizedEnergy`.
-/
def routeVisibleWindowNormFloorSq (X : ℕ) : ℝ :=
  (((1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2))) ^ 2

lemma routeVisibleWindowNormFloorSq_nonneg (X : ℕ) : 0 ≤ routeVisibleWindowNormFloorSq X := by
  exact sq_nonneg ((1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2))

/--
Uniform upper comparison for the `q0NormFactor` layer across the canonical even window.

This is shared normalization infrastructure: the exact `N`-dependence of `q0NormFactor` varies
across `EvenIn X H`, but only by a fixed logarithmic ratio compared to the route-visible floor.
-/
theorem q0NormFactor_sq_le_routeVisibleWindowNormFloorSq
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
      ≤ ((14 : ℝ) / 13) ^ 4 * routeVisibleWindowNormFloorSq X := by
  have hXleN : X ≤ N :=
    Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds.X_le_of_mem_EvenIn (X := X) (N := N) hN
  have hX0leN : X0 ≤ N := le_trans hX hXleN
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leN
  have hlogXH_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    linarith
  have hlogXH_pos : 0 < Real.log ((X + H : ℕ) : ℝ) := by
    linarith
  have hXH_le_twoX : X + H ≤ 2 * X := by
    have hHX : H ≤ X := le_trans (by decide : H ≤ X0) hX
    omega
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast hXpos_nat
  have hXHpos : (0 : ℝ) < (((X + H : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX0leXH)
  have hlogXH_le :
      Real.log ((X + H : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    exact Real.log_le_log hXHpos (by exact_mod_cast hXH_le_twoX)
  have hlog_two_mul :
      Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 : ℝ) + Real.log (X : ℝ) := by
    have hXne : (X : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hXpos_nat)
    simpa [Nat.cast_mul] using Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXne
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hlogX_leN : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log hXpos (by exact_mod_cast hXleN)
  have hlogXH_le14 :
      Real.log ((X + H : ℕ) : ℝ) ≤ ((14 : ℝ) / 13) * Real.log (N : ℝ) := by
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
  have hratio :
      Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ) ≤ (14 : ℝ) / 13 := by
    have hmul :
        Real.log ((X + H : ℕ) : ℝ) * (Real.log (N : ℝ))⁻¹
          ≤
        (((14 : ℝ) / 13) * Real.log (N : ℝ)) * (Real.log (N : ℝ))⁻¹ := by
      exact mul_le_mul_of_nonneg_right hlogXH_le14 (inv_nonneg.mpr (le_of_lt hlogN_pos))
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 := hlogN_pos.ne'
    calc
      Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)
          = Real.log ((X + H : ℕ) : ℝ) * (Real.log (N : ℝ))⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ (((14 : ℝ) / 13) * Real.log (N : ℝ)) * (Real.log (N : ℝ))⁻¹ := hmul
      _ = (14 : ℝ) / 13 := by
        field_simp [hlogN_ne]
  have hratio_nonneg :
      0 ≤ Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg (le_of_lt hlogXH_pos) (le_of_lt hlogN_pos)
  have hratio4 :
      (Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)) ^ 4 ≤ ((14 : ℝ) / 13) ^ 4 := by
    exact pow_le_pow_left₀ hratio_nonneg hratio 4
  have hrew :
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 =
        (Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)) ^ 4 * routeVisibleWindowNormFloorSq X := by
    rw [Q0MinorNormalizedEnergy.norm_q0NormFactor, routeVisibleWindowNormFloorSq]
    field_simp [hlogN_pos.ne', hlogXH_pos.ne']
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hratio4 (routeVisibleWindowNormFloorSq_nonneg X)

/--
Fourth-power version of the canonical `q0` normalization comparison. This is the form needed by
the geometric Route-A window estimate after the outer `q0` layer has been factored off.
-/
theorem q0NormFactor_four_le_routeVisibleWindowNormFloorSq
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
      ≤ ((14 : ℝ) / 13) ^ 4 * routeVisibleWindowNormFloorSq X := by
  have hsq :=
    q0NormFactor_sq_le_routeVisibleWindowNormFloorSq (X := X) (N := N) hX hN
  have hXleN : X ≤ N :=
    Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds.X_le_of_mem_EvenIn (X := X) (N := N) hN
  have hX0leN : X0 ≤ N := le_trans hX hXleN
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leN
  have hInv_le_one : (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) ≤ 1 := by
    have hsq_ge_one : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
      nlinarith
    simpa using (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1) hsq_ge_one)
  have hnorm_le_small : ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ≤ (1 / 800 : ℝ) := by
    rw [Q0MinorNormalizedEnergy.norm_q0NormFactor]
    have hInv_nonneg : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) := by positivity
    nlinarith
  have hsq_le_one : ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (Q0MinorNormalizationBridge.q0NormFactor N), hnorm_le_small]
  have hpow_le_sq : ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
      ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 := by
    nlinarith [sq_nonneg ‖Q0MinorNormalizationBridge.q0NormFactor N‖, hsq_le_one]
  exact le_trans hpow_le_sq hsq

/--
Route-facing residual target for the fixed-formula bridge witness `G + SS + R`.

This is the theorem-sized inequality that should be used to judge whether the frozen formula pair
`(G_formula, SS_formula)` leaves an acceptable remainder in the actual route scalar window norm.
-/
structure RouteVisibleResidualTarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      routeVisibleResidualWindowEnergy X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

/--
First actual route-facing approximation theorem target for the current frozen witness.

This is the theorem surface the next proof phase should aim to prove: the exact route-visible
scalar is explained by the frozen `(G_formula, SS_formula)` witness plus a residual controlled in
the normalized route scalar window norm.
-/
structure FrozenRouteVisibleApproximationTarget (C2 C3 : ℝ) : Prop where
  residual_target : RouteVisibleResidualTarget C2 C3

theorem frozenRouteVisibleApproximationTarget_eq_window_bound
    {C2 C3 : ℝ} (hT : FrozenRouteVisibleApproximationTarget C2 C3) :
    ∀ {X : ℕ}, X0 ≤ X →
      routeVisibleResidualWindowEnergy X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
  exact hT.residual_target.bound

/--
The exact route-visible scalar is the normalized minor residual on the canonical route window.
-/
theorem routeVisibleScalar_eq_minorResidual
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    routeVisibleScalar X N = minorResidual X N TurnkeyRouteQ0.Δ_canon := by
  simpa [routeVisibleScalar] using
    (Q0MinorRouteVisibleAnalysis.routeVisibleValue_eq_minorResidual (X := X) (N := N) hX hN)

/--
The residual target is naturally judged in the same normalized-window shape used by the canonical
minor-energy route.
-/
theorem routeVisibleResidualTarget_eq_window_bound
    {C2 C3 : ℝ} (hR : RouteVisibleResidualTarget C2 C3) :
    ∀ {X : ℕ}, X0 ≤ X →
      routeVisibleResidualWindowEnergy X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) :=
  hR.bound

/--
The zero-mode arithmetic remainder after removing the singular-series-type correction from the
exact zero-mode scalar. This is included because current diagnostics indicate that the post-geometric
route-visible residual is overwhelmingly concentrated at `t = 0`.
-/
noncomputable def zeroModeArithmeticResidual
    (M : RouteVisibleScalarModel) (X N : ℕ) : ℂ :=
  zeroModeScalar X N - M.singularSeriesZeroModeCorrection X N

theorem zeroModeScalar_eq_singularSeries_add_zeroModeArithmeticResidual
    (M : RouteVisibleScalarModel) (X N : ℕ) :
    zeroModeScalar X N
      =
    M.singularSeriesZeroModeCorrection X N + zeroModeArithmeticResidual M X N := by
  unfold zeroModeArithmeticResidual zeroModeScalar
  ring

/--
Exact mean-channel residual after subtracting the frozen geometric scalar witness.
-/
noncomputable def meanChannelApproxError (X N : ℕ) : ℂ :=
  meanChannelScalar X N - G_formula X N

theorem meanChannelScalar_eq_G_formula_add_meanChannelApproxError
    (X N : ℕ) :
    meanChannelScalar X N = G_formula X N + meanChannelApproxError X N := by
  unfold meanChannelApproxError
  ring

/-- Squared `ℓ²(EvenIn X H)` energy of the exact mean-channel approximation error. -/
noncomputable def meanChannelApproxErrorWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖meanChannelApproxError X N‖ ^ 2

/--
Route-facing approximation target for the mean-channel geometric witness `G_formula`.
-/
structure MeanChannelApproxTarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      meanChannelApproxErrorWindowEnergy X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

end

end Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
