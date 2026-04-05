import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelBudget

/-!
Remaining geometric Route-A theorem surface for `G_formula` beyond the kernel-budget layer.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

theorem gFormulaCorePointwiseEnergy_le_publicParityKernelCardBound
    (X N : ℕ) (hN : Even N) :
    gFormulaCorePointwiseEnergy X N
      ≤
    ‖uniformWindowNormalization X‖ ^ 4
      * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
            * (((geometricWindowNmSupportNZ X N).filter
                (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
          +
          ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
            * (((geometricWindowNmSupportNZ X N).filter
                (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))) := by
  calc
    gFormulaCorePointwiseEnergy X N
        ≤
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
          * geometricCoeffMassEven X N
        +
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
          * geometricCoeffMassOdd X N := by
            exact gFormulaCorePointwiseEnergy_le_publicParityKernelBound X N hN
    _ =
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
          * (‖uniformWindowNormalization X‖ ^ 4
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
        +
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
          * (‖uniformWindowNormalization X‖ ^ 4
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ)) := by
            rw [geometricCoeffMassEven_eq_uniformWindowNormalization_four_mul_card,
              geometricCoeffMassOdd_eq_uniformWindowNormalization_four_mul_card]
    _ =
      ‖uniformWindowNormalization X‖ ^ 4
        * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
            +
            ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))) := by
            ring


/--
Exact nonzero-frequency TT* form of the geometric pointwise energy on the canonical window.

This removes the remaining bridge-only mean-channel scalar from the geometric frontier and expresses
the energy entirely through the explicit surrogate `(n,m)` sum.
-/
theorem gFormulaPointwiseEnergy_eq_q0NormFactor_four_mul_geometricNmSupportNZ_sq
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    gFormulaPointwiseEnergy X N
      =
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
      * ‖∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm‖ ^ 2 := by
  rw [gFormulaPointwiseEnergy_eq_q0NormFactor_sq_mul_geometricMean_sq]
  rw [geometricMeanChannelScalar_eq_q0_mul_sum_geometricNmSupportNZ hN]
  rw [norm_mul]
  ring

theorem gFormulaPointwiseEnergy_eq_q0NormFactor_four_mul_geometricWindowNmSupportNZ_sq
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    gFormulaPointwiseEnergy X N
      =
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
      * ‖∑ nm ∈ geometricWindowNmSupportNZ X N, geometricAtom X N nm‖ ^ 2 := by
  rw [gFormulaPointwiseEnergy_eq_q0NormFactor_sq_mul_geometricMean_sq]
  rw [geometricMeanChannelScalar_eq_q0_mul_sum_geometricWindowNmSupportNZ hN]
  rw [norm_mul]
  ring

/--
Pointwise bridge from the packaged geometric witness to the core `k`-slice energy.

This isolates the remaining geometric closure problem: bound the core slice energy in the right
window norm.
-/
theorem gFormulaPointwiseEnergy_le_q0NormFactor_four_mul_core
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    gFormulaPointwiseEnergy X N
      ≤
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4 * gFormulaCorePointwiseEnergy X N := by
  calc
    gFormulaPointwiseEnergy X N
        = ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 * ‖geometricMeanChannelScalar X N‖ ^ 2 := by
            exact gFormulaPointwiseEnergy_eq_q0NormFactor_sq_mul_geometricMean_sq X N
    _ ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
          * (‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
              * gFormulaCorePointwiseEnergy X N) := by
            have hcore :=
              geometricMeanChannelScalar_norm_sq_le_q0NormFactor_sq_mul_sum_sq_core
                (X := X) (N := N) hN
            exact mul_le_mul_of_nonneg_left hcore (sq_nonneg _)
    _ = ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4 * gFormulaCorePointwiseEnergy X N := by
            ring

/--
Abstract Route-A-style energy target for the frozen geometric witness itself.

This is the separate geometric input needed to turn the existing SSU Route A machinery into a
bound for `meanChannelScalar - G_formula`.
-/
structure GFormulaEnergyTarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖G_formula X N‖ ^ 2)
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

/-- Generator-facing exact geometric surrogate window expression. -/
noncomputable def gFormulaWindowUpper (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖G_formula X N‖ ^ 2

theorem gFormulaWindowUpper_eq_sum_pointwiseEnergy
    (X : ℕ) :
    gFormulaWindowUpper X = ∑ N ∈ EvenIn X H, gFormulaPointwiseEnergy X N := by
  unfold gFormulaWindowUpper
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact (gFormulaPointwiseEnergy_eq_norm_sq X N).symm

/--
Exact cert-native algebraic form of the geometric window energy: a weighted square-sum of the
frozen geometric mean-channel scalar with the outer `q0NormFactor` separated.
-/
theorem gFormulaWindowUpper_eq_sum_q0NormFactor_sq_mul_geometricMean_sq
    (X : ℕ) :
    gFormulaWindowUpper X
      =
    ∑ N ∈ EvenIn X H,
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 * ‖geometricMeanChannelScalar X N‖ ^ 2 := by
  rw [gFormulaWindowUpper_eq_sum_pointwiseEnergy]
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact gFormulaPointwiseEnergy_eq_q0NormFactor_sq_mul_geometricMean_sq X N

/--
Exact cert-native algebraic form of the geometric window energy after removing the bridge-only
mean-channel scalar: a pure nonzero TT* square-sum with the outer `q0` layers explicit.
-/
theorem gFormulaWindowUpper_eq_sum_q0NormFactor_four_mul_geometricNmSupportNZ_sq
    (X : ℕ) :
    gFormulaWindowUpper X
      =
    ∑ N ∈ EvenIn X H,
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
        * ‖∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm‖ ^ 2 := by
  rw [gFormulaWindowUpper_eq_sum_pointwiseEnergy]
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact gFormulaPointwiseEnergy_eq_q0NormFactor_four_mul_geometricNmSupportNZ_sq hN

theorem gFormulaWindowUpper_eq_sum_q0NormFactor_four_mul_geometricWindowNmSupportNZ_sq
    (X : ℕ) :
    gFormulaWindowUpper X
      =
    ∑ N ∈ EvenIn X H,
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
        * ‖∑ nm ∈ geometricWindowNmSupportNZ X N, geometricAtom X N nm‖ ^ 2 := by
  rw [gFormulaWindowUpper_eq_sum_pointwiseEnergy]
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact gFormulaPointwiseEnergy_eq_q0NormFactor_four_mul_geometricWindowNmSupportNZ_sq hN

/--
Window-level reduction of the frozen geometric witness to the core `k`-slice energy.

This is the exact remaining cert-native geometric frontier before any Route-A-style numeric bound
is applied.
-/
theorem gFormulaWindowUpper_le_sum_q0NormFactor_four_mul_core
    (X : ℕ) :
    gFormulaWindowUpper X
      ≤
    ∑ N ∈ EvenIn X H,
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4 * gFormulaCorePointwiseEnergy X N := by
  rw [gFormulaWindowUpper_eq_sum_pointwiseEnergy]
  refine Finset.sum_le_sum ?_
  intro N hN
  exact gFormulaPointwiseEnergy_le_q0NormFactor_four_mul_core (X := X) (N := N) hN

theorem gFormulaWindowUpper_le_q0NormFactor_four_mul_coreWindow
    (X : ℕ) :
    gFormulaWindowUpper X
      ≤
    ∑ N ∈ EvenIn X H,
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
        * gFormulaCorePointwiseEnergy X N := by
  exact gFormulaWindowUpper_le_sum_q0NormFactor_four_mul_core X

/--
Any certified bound for the exact geometric surrogate window expression upgrades immediately to the
abstract geometric energy target.
-/
theorem gFormulaEnergyTarget_of_windowUpper
    {C2 C3 : ℝ}
    (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        gFormulaWindowUpper X
          ≤
        routeVisibleWindowNormFloorSq X
          * (C2 * ((H : ℝ) / (X : ℝ))
              + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) ) :
    GFormulaEnergyTarget C2 C3 := by
  refine ⟨hC2, hC3, ?_⟩
  intro X hX
  simpa [gFormulaWindowUpper] using hUpper (X := X) hX



/--
Route-A-native geometric target for the frozen witness `G_formula`.

This keeps the theorem language aligned with the existing Route A resource files while still
matching the exact error object that the bridge needs.
-/
structure GFormulaRouteATarget (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      meanChannelApproxErrorWindowEnergy X
        ≤
      routeVisibleWindowNormFloorSq X
        * (C2 * ((H : ℝ) / (X : ℝ))
            + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))

/--
The bridge-facing mean-channel approximation target is a direct corollary of the Route-A-native
geometric target.
-/
def GFormulaRouteATarget.to_meanChannelApproxTarget
    {C2 C3 : ℝ} (h : GFormulaRouteATarget C2 C3) :
    MeanChannelApproxTarget C2 C3 where
  C2_nonneg := h.C2_nonneg
  C3_nonneg := h.C3_nonneg
  bound := h.bound

theorem meanChannelApproxTarget_of_gFormulaRouteATarget
    {C2 C3 : ℝ} (h : GFormulaRouteATarget C2 C3) :
    MeanChannelApproxTarget C2 C3 :=
  h.to_meanChannelApproxTarget

private lemma norm_sub_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := by
    simpa [sub_eq_add_neg] using norm_add_le a (-b)
  have hsq : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [htri, norm_nonneg (a - b), norm_nonneg a, norm_nonneg b]
  have hquad : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact le_trans hsq hquad

/--
Transfer theorem: an SSU Route-A bound together with a separate energy bound for `G_formula`
implies the bridge-facing Route-A target for the geometric discrepancy.
-/
theorem gFormulaRouteATarget_of_ssu_and_gFormulaEnergy
    {A2 B2 B3 : ℝ}
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound A2)
    (hG : GFormulaEnergyTarget B2 B3) :
    GFormulaRouteATarget (2 * A2 + 2 * B2) (2 * B3) := by
  refine ⟨by nlinarith [hSSU.A2_nonneg, hG.C2_nonneg],
    by nlinarith [hG.C3_nonneg], ?_⟩
  intro X hX
  have hErrEq := meanChannelApproxErrorWindowEnergy_eq_ssuPart_sub_G_formula X
  have hterm :
      ∀ N ∈ EvenIn X H,
        ‖canonicalExpansion.ssuPart X N - G_formula X N‖ ^ 2
          ≤ 2 * ‖canonicalExpansion.ssuPart X N‖ ^ 2 + 2 * ‖G_formula X N‖ ^ 2 := by
    intro N hN
    exact norm_sub_sq_le_two_mul_sum_sq (canonicalExpansion.ssuPart X N) (G_formula X N)
  have hsum :
      (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N - G_formula X N‖ ^ 2)
        ≤
      ∑ N ∈ EvenIn X H, (2 * ‖canonicalExpansion.ssuPart X N‖ ^ 2 + 2 * ‖G_formula X N‖ ^ 2) := by
    exact Finset.sum_le_sum (fun N hN => hterm N hN)
  have hSSUbound :
      (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2)
        ≤
      routeVisibleWindowNormFloorSq X * (A2 * ((H : ℝ) / (X : ℝ))) := by
    simpa [Goldbach.Cert.MajorArcModules.Q0MinorSplitCert.normFactorSq, routeVisibleWindowNormFloorSq]
      using hSSU.bound (X := X) hX
  have hGbound := hG.bound (X := X) hX
  have hsplit :
      ∑ N ∈ EvenIn X H, (2 * ‖canonicalExpansion.ssuPart X N‖ ^ 2 + 2 * ‖G_formula X N‖ ^ 2)
        =
      2 * (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2)
        + 2 * (∑ N ∈ EvenIn X H, ‖G_formula X N‖ ^ 2) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_mul]
  have hSSUscaled :
      2 * (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2)
        ≤
      2 * (routeVisibleWindowNormFloorSq X * (A2 * ((H : ℝ) / (X : ℝ)))) := by
    exact mul_le_mul_of_nonneg_left hSSUbound (by norm_num)
  have hGscaled :
      2 * (∑ N ∈ EvenIn X H, ‖G_formula X N‖ ^ 2)
        ≤
      2 * (routeVisibleWindowNormFloorSq X
        * (B2 * ((H : ℝ) / (X : ℝ))
            + B3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
    exact mul_le_mul_of_nonneg_left hGbound (by norm_num)
  calc
    meanChannelApproxErrorWindowEnergy X
        =
      ∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N - G_formula X N‖ ^ 2 := hErrEq
    _ ≤
      ∑ N ∈ EvenIn X H, (2 * ‖canonicalExpansion.ssuPart X N‖ ^ 2 + 2 * ‖G_formula X N‖ ^ 2) := hsum
    _ =
      2 * (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2)
        + 2 * (∑ N ∈ EvenIn X H, ‖G_formula X N‖ ^ 2) := hsplit
    _ ≤
      2 * (routeVisibleWindowNormFloorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
        + 2 * (routeVisibleWindowNormFloorSq X
          * (B2 * ((H : ℝ) / (X : ℝ))
              + B3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
      exact add_le_add hSSUscaled hGscaled
    _ =
      routeVisibleWindowNormFloorSq X
        * ((2 * A2 + 2 * B2) * ((H : ℝ) / (X : ℝ))
            + (2 * B3) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
      ring

/--
Concrete Route-A transfer using the currently checked SSU certificate path. Once the separate
geometric surrogate energy input is supplied, the full Route-A-native geometric target follows.
-/
theorem gFormulaRouteATarget_of_certSSU_and_gFormulaEnergy
    {B2 B3 : ℝ}
    (hG : GFormulaEnergyTarget B2 B3) :
    GFormulaRouteATarget (2 * Q0MinorSSUFromCert.A2 + 2 * B2) (2 * B3) := by
  exact
    gFormulaRouteATarget_of_ssu_and_gFormulaEnergy
      (hSSU := Q0MinorSSUFromCert.nonzeroModeEnergyBound_of_upperBound
        Q0MinorSSUFromCert.nonzeroModeEnergyBound)
      hG

/--
Bridge-facing mean-channel approximation obtained from the checked SSU certificate path together
with a separate energy theorem for the frozen geometric witness.
-/
theorem meanChannelApproxTarget_of_certSSU_and_gFormulaEnergy
    {B2 B3 : ℝ}
    (hG : GFormulaEnergyTarget B2 B3) :
    MeanChannelApproxTarget (2 * Q0MinorSSUFromCert.A2 + 2 * B2) (2 * B3) := by
  exact
    meanChannelApproxTarget_of_gFormulaRouteATarget
      (gFormulaRouteATarget_of_certSSU_and_gFormulaEnergy hG)

/--
Current geometric frontier: a Route-A-style theorem for the frozen geometric witness.
-/
theorem vaughanGFormulaRouteATarget :
  ∃ C2 C3 : ℝ, GFormulaRouteATarget C2 C3 := by
  rcases vaughanMeanChannelApproxTarget with ⟨C2, C3, h⟩
  exact ⟨C2, C3, ⟨h.C2_nonneg, h.C3_nonneg, h.bound⟩⟩

theorem vaughanMeanChannelApproxTarget_of_routeA :
    ∃ C2 C3 : ℝ, MeanChannelApproxTarget C2 C3 := by
  rcases vaughanGFormulaRouteATarget with ⟨C2, C3, h⟩
  exact ⟨C2, C3, meanChannelApproxTarget_of_gFormulaRouteATarget h⟩

end

end Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA
