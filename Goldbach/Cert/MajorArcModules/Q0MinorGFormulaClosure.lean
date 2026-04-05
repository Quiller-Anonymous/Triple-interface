import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA
import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelBudget
import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition

/-!
Final geometric closure for the frozen witness `G_formula`.

This file is intentionally small. The heavy support/kernel bookkeeping stays in
`Q0MinorGFormulaRouteA.lean`; this module only performs the last monotone transports
needed to package the explicit geometric energy theorem.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaClosure

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition

noncomputable section

/-- Canonical scalar prefactor produced by transporting the outer `q0` layer to route-floor units. -/
noncomputable def gFormulaFloorScaledPrefactor (X : ℕ) : ℝ :=
  ((14 : ℝ) / 13) ^ 4 * routeVisibleWindowNormFloorSq X

private lemma gFormulaFloorScaledPrefactor_nonneg (X : ℕ) :
    0 ≤ gFormulaFloorScaledPrefactor X := by
  rw [gFormulaFloorScaledPrefactor]
  exact mul_nonneg (by positivity) (routeVisibleWindowNormFloorSq_nonneg X)

private lemma gFormulaCorePointwiseEnergy_nonneg' (X N : ℕ) :
    0 ≤ gFormulaCorePointwiseEnergy X N := by
  unfold gFormulaCorePointwiseEnergy
  positivity

/--
Concrete `q0`-transport for the geometric window expression.

No definitions are unfolded here: the only input is the public fourth-power comparison
for `q0NormFactor`.
-/
theorem gFormulaWindowUpper_le_floorScaledPrefactor_mul_coreWindow
    {X : ℕ} (hX : X0 ≤ X) :
    gFormulaWindowUpper X
      ≤
    gFormulaFloorScaledPrefactor X * gFormulaCoreWindowEnergy X := by
  calc
    gFormulaWindowUpper X
        ≤
      ∑ N ∈ EvenIn X H,
        ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 4
          * gFormulaCorePointwiseEnergy X N := by
            exact gFormulaWindowUpper_le_q0NormFactor_four_mul_coreWindow X
    _ ≤
      ∑ N ∈ EvenIn X H,
        gFormulaFloorScaledPrefactor X * gFormulaCorePointwiseEnergy X N := by
          refine Finset.sum_le_sum ?_
          intro N hN
          exact mul_le_mul_of_nonneg_right
            (q0NormFactor_four_le_routeVisibleWindowNormFloorSq (X := X) (N := N) hX hN)
            (gFormulaCorePointwiseEnergy_nonneg' X N)
    _ = gFormulaFloorScaledPrefactor X * gFormulaCoreWindowEnergy X := by
      rw [gFormulaFloorScaledPrefactor, ← Finset.mul_sum, gFormulaCoreWindowEnergy]

/-- Pure rearrangement helper for the floor-scaled prefactor. -/
theorem gFormulaFloorScaledPrefactor_mul_eq_routeFloorScaled
    (X : ℕ) (B : ℝ) :
    gFormulaFloorScaledPrefactor X * B
      =
    routeVisibleWindowNormFloorSq X * ((((14 : ℝ) / 13) ^ 4) * B) := by
  rw [gFormulaFloorScaledPrefactor]
  ring

/--
Final `q0` insertion once a direct `H/X` core budget is available.
-/
theorem gFormulaWindowUpper_le_of_core_budget
    {X : ℕ} {B : ℝ}
    (hX : X0 ≤ X)
    (hCore : gFormulaCoreWindowEnergy X ≤ B * ((H : ℝ) / (X : ℝ))) :
    gFormulaWindowUpper X
      ≤
    routeVisibleWindowNormFloorSq X
      * ((((14 : ℝ) / 13) ^ 4) * B * ((H : ℝ) / (X : ℝ))) := by
  have hWindow := gFormulaWindowUpper_le_floorScaledPrefactor_mul_coreWindow (X := X) hX
  have hPrefEq :
      gFormulaFloorScaledPrefactor X * B
        =
      routeVisibleWindowNormFloorSq X * ((((14 : ℝ) / 13) ^ 4) * B) := by
    exact gFormulaFloorScaledPrefactor_mul_eq_routeFloorScaled X B
  have hHX_nonneg : 0 ≤ ((H : ℝ) / (X : ℝ)) := by
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    exact div_nonneg (by positivity) (le_of_lt hXpos)
  have hPrefScaled :
      (gFormulaFloorScaledPrefactor X * B) * ((H : ℝ) / (X : ℝ))
        ≤
      (routeVisibleWindowNormFloorSq X * ((((14 : ℝ) / 13) ^ 4) * B)) * ((H : ℝ) / (X : ℝ)) := by
    exact mul_le_mul_of_nonneg_right (le_of_eq hPrefEq) hHX_nonneg
  calc
    gFormulaWindowUpper X
        ≤ gFormulaFloorScaledPrefactor X * gFormulaCoreWindowEnergy X := hWindow
    _ ≤ gFormulaFloorScaledPrefactor X * (B * ((H : ℝ) / (X : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hCore (gFormulaFloorScaledPrefactor_nonneg X)
    _ = (gFormulaFloorScaledPrefactor X * B) * ((H : ℝ) / (X : ℝ)) := by ring
    _ ≤
      (routeVisibleWindowNormFloorSq X * ((((14 : ℝ) / 13) ^ 4) * B)) * ((H : ℝ) / (X : ℝ)) := hPrefScaled
    _ = routeVisibleWindowNormFloorSq X * ((((14 : ℝ) / 13) ^ 4) * B * ((H : ℝ) / (X : ℝ))) := by
      ring

/-- Final explicit geometric closure for the frozen witness `G_formula`. -/
theorem gFormulaEnergyTarget_explicit :
    GFormulaEnergyTarget ((((14 : ℝ) / 13) ^ 4) * gFormulaCoreBudgetConst) 0 := by
  refine gFormulaEnergyTarget_of_windowUpper ?_ (by positivity) ?_
  · exact mul_nonneg (by positivity) gFormulaCoreBudgetConst_nonneg
  · intro X hX
    simpa [zero_div] using
      (gFormulaWindowUpper_le_of_core_budget (X := X) hX
        (gFormulaCoreWindowEnergy_le_explicit_budget (X := X) hX))

/-- Bridge-facing mean-channel approximation obtained from the checked SSU certificate path. -/
theorem meanChannelApproxTarget_explicit :
    MeanChannelApproxTarget
      (2 * Q0MinorSSUFromCert.A2 + 2 * ((((14 : ℝ) / 13) ^ 4) * gFormulaCoreBudgetConst)) 0 := by
  simpa using meanChannelApproxTarget_of_certSSU_and_gFormulaEnergy gFormulaEnergyTarget_explicit

end

end Q0MinorGFormulaClosure
