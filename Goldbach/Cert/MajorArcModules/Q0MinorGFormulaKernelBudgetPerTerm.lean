import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelWindowLift

/-!
Per-term budget transport for the geometric Route A kernel layer.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- Explicit core-budget constant obtained from the parity-summed Route-A kernel budget. -/
noncomputable def gFormulaCoreBudgetConst : ℝ :=
  ((((H + 1 : ℕ) : ℝ) / (H : ℝ)) : ℝ) * kernelMassNZParity_upper_routeA_const

theorem gFormulaCoreBudgetConst_nonneg :
    0 ≤ gFormulaCoreBudgetConst := by
  rw [gFormulaCoreBudgetConst]
  have hcore_nonneg : 0 ≤ Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore := by
    rw [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCore_eq_collapsed]
    dsimp [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCoreCollapsed]
    positivity
  have hkernel_nonneg : 0 ≤ kernelMassNZParity_upper_routeA_const := by
    rw [kernelMassNZParity_upper_routeA_const]
    nlinarith [hcore_nonneg, Q0MajorTailTTStarStep5KernelMassBound.δ_weightSplit_pos]
  exact mul_nonneg (by positivity) hkernel_nonneg

noncomputable def gFormulaBudgetPerTerm (X : ℕ) : ℝ :=
  kernelMassNZParity_upper_routeA_const / (X : ℝ)

theorem gFormulaBudgetPerTerm_nonneg {X : ℕ} (hX : X0 ≤ X) :
    0 ≤ gFormulaBudgetPerTerm X := by
  have hcore_nonneg : 0 ≤ Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore := by
    rw [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCore_eq_collapsed]
    dsimp [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCoreCollapsed]
    positivity
  have hkernel_nonneg : 0 ≤ kernelMassNZParity_upper_routeA_const := by
    rw [kernelMassNZParity_upper_routeA_const]
    nlinarith [hcore_nonneg, Q0MajorTailTTStarStep5KernelMassBound.δ_weightSplit_pos]
  rw [gFormulaBudgetPerTerm]
  exact div_nonneg hkernel_nonneg (by positivity)

theorem kernelParityWindowPointwiseConst_le_budgetPerTerm
    {X : ℕ} (hX : X0 ≤ X) :
    kernelParityWindowPointwiseConst X ≤ gFormulaBudgetPerTerm X := by
  simpa [gFormulaBudgetPerTerm, kernelParityWindowPointwiseConst] using
    (kernelMassNZParity_upper_routeA_le_const_div_X (X := X) hX)

theorem sum_kernelParityWindowPointwiseConst_le_sum_budgetPerTerm
    {X : ℕ} (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, kernelParityWindowPointwiseConst X)
      ≤
    ∑ N ∈ EvenIn X H, gFormulaBudgetPerTerm X := by
  refine Finset.sum_le_sum ?_
  intro N hN
  exact kernelParityWindowPointwiseConst_le_budgetPerTerm hX

theorem sum_budgetPerTerm_eq_card_mul_budgetPerTerm
    {X : ℕ} :
    (∑ N ∈ EvenIn X H, gFormulaBudgetPerTerm X)
      =
    ((EvenIn X H).card : ℝ) * gFormulaBudgetPerTerm X := by
  rw [Finset.sum_const, nsmul_eq_mul]

end

end Q0MinorGFormulaRouteA
