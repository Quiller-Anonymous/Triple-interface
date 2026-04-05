import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelBudgetCardinality

/-! Final explicit budget wrapper for the geometric Route A kernel layer. -/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

/--
Route-sized core budget for the geometric window energy.
-/
theorem gFormulaCoreWindowEnergy_le_explicit_budget
    {X : ℕ} (hX : X0 ≤ X) :
    gFormulaCoreWindowEnergy X ≤ gFormulaCoreBudgetConst * ((H : ℝ) / (X : ℝ)) := by
  have hsum :
      gFormulaCoreWindowEnergy X ≤ ∑ N ∈ EvenIn X H, kernelParityWindowPointwiseConst X := by
    exact gFormulaCoreWindowEnergy_le_sum_kernelParityWindowPointwiseConst (X := X) hX
  have hsum_budget :
      (∑ N ∈ EvenIn X H, kernelParityWindowPointwiseConst X)
        ≤
      ∑ N ∈ EvenIn X H, gFormulaBudgetPerTerm X := by
    exact sum_kernelParityWindowPointwiseConst_le_sum_budgetPerTerm hX
  have hcollapse :
      (∑ N ∈ EvenIn X H, gFormulaBudgetPerTerm X)
        =
      ((EvenIn X H).card : ℝ) * gFormulaBudgetPerTerm X := by
    exact sum_budgetPerTerm_eq_card_mul_budgetPerTerm
  have hfinal :
      ((EvenIn X H).card : ℝ) * gFormulaBudgetPerTerm X
        ≤
      gFormulaCoreBudgetConst * ((H : ℝ) / (X : ℝ)) := by
    exact card_evenIn_mul_budgetPerTerm_le_explicit_budget hX
  exact hsum.trans <| hsum_budget.trans <| hcollapse.le.trans hfinal


end

end Q0MinorGFormulaRouteA
