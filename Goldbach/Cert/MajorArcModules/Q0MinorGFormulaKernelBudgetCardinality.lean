import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelBudgetPerTerm

/-!
Cardinality-level budget transport for the geometric Route A kernel layer.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

theorem card_evenIn_le_H_add_one_for_budget (X : ℕ) :
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

theorem card_evenIn_mul_budgetPerTerm_le_explicit_budget
    {X : ℕ} (hX : X0 ≤ X) :
    ((EvenIn X H).card : ℝ) * gFormulaBudgetPerTerm X
      ≤
    gFormulaCoreBudgetConst * ((H : ℝ) / (X : ℝ)) := by
  have hcard_nat := card_evenIn_le_H_add_one_for_budget X
  have hcard :
      ((EvenIn X H).card : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hmul :
      ((EvenIn X H).card : ℝ) * gFormulaBudgetPerTerm X
        ≤
      ((H + 1 : ℕ) : ℝ) * gFormulaBudgetPerTerm X := by
    exact mul_le_mul_of_nonneg_right hcard (gFormulaBudgetPerTerm_nonneg hX)
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hrewrite :
      ((H + 1 : ℕ) : ℝ) * gFormulaBudgetPerTerm X
        =
      gFormulaCoreBudgetConst * ((H : ℝ) / (X : ℝ)) := by
    rw [gFormulaBudgetPerTerm, gFormulaCoreBudgetConst]
    have hHpos_nat : 0 < H := by native_decide
    have hHne : (H : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hHpos_nat)
    have hXne : (X : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hXpos_nat)
    field_simp [hHne, hXne]
  exact hmul.trans_eq hrewrite

end

end Q0MinorGFormulaRouteA
