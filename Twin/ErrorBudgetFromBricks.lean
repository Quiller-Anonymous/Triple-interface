/-
  Twin/ErrorBudgetFromBricks.lean
  From the bricks (CLS + desmooth budgets and tail cap) to the window ErrorBudget.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperBricks
import Twin.TargetsFromBricks
import Twin.SingularSeries
import Twin.Ledger
import Twin.LedgerExtra

noncomputable section

namespace Twin.ErrorBudgetFromBricks

open Twin
open Twin.GoalAPI
open Twin.PaperBricks
open Twin.LedgerExtra
open Twin.TargetsFromBricks  -- for withErr / errFrom

/-- From the paper bricks, the window-summed error budget for the derived `err`. -/
theorem errorBudget_from_bricks {P : Params} (b : Bricks P) :
  ErrorBudget (withErr P (errFrom P b)) := by
  intro X hX
  -- Decompose the window-sum of `errFrom` into three pieces.
  have h_add1 :
    Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n| + b.E.eds n)
      = Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
        + Twin.Ledger.windowSum X P.H (b.E.eds) := by
    simpa using
      Twin.LedgerExtra.windowSum_add (X := X) (H := P.H)
        (f := fun n => |b.E.emin n|) (g := fun n => b.E.eds n)

  have h_add2 :
    Twin.Ledger.windowSum X P.H
        (fun n => |b.E.emin n| + b.E.eds n + (P.eps * truncSingularSeries P.S) / 3)
      = Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n| + b.E.eds n)
        + Twin.Ledger.windowSum X P.H (fun _ => (P.eps * truncSingularSeries P.S) / 3) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      Twin.LedgerExtra.windowSum_add (X := X) (H := P.H)
        (f := fun n => |b.E.emin n| + b.E.eds n)
        (g := fun _ => (P.eps * truncSingularSeries P.S) / 3)

  have h_decomp :
    Twin.Ledger.windowSum X P.H (errFrom P b)
      = (Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
         + Twin.Ledger.windowSum X P.H (b.E.eds))
        + Twin.Ledger.windowSum X P.H (fun _ => (P.eps * truncSingularSeries P.S) / 3) := by
    unfold errFrom
    have := h_add2
    simpa [add_comm, add_left_comm, add_assoc, h_add1] using this

  -- Bounds for each piece.
  have h_cls : Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
      ≤ P.eps * truncSingularSeries P.S * (P.H + 1) / 3 :=
    b.cls_budget (X := X) hX

  have h_ds  : Twin.Ledger.windowSum X P.H (b.E.eds)
      ≤ P.eps * truncSingularSeries P.S * (P.H + 1) / 3 :=
    b.desmooth_budget (X := X) hX

  have h_tail_eq :
      Twin.Ledger.windowSum X P.H (fun _ => (P.eps * truncSingularSeries P.S) / 3)
        = (P.H + 1 : ℝ) * ((P.eps * truncSingularSeries P.S) / 3) := by
    simpa using
      Twin.LedgerExtra.windowSum_const (X := X) (H := P.H)
        (c := (P.eps * truncSingularSeries P.S) / 3)

  have h_tail_le :
      Twin.Ledger.windowSum X P.H (fun _ => (P.eps * truncSingularSeries P.S) / 3)
        ≤ P.eps * truncSingularSeries P.S * (P.H + 1) / 3 := by
    -- Just rewrite to match the budget shape.
    have : P.eps * truncSingularSeries P.S * (P.H + 1) / 3
          = (P.H + 1 : ℝ) * ((P.eps * truncSingularSeries P.S) / 3) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [this] using (le_of_eq h_tail_eq)

  -- Sum the three budgets (each ≤ one third).
  have h_sum_le :
      (Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
       + Twin.Ledger.windowSum X P.H (b.E.eds))
       + Twin.Ledger.windowSum X P.H (fun _ => (P.eps * truncSingularSeries P.S) / 3)
        ≤ (P.eps * truncSingularSeries P.S * (P.H + 1) / 3)
          + (P.eps * truncSingularSeries P.S * (P.H + 1) / 3)
          + (P.eps * truncSingularSeries P.S * (P.H + 1) / 3) := by
    exact add_le_add (add_le_add h_cls h_ds) h_tail_le

  -- Convert "three thirds" to "one".
  have h_thirds : ((1 : ℝ) / 3 + 1/3 + 1/3) = (1 : ℝ) := by
    norm_num
  have h_rhs_eq :
      (P.eps * truncSingularSeries P.S * (P.H + 1) / 3)
      + (P.eps * truncSingularSeries P.S * (P.H + 1) / 3)
      + (P.eps * truncSingularSeries P.S * (P.H + 1) / 3)
      = P.eps * truncSingularSeries P.S * (P.H + 1) := by
    -- Factor and use h_thirds
    set c : ℝ := P.eps * truncSingularSeries P.S * (P.H + 1) with hc
    -- (c/3 + c/3 + c/3) = c * (1/3 + 1/3 + 1/3) = c
    calc c / 3 + c / 3 + c / 3
        = c * (1/3 : ℝ) + c * (1/3) + c * (1/3) := by simp [div_eq_mul_inv]
      _ = c * (1/3 + 1/3 + 1/3) := by ring
      _ = c * 1 := by rw [h_thirds]
      _ = c := by ring

  -- Conclude the target bound.
  have : Twin.Ledger.windowSum X P.H (errFrom P b)
      ≤ P.eps * truncSingularSeries P.S * (P.H + 1) := by
    -- Use the decomposition equality, then rewrite the RHS sum of thirds to a single term.
    have := h_sum_le
    simpa [h_decomp, h_rhs_eq] using this

  -- This is exactly the GoalAPI ErrorBudget inequality for `withErr P (errFrom P b)`.
  simpa [withErr] using this

end Twin.ErrorBudgetFromBricks
