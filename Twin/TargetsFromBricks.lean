/-
  Twin/TargetsFromBricks.lean
  From the paper bricks to the GoalAPI targets.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperBricks
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger

noncomputable section

namespace Twin.TargetsFromBricks

open Twin
open Twin.GoalAPI
open Twin.PaperBricks

/-- Replace the `err` field of a Params record. -/
def withErr (P : Params) (err' : ℕ → ℝ) : Params := { P with err := err' }

/-- The error profile built from the bricks: |emin| + eds + constant tail cap. -/
def errFrom (P : Params) (b : Bricks P) : ℕ → ℝ :=
  fun n => (b.E.absEmin n) + (b.E.eds n) + (P.eps * truncSingularSeries P.S) / 3

/-!
With the *window-sum* gate, the natural downstream target is positivity of the
localized twin mass. This is enough to produce a twin pair in the window via
`Twin.Bridge.existsTwin_of_mass_pos`.
-/

/-- The localized twin mass is strictly positive in each large window, provided
the bricks’ three budgets each contribute ≤ one third of the main term. -/
theorem localizedTwinMass_pos_from_bricks
  {P : Params} (b : Bricks P)
  (ss_pos : 0 < truncSingularSeries P.S)
  (eps_lt_half : P.eps < (1 : ℝ) / 2) :
  ∀ {X : ℕ}, P.X0 ≤ X → 0 < Twin.Bridge.localizedTwinMass X P.H := by
  classical
  intro X hX
  set SS : ℝ := truncSingularSeries P.S
  set t  : ℝ := P.eps * SS * (P.H + 1) / 3
  set mass : ℝ := Twin.Bridge.localizedTwinMass X P.H

  have hem_le :
      Twin.Ledger.windowSum X P.H b.E.emin
        ≤ Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|) := by
    unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
    refine Finset.sum_le_sum ?_
    intro k hk
    simpa using le_abs_self (b.E.emin (X + k))

  -- Gate: (1-ε)·SS·(H+1) ≤ mass + windowSum emin + windowSum eds + t
  have hgate := b.gate_major (X := X) hX

  have hgate' :
      (1 - P.eps) * SS * (P.H + 1)
        ≤ mass
          + Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
          + Twin.Ledger.windowSum X P.H b.E.eds
          + t := by
    have hrhs_le :
        mass + Twin.Ledger.windowSum X P.H b.E.emin
              + Twin.Ledger.windowSum X P.H b.E.eds
              + t
          ≤ mass + Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
              + Twin.Ledger.windowSum X P.H b.E.eds
              + t := by
      have := add_le_add_left hem_le (mass + Twin.Ledger.windowSum X P.H b.E.eds + t)
      simpa [add_assoc, add_comm, add_left_comm] using this
    have hgate'' :
        (1 - P.eps) * SS * (P.H + 1)
          ≤ mass + Twin.Ledger.windowSum X P.H b.E.emin
              + Twin.Ledger.windowSum X P.H b.E.eds
              + t := by
      simpa [SS, t, mass, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
        using hgate
    exact le_trans hgate'' hrhs_le

  -- Budget bounds for the two windowed error terms
  have h_cls :
      Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|) ≤ t := by
    simpa [SS, t, mul_assoc, mul_comm, mul_left_comm] using b.cls_budget (X := X) hX

  have h_ds :
      Twin.Ledger.windowSum X P.H b.E.eds ≤ t := by
    simpa [SS, t, mul_assoc, mul_comm, mul_left_comm] using b.desmooth_budget (X := X) hX

  -- Thus the total window error ≤ ε·SS·(H+1)
  have hErr_le :
      Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
        + Twin.Ledger.windowSum X P.H b.E.eds
        + t
        ≤ P.eps * SS * (P.H + 1) := by
    have : t + t + t = P.eps * SS * (P.H + 1) := by
      -- (c/3 + c/3 + c/3) = c
      set c : ℝ := P.eps * SS * (P.H + 1) with hc
      calc
        t + t + t = c / 3 + c / 3 + c / 3 := by simp [t, hc, div_eq_mul_inv, mul_assoc]
        _ = c := by ring
        _ = P.eps * SS * (P.H + 1) := by simp [hc]
    have hsum_le :
        Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
          + Twin.Ledger.windowSum X P.H b.E.eds
          + t
          ≤ t + t + t := by
      have h12 :
          Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
            + Twin.Ledger.windowSum X P.H b.E.eds
            ≤ t + t :=
        add_le_add h_cls h_ds
      have := add_le_add_right h12 t
      simpa [add_assoc, add_comm, add_left_comm] using this
    exact le_trans hsum_le (le_of_eq this)

  -- Rearrange: mass ≥ (1-ε)·SS·(H+1) - (window errors)
  have hmass_ge :
      (1 - P.eps) * SS * (P.H + 1)
        - (Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
            + Twin.Ledger.windowSum X P.H b.E.eds
            + t)
        ≤ mass := by
    -- `a ≤ mass + b` ↔ `a - b ≤ mass`
    have : (1 - P.eps) * SS * (P.H + 1)
        ≤ mass + (Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
            + Twin.Ledger.windowSum X P.H b.E.eds + t) := by
      simpa [mass, add_assoc, add_comm, add_left_comm] using hgate'
    exact (sub_le_iff_le_add).2 (by simpa [add_assoc, add_comm, add_left_comm] using this)

  -- Clean lower bound: ≥ (1 - 2ε)·SS·(H+1)
  have hclean :
      (1 - (2 * P.eps)) * SS * (P.H + 1)
        ≤ (1 - P.eps) * SS * (P.H + 1)
          - (Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
              + Twin.Ledger.windowSum X P.H b.E.eds
              + t) := by
    have : (1 - (2 * P.eps)) * SS * (P.H + 1)
        = (1 - P.eps) * SS * (P.H + 1) - (P.eps * SS * (P.H + 1)) := by ring
    -- use `err ≤ ε·SS·(H+1)` to get `-err ≥ -ε·SS·(H+1)`
    have hsub :
        (1 - P.eps) * SS * (P.H + 1)
          - (P.eps * SS * (P.H + 1))
        ≤ (1 - P.eps) * SS * (P.H + 1)
          - (Twin.Ledger.windowSum X P.H (fun n => |b.E.emin n|)
              + Twin.Ledger.windowSum X P.H b.E.eds
              + t) := by
      exact sub_le_sub_left hErr_le ((1 - P.eps) * SS * (P.H + 1))
    simpa [this] using hsub

  have hmass_lower : (1 - (2 * P.eps)) * SS * (P.H + 1) ≤ mass :=
    le_trans hclean hmass_ge

  -- positivity of the clean lower bound
  have h_one_minus_two_eps : 0 < 1 - (2 * P.eps) := by
    have : 2 * P.eps < 1 := by linarith
    linarith
  have hHpos : 0 < (P.H + 1 : ℝ) := by exact_mod_cast Nat.succ_pos P.H
  have hpos_clean : 0 < (1 - (2 * P.eps)) * SS * (P.H + 1) :=
    mul_pos (mul_pos h_one_minus_two_eps ss_pos) hHpos

  -- conclude mass > 0
  exact lt_of_lt_of_le hpos_clean hmass_lower

end Twin.TargetsFromBricks
