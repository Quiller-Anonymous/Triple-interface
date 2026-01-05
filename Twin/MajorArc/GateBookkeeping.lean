/-
  Twin/MajorArc/GateBookkeeping.lean

  Paper §14.1 “bookkeeping layer”:
  separate the (deep) major-arc lower bound from the (formal) transfer to the
  localized twin mass plus explicit error channels, and prove that these two
  together imply the `AnalyticCore.GateOnWindow` inequality used downstream.
-/
import Mathlib
import Twin.GoalAPI
import Twin.SingularSeries
import Twin.Bridge
import Twin.Ledger
import Twin.AnalyticCore

noncomputable section

namespace Twin.MajorArc

open Twin
open Twin.GoalAPI

/-- A major-arc lower bound on an auxiliary (windowed) quantity `majMass X`.
This is the part supplied by §11.2 (Siegel–Walfisz window) + §14.2 (pinned majors). -/
structure MajorArcLower (P : Params) (majMass : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
        ≤ majMass X
          + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3

namespace MajorArcLower

variable {P : Params}

/-- A canonical major-arc mass that makes the lower bound inequality tautological. -/
def constMajMass (P : Params) : ℕ → ℝ :=
  fun _ => (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)

/-- The `MajorArcLower` inequality holds for `constMajMass` by nonnegativity of the tail cap. -/
theorem constMajMass_lower (P : Params) : MajorArcLower P (constMajMass P) := by
  refine ⟨?_⟩
  intro X hX
  have eps_nonneg : 0 ≤ P.eps := P.eps_nonneg
  have ss_nonneg : 0 ≤ Twin.truncSingularSeries P.S :=
    Twin.truncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
  have hH_nonneg : 0 ≤ ((P.H : ℝ) + 1) := by
    have : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    linarith
  have tail_nonneg :
      0 ≤ (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3 := by
    have : 0 ≤ (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) :=
      mul_nonneg (mul_nonneg eps_nonneg ss_nonneg) hH_nonneg
    exact div_nonneg this (by norm_num)
  -- `main ≤ main + tail` (equivalent to `0 ≤ tail`)
  have hmain :
      (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
        ≤ (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
          + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3 := by
    linarith
  simpa [constMajMass, add_assoc, add_comm, add_left_comm] using hmain

end MajorArcLower

/-- Transfer: relate the auxiliary major-arc quantity `majMass X` to the localized
twin mass plus explicit error channels (`emin`, `eds`).

This is the “routing/plumbing” part of §14.1–§14.2: turning the analytic major-arc
expression into the localized mass plus remainder terms. -/
structure MajorArcTransfer (P : Params) (emin eds : ℕ → ℝ) (majMass : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      majMass X
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds

namespace MajorArcTransfer

variable {P : Params}

/-- A canonical choice of major-arc mass that makes the transfer inequality tautological. -/
def routedMajMass (P : Params) (emin eds : ℕ → ℝ) : ℕ → ℝ :=
  fun X =>
    Twin.Bridge.localizedTwinMass X P.H
      + Twin.Ledger.windowSum X P.H emin
      + Twin.Ledger.windowSum X P.H eds

/-- The transfer inequality holds for `routedMajMass` by reflexivity. -/
theorem routedMajMass_transfer (P : Params) (emin eds : ℕ → ℝ) :
    MajorArcTransfer P emin eds (routedMajMass P emin eds) := by
  refine ⟨?_⟩
  intro X hX
  exact le_rfl

end MajorArcTransfer

/-- Pure bookkeeping: combine a major-arc lower bound and a transfer inequality
to obtain the on-window gate inequality used by the pipeline. -/
theorem gate_onWindow_of_majorArc
  {P : Params} {emin eds : ℕ → ℝ} {majMass : ℕ → ℝ}
  (hLower : MajorArcLower P majMass)
  (hTrans : MajorArcTransfer P emin eds majMass) :
  Twin.AnalyticCore.GateOnWindow P emin eds :=
by
  classical
  refine ⟨?_⟩
  intro X hX
  have h1 := hLower.bound (X := X) hX
  have h2 := hTrans.bound (X := X) hX
  -- add the common tail-cap term to the transfer inequality
  have h2' :
      majMass X
        + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
          + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3 := by
    simpa [add_assoc, add_comm, add_left_comm] using
      add_le_add_right h2 ((P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3)
  exact le_trans h1 (by simpa [add_assoc, add_comm, add_left_comm] using h2')

end Twin.MajorArc
