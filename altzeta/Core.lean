/-
  Alt-Zeta: core parameters and baseline-conditional data
  Lean 4.25.0-rc2
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Real

namespace AltZeta

/-- A dyadic window [X, 2X] with X>0. -/
structure Window where
  X : ℝ
  hX : 0 < X := by decide
deriving Repr

/-- Canonical schedule parameters for the dyadic window (H,Q,c,B ≥ 0). -/
structure Schedule where
  H Q c B : ℝ
  hH : 0 ≤ H := by decide
  hQ : 0 ≤ Q := by decide
  hc : 0 < c := by decide
  hB : 0 ≤ B := by decide
deriving Repr

/-- Fixed analytic constants in the "ledger": C1 ε_H + C2/H + C3 e^{-B}. -/
structure Ledger where
  C1 C2 C3 : ℝ
  hC1 : 0 ≤ C1 := by decide
  hC2 : 0 ≤ C2 := by decide
  hC3 : 0 ≤ C3 := by decide
deriving Repr

/-- Completion bound `CΓ := sup_x |Γ-side(x)|`. Purely analytic/kernel-dependent. -/
structure CompletionBound where
  CGamma : ℝ
  hCGamma : 0 ≤ CGamma := by decide
deriving Repr

/-- Certified spectral envelope upper bound `S_cert ≥ S`. Source: numeric AP-census or PSD-coercive route. -/
structure EnvelopeCert where
  S_cert : ℝ
  hS : 0 ≤ S_cert := by decide
deriving Repr

/-- Margin (left-hand side of barrier): M_H := c0 - (C1 ε_H + C2/H + C3 e^{-B}). -/
def margin (c0 εH : ℝ) (L : Ledger) (Sch : Schedule) : ℝ :=
  c0 - (L.C1 * εH + L.C2 / max Sch.H 1 + L.C3 * exp (-(Sch.B)))

/-- The baseline barrier inequality at a particular x ∈ [X,2X]. -/
def BarrierHolds (M CGamma x S : ℝ) : Prop :=
  M > CGamma + sqrt x * S

/-- Convenience: choose any x in [X,2X] with X>0; we will not formalize the interval here. -/
def ValidX (W : Window) (x : ℝ) : Prop := (W.X ≤ x) ∧ (x ≤ 2 * W.X) ∧ 0 < x

end AltZeta
