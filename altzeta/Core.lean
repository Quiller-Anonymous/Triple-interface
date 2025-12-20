/-
  Alt-Zeta: core parameters and baseline-conditional data
  Lean 4.25.0-rc2
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace AltZeta

/-- A dyadic window [X, 2X] with X>0. -/
structure Window where
  X : ℝ
  hX : 0 < X

structure Schedule where
  H : ℝ
  Q : ℝ
  c : ℝ
  B : ℝ
  hH : 0 ≤ H
  hQ : 0 ≤ Q
  hc : 0 < c
  hB : 0 ≤ B

structure Ledger where
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  hC1 : 0 ≤ C1
  hC2 : 0 ≤ C2
  hC3 : 0 ≤ C3

structure CompletionBound where
  CGamma : ℝ
  hCGamma : 0 ≤ CGamma

structure EnvelopeCert where
  S_cert : ℝ
  hS : 0 ≤ S_cert

open scoped BigOperators
open Real

/-- Margin (left-hand side of barrier): M_H := c0 - (C1 ε_H + C2/H + C3 e^{-B}). -/
noncomputable def margin (c0 εH : ℝ) (L : Ledger) (Sch : Schedule) : ℝ :=
  c0 - (L.C1 * εH + L.C2 / max Sch.H 1 + L.C3 * exp (-(Sch.B)))

/-- The baseline barrier inequality at a particular x ∈ [X,2X]. -/
noncomputable def BarrierHolds (M CGamma x S : ℝ) : Prop :=
  M > CGamma + sqrt x * S

/-- Convenience: choose any x in [X,2X] with X>0; we will not formalize the interval here. -/
def ValidX (W : Window) (x : ℝ) : Prop := (W.X ≤ x) ∧ (x ≤ 2 * W.X) ∧ 0 < x

end AltZeta
