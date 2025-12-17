/-
  ETI: transparent, integrated arithmetic dependency (E1)–(E3).
  (E4) optional; baseline path does not use it.
-/
import Mathlib.Data.Real.Basic
import AltZeta.Core

noncomputable section
open AltZeta

namespace AltZeta

/-- ETI(E1–E3) data on a dyadic window `[X,2X]`. -/
structure ETI where
  W  : Window
  Sch : Schedule
  /- (E1) pin level -/
  c0 : ℝ
  hc0 : 0 < c0
  /- (E2) ledger/variance scale (canonical or better) -/
  εH : ℝ
  hε : 0 ≤ εH
  /- (E3) masked short-shift uniformity constant (not used directly here, but recorded). -/
  C_AO_SSU : ℝ
  hAOSSU : 1 ≤ C_AO_SSU
deriving Repr

/-- Baseline ledger using ETI's pin and variance scale. -/
def ETI.margin (E : ETI) (L : Ledger) : ℝ :=
  margin E.c0 E.εH L E.Sch

end AltZeta
