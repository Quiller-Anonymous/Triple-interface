/-
  Goldbach/TypeI_Leak.lean

  Type–I leakage: with `errTI = 0` (current bank identity choice),
  both the windowwise bound and calibration are proved.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.BG_Identity  -- for errTI

namespace Goldbach.BG_Tenor

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.BG_Tenor

/-- Type–I envelope (current placeholder) is 0. -/
def δTI (X : ℕ) : ℝ := 0

/-- Proven windowwise bound for Type–I channel (trivial with δTI=0).
    We use the canonical cutoff `U = H` in `BG_Identity.errTI`. -/
theorem errTI_bound :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    |BG_Identity.errTI H X N| ≤ δTI X := by
  intro X N _hX _hN
  have h0 : |BG_Identity.errTI H X N| = 0 := by
    simp [BG_Identity.errTI, BG_Identity.outerBand]
  simpa [δTI] using (le_of_eq h0)

/-- Calibration for Type–I (trivial with δTI=0). -/
theorem δTI_calib : ∀ {X : ℕ}, X0 ≤ X → δTI X ≤ (0.004 : ℝ) := by
  intro X _hX
  simpa [δTI] using (show (0 : ℝ) ≤ 0.004 by norm_num)

end Goldbach.BG_Tenor
