/-
  Goldbach/BankBridge.lean

  Goal: derive the bank bound on the working window from your BG pieces:
    • decomposition: (R N) - M N = errTI X N + errBG X N
    • bounds:       |errTI| ≤ δTI,  |errBG| ≤ δBG   on the window
    • calibration:  δTI + δBG ≤ ε * S  (canonical: ε=0.01, S=1)

  This file exports:
    - bank_abs_deviation_canonical
    - bank_lower_canonical

  Adapt only the names on the 3 lines marked [ADAPT] if your BG files use
  different identifiers. Everything else is pure algebra.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.Rep
-- [ADAPT] import the actual BG leaf files that provide the three ingredients:
import Goldbach.BG_Identity
import Goldbach.TypeI_Leak
import Goldbach.BG_Operator
import Goldbach.BG_Calib

namespace Goldbach.BankBridge
open Real
open Goldbach
open Goldbach.Windows
open Goldbach.Rep

noncomputable section

/-- Absolute deviation on the canonical window:
    for X0=10^6, H=10^4, S=1.0, ε=0.01. -/
theorem bank_abs_deviation_canonical
  (X0 := (10^6 : ℕ)) (H := (10^4 : ℕ)) (S := (1.0 : ℝ)) (ε := (0.01 : ℝ))
  (Mproj : ℕ → ℝ)
  : ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
      |(R N : ℝ) - Mproj N| ≤ ε * S := by
  intro X N hX hN
  -- [ADAPT] 1) decomposition of (R - M) into two error channels on the window
  have hdecomp :
    (R N : ℝ) - Mproj N =
      BG_Identity.errTI X N + BG_Operator.errBG X N := by
    simpa using BG_Identity.bank_decomp (X:=X) (N:=N) (Mproj:=Mproj) hX hN
  -- [ADAPT] 2) bounds on each channel on the window
  have hTI : |BG_Identity.errTI X N| ≤ BG_Calib.δTI :=
    TypeI_Leak.errTI_bound (X:=X) (N:=N) hX hN
  have hBG : |BG_Operator.errBG X N| ≤ BG_Calib.δBG :=
    BG_Operator.errBG_bound (X:=X) (N:=N) hX hN
  -- [ADAPT] 3) calibration that adds the envelopes to ε*S
  have hcal : BG_Calib.δTI + BG_Calib.δBG ≤ ε * S := BG_Calib.calibration
  -- triangle + calibration
  calc
    |(R N : ℝ) - Mproj N|
        = |BG_Identity.errTI X N + BG_Operator.errBG X N| := by simpa [hdecomp]
    _   ≤ |BG_Identity.errTI X N| + |BG_Operator.errBG X N| := by
            simpa using abs_add_le_abs_add_abs
              (BG_Identity.errTI X N) (BG_Operator.errBG X N)
    _   ≤ BG_Calib.δTI + BG_Calib.δBG := add_le_add hTI hBG
    _   ≤ ε * S := hcal

/-- One-sided bank inequality `R ≥ M − ε S` derived from the absolute deviation. -/
theorem bank_lower_canonical
  (X0 := (10^6 : ℕ)) (H := (10^4 : ℕ)) (S := (1.0 : ℝ)) (ε := (0.01 : ℝ))
  (Mproj : ℕ → ℝ)
  : ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
      (R N : ℝ) ≥ Mproj N - ε * S := by
  intro X N hX hN
  have habs := bank_abs_deviation_canonical (Mproj:=Mproj) (X:=X) (N:=N) hX hN
  -- |a-b| ≤ t  ⇒  a ≥ b - t
  have hleft : -(ε * S) ≤ (R N : ℝ) - Mproj N := (abs_le.mp habs).1
  have : Mproj N - ε * S ≤ (R N : ℝ) := by
    -- add `Mproj N` to both sides of `-(ε S) ≤ (R N) - Mproj N`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using add_le_add_left hleft (Mproj N)
  exact this

end Goldbach.BankBridge
