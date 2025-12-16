-- Goldbach/Params.lean
import Mathlib  -- Real.rpow, log, etc.

open Real

/-! # Shared Parameters -/

/-- Global parameters used to define analytic scales. -/
structure GoldbachParams where
  A : ℝ
  gamma : ℝ
  h_A : A ≥ 10
  h_gamma : 0 < gamma ∧ gamma < (1 : ℝ) / 2

/-- Window scale `H(X) = (log X)^A`. Uses real exponentiation `Real.rpow`. -/
noncomputable def H_scale (p : GoldbachParams) (X : ℝ) : ℝ :=
  Real.rpow (Real.log X) p.A

/-- Auxiliary scale `Q(X) = H(X)^γ`. -/
noncomputable def Q_scale (p : GoldbachParams) (X : ℝ) : ℝ :=
  Real.rpow (H_scale p X) p.gamma

def X0 : Nat := 100000
