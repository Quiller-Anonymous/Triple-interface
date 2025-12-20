-- FiniteConditional.lean
/-
  Smoke tests for the finite-conditional pipeline.
  No `main` here (library-only build).
-/
import Mathlib
import Goldbach.Final
import Goldbach.BuildWitness
import Goldbach.FiniteBase
import Goldbach.AnalyticPointwise
import Goldbach.Windows

open Goldbach
open Goldbach.Analytic

/-- Fix the canonical analytic witness in scope. -/
abbrev W : PointwiseWitness := Goldbach.BuildWitness.canonical

/-- Large-`N` consequence of the witness alone (no finite base needed). -/
theorem _finiteConditional_largeN :
  ∀ N, W.X0 ≤ N → Goldbach.Windows.IsEven N →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  intro N hX0 hE
  simpa using
    (Goldbach.Analytic.PointwiseWitness.representable_large
      (w := W) hE hX0)

/-- Finite-conditional: keep evenness for a concrete `N` as an explicit hypothesis. -/
theorem _finiteConditional_N10
  (finiteBase : Goldbach.FiniteBase.Cert W.X0)
  (hE10 : Goldbach.Windows.IsEven 10) :
  ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 10 := by
  -- Turn the certificate into the `FiniteBaseUpTo` form expected by `goldbach_final`.
  have finiteBaseUpTo :
      Goldbach.Base.FiniteBaseUpTo W.X0 := by
    intro N hEven h4 hN
    have hWin : Goldbach.Windows.IsEven N :=
      Goldbach.Windows.isEven_of_even hEven
    exact finiteBase hWin h4 hN
  -- Combine the analytic witness with the finite base.
  have H := Goldbach.Final.goldbach_final (w := W) finiteBaseUpTo
  have hEven10 : Even 10 := Goldbach.Windows.even_of_isEven hE10
  have h4 : 4 ≤ 10 := by decide
  simpa using H (N := 10) hEven10 h4
