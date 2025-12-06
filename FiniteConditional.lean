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
  -- Final theorem takes a witness + finite base and yields all even N ≥ 4
  have H := Goldbach.Final.goldbach_unconditional (w := W) finiteBase
  have h4 : 4 ≤ 10 := by decide
  simpa using H (N := 10) hE10 h4
