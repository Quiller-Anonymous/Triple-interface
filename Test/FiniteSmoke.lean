-- Test/FiniteSmoke.lean
import Mathlib
import Goldbach.Final
import Goldbach.BuildWitness
import Goldbach.FiniteBase
import Goldbach.Windows
import Goldbach.AnalyticAssemble   -- builds AnalyticHyp
import Goldbach.TenorCanon         -- for Mcanon

open Goldbach
open Goldbach.Analytic
open Goldbach.Windows

noncomputable abbrev AH
  : AnalyticHyp (10^6) (10^4) 1.0 (0.05) (0.01) :=
  Goldbach.AnalyticAssemble.canonical (M := Goldbach.TenorCanon.Mcanon)

noncomputable abbrev W : PointwiseWitness :=
  Goldbach.BuildWitness.canonical AH

theorem _smoke_2024
  (finiteBase : Goldbach.FiniteBase.Cert W.X0)
  (hE : Goldbach.Windows.IsEven 2024 := by decide) :
  ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2024 := by
  have H := Goldbach.Final.goldbach_unconditional (w := W) finiteBase
  have h4 : 4 ≤ 2024 := by decide
  simpa using H (N := 2024) hE h4
