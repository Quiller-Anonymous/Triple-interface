-- Goldbach/Final.lean
/-
  Finite-conditional Goldbach: combine a pointwise witness with
  a finite base certificate.
-/
import Mathlib
import Goldbach.AnalyticPointwise
import Goldbach.ClosureBridge
import Goldbach.FiniteBase
import Goldbach.Windows

namespace Goldbach.Final

open Goldbach
open Goldbach.Analytic
open Goldbach.Bridge

/-- Finite-conditional Goldbach: small `N` via finite base, large `N` via witness. -/
theorem goldbach_unconditional
  (w : PointwiseWitness)
  (finiteBase : Goldbach.FiniteBase.Cert w.X0) :
  ∀ ⦃N : ℕ⦄, Goldbach.Windows.IsEven N → 4 ≤ N →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N :=
by
  intro N hE h4
  exact Goldbach.Bridge.goldbach_from_global_pointwise
    (finiteBase := finiteBase) (gclosure := w.global) hE h4

end Goldbach.Final
