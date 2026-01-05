import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridgeTenor

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.BridgeTenor
open Goldbach.Base

namespace Goldbach

/-- Tenor-aligned pointwise witness: same shape as `Analytic.PointwiseWitness`, but for
`ClosurePointwiseTenor` (i.e. using `R_bank_tenorPrime`). -/
structure PointwiseWitnessTenor where
  X0 : ℕ
  H : ℕ
  S : ℝ
  c0 : ℝ
  ε : ℝ
  hX0 : BankParams.X0 ≤ X0
  global : ∀ {X : ℕ}, X0 ≤ X → ClosurePointwiseTenor X H S c0 ε

/-- Final finite-conditional statement (Tenor-aligned closure): small cases by finite base,
large by pointwise Tenor closure. -/
theorem goldbach_final_tenor (w : PointwiseWitnessTenor) (hBase : FiniteBaseUpTo w.X0) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro N hEven h4
  by_cases hSmall : N ≤ w.X0
  · exact hBase hEven h4 hSmall
  ·
    have hX : w.X0 ≤ N := le_of_not_ge hSmall
    have hcl : ClosurePointwiseTenor N w.H w.S w.c0 w.ε := w.global hX
    have hX' : BankParams.X0 ≤ N := le_trans w.hX0 hX
    have hEven' : IsEven N := isEven_of_even hEven
    have hWin : N ∈ EvenIn N w.H := mem_EvenIn_self (N := N) (H := w.H) hEven'
    exact closurePointwiseTenor_to_rep (X := N) (H := w.H) (S := w.S) (c0 := w.c0) (ε := w.ε)
      hcl hX' hWin

end Goldbach
