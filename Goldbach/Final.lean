import Mathlib
import Goldbach.AnalyticPointwise
import Goldbach.ClosureBridge
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
-- import Goldbach.FiniteBase.UseGenerated  -- gives FiniteBase.lookup/base_000004_100000 if you have it

open scoped Real
open Goldbach
open Goldbach.Analytic
open Goldbach.Bridge
open Goldbach.Base
open Windows

namespace Goldbach

/-- Main finite-conditional theorem: for any `w : PointwiseWitness` and a finite base up to `w.X0`,
    every even `N ≥ 4` has a Goldbach representation. -/
theorem goldbach_final (w : PointwiseWitness) (hBase : FiniteBaseUpTo w.X0) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro N hEven h4
  by_cases hSmall : N ≤ w.X0
  ·
    -- Small range: discharge via the finite base
    -- FiniteBaseUpTo X0 is `FiniteBaseOn 4 X0`, i.e.
    --   ∀ N, Even N → 4 ≤ N → N ≤ X0 → GoldbachRep N
    exact hBase hEven h4 hSmall
  ·
    -- Large range: use the pointwise closure witness
    have hX : w.X0 ≤ N := le_of_not_le hSmall
    have hcl : ClosurePointwise N w.H w.S w.c0 w.ε := w.global hX

    -- Supply window-membership that `closurePointwise_to_rep` expects.
    -- If you already have a helper lemma in `Windows.lean` like
    --   `mem_evenIn_self : Even N → N ∈ EvenIn N H`
    -- then the next two lines can be replaced by:
    --   have hWin : N ∈ EvenIn N w.H := mem_evenIn_self (H := w.H) hEven

    -- Generic construction (works if `EvenIn N H` is defined as
    -- `IccShift N H ∧ IsEven N`):
    have hIn  : N ∈ IccShift N w.H := memIccShift_self (N := N) (H := w.H)
    have hWin : N ∈ EvenIn N w.H := ⟨hIn, hEven⟩

    -- Bridge: closure ⇒ representation at the window center
    exact closurePointwise_to_rep (N := N) (H := w.H) hcl hWin

end Goldbach
