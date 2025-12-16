import Mathlib
import Goldbach.AnalyticPointwise
import Goldbach.ClosureBridge
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
import Goldbach.FiniteBase.UseGenerated
import Goldbach.FiniteBase.FromGenerated
import Goldbach.FiniteBase.Generated_real_Proofs

open Goldbach
open Goldbach.Analytic
open Goldbach.Bridge
open Goldbach.Windows
open Goldbach.Base
open Goldbach.FiniteBase

/-- Final (finite-conditional) statement:
    either handled by the finite base for small N, or by closure+bridge for large N. -/
theorem goldbach_final
  (w : PointwiseWitness)
  (hBase : FiniteBaseUpTo w.X0) :
∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
intro N hEven h4

have hBase : FiniteBaseUpTo w.X0 :=
  (Goldbach.FiniteBase.base_000004_100000).mono_right
    (hle := by exact ?_)   -- if you ever need to extend the upper bound
-- (Most of the time you won’t need `mono_right` here: `goldbach_final`
-- directly consumes `FiniteBaseUpTo w.X0`.)

by_cases hSmall : N ≤ Goldbach.FiniteBase.HI
  · -- small range: finite base handles it
    exact hBase hEven h4 hSmall
  · -- large range: use the analytic witness (PointwiseWitness) + closure bridge
    have hX : w.X0 ≤ N := by
      -- your monotonicity logic to ensure you can apply `w.global` at X = N
      ...
    have hcl : ClosurePointwise N w.H w.S w.c0 w.ε := w.global hX
    exact closurePointwise_to_rep hcl ⟨..., ...⟩ -- your window-membership facts

  -- from your `Even N` hypothesis
  have hEvenWin : Windows.IsEven N := isEven_of_even hEven

  -- `N` is always in its own centered window
  have hIn : N ∈ Windows.IccShift N w.H := self_mem_IccShift N w.H

  -- therefore in the even-filtered window
  have hWin : N ∈ Windows.EvenIn N w.H :=
    mem_EvenIn_of_mem_IccShift_and_even hIn hEvenWin

  exact closurePointwise_to_rep (X := N) (H := w.H) (S := w.S) (c0 := w.c0) (ε := w.ε) hcl hWin

/-- Finite base: every even N in [4, 100000] has a Goldbach representation. -/
theorem base_000004_100000 : FiniteBaseOn 4 100000 := by
  -- This should be a thin wrapper around your stitched table correctness.
  -- If your `Generated_real` exposes `rep_in_range : ... → GoldbachRep N`,
  -- then:
  intro N hEven h4 hNle
  exact Generated_real_Proofs.rep_in_range hEven h4 hNle
