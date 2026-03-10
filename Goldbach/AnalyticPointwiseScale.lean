import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridgeScale
import Goldbach.AnalyticGlobalScale

open Goldbach
open Goldbach.Windows
open Goldbach.Base

namespace Goldbach.Analytic

/--
Scale-sensitive packaged witness.

Compared to `PointwiseWitnessFun`, the lower-margin constant is allowed to vary with the scale
`X`, while `S` and `ε` remain scalar.
-/
structure PointwiseWitnessScale where
  X0 : ℕ
  H : ℕ → ℕ
  S : ℝ
  c0 : ℕ → ℝ
  eps : ℝ
  global :
    ∀ {X : ℕ}, X0 ≤ X →
      Goldbach.Bridge.ClosurePointwiseScale X H S c0 eps

@[simp] abbrev PointwiseWitnessScale.ε (w : PointwiseWitnessScale) : ℝ := w.eps

namespace PointwiseWitnessScale

/-- Build a scale-sensitive witness from the global closure statement. -/
def of_global
    (X0 : ℕ) (H : ℕ → ℕ) (S : ℝ) (c0 : ℕ → ℝ) (eps : ℝ)
    (g : Goldbach.Bridge.GlobalClosurePointwiseScale X0 H S c0 eps) :
    PointwiseWitnessScale :=
  { X0 := X0
    H := H
    S := S
    c0 := c0
    eps := eps
    global := by
      intro X hX
      exact g hX }

/-- Repackage a scale-sensitive analytic hypothesis as a scale-sensitive pointwise witness. -/
def ofAnalytic
    {X0 : ℕ} {H : ℕ → ℕ} {S : ℝ} {c0 : ℕ → ℝ} {eps : ℝ}
    (h : Goldbach.AnalyticHypScale X0 H S c0 eps) :
    PointwiseWitnessScale :=
  of_global X0 H S c0 eps (Goldbach.AnalyticHypScale.globalClosure h)

lemma S_pos (w : PointwiseWitnessScale) : 0 < w.S := by
  exact (w.global (X := w.X0) le_rfl).1

lemma c0_pos (w : PointwiseWitnessScale) {X : ℕ} (hX : w.X0 ≤ X) : 0 < w.c0 X := by
  exact (w.global (X := X) hX).2.1

lemma eps_lt_c0 (w : PointwiseWitnessScale) {X : ℕ} (hX : w.X0 ≤ X) : w.eps < w.c0 X := by
  exact (w.global (X := X) hX).2.2.1

/--
For every even `N ≥ w.X0`, the scale-sensitive witness yields a Goldbach representation.
-/
theorem representable_large
  (w : PointwiseWitnessScale) :
  ∀ {N : ℕ}, IsEven N → w.X0 ≤ N → GoldbachRep N := by
  intro N hEven hX0
  have hpt : Goldbach.Bridge.ClosurePointwiseScale N w.H w.S w.c0 w.eps :=
    w.global (X := N) hX0
  have hmem : N ∈ EvenIn N (w.H N) := Goldbach.Windows.mem_EvenIn_self hEven
  exact Goldbach.Bridge.closurePointwiseScale_to_rep hpt hmem

end PointwiseWitnessScale
end Goldbach.Analytic
