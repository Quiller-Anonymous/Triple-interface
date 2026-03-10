import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridgeScaleNorm
import Goldbach.AnalyticGlobalScaleNorm

open Goldbach
open Goldbach.Windows
open Goldbach.Base

namespace Goldbach.Analytic

/-- Packaged witness for the variable-scale normalization route. -/
structure PointwiseWitnessScaleNorm where
  X0 : ℕ
  H : ℕ → ℕ
  S : ℕ → ℝ
  c0 : ℕ → ℝ
  eps : ℝ
  global :
    ∀ {X : ℕ}, X0 ≤ X →
      Goldbach.Bridge.ClosurePointwiseScaleNorm X H S c0 eps

@[simp] abbrev PointwiseWitnessScaleNorm.ε (w : PointwiseWitnessScaleNorm) : ℝ := w.eps

namespace PointwiseWitnessScaleNorm

def of_global
    (X0 : ℕ) (H : ℕ → ℕ) (S c0 : ℕ → ℝ) (eps : ℝ)
    (g : Goldbach.Bridge.GlobalClosurePointwiseScaleNorm X0 H S c0 eps) :
    PointwiseWitnessScaleNorm :=
  { X0 := X0
    H := H
    S := S
    c0 := c0
    eps := eps
    global := by
      intro X hX
      exact g hX }

def ofAnalytic
    {X0 : ℕ} {H : ℕ → ℕ} {S c0 : ℕ → ℝ} {eps : ℝ}
    (h : Goldbach.AnalyticHypScaleNorm X0 H S c0 eps) :
    PointwiseWitnessScaleNorm :=
  of_global X0 H S c0 eps (Goldbach.AnalyticHypScaleNorm.globalClosure h)

lemma S_pos (w : PointwiseWitnessScaleNorm) {X : ℕ} (hX : w.X0 ≤ X) : 0 < w.S X := by
  exact (w.global (X := X) hX).1

lemma c0_pos (w : PointwiseWitnessScaleNorm) {X : ℕ} (hX : w.X0 ≤ X) : 0 < w.c0 X := by
  exact (w.global (X := X) hX).2.1

lemma eps_lt_c0 (w : PointwiseWitnessScaleNorm) {X : ℕ} (hX : w.X0 ≤ X) : w.eps < w.c0 X := by
  exact (w.global (X := X) hX).2.2.1

theorem representable_large
  (w : PointwiseWitnessScaleNorm) :
  ∀ {N : ℕ}, IsEven N → w.X0 ≤ N → GoldbachRep N := by
  intro N hEven hX0
  have hpt : Goldbach.Bridge.ClosurePointwiseScaleNorm N w.H w.S w.c0 w.eps :=
    w.global (X := N) hX0
  have hmem : N ∈ EvenIn N (w.H N) := Goldbach.Windows.mem_EvenIn_self hEven
  exact Goldbach.Bridge.closurePointwiseScaleNorm_to_rep hpt hmem

end PointwiseWitnessScaleNorm
end Goldbach.Analytic

