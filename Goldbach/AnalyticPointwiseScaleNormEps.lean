import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridgeScaleNormEps
import Goldbach.AnalyticGlobalScaleNormEps

open Goldbach
open Goldbach.Windows
open Goldbach.Base

namespace Goldbach.Analytic

/-- Packaged witness for the variable-scale, variable-slack normalization route. -/
structure PointwiseWitnessScaleNormEps where
  X0 : ℕ
  H : ℕ → ℕ
  S : ℕ → ℝ
  c0 : ℕ → ℝ
  eps : ℕ → ℝ
  global :
    ∀ {X : ℕ}, X0 ≤ X →
      Goldbach.Bridge.ClosurePointwiseScaleNormEps X H S c0 eps

namespace PointwiseWitnessScaleNormEps

def of_global
    (X0 : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ)
    (g : Goldbach.Bridge.GlobalClosurePointwiseScaleNormEps X0 H S c0 eps) :
    PointwiseWitnessScaleNormEps :=
  { X0 := X0
    H := H
    S := S
    c0 := c0
    eps := eps
    global := by
      intro X hX
      exact g hX }

def ofAnalytic
    {X0 : ℕ} {H : ℕ → ℕ} {S c0 eps : ℕ → ℝ}
    (h : Goldbach.AnalyticHypScaleNormEps X0 H S c0 eps) :
    PointwiseWitnessScaleNormEps :=
  of_global X0 H S c0 eps (Goldbach.AnalyticHypScaleNormEps.globalClosure h)

lemma S_pos (w : PointwiseWitnessScaleNormEps) {X : ℕ} (hX : w.X0 ≤ X) : 0 < w.S X := by
  exact (w.global (X := X) hX).1

lemma c0_pos (w : PointwiseWitnessScaleNormEps) {X : ℕ} (hX : w.X0 ≤ X) : 0 < w.c0 X := by
  exact (w.global (X := X) hX).2.1

lemma eps_lt_c0 (w : PointwiseWitnessScaleNormEps) {X : ℕ} (hX : w.X0 ≤ X) :
    w.eps X < w.c0 X := by
  exact (w.global (X := X) hX).2.2.1

theorem representable_large
  (w : PointwiseWitnessScaleNormEps) :
  ∀ {N : ℕ}, IsEven N → w.X0 ≤ N → GoldbachRep N := by
  intro N hEven hX0
  have hpt : Goldbach.Bridge.ClosurePointwiseScaleNormEps N w.H w.S w.c0 w.eps :=
    w.global (X := N) hX0
  have hmem : N ∈ EvenIn N (w.H N) := Goldbach.Windows.mem_EvenIn_self hEven
  exact Goldbach.Bridge.closurePointwiseScaleNormEps_to_rep hpt hmem

end PointwiseWitnessScaleNormEps
end Goldbach.Analytic
