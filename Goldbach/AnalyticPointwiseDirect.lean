import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridgeDirect
import Goldbach.AnalyticGlobalDirect

open Goldbach
open Goldbach.Windows
open Goldbach.Base

namespace Goldbach.Analytic

/-- Packaged witness for the direct lower-term closure route. -/
structure PointwiseWitnessDirect where
  X0 : ℕ
  H : ℕ → ℕ
  L : ℕ → ℝ
  Δ : ℕ → ℝ
  global :
    ∀ {X : ℕ}, X0 ≤ X →
      Goldbach.Bridge.ClosurePointwiseDirect X H L Δ

namespace PointwiseWitnessDirect

def of_global
    (X0 : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ)
    (g : Goldbach.Bridge.GlobalClosurePointwiseDirect X0 H L Δ) :
    PointwiseWitnessDirect :=
  { X0 := X0
    H := H
    L := L
    Δ := Δ
    global := by
      intro X hX
      exact g hX }

def ofAnalytic
    {X0 : ℕ} {H : ℕ → ℕ} {L Δ : ℕ → ℝ}
    (h : Goldbach.AnalyticHypDirect X0 H L Δ) :
    PointwiseWitnessDirect :=
  of_global X0 H L Δ (Goldbach.AnalyticHypDirect.globalClosure h)

lemma gap_nonneg (w : PointwiseWitnessDirect) {X : ℕ} (hX : w.X0 ≤ X) : 0 ≤ w.Δ X := by
  exact (w.global (X := X) hX).1

lemma gap_lt_lower (w : PointwiseWitnessDirect) {X : ℕ} (hX : w.X0 ≤ X) :
    w.Δ X < w.L X := by
  have hgap : 0 < w.L X - w.Δ X := (w.global (X := X) hX).2.1
  linarith

theorem representable_large
  (w : PointwiseWitnessDirect) :
  ∀ {N : ℕ}, IsEven N → w.X0 ≤ N → GoldbachRep N := by
  intro N hEven hX0
  have hpt : Goldbach.Bridge.ClosurePointwiseDirect N w.H w.L w.Δ :=
    w.global (X := N) hX0
  have hmem : N ∈ EvenIn N (w.H N) := Goldbach.Windows.mem_EvenIn_self hEven
  exact Goldbach.Bridge.closurePointwiseDirect_to_rep hpt hmem

end PointwiseWitnessDirect
end Goldbach.Analytic
