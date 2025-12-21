/-
  Bank absolute-deviation hook for the working window.
  Goal:  |R N - M N| ≤ 0.01 * 1  for all N ∈ Windows.EvenIn X H, X ≥ X0

  Fill in your decomposition and component bounds; no axioms/sorries here.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.Windows
import Goldbach.SingularSeries
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma   -- C2_numeric, X0, H

namespace Goldbach
namespace BankPieces
namespace Working

open Real
open Goldbach.Analytic   -- X0, H, C2_numeric

/-- Triangle inequality (rewritten): `|a + b| ≤ |a| + |b|`. -/
@[simp] lemma abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  simpa using abs_add a b

/-- Hook: if on the working window you have `R - M = AO + BG` and each component
    is bounded by 0.005, then `|R - M| ≤ 0.01` on that window. -/
theorem bound_working
  (AO BG : ℕ → ℝ)
  (hDecomp :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      (R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N = AO N + BG N)
  (hAO :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |AO N| ≤ (0.005 : ℝ))
  (hBG :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |BG N| ≤ (0.005 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
    |(R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ) * (1 : ℝ) := by
  intro X N hX hN
  have hde := hDecomp hX hN
  have hA  := hAO hX hN
  have hB  := hBG hX hN
  calc
    |(R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N|
        = |AO N + BG N| := by simpa [hde]
    _ ≤ |AO N| + |BG N| := abs_add_le' _ _
    _ ≤ (0.005 : ℝ) + (0.005 : ℝ) := add_le_add hA hB
    _ = (0.01 : ℝ) * (1 : ℝ) := by norm_num

end Working
end BankPieces
end Goldbach
