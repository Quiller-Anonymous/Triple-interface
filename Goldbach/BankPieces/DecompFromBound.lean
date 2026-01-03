/-
  Turn a proved pointwise absolute-error bound into `DecompBounds`.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.BankPieces  -- BankAbsDeviation, DecompBounds
import Goldbach.SingularSeries
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma   -- C2_numeric, X0, H

namespace Goldbach
namespace BankPieces

open Goldbach

/-- General constructor from a proved pointwise absolute deviation. -/
def decomp_of_bound
  {X0 H : ℕ} {S ε : ℝ} {δ : ℝ} {M : ℕ → ℝ}
  (h : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
        |(Goldbach.Rep.R N : ℝ) - M N| ≤ ε * S) :
  DecompBounds X0 H S ε δ M :=
{ abs := { bound := by intro X N hX hN; exact h hX hN } }

namespace Working

open Goldbach.Analytic

/-- Once you supply `bound_working`, this is the exact witness TenorBridge expects. -/
def decomp_canonical
  (bound_working : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |(Goldbach.Rep.R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ) * (1 : ℝ)) :
  DecompBounds X0 H (1 : ℝ) (0.01 : ℝ) (0 : ℝ) (Goldbach.MainTerm.M C2_numeric) :=
  decomp_of_bound (X0:=X0) (H:=H) (S:=1) (ε:=0.01) (δ:=0)
    (M:=Goldbach.MainTerm.M C2_numeric)
    (h:=by intro X N hX hN; exact bound_working hX hN)

end Working
end BankPieces
end Goldbach
