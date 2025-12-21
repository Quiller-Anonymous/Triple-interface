import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Data.Real.Basic
import Goldbach.Windows
import Goldbach.BankPieces

namespace Goldbach
namespace BankPieces

variable {X0 H : ℕ} {S ε : ℝ}

/-- Triangle inequality for two components. -/
lemma abs_sum2_le (a b : ℝ) : |a + b| ≤ |a| + |b| := by simpa using abs_add a b

/-- If `R-M = A + B` on the window and `|A| ≤ ε/2·S`, `|B| ≤ ε/2·S`, then
    `|R - M| ≤ ε·S` on the window. -/
lemma bound_from_two_components
  {M : ℕ → ℝ} {A B : ℕ → ℝ}
  (decomp : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → (R N : ℝ) - M N = A N + B N)
  (hA : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → |A N| ≤ (ε/2) * S)
  (hB : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → |B N| ≤ (ε/2) * S) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → |(R N : ℝ) - M N| ≤ ε * S := by
  intro X N hX hN
  have hde := decomp hX hN
  have hA' := hA hX hN
  have hB' := hB hX hN
  have : |(R N : ℝ) - M N| = |A N + B N| := by simpa [hde]
  calc
    |(R N : ℝ) - M N| = |A N + B N| := this
    _ ≤ |A N| + |B N| := abs_sum2_le _ _
    _ ≤ (ε/2) * S + (ε/2) * S := add_le_add hA' hB'
    _ = ε * S := by ring

/-- Package the two-component bound into the instance TenorBridge needs. -/
def decomp_from_two_components
  {M : ℕ → ℝ} {A B : ℕ → ℝ}
  (decomp : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → (R N : ℝ) - M N = A N + B N)
  (hA : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → |A N| ≤ (ε/2) * S)
  (hB : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → |B N| ≤ (ε/2) * S) :
  DecompBounds X0 H S ε 0 M :=
{ abs := { bound := by intro X N hX hN; exact bound_from_two_components (X0:=X0) (H:=H) (S:=S) (ε:=ε)
    (M:=M) (A:=A) (B:=B) decomp hA hB hX hN } }

end BankPieces
end Goldbach
