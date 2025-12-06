-- Goldbach/Windows.lean
import Mathlib

namespace Goldbach.Windows

open Finset

/-- Decidable evenness as a proposition (avoids depending on `Nat.Even`). -/
def IsEven (n : ℕ) : Prop := n % 2 = 0

-- Make `filter (fun n => IsEven n)` work without extra imports
instance : DecidablePred IsEven := by
  intro n; dsimp [IsEven]; infer_instance

/-- The window `[X, X+H]` using a stable construction. -/
def IccShift (X H : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).image (fun k => X + k)

/-- Even numbers in the window, using the decidable predicate `IsEven`. -/
def EvenIn (X H : ℕ) : Finset ℕ :=
  (IccShift X H).filter (fun n => IsEven n)

/-- The left endpoint is in its own window; if it’s even, it’s in `EvenIn`. -/
lemma mem_EvenIn_self {N H : ℕ} (hEven : IsEven N) : N ∈ EvenIn N H := by
  classical
  unfold EvenIn IccShift
  have hz : 0 ∈ Finset.range (H + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos _)
  have himg : N ∈ (Finset.range (H + 1)).image (fun k => N + k) := by
    refine Finset.mem_image.mpr ?_
    exact ⟨0, hz, by simp⟩
  exact Finset.mem_filter.mpr ⟨himg, hEven⟩

end Goldbach.Windows
