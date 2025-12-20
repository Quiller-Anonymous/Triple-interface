-- Goldbach/Windows.lean
import Mathlib

namespace Goldbach.Windows

open Finset

/-- Decidable evenness as a proposition (avoids depending on `Nat.Even`). -/
def IsEven (n : ℕ) : Prop := n % 2 = 0

/-- Turn `Even n` into `IsEven n` using divisibility. -/
lemma isEven_of_even {n : ℕ} (h : Even n) : IsEven n := by
  rcases h with ⟨k, hk⟩
  -- Want: n % 2 = 0 from 2 ∣ n
  have hdiv : 2 ∣ n := ⟨k, by simpa [two_mul] using hk⟩
  simpa [IsEven] using Nat.mod_eq_zero_of_dvd hdiv

/-- Convert `IsEven n` back to the standard `Even n`. -/
lemma even_of_isEven {n : ℕ} (h : IsEven n) : Even n := by
  refine ⟨n / 2, ?_⟩
  have h' : n % 2 = 0 := h
  have hx : 2 * (n / 2) = n := by
    simpa [h', add_comm, add_left_comm, add_assoc] using Nat.mod_add_div n 2
  simpa [two_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hx.symm

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

lemma isEven_of_even' {n : ℕ} (h : Even n) : IsEven n := by
  rcases h with ⟨k, hk⟩
  -- Convert n = k + k to n = 2 * k using Nat.two_mul
  have : n = 2 * k := by rw [Nat.two_mul, ←hk]
  have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨k, this⟩
  simpa [IsEven] using this

/-- The center point `N` is in its own shifted window list `IccShift N H`
    (which is a dedup of `map (fun k => N + k) (range (H+1))`). -/
lemma mem_IccShift_center {N H : ℕ} : N ∈ IccShift N H := by
  -- unfold to list membership
  dsimp [IccShift]
  -- 0 is in `range (H+1)`
  have h0 : 0 ∈ List.range (H+1) := by
    simpa using (List.mem_range.mpr (Nat.succ_pos H))
  -- hence `N + 0` is in the mapped list
  have hmap : N + 0 ∈ (List.range (H+1)).map (fun k => N + k) :=
    List.mem_map.mpr ⟨0, h0, by simp⟩
  -- and `dedup` preserves membership; also `N + 0 = N`
  simpa using (List.mem_dedup.mpr (by simpa using hmap))

/-- `N` is always in its own centered window. -/
lemma self_mem_IccShift (N H : ℕ) : N ∈ IccShift N H := by
  -- Make the target literally a `Finset.image (fun k => N + k) (Finset.range (H+1))` membership
  unfold IccShift
  -- 0 ∈ Finset.range (H+1)
  have h0 : 0 ∈ Finset.range (H + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  -- Map witness 0 to N since (N + 0) = N
  refine Finset.mem_image.mpr ?_
  exact ⟨0, h0, by simp⟩

/-- If `N` is in the unfiltered window and is even, then it lies in the even-filtered window. -/
lemma mem_EvenIn_of_mem_IccShift_and_even
    {N H : ℕ} (hIn : N ∈ IccShift N H) (hE : IsEven N) :
    N ∈ EvenIn N H := by
  unfold EvenIn
  simpa [Finset.mem_filter] using And.intro hIn hE

end Goldbach.Windows
