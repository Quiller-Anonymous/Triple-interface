import SSU.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval

namespace SSU
namespace Hilbert

/-!
Distance on `ℤ` for dyadic / two-sided packet indices.

We use the symmetric distance

`distZ i j := Int.natAbs (i - j) : ℕ`.
-/

def distZ (i j : ℤ) : ℕ :=
  Int.natAbs (i - j)

@[simp] lemma distZ_self (i : ℤ) : distZ i i = 0 := by
  simp [distZ]

lemma distZ_comm (i j : ℤ) : distZ i j = distZ j i := by
  -- `natAbs (i - j) = natAbs (-(i - j)) = natAbs (j - i)`.
  have h : (i - j).natAbs = (-(i - j)).natAbs := by
    simpa using (Int.natAbs_neg (i - j)).symm
  -- `-(i - j) = j - i`.
  simpa [distZ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-!
## Deterministic diameter bounds on intervals

These lemmas are used to discharge “`distZ` ≤ R” hypotheses when the index set is an interval
`Finset.Icc A B` (as in the TeX Step 3/4 bounds, where indices live in dyadic boxes).
-/

lemma distZ_le_toNat_sub_of_mem_Icc {A B i j : ℤ}
    (hi : i ∈ Finset.Icc A B) (hj : j ∈ Finset.Icc A B) :
    distZ i j ≤ Int.toNat (B - A) := by
  classical
  by_cases hAB : A ≤ B
  · -- Convert interval membership into inequalities.
    have hi' : A ≤ i ∧ i ≤ B := by simpa [Finset.mem_Icc] using hi
    have hj' : A ≤ j ∧ j ≤ B := by simpa [Finset.mem_Icc] using hj
    -- Bound `i - j` between `-(B-A)` and `B-A`.
    have hUpper : i - j ≤ B - A := by linarith [hi'.2, hj'.1]
    have hLower : -(B - A) ≤ i - j := by linarith [hi'.1, hj'.2]
    have habs : |i - j| ≤ B - A := by
      -- `abs_le` expects `-x ≤ y` and `y ≤ x`.
      have : -(B - A) ≤ i - j ∧ i - j ≤ B - A := ⟨hLower, hUpper⟩
      simpa using (abs_le.2 this)
    -- Convert `|i-j|` to `natAbs (i-j)` and compare with `toNat (B-A)`.
    have habs' : ((i - j).natAbs : ℤ) ≤ B - A := by
      -- `((i-j).natAbs : ℤ) = |i-j|`.
      simpa [Int.natCast_natAbs] using habs
    have hBA0 : 0 ≤ B - A := sub_nonneg.mpr hAB
    have habs'' : ((i - j).natAbs : ℤ) ≤ (Int.toNat (B - A) : ℤ) := by
      simpa [Int.toNat_of_nonneg hBA0] using habs'
    have hnatAbs : (i - j).natAbs ≤ Int.toNat (B - A) :=
      (Int.ofNat_le).1 habs''
    simpa [distZ] using hnatAbs
  · -- If `A ≤ B` fails, the interval is empty, contradiction.
    have : (Finset.Icc A B : Finset ℤ) = ∅ := by
      simpa [Finset.Icc_eq_empty, not_le] using hAB
    simpa [this] using hi

end SSU.Hilbert
