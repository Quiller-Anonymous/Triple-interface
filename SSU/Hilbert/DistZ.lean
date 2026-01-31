import SSU.Basic
import Mathlib.Data.Int.Basic

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

end SSU.Hilbert
