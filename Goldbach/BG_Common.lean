/-
  Goldbach/BG_Common.lean

  Small helper lemmas frequently needed in BG files to remove easy admits.
-/
import Mathlib

namespace Goldbach.BG_Common
open Real

/-- Triangle inequality in the form we often need. -/
lemma abs_add_le {a b : ℝ} : |a + b| ≤ |a| + |b| := by simpa using abs_add a b

/-- From bounds on |a| and |b| to a bound on |a + b|. -/
lemma abs_add_le_of_two_bounds {a b c d : ℝ}
  (ha : |a| ≤ c) (hb : |b| ≤ d) : |a + b| ≤ c + d := by
  calc
    |a + b| ≤ |a| + |b| := abs_add_le
    _ ≤ c + d := add_le_add ha hb

/-- Absolute-deviation to one-sided lower bound. -/
lemma lower_from_abs_le {x m t : ℝ} (h : |x - m| ≤ t) : x ≥ m - t :=
  (abs_le.mp h).1 |> by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Absolute-deviation to one-sided upper bound. -/
lemma upper_from_abs_le {x m t : ℝ} (h : |x - m| ≤ t) : x ≤ m + t :=
  (abs_le.mp h).2 |> by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Tiny algebra that shows up constantly. -/
@[simp] lemma add_mul_right (a b c : ℝ) : (a + b) * c = a*c + b*c := by ring
@[simp] lemma mul_add_right (a b c : ℝ) : c * (a + b) = c*a + c*b := by ring

end Goldbach.BG_Common
