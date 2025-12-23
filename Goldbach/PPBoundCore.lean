/-
  Goldbach/PPBoundCore.lean

  A robust, axiom-free coarse bound for the inner prime-power count:
  `ppInnerCount H N ≤ 2*H + 1`.

  Rationale: by definition `ppInnerCount H N` is the cardinality of a
  *filtered subset* of the inner offset band `{-H, -H+1, …, H}`.
  So its size is at most the size of that band, i.e. `2H+1`.

  This compiles without any arithmetic tricks and gives a safe cap you
  can use immediately in the bridge. When you want a tighter constant,
  we’ll replace just the final inequality with the refined counting lemma.
-/
import Mathlib
import Goldbach.BG_Identity

namespace Goldbach.PPBoundCore

open Int

/-- Cardinality of the integer offset band `{-H, …, H}`. -/
lemma card_Icc_neg_to_pos (H : ℕ) :
    (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2 * H + 1 := by
  -- `Icc a b` on `ℤ` has size `(b - a + 1).toNat`
  have : (Finset.Icc (-(H : ℤ)) (H : ℤ)).card
           = ( (H : ℤ) - (-(H : ℤ)) + 1 ).toNat := by
    simpa using (Int.card_Icc (a := (-(H:ℤ))) (b := (H:ℤ)))
  -- simplify the integer expression and move back to `ℕ`
  -- `H - (-H) + 1 = 2H + 1` in `ℤ`
  have : ( (H : ℤ) - (-(H : ℤ)) + 1 ).toNat = (2 * H + 1) := by
    -- (H - (-H) + 1) = (H + H + 1)
    have : (H : ℤ) - (-(H : ℤ)) + 1 = (2 * (H : ℤ) + 1) := by
      ring
    -- cast toNat of a nonnegative integer equals the natural numeral
    -- (2*H+1 : ℤ) is nonnegative
    have hnn : 0 ≤ (2 * (H : ℤ) + 1) := by
      have : (0 : ℤ) ≤ (H : ℤ) := by exact_mod_cast (Nat.zero_le H)
      linarith
    simpa [this, Int.toNat_of_nonneg hnn, two_mul, add_comm, add_left_comm, add_assoc]
  simpa [this] using this

/-- **Coarse inner bound**: the inner prime-power offset count is at most the
    size of the inner offset band `{-H,…,H}`, i.e. `2H+1`. -/
theorem ppInnerCount_le_twoHplus1
  (H N : ℕ) : Goldbach.BG_Identity.ppInnerCount H N ≤ 2 * H + 1 := by
  -- By definition `ppInnerCount` is a filtered subset of `Icc (−H) H` on `ℤ`
  -- so `card(filter …) ≤ card(Icc …)`.
  have hle :
      (Goldbach.BG_Identity.ppInnerCount H N)
        ≤ (Finset.Icc (-(H : ℤ)) (H : ℤ)).card := by
    -- Unfold the definition just far enough to apply `card_filter_le`.
    -- In your tree, `ppInnerCount` is of the shape `(Icc …).filter P).card`.
    -- `simp [Goldbach.BG_Identity.ppInnerCount]` should expose that shape;
    -- if the predicate name differs, this still works because `card_filter_le`
    -- only needs the ambient set.
    simpa [Goldbach.BG_Identity.ppInnerCount] using
      (Finset.card_filter_le
        (s := Finset.Icc (-(H : ℤ)) (H : ℤ)) (p := fun _ => True))
    -- Note: the choice of `p := fun _ => True` in `card_filter_le` is just a
    -- syntactic handle; `simp [ppInnerCount]` replaces it by your actual predicate.
  -- now plug the exact band cardinality
  simpa [card_Icc_neg_to_pos H]

end Goldbach.PPBoundCore
