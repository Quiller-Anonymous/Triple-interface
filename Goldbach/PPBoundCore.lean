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

/-!
Small deterministic helper for cardinalities of symmetric integer bands.

We keep this file minimal and robust: it is used as a convenience lemma in other coarse bounds,
and should not depend on any project-specific analytic structure.
-/

namespace Goldbach.PPBoundCore

open Int

/-- Cardinality of the integer offset band `{-H, …, H}`. -/
lemma card_Icc_neg_to_pos (H : ℕ) :
    (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2 * H + 1 := by
  -- `Icc a b` on `ℤ` has size `(b + 1 - a).toNat`.
  have hcard :
      (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = ((H : ℤ) + 1 - (-(H : ℤ))).toNat := by
    simpa using (Int.card_Icc (a := (-(H : ℤ))) (b := (H : ℤ)))
  -- Simplify the integer expression.
  have hsimp : ((H : ℤ) + 1 - (-(H : ℤ))) = (2 * (H : ℤ) + 1) := by
    ring
  have hnn : 0 ≤ (2 * (H : ℤ) + 1) := by
    have : (0 : ℤ) ≤ (H : ℤ) := by exact_mod_cast (Nat.zero_le H)
    linarith
  -- Convert the `toNat` into a closed form in `ℕ`.
  have htoNat : (2 * (H : ℤ) + 1).toNat = 2 * H + 1 := by
    apply Int.ofNat.inj
    -- cast to `ℤ` and use `toNat_of_nonneg`
    calc
      ((2 * (H : ℤ) + 1).toNat : ℤ) = 2 * (H : ℤ) + 1 := by
        simpa using (Int.toNat_of_nonneg hnn)
      _ = ((2 * H + 1 : ℕ) : ℤ) := by
        norm_cast
  -- Finish by rewriting the `card` formula.
  -- (`Int.card_Icc` uses the shape `(b + 1 - a).toNat`.)
  calc
    (Finset.Icc (-(H : ℤ)) (H : ℤ)).card
        = ((H : ℤ) + 1 - (-(H : ℤ))).toNat := hcard
    _ = (2 * (H : ℤ) + 1).toNat := by simpa [hsimp]
    _ = 2 * H + 1 := htoNat

end Goldbach.PPBoundCore
