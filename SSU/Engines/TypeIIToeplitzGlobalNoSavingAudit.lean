import SSU.Engines.TypeIIToeplitz

/-!
# Global `Step34ProdSum` no-saving audit

The global interface quantifies over every coefficient array. Testing it at frequency zero with the
constant-one array forces its displayed effective constant to be at least the cardinality of the
tube. Thus the visible `sqrt (H / X)` factor cannot by itself be read as a saving over the trivial
per-frequency bound. A useful arithmetic application must use a restricted array theorem or some
additional integrated structure.
-/

namespace SSU.Engines.TypeIIToeplitz.Step34ProdSum

open scoped BigOperators

open SSU
open SSU.Engines.TypeII

noncomputable section

/-- Every global Step-3/4 witness pays at least the trivial cardinality at frequency zero. -/
theorem card_le_effective_constant
    {X H : ℝ} {T : Finset TubePoint}
    (hT : T.Nonempty) (hH : 0 < H) (h : Step34ProdSum X H T) :
    (T.card : ℝ) ≤ h.C * Real.sqrt (H / X) := by
  classical
  let F : TubePoint → ℂ := fun _ => 1
  have hband : |(0 : ℝ)| ≤ 1 / H := by
    simp [le_of_lt hH]
  have hbound := h.bound 0 hband F
  have hsum : PT.prodSum X 0 T F = (T.card : ℂ) := by
    simp [PT.prodSum, SSU.Engines.TypeII.ProductToeplitz.prodSum,
      SSU.Engines.TypeII.e, F]
  have henergy : tubeEnergy T F = (T.card : ℝ) := by
    simp [tubeEnergy, F]
  rw [hsum, henergy] at hbound
  have hcardPos : (0 : ℝ) < T.card := by
    exact_mod_cast (Finset.card_pos.mpr hT)
  have hcardNorm : ‖(T.card : ℂ)‖ = (T.card : ℝ) := by
    rw [Complex.norm_natCast]
  rw [hcardNorm] at hbound
  nlinarith

end

end SSU.Engines.TypeIIToeplitz.Step34ProdSum
