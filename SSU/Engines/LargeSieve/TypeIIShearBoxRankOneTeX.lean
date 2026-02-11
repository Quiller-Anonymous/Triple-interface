import SSU.Engines.LargeSieve.TypeIIShearSumTeX
import SSU.Engines.LargeSieve.RankOneShearBoxLargeSieveTeX

/-!
TeX-facing wiring lemma: rank-one bound on `typeIISum` via the shear-image box model.

This is “plumbing only”:
if you can identify the shear image `T' := (shearMap a q) '' T` with a product box
`J × Icc(a,a+N-1)`, then the MV large sieve for `shearSum` gives a bound for `typeIISum`.

It is intended as a lightweight adapter between:
- `TypeIIShearSumTeX` (deterministic change-of-variables), and
- `RankOneShearBoxLargeSieveTeX` (MV bound on a rank-one shear box).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace ShearBoxRankOne

open SSU.Engines.TypeII
open RankOneShearBox

private theorem tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc
    (td : TubeData) (A B a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (hImage : td.T.image (shearMap td.a td.q) = box (Finset.Icc A B) a N) :
    tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
      =
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β := by
  classical
  -- First rewrite `tubeEnergy` as a sum over the shear image.
  have hsum :
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        =
      ∑ uv ∈ td.T.image (shearMap td.a td.q), ‖β uv.1 * α uv.2‖ ^ 2 := by
    -- Use the deterministic “factors through shearMap” lemma.
    simpa using
      (tubeEnergy_eq_sum_image_shearMap_of_comp (td := td)
        (G := fun uv : ShearPoint => β uv.1 * α uv.2))
  -- Replace the image by the explicit box and then rewrite the box energy.
  have hbox :
      (∑ uv ∈ td.T.image (shearMap td.a td.q), ‖β uv.1 * α uv.2‖ ^ 2)
        =
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β := by
    simpa [hImage] using
      (RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy (J := Finset.Icc A B) (a := a) (N := N)
        (α := α) (β := β))
  exact hsum.trans hbox

/-- If the shear image of `td.T` is exactly the rank-one box `Icc A B × Icc a (a+N-1)`, then
the MV rank-one bound for `shearSum` implies the corresponding bound for `typeIISum` with the
pulled-back coefficients. -/
theorem norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc
    (td : TubeData) (ξ : ℝ)
    (A B a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (hImage :
      td.T.image (shearMap td.a td.q) = box (Finset.Icc A B) a N)
    (ht : |(ξ / ((td.q : ℝ) * td.X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => β (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((td.q : ℝ) * td.X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β := by
  classical
  -- Rewrite `typeIISum` as `shearSum` on the shear image (no classical inverse needed).
  let G : ShearPoint → ℂ := fun uv => β uv.1 * α uv.2
  have hSum :
      typeIISum td.a td.q td.X ξ td.T (fun p => G (shearMap td.a td.q p))
        =
      shearSum td.q td.X ξ (td.T.image (shearMap td.a td.q)) G := by
    simpa [G] using (typeIISum_eq_shearSum_image_of_comp (td := td) (ξ := ξ) (G := G))
  have hF :
      (fun p => β (shearU td.a td.q p) * α (shearV p))
        =
      (fun p => G (shearMap td.a td.q p)) := by
    funext p
    rfl

  -- Apply the shear-box bound, then transport across the deterministic rewrite.
  have hMV :=
    norm_shearSum_sq_le_one_add_log_boxEnergy_Icc
      (q := td.q) (X := td.X) (ξ := ξ) (A := A) (B := B)
      (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β)

  -- Replace the shear image by the explicit box and rewrite `typeIISum` to `shearSum`.
  -- (The pointwise coefficient function is already `fun uv => β uv.1 * α uv.2`.)
  -- Note: `simp` handles `hF` and the `hSum` rewrite under `‖·‖^2`.
  simpa [hF, hSum, hImage, G] using hMV

/-- Same bound as `norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc`, but with the
RHS written as `tubeEnergy td.T` for the pulled-back rank-one coefficient array. -/
theorem norm_typeIISum_sq_le_one_add_log_tubeEnergy_of_image_eq_box_Icc
    (td : TubeData) (ξ : ℝ)
    (A B a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (hImage :
      td.T.image (shearMap td.a td.q) = box (Finset.Icc A B) a N)
    (ht : |(ξ / ((td.q : ℝ) * td.X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => β (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((td.q : ℝ) * td.X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) := by
  have h :=
    norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc
      (td := td) (ξ := ξ) (A := A) (B := B) (a := a) (N := N) (α := α) (β := β)
      (hImage := hImage) (ht := ht) (ht0 := ht0)
  -- Rewrite `boxEnergy` as `tubeEnergy`.
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β
        =
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) :=
    (tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc (td := td) (A := A) (B := B) (a := a) (N := N)
      (α := α) (β := β) hImage).symm
  simpa [hE] using h

end ShearBoxRankOne

end

end LargeSieve
end TypeII
end Engines
end SSU
