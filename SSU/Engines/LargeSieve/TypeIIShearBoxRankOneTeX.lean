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

/-- Same bound as `norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc`, but with the
RHS written as the *literal* `ℓ²` energy on the box:
`∑_{(u,v)∈box} ‖β(u)α(v)‖²`. -/
theorem norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc
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
      (∑ uv ∈ box (Finset.Icc A B) a N, ‖β uv.1 * α uv.2‖ ^ 2) := by
  have h :=
    norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc
      (td := td) (ξ := ξ) (A := A) (B := B) (a := a) (N := N) (α := α) (β := β)
      (hImage := hImage) (ht := ht) (ht0 := ht0)
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β
        =
      (∑ uv ∈ box (Finset.Icc A B) a N, ‖β uv.1 * α uv.2‖ ^ 2) :=
    (RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy
      (J := Finset.Icc A B) (a := a) (N := N) (α := α) (β := β)).symm
  simpa [hE] using h

/-- Same bound as `norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc`, but with
the RHS written as `tubeEnergy td.T` for the pulled-back rank-one coefficient array. -/
theorem norm_typeIISum_sq_le_one_add_log_tubeEnergy_of_image_eq_box_Icc'
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
    norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc
      (td := td) (ξ := ξ) (A := A) (B := B) (a := a) (N := N) (α := α) (β := β)
      (hImage := hImage) (ht := ht) (ht0 := ht0)
  have hE :
      (∑ uv ∈ box (Finset.Icc A B) a N, (‖β uv.1‖ * ‖α uv.2‖) ^ 2)
        =
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) := by
    -- Convert via `boxEnergy` (and rewrite `‖β*α‖` to `‖β‖*‖α‖`).
    have hE0 :
        (∑ uv ∈ box (Finset.Icc A B) a N, (‖β uv.1‖ * ‖α uv.2‖) ^ 2)
          =
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β := by
      -- `sum_norm_sq_on_box_eq_boxEnergy` is stated with `‖β*α‖²`.
      have h0 :=
        (RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy
          (J := Finset.Icc A B) (a := a) (N := N) (α := α) (β := β))
      -- Rewrite the LHS integrand.
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using h0
    have hE1 :
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β
          =
        tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) :=
      (tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc (td := td) (A := A) (B := B) (a := a) (N := N)
        (α := α) (β := β) hImage).symm
    exact hE0.trans hE1
  simpa [hE] using h

/--
Variant of `norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc` where we *shrink* the
`u`-support by replacing `β` with `βrestrict J' β` on a larger box.

This is the TeX-faithful “tube by restriction” move: the box estimate is proved once for a larger
interval, and the tube bound is obtained by cutting down support (without breaking rank-one).
-/
theorem norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc_left_restrict
    (td : TubeData) (ξ : ℝ)
    (A B a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (J' : Finset ℤ) (hsub : J' ⊆ Finset.Icc A B)
    (hImage :
      td.T.image (shearMap td.a td.q) = box (Finset.Icc A B) a N)
    (ht : |(ξ / ((td.q : ℝ) * td.X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => (βrestrict J' β) (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((td.q : ℝ) * td.X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β := by
  classical
  -- Apply the box estimate on `Icc A B` with the restricted `β`.
  have h :=
    norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc
      (td := td) (ξ := ξ) (A := A) (B := B) (a := a) (N := N) (α := α) (β := βrestrict J' β)
      (hImage := hImage) (ht := ht) (ht0 := ht0)
  -- Rewrite `boxEnergy` on the RHS using the deterministic restriction identity.
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α (βrestrict J' β)
        =
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β :=
    RankOneShearBox.boxEnergy_left_restrict_eq
      (J := Finset.Icc A B) (J' := J') (hsub := hsub) (a := a) (N := N) (α := α) (β := β)
  simpa [hE] using h

/-- Literal-energy version of
`norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc_left_restrict`. -/
theorem norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc_left_restrict
    (td : TubeData) (ξ : ℝ)
    (A B a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (J' : Finset ℤ) (hsub : J' ⊆ Finset.Icc A B)
    (hImage :
      td.T.image (shearMap td.a td.q) = box (Finset.Icc A B) a N)
    (ht : |(ξ / ((td.q : ℝ) * td.X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => (βrestrict J' β) (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((td.q : ℝ) * td.X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      (∑ uv ∈ box J' a N, ‖β uv.1 * α uv.2‖ ^ 2) := by
  have h :=
    norm_typeIISum_sq_le_one_add_log_boxEnergy_of_image_eq_box_Icc_left_restrict
      (td := td) (ξ := ξ) (A := A) (B := B) (a := a) (N := N) (α := α) (β := β)
      (J' := J') (hsub := hsub) (hImage := hImage) (ht := ht) (ht0 := ht0)
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β
        =
      (∑ uv ∈ box J' a N, ‖β uv.1 * α uv.2‖ ^ 2) :=
    (RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy (J := J') (a := a) (N := N)
      (α := α) (β := β)).symm
  simpa [hE] using h

/-- Tube-energy version of
`norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc_left_restrict`. -/
theorem norm_typeIISum_sq_le_one_add_log_tubeEnergy_of_image_eq_box_Icc_left_restrict'
    (td : TubeData) (ξ : ℝ)
    (A B a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (J' : Finset ℤ) (hsub : J' ⊆ Finset.Icc A B)
    (hImage :
      td.T.image (shearMap td.a td.q) = box (Finset.Icc A B) a N)
    (ht : |(ξ / ((td.q : ℝ) * td.X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => (βrestrict J' β) (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((td.q : ℝ) * td.X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      tubeEnergy td.T (fun p => (βrestrict J' β) (shearU td.a td.q p) * α (shearV p)) := by
  have h :=
    norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc_left_restrict
      (td := td) (ξ := ξ) (A := A) (B := B) (a := a) (N := N) (α := α) (β := β)
      (J' := J') (hsub := hsub) (hImage := hImage) (ht := ht) (ht0 := ht0)
  have hE :
      (∑ uv ∈ box J' a N, (‖β uv.1‖ * ‖α uv.2‖) ^ 2)
        =
      tubeEnergy td.T (fun p => (βrestrict J' β) (shearU td.a td.q p) * α (shearV p)) := by
    -- Convert via `boxEnergy` and the restriction identities.
    have hE0 :
        (∑ uv ∈ box J' a N, (‖β uv.1‖ * ‖α uv.2‖) ^ 2)
          =
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β :=
    by
      have h0 :=
        (RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy (J := J') (a := a) (N := N)
          (α := α) (β := β))
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using h0
    have hE1 :
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β
          =
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α (βrestrict J' β) := by
      -- use the deterministic restriction rewrite, but in the opposite direction
      symm
      exact
        RankOneShearBox.boxEnergy_left_restrict_eq
          (J := Finset.Icc A B) (J' := J') (hsub := hsub) (a := a) (N := N) (α := α) (β := β)
    have hE2 :
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α (βrestrict J' β)
          =
        tubeEnergy td.T (fun p => (βrestrict J' β) (shearU td.a td.q p) * α (shearV p)) :=
      (tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc (td := td) (A := A) (B := B) (a := a) (N := N)
        (α := α) (β := βrestrict J' β) hImage).symm
    exact hE0.trans (hE1.trans hE2)
  simpa [hE] using h

/-!
### Symmetric dyadic shear-box specializations

These are convenience wrappers matching the TeX dyadic shear box convention:

* `u ∈ [-U, U]`, and
* `v ∈ (D, 2D]`, encoded as `Icc (D+1) (2D) = Icc ((D:ℤ)+1) (((D:ℤ)+1)+D-1)`.

They transport the already-proved `shearSum` MV bounds in
`RankOneShearBoxLargeSieveTeX` to `typeIISum`, under an `image(shearMap)=box` hypothesis.
-/

theorem norm_typeIISum_sq_le_outerUConst_tubeEnergy_of_image_eq_box_symmDyadic
    (td : TubeData) (ξ : ℝ) (U D : ℕ) (α β : ℤ → ℂ)
    (hImage :
      td.T.image (shearMap td.a td.q)
        =
      box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
    (htu : |(ξ / ((td.q : ℝ) * td.X))| * (2 * U : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => β (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    outerUConst td.q td.X ξ U D * tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) := by
  classical
  -- Rewrite `typeIISum` as `shearSum` on the shear image (coefficients factor through `shearMap`).
  have hSum :
      typeIISum td.a td.q td.X ξ td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        =
      shearSum td.q td.X ξ (td.T.image (shearMap td.a td.q)) (fun uv => β uv.1 * α uv.2) := by
    simpa using
      (typeIISum_eq_shearSum_image_of_comp (td := td) (ξ := ξ)
        (G := fun uv : ShearPoint => β uv.1 * α uv.2))
  -- Apply the proved MV bound on the symmetric dyadic shear box.
  have hMV :=
    RankOneShearBox.norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic
      (q := td.q) (X := td.X) (ξ := ξ) (U := U) (D := D)
      (ht := htu) (ht0 := ht0) (α := α) (β := β)
  -- Rewrite the `boxEnergy` RHS into `tubeEnergy td.T` using the `image=box` hypothesis.
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D α β
        =
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) :=
    (tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc (td := td) (A := (-(U : ℤ))) (B := (U : ℤ))
      (a := (D : ℤ) + 1) (N := D) (α := α) (β := β) (hImage := hImage)).symm
  -- Transport across the deterministic rewrite.
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hSum
  -- `simp` both normalizes the box via `hImage` and rewrites `boxEnergy` to `tubeEnergy`.
  simpa [hnorm, hImage, hE, outerUConst, mul_assoc, mul_left_comm, mul_comm] using hMV

theorem norm_typeIISum_sq_le_outerVConst_tubeEnergy_of_image_eq_box_symmDyadic
    (td : TubeData) (ξ : ℝ) (U D : ℕ) (α β : ℤ → ℂ)
    (hImage :
      td.T.image (shearMap td.a td.q)
        =
      box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
    (htv :
      |(ξ / ((td.q : ℝ) * td.X))| *
          (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => β (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    outerVConst td.q td.X ξ U D * tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) := by
  classical
  have hSum :
      typeIISum td.a td.q td.X ξ td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        =
      shearSum td.q td.X ξ (td.T.image (shearMap td.a td.q)) (fun uv => β uv.1 * α uv.2) := by
    simpa using
      (typeIISum_eq_shearSum_image_of_comp (td := td) (ξ := ξ)
        (G := fun uv : ShearPoint => β uv.1 * α uv.2))
  have hMV :=
    RankOneShearBox.norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic_outerV
      (q := td.q) (X := td.X) (ξ := ξ) (U := U) (D := D)
      (ht := htv) (ht0 := ht0) (α := α) (β := β)
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D α β
        =
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) :=
    (tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc (td := td) (A := (-(U : ℤ))) (B := (U : ℤ))
      (a := (D : ℤ) + 1) (N := D) (α := α) (β := β) (hImage := hImage)).symm
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hSum
  simpa [hnorm, hImage, hE, outerVConst, mul_assoc, mul_left_comm, mul_comm] using hMV

theorem norm_typeIISum_sq_le_geomMean_tubeEnergy_of_image_eq_box_symmDyadic
    (td : TubeData) (ξ : ℝ) (U D : ℕ) (α β : ℤ → ℂ)
    (hImage :
      td.T.image (shearMap td.a td.q)
        =
      box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
    (htu : |(ξ / ((td.q : ℝ) * td.X))| * (2 * U : ℝ) ≤ (1 / 2 : ℝ))
    (htv :
      |(ξ / ((td.q : ℝ) * td.X))| *
          (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((td.q : ℝ) * td.X) ≠ 0) :
    ‖typeIISum td.a td.q td.X ξ td.T
        (fun p => β (shearU td.a td.q p) * α (shearV p))‖ ^ 2
      ≤
    Real.sqrt (outerUConst td.q td.X ξ U D * outerVConst td.q td.X ξ U D)
        *
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) := by
  classical
  have hSum :
      typeIISum td.a td.q td.X ξ td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        =
      shearSum td.q td.X ξ (td.T.image (shearMap td.a td.q)) (fun uv => β uv.1 * α uv.2) := by
    simpa using
      (typeIISum_eq_shearSum_image_of_comp (td := td) (ξ := ξ)
        (G := fun uv : ShearPoint => β uv.1 * α uv.2))
  have hMV :=
    RankOneShearBox.norm_shearSum_sq_le_geomMean_boxEnergy_symmDyadic
      (q := td.q) (X := td.X) (ξ := ξ) (U := U) (D := D)
      (htu := htu) (htv := htv) (ht0 := ht0) (α := α) (β := β)
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D α β
        =
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p)) :=
    (tubeEnergy_eq_boxEnergy_of_image_eq_box_Icc (td := td) (A := (-(U : ℤ))) (B := (U : ℤ))
      (a := (D : ℤ) + 1) (N := D) (α := α) (β := β) (hImage := hImage)).symm
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hSum
  simpa [hnorm, hImage, hE, mul_assoc, mul_left_comm, mul_comm] using hMV

end ShearBoxRankOne

end

end LargeSieve
end TypeII
end Engines
end SSU
