import SSU.Engines.TypeII

/-!
TeX-faithful shear-coordinate signal `S(ξ)` and a deterministic bridge from `typeIISum`.

In `05b_SSU.tex` (lines ~527–530), after shearing one defines a sum over `(u,v)`:

`S(ξ) := ∑_{(u,v)∈T'} F(v,u) e( ξ u v / (qX) )`.

Lean-side, the existing object is the tube-point sum

`typeIISum a q X ξ T F := ∑_{p∈T} F p e( ξ * shearU(p) * shearV(p) / (qX) )`.

This file provides a deterministic change-of-variables lemma identifying these two sums,
by summing over the image of the (injective) shear map.

No analytic bounds happen here; this is purely “plumbing” for Step 3/4.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

abbrev ShearPoint : Type := ℤ × ℤ

@[simp] theorem ShearPoint.fst_def (p : ShearPoint) : p.1 = p.fst := rfl
@[simp] theorem ShearPoint.snd_def (p : ShearPoint) : p.2 = p.snd := rfl

/-! The TeX shear-coordinate oscillatory sum over a finite set `T' ⊂ ℤ×ℤ`. -/
def shearSum (q : ℤ) (X : ℝ) (ξ : ℝ) (T' : Finset ShearPoint) (F : ShearPoint → ℂ) : ℂ :=
  ∑ uv ∈ T', F uv * e (ξ * (uv.1 : ℝ) * (uv.2 : ℝ) / ((q : ℝ) * X))

namespace ShearInv

open Classical

instance : Inhabited TubePoint := ⟨(0, 0)⟩

variable (td : TubeData)

def image : Finset ShearPoint :=
  td.T.image (shearMap td.a td.q)

noncomputable def inv (uv : ShearPoint) : TubePoint :=
  if huv : uv ∈ image td then
    Classical.choose (Finset.mem_image.1 huv)
  else
    default

theorem inv_mem_of_mem_image {uv : ShearPoint} (huv : uv ∈ image td) :
    inv td uv ∈ td.T := by
  classical
  have := Classical.choose_spec (Finset.mem_image.1 huv)
  simpa [inv, huv] using this.1

theorem shearMap_inv_of_mem_image {uv : ShearPoint} (huv : uv ∈ image td) :
    shearMap td.a td.q (inv td uv) = uv := by
  classical
  have := Classical.choose_spec (Finset.mem_image.1 huv)
  simpa [inv, huv] using this.2

theorem inv_shearMap_of_mem (p : TubePoint) (hp : p ∈ td.T) :
    inv td (shearMap td.a td.q p) = p := by
  classical
  have hq : td.q ≠ 0 := ne_of_gt td.q_pos
  have hinj : Function.Injective (shearMap td.a td.q) :=
    shearMap_injective (a := td.a) (q := td.q) hq
  -- Unfold `inv` at the membership proof.
  have hmem : shearMap td.a td.q p ∈ image td := by
    exact Finset.mem_image_of_mem _ hp
  -- Use the characterization supplied by the `choose` witness and injectivity.
  have hs : shearMap td.a td.q (inv td (shearMap td.a td.q p)) = shearMap td.a td.q p := by
    simpa [inv, image, dif_pos hmem] using
      (shearMap_inv_of_mem_image (td := td) (uv := shearMap td.a td.q p) hmem)
  exact hinj hs

end ShearInv

/-!
## Main deterministic bridge

We sum `typeIISum` over tube points, but we can just as well sum over the shear image and pull
back coefficients via the (classical) shear inverse.
-/

theorem typeIISum_eq_shearSum_image
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    shearSum td.q td.X ξ (ShearInv.image td) (fun uv => F (ShearInv.inv td uv)) := by
  classical
  have hq : td.q ≠ 0 := ne_of_gt td.q_pos
  have hinj : Function.Injective (shearMap td.a td.q) :=
    shearMap_injective (a := td.a) (q := td.q) hq
  -- Rewrite the RHS via `Finset.sum_image` and the left-inverse property of `ShearInv.inv`.
  unfold shearSum ShearInv.image
  -- `sum_image` turns a sum over the image into a sum over the original finset.
  have hsum :
      (∑ uv ∈ td.T.image (shearMap td.a td.q),
          F (ShearInv.inv td uv) *
              e (ξ * (uv.1 : ℝ) * (uv.2 : ℝ) / ((td.q : ℝ) * td.X)))
        =
      ∑ p ∈ td.T,
        F (ShearInv.inv td (shearMap td.a td.q p)) *
            e (ξ * ((shearMap td.a td.q p).1 : ℝ) * ((shearMap td.a td.q p).2 : ℝ) /
                ((td.q : ℝ) * td.X)) := by
    -- `Finset.sum_image` requires injectivity on the source finset.
    have hinjOn : Set.InjOn (shearMap td.a td.q) (td.T : Set TubePoint) :=
      fun p hp p' hp' hpp' => hinj hpp'
    -- Note: `Finset.sum_image` is stated as `∑ uv ∈ image g s, f uv = ∑ p ∈ s, f (g p)`.
    simpa using
      (Finset.sum_image (s := td.T) (g := shearMap td.a td.q)
        (f := fun uv : ShearPoint =>
          F (ShearInv.inv td uv) *
            e (ξ * (uv.1 : ℝ) * (uv.2 : ℝ) / ((td.q : ℝ) * td.X))) hinjOn)
  -- Simplify the inverse on the shear image, and unfold `typeIISum`.
  have hinv (p : TubePoint) (hp : p ∈ td.T) :
      ShearInv.inv td (shearMap td.a td.q p) = p :=
    ShearInv.inv_shearMap_of_mem (td := td) (p := p) hp
  -- Also simplify the phase using `shearMap_fst/snd`.
  calc
    typeIISum td.a td.q td.X ξ td.T F
        =
      ∑ p ∈ td.T,
        F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)) := by
          rfl
    _ =
      ∑ p ∈ td.T,
        F (ShearInv.inv td (shearMap td.a td.q p)) *
            e (ξ * ((shearMap td.a td.q p).1 : ℝ) * ((shearMap td.a td.q p).2 : ℝ) /
                ((td.q : ℝ) * td.X)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          simp [hinv p hp, shearMap_fst, shearMap_snd, mul_assoc, mul_left_comm, mul_comm,
            div_eq_mul_inv]
    _ =
      ∑ uv ∈ td.T.image (shearMap td.a td.q),
          F (ShearInv.inv td uv) *
              e (ξ * (uv.1 : ℝ) * (uv.2 : ℝ) / ((td.q : ℝ) * td.X)) := by
          simpa using hsum.symm

/-!
## TeX-facing specializations

The TeX (Step 2–4) treats the coefficient array as a function of shear coordinates `(u,v)`.
If the tube coefficient function `F : TubePoint → ℂ` factors through the shear map, then the
oscillatory sum and the energy also factor through the shear image without any classical inverse.
-/

theorem typeIISum_eq_shearSum_image_of_comp
    (td : TubeData) (ξ : ℝ) (G : ShearPoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T (fun p => G (shearMap td.a td.q p))
      =
    shearSum td.q td.X ξ (td.T.image (shearMap td.a td.q)) G := by
  classical
  have hq : td.q ≠ 0 := ne_of_gt td.q_pos
  have hinj : Function.Injective (shearMap td.a td.q) :=
    shearMap_injective (a := td.a) (q := td.q) hq
  have hinjOn : Set.InjOn (shearMap td.a td.q) (td.T : Set TubePoint) :=
    fun p hp p' hp' hpp' => hinj hpp'
  -- Rewrite `shearSum` over the image, then apply `Finset.sum_image`.
  unfold shearSum
  -- `Finset.sum_image` gives `∑ uv∈image, f uv = ∑ p∈T, f (shearMap p)`.
  have hsum :=
    (Finset.sum_image (s := td.T) (g := shearMap td.a td.q)
      (f := fun uv : ShearPoint =>
        G uv * e (ξ * (uv.1 : ℝ) * (uv.2 : ℝ) / ((td.q : ℝ) * td.X))) hinjOn)
  -- Finish by unfolding `typeIISum`.
  simpa [typeIISum, shearMap_fst, shearMap_snd, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv] using hsum.symm

theorem tubeEnergy_eq_sum_image_shearMap_of_comp
    (td : TubeData) (G : ShearPoint → ℂ) :
    tubeEnergy td.T (fun p => G (shearMap td.a td.q p))
      =
    ∑ uv ∈ td.T.image (shearMap td.a td.q), ‖G uv‖ ^ 2 := by
  classical
  have hq : td.q ≠ 0 := ne_of_gt td.q_pos
  have hinj : Function.Injective (shearMap td.a td.q) :=
    shearMap_injective (a := td.a) (q := td.q) hq
  have hinjOn : Set.InjOn (shearMap td.a td.q) (td.T : Set TubePoint) :=
    fun p hp p' hp' hpp' => hinj hpp'
  -- `tubeEnergy` is a sum over `td.T`; rewrite it as a `sum_image`.
  unfold tubeEnergy
  -- `Finset.sum_image` gives the image-sum equality; we use it with `f uv := ‖G uv‖²`.
  have hsum :=
    (Finset.sum_image (s := td.T) (g := shearMap td.a td.q)
      (f := fun uv : ShearPoint => (‖G uv‖ : ℝ) ^ 2) hinjOn)
  simpa using hsum.symm

end

end LargeSieve
end TypeII
end Engines
end SSU
