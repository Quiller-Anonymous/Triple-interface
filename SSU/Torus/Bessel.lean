import SSU.Torus.Multipliers
import Mathlib.MeasureTheory.Function.L2Space

/-!
Deterministic `L²` overlap → Bessel bounds on the SSU torus.

If a finite family of `L^∞` multipliers has pointwise bounded sum of squares, then the associated
`L²` multiplier operators satisfy a Bessel-type inequality.
-/

namespace SSU
namespace Torus

open scoped BigOperators ENNReal InnerProductSpace

open MeasureTheory

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace Multipliers

local notation "p∞" => (∞ : ℝ≥0∞)
local notation "p2" => (2 : ℝ≥0∞)

local notation "⟪" x ", " y "⟫" => inner ℂ x y

private theorem integrable_norm_sq (g : L2) : Integrable (fun x : UC => ‖g x‖ ^ 2) μ := by
  have hg : MemLp (fun x : UC => g x) (2 : ℝ≥0∞) μ := Lp.memLp g
  have h :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm (μ := μ) (f := fun x : UC => g x)
          (hf := Lp.aestronglyMeasurable g)).1 hg
  simpa using h

theorem norm_sq_eq_integral_norm_sq (g : L2) : ‖g‖ ^ 2 = ∫ x : UC, ‖g x‖ ^ 2 ∂μ := by
  have hinner : ‖g‖ ^ 2 = RCLike.re ⟪g, g⟫ := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := g)).symm
  have hint : Integrable (fun x : UC => ⟪g x, g x⟫) μ :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℂ) g g
  calc
    ‖g‖ ^ 2 = RCLike.re ⟪g, g⟫ := hinner
    _ = RCLike.re (∫ x : UC, ⟪g x, g x⟫ ∂μ) := by
      -- apply `congrArg re` to the `L²` inner-product formula
      simpa using congrArg RCLike.re (MeasureTheory.L2.inner_def (𝕜 := ℂ) g g)
    _ = ∫ x : UC, RCLike.re ⟪g x, g x⟫ ∂μ := by
      simpa using (integral_re (μ := μ) (f := fun x : UC => ⟪g x, g x⟫) hint).symm
    _ = ∫ x : UC, ‖g x‖ ^ 2 ∂μ := by
      refine integral_congr_ae <| Filter.Eventually.of_forall fun x => ?_
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := g x))

/--
Finite-overlap `L²` Bessel bound for multiplier cutoffs.

If `∑_{i∈s} ‖φ i x‖^2 ≤ Λ` almost everywhere, then for all `f ∈ L²`,
`∑_{i∈s} ‖(φ i) • f‖^2 ≤ Λ * ‖f‖^2`.
-/
theorem sum_norm_sq_smul_le_of_ae_sum_norm_sq_le {ι : Type*} (s : Finset ι) (φ : ι → Linf)
    (Λ : ℝ) (_hΛ : 0 ≤ Λ)
    (hpoint : (∀ᵐ x : UC ∂μ, (∑ i ∈ s, ‖φ i x‖ ^ 2) ≤ Λ)) (f : L2) :
    (∑ i ∈ s, ‖(φ i • f : L2)‖ ^ 2) ≤ Λ * ‖f‖ ^ 2 := by
  classical
  have hintR : Integrable (fun x : UC => Λ * ‖f x‖ ^ 2) μ :=
    (integrable_norm_sq (g := f)).const_mul Λ

  have hcoeAll :
      (∀ᵐ x : UC ∂μ, ∀ i ∈ s, (φ i • f : L2) x = (φ i x) • (f x)) := by
    classical
    refine s.induction_on ?_ ?_
    · refine Filter.Eventually.of_forall ?_
      intro x i hi
      exact (Finset.notMem_empty i hi).elim
    · intro a s ha hs
      have haEq : ∀ᵐ x : UC ∂μ, (φ a • f : L2) x = (φ a x) • (f x) := by
        -- `Lp.coeFn_lpSMul` is an `EventuallyEq`; extract the pointwise equality event.
        have h :=
          (MeasureTheory.Lp.coeFn_lpSMul (μ := μ) (p := p∞) (q := p2) (r := p2) (f := φ a)
                (g := f) : ((φ a • f : L2) =ᵐ[μ] fun x : UC => (φ a x) • (f x)))
        -- `h.eventually` gives `(φ a • f) x = (⇑(φ a) • ⇑f) x`; simplify the RHS.
        refine (h.eventually).mono ?_
        intro x hx
        simpa using hx
      refine (haEq.and hs).mono ?_
      intro x hx i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact hx.1
      · exact hx.2 i hi'

  have hmul :
      (fun x : UC => (∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2)) ≤ᵐ[μ]
        (fun x : UC => Λ * ‖f x‖ ^ 2) := by
    -- expand the definition of `≤ᵐ[μ]` as an `ae`-eventually statement
    show ∀ᵐ x : UC ∂μ,
        (∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2) ≤ Λ * ‖f x‖ ^ 2
    refine (hpoint.and hcoeAll).mono ?_
    rintro x ⟨hxPoint, hxCoe⟩
    have hterm :
        (∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2) =
          (∑ i ∈ s, ‖φ i x‖ ^ 2) * ‖f x‖ ^ 2 := by
      calc
        (∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2) =
            ∑ i ∈ s, ‖(φ i x) • (f x)‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [hxCoe i hi]
        _ = ∑ i ∈ s, (‖φ i x‖ ^ 2) * ‖f x‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [mul_pow]
        _ = (∑ i ∈ s, ‖φ i x‖ ^ 2) * ‖f x‖ ^ 2 := by
              -- factor out the constant `‖f x‖^2`
              simpa using
                (Finset.sum_mul (s := s) (f := fun i => ‖φ i x‖ ^ 2) (a := ‖f x‖ ^ 2)).symm
    -- apply the pointwise bound and multiply by the nonnegative factor `‖f x‖^2`
    have hmul' :
        (∑ i ∈ s, ‖φ i x‖ ^ 2) * ‖f x‖ ^ 2 ≤ Λ * ‖f x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hxPoint (sq_nonneg ‖f x‖)
    simpa [hterm, mul_assoc] using hmul'

  have hintL : Integrable (fun x : UC => ∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2) μ := by
    classical
    refine s.induction_on ?_ ?_
    · simp
    · intro a s ha hs
      have haI : Integrable (fun x : UC => ‖(φ a • f : L2) x‖ ^ 2) μ :=
        integrable_norm_sq (g := (φ a • f : L2))
      simpa [Finset.sum_insert ha] using haI.add hs
  -- Convert the outer sum of `L²` norms to an integral of pointwise squares, then bound pointwise.
  have hL :
      (∑ i ∈ s, ‖(φ i • f : L2)‖ ^ 2) =
        ∫ x : UC, (∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2) ∂μ := by
    -- Use `‖g‖^2 = ∫ ‖g x‖^2` for each term and commute sum/integral.
    calc
      (∑ i ∈ s, ‖(φ i • f : L2)‖ ^ 2) =
          ∑ i ∈ s, (∫ x : UC, ‖(φ i • f : L2) x‖ ^ 2 ∂μ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (norm_sq_eq_integral_norm_sq (g := (φ i • f : L2)))
      _ = ∫ x : UC, (∑ i ∈ s, ‖(φ i • f : L2) x‖ ^ 2) ∂μ := by
            symm
            exact MeasureTheory.integral_finset_sum s
              (f := fun i => fun x : UC => ‖(φ i • f : L2) x‖ ^ 2) fun i hi =>
                integrable_norm_sq (g := (φ i • f : L2))

  have hR : ∫ x : UC, Λ * ‖f x‖ ^ 2 ∂μ = Λ * ‖f‖ ^ 2 := by
    calc
      (∫ x : UC, Λ * ‖f x‖ ^ 2 ∂μ) = Λ * ∫ x : UC, ‖f x‖ ^ 2 ∂μ := by
        simpa using (MeasureTheory.integral_const_mul (μ := μ) (r := Λ) (f := fun x : UC => ‖f x‖ ^ 2))
      _ = Λ * ‖f‖ ^ 2 := by
        simp [norm_sq_eq_integral_norm_sq (g := f)]

  have hI := MeasureTheory.integral_mono_ae hintL hintR hmul
  -- Rewrite both sides back into the desired form.
  simpa [hL, hR] using hI

end Multipliers

end

end Torus
end SSU
