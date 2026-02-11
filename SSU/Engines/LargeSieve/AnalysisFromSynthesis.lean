import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Norm

/-!
Helper lemmas for turning finite synthesis/pointwise bounds into “analysis-side” bounds.

Note: a *sharp* “analysis from synthesis with the same constant” lemma (frame/Bessel duality)
is desirable for the eventual Montgomery–Vaughan large sieve proof.

For now we provide a lightweight fallback that is often sufficient for plumbing:

`∑ ‖⟪v i, x⟫‖² ≤ (∑ ‖v i‖²) * ‖x‖²`,

proved by pointwise Cauchy–Schwarz.
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- Sharp “analysis from synthesis” (finite Bessel duality).

If a finite family `v i` satisfies the synthesis bound

`‖∑ i∈J c i • v i‖² ≤ C * ∑ i∈J ‖c i‖²`,

then it also satisfies the analysis/Bessel bound

`∑ i∈J ‖⟪v i, x⟫‖² ≤ C * ‖x‖²`.

This is a purely Hilbert-space lemma (no arithmetic). -/
theorem sum_norm_inner_sq_le_of_synthesisBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : Finset ℤ) (v : ℤ → E) (C : ℝ)
    (hC : 0 ≤ C)
    (hSynth :
      ∀ c : ℤ → ℂ,
        ‖∑ i ∈ J, c i • v i‖ ^ 2 ≤ C * ∑ i ∈ J, ‖c i‖ ^ 2) :
    ∀ x : E, (∑ i ∈ J, ‖⟪v i, x⟫‖ ^ 2) ≤ C * ‖x‖ ^ 2 := by
  classical
  intro x
  let c : ℤ → ℂ := fun i => ⟪v i, x⟫
  let w : E := ∑ i ∈ J, c i • v i
  let S : ℝ := ∑ i ∈ J, ‖c i‖ ^ 2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine Finset.sum_nonneg ?_
    intro i hi
    positivity
  have hSynth' : ‖w‖ ^ 2 ≤ C * S := by
    simpa [w, c, S] using hSynth c
  have hinner : ⟪w, x⟫ = (S : ℂ) := by
    -- Expand and use `conj z * z = (normSq z : ℂ)` and `normSq z = ‖z‖^2`.
    have :
        ⟪w, x⟫ = ∑ i ∈ J, (Complex.normSq (c i) : ℂ) := by
      -- Expand the inner product across the finite sum by induction.
      have inner_sum_left' (s : Finset ℤ) (g : ℤ → E) (y : E) :
          ⟪∑ i ∈ s, g i, y⟫ = ∑ i ∈ s, ⟪g i, y⟫ := by
        classical
        refine Finset.induction_on s ?_ ?_
        · simp
        · intro a s ha hs
          simp [ha, hs, inner_add_left]
      calc
        ⟪w, x⟫
            = ∑ i ∈ J, ⟪c i • v i, x⟫ := by
                simpa [w] using
                  (inner_sum_left' (s := J) (g := fun i => c i • v i) (y := x))
        _ = ∑ i ∈ J, (star (c i)) * ⟪v i, x⟫ := by
                simp [inner_smul_left]
        _ = ∑ i ∈ J, (Complex.normSq (c i) : ℂ) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                -- `star (⟪v i, x⟫) = ⟪x, v i⟫`.
                -- Hence `star (c i) * ⟪v i, x⟫ = conj (c i) * c i = (normSq (c i) : ℂ)`.
                simp [c, Complex.normSq_eq_conj_mul_self, inner_conj_symm, mul_assoc, mul_left_comm,
                  mul_comm]
    -- Convert `normSq` into `‖·‖²` and factor the coercion.
    -- (`simp` knows `Complex.normSq_eq_norm_sq`.)
    simpa [S, Complex.normSq_eq_norm_sq] using this
  have hcs : ‖⟪w, x⟫‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖x‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) w x
    have h' := pow_le_pow_left₀ (by positivity) h 2
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h'
  -- Rewrite Cauchy–Schwarz in terms of `S`.
  have hSsq : S ^ 2 ≤ ‖w‖ ^ 2 * ‖x‖ ^ 2 := by
    -- `‖(S : ℂ)‖ = S` since `S ≥ 0`.
    have hn : ‖(S : ℂ)‖ = S := by
      -- `‖(r:ℂ)‖ = ‖r‖ = |r| = r` for `r ≥ 0`.
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS_nonneg] using
        (Complex.norm_real S)
    -- Use `hinner` and `hn`.
    simpa [hinner, hn] using hcs
  by_cases hS0 : S = 0
  · -- Then the LHS is zero.
    have : (∑ i ∈ J, ‖⟪v i, x⟫‖ ^ 2) = 0 := by
      -- `S = ∑ ‖c i‖²`, and `c i = ⟪v i, x⟫`.
      simpa [S, c, hS0]
    simpa [this] using (mul_nonneg hC (by positivity : 0 ≤ ‖x‖ ^ 2))
  · -- Cancel the positive factor `S`.
    have hSpos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
    have h :
        S ^ 2 ≤ (C * S) * ‖x‖ ^ 2 := by
      calc
        S ^ 2 ≤ ‖w‖ ^ 2 * ‖x‖ ^ 2 := hSsq
        _ ≤ (C * S) * ‖x‖ ^ 2 := by
              exact mul_le_mul_of_nonneg_right hSynth' (by positivity)
    -- `S^2 = S*S` and divide by `S`.
    have : S ≤ C * ‖x‖ ^ 2 := by
      have h' : S * S ≤ S * (C * ‖x‖ ^ 2) := by
        -- Rearrange the RHS to expose a left factor `S`.
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
      exact (mul_le_mul_left hSpos).1 h'
    -- Rewrite the goal.
    simpa [S, c] using this

theorem sum_norm_inner_sq_le_sum_norm_sq_mul_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : Finset ℤ) (v : ℤ → E) (x : E) :
    (∑ i ∈ J, ‖⟪v i, x⟫‖ ^ 2)
        ≤
    (∑ i ∈ J, ‖v i‖ ^ 2) * ‖x‖ ^ 2 := by
  classical
  -- Pointwise: `‖⟪v i, x⟫‖ ≤ ‖v i‖ * ‖x‖`.
  have hpoint (i : ℤ) :
      ‖⟪v i, x⟫‖ ^ 2 ≤ (‖v i‖ ^ 2) * (‖x‖ ^ 2) := by
    have hcs : ‖⟪v i, x⟫‖ ≤ ‖v i‖ * ‖x‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℂ) (v i) x)
    -- Square both sides.
    have := pow_le_pow_left₀ (by positivity) hcs 2
    -- Rewrite `(a*b)^2 = a^2*b^2`.
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  -- Sum and factor out the constant `‖x‖^2`.
  calc
    (∑ i ∈ J, ‖⟪v i, x⟫‖ ^ 2)
        ≤
      ∑ i ∈ J, (‖v i‖ ^ 2) * (‖x‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hpoint i
    _ =
      (∑ i ∈ J, ‖v i‖ ^ 2) * ‖x‖ ^ 2 := by
          simpa using
            (Finset.sum_mul (s := J) (f := fun i : ℤ => ‖v i‖ ^ 2) (a := ‖x‖ ^ 2)).symm

end
end LargeSieve
end Engines
end SSU
