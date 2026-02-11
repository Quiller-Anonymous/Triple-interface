import SSU.Hilbert.InterzoneZ

/-!
Turn a row-sum Gram bound (Schur / Cotlar–Stein style) into a “dual large sieve” inequality.

This is a purely Hilbert-space lemma, meant as glue:

If a finite family `v i` has Gram decay controlled by a nonnegative weight `a(distZ i j)`, and
`a` has a uniform row-sum bound on `J`, then any linear combination `∑ c i • v i` satisfies

`‖∑ c i • v i‖² ≤ Crow * ∑ ‖c i‖²`.

The analytic work in the Montgomery–Vaughan proof is to produce a good `a` (typically using
Dirichlet kernel bounds), and then to bound the row-sum `Crow` (polylog is acceptable).
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- InterzoneZ → dual large sieve: coefficients are absorbed into the vectors. -/
theorem norm_sum_smul_sq_le_of_rowSum_gram_boundZ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Finset ℤ} {v : ℤ → E} {a : ℕ → NNReal} {Crow : ℝ}
    (hGram :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪v i, v j⟫‖ ≤ (a (SSU.Hilbert.distZ i j) : ℝ))
    (hRow :
      ∀ i ∈ J, (∑ j ∈ J, (a (SSU.Hilbert.distZ i j) : ℝ)) ≤ Crow) :
    ∀ c : ℤ → ℂ,
      ‖∑ i ∈ J, c i • v i‖ ^ 2 ≤ Crow * ∑ i ∈ J, ‖c i‖ ^ 2 := by
  classical
  intro c
  -- Apply `InterzoneZ` to the scaled vectors `w i := c i • v i`, with diagonal weights `D i := ‖c i‖²`.
  let w : ℤ → E := fun i => c i • v i
  let D : ℤ → ℝ := fun i => ‖c i‖ ^ 2

  have hD : ∀ i ∈ J, 0 ≤ D i := by
    intro i hi
    dsimp [D]
    positivity

  have hGram' :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪w i, w j⟫‖ ≤ (a (SSU.Hilbert.distZ i j) : ℝ) * Real.sqrt (D i) * Real.sqrt (D j) := by
    intro i hi j hj
    dsimp [w, D]
    have :
        ⟪c i • v i, c j • v j⟫ = (star (c i)) * (c j) * ⟪v i, v j⟫ := by
      -- `simp` gives a permuted product; commute in `ℂ`.
      simp [mul_assoc, mul_left_comm, mul_comm]
    -- Take norms and bound.
    have hsqrt : ∀ z : ℂ, Real.sqrt (‖z‖ ^ 2) = ‖z‖ := by
      intro z
      -- `‖z‖ ≥ 0`, so `|‖z‖| = ‖z‖`.
      simpa [pow_two, abs_of_nonneg (by positivity : 0 ≤ ‖z‖)] using
        (Real.sqrt_sq_eq_abs ‖z‖)
    calc
      ‖⟪c i • v i, c j • v j⟫‖
          = ‖(star (c i)) * (c j) * ⟪v i, v j⟫‖ := by simpa [this]
      _ = ‖c i‖ * ‖c j‖ * ‖⟪v i, v j⟫‖ := by
            -- expand norms and simplify `‖star z‖ = ‖z‖`.
            simp [mul_assoc, norm_mul]
      _ ≤ ‖c i‖ * ‖c j‖ * (a (SSU.Hilbert.distZ i j) : ℝ) := by
            gcongr
            exact hGram i hi j hj
      _ = (a (SSU.Hilbert.distZ i j) : ℝ) * Real.sqrt (‖c i‖ ^ 2) * Real.sqrt (‖c j‖ ^ 2) := by
            simp [mul_assoc, mul_left_comm, mul_comm, hsqrt]

  have hRow' :
      ∀ i ∈ J, (∑ j ∈ J, (a (SSU.Hilbert.distZ i j) : ℝ)) ≤ Crow := hRow

  -- Now apply the interzone lemma.
  simpa [w, D] using
    (SSU.Hilbert.norm_sum_sq_le_of_rowSum_gram_boundZ
      (J := J) (v := w) (D := D) (a := a) (Crow := Crow)
      hD hGram' hRow')

end

end LargeSieve
end Engines
end SSU
