import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Dist

/-!
`MajorArcModules/Q0MinorInterzone` is a project-neutral “almost-orthogonality” brick
for the ε₁ (minor / Q0-complement) side. "Interzone" here is just a cheeky way of
referring to the attempt to connect two 'zones', Q0MinorEnergyLedgerEngine in Goldbach and
MinorArcDispersionEnergyBoundNorm in Twin.

The goal is to package a *textbook* Hilbert-space estimate of the following form.

Let `f_j` be a finite family of vectors in an `ℓ²`-type space (in this repo: functions on
`EvenIn X H`). Assume:

* diagonal control: `‖f_j‖² ≤ D_j`;
* cross-level decay: `‖⟪f_i,f_j⟫‖ ≤ a(dist i j) * √D_i * √D_j`;
* a uniform row-sum bound `∑_{j} a(dist i j) ≤ C`.

Then

`‖∑_j f_j‖² ≤ C * ∑_j D_j`.

This is the standard “almost orthogonality” glue (a Cotlar–Stein / Schur-type estimate) and is
independent of the arithmetic meaning of the indices.  In the Goldbach pdf language, one typically
chooses the indices to be dyadic denominator levels, but this file does not hard-code that choice.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorInterzone

open scoped BigOperators

open Complex

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

private lemma re_sum_le_sum_norm {α : Type*} [DecidableEq α] {s : Finset α} (f : α → ℂ) :
    (∑ a ∈ s, (f a).re) ≤ ∑ a ∈ s, ‖f a‖ := by
  classical
  refine Finset.sum_le_sum ?_
  intro a ha
  exact re_le_norm (f a)

private lemma mul_sqrt_mul_sqrt_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  have h := two_mul_le_add_sq (Real.sqrt a) (Real.sqrt b)
  -- `2 * √a * √b ≤ (√a)^2 + (√b)^2 = a + b`.
  have hsqa : (Real.sqrt a) ^ 2 = a := by
    simpa [pow_two] using (Real.sq_sqrt ha)
  have hsqb : (Real.sqrt b) ^ 2 = b := by
    simpa [pow_two] using (Real.sq_sqrt hb)
  have h' : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
    -- rewrite the squares
    simpa [pow_two, hsqa, hsqb, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm,
      add_assoc] using h
  -- Divide by 2 (via `nlinarith`).
  nlinarith

/-!
### The core interzone inequality (finite family)

The statement is formulated in an arbitrary complex inner-product space `E`.  In applications,
`E` will be an `L²`-type space such as `EuclideanSpace ℂ ι`.
-/

theorem norm_sum_sq_le_of_rowSum_gram_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Finset ℕ} {v : ℕ → E} {D : ℕ → ℝ} {a : ℕ → ℝ} {C : ℝ}
    (hD : ∀ j ∈ J, 0 ≤ D j)
    (ha : ∀ k, 0 ≤ a k)
    (hGram :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪v i, v j⟫‖ ≤ a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j))
    (hRow :
      ∀ i ∈ J, (∑ j ∈ J, a (Nat.dist i j)) ≤ C) :
    ‖∑ j ∈ J, v j‖ ^ 2 ≤ C * ∑ j ∈ J, D j := by
  classical
  -- Expand `‖∑ v‖²` via `re ⟪·,·⟫` and bound by the sum of norms of Gram entries.
  have hnorm :
      ‖∑ j ∈ J, v j‖ ^ 2
        =
      (⟪∑ j ∈ J, v j, ∑ j ∈ J, v j⟫).re := by
    -- `norm_sq_eq_re_inner` is the defining axiom of an inner-product space.
    simpa [pow_two] using (norm_sq_eq_re_inner (𝕜 := ℂ) (∑ j ∈ J, v j))
  -- Rewrite the inner product as a double sum.
  have hinner :
      (⟪∑ j ∈ J, v j, ∑ j ∈ J, v j⟫ : ℂ)
        =
      ∑ i ∈ J, ∑ j ∈ J, ⟪v i, v j⟫ := by
    -- Bilinearity of `inner` over finite sums.
    -- We avoid `simp` here because `simp` sometimes rewrites `⟪x,x⟫` to `‖x‖²`.
    calc
      (⟪∑ j ∈ J, v j, ∑ j ∈ J, v j⟫ : ℂ)
          = ∑ i ∈ J, ⟪v i, ∑ j ∈ J, v j⟫ := by
              simpa using (sum_inner (𝕜 := ℂ) (E := E) J v (∑ j ∈ J, v j))
      _ = ∑ i ∈ J, ∑ j ∈ J, ⟪v i, v j⟫ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (inner_sum (𝕜 := ℂ) (E := E) J v (v i))
  -- Bound the real part termwise by the norm.
  have hRe_le :
      (∑ i ∈ J, ∑ j ∈ J, (⟪v i, v j⟫ : ℂ).re)
        ≤
      ∑ i ∈ J, ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖ := by
    -- Apply `re ≤ ‖·‖` pointwise.
    refine Finset.sum_le_sum ?_
    intro i hi
    have :
        (∑ j ∈ J, (⟪v i, v j⟫ : ℂ).re) ≤ ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖ :=
      re_sum_le_sum_norm (s := J) (f := fun j => (⟪v i, v j⟫ : ℂ))
    exact this
  -- Put the pieces together to get an upper bound by the Gram norms.
  have hsumGram :
      ‖∑ j ∈ J, v j‖ ^ 2 ≤ ∑ i ∈ J, ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖ := by
    -- Convert `‖·‖²` to `re ⟪·,·⟫`, expand, and bound.
    rw [hnorm, hinner]
    -- `re` distributes over sums.
    have hre : (∑ i ∈ J, ∑ j ∈ J, ⟪v i, v j⟫).re
        = ∑ i ∈ J, ∑ j ∈ J, (⟪v i, v j⟫ : ℂ).re := by
      simp
    -- Now bound termwise.
    simpa [hre] using hRe_le

  -- Use the assumed Gram bound to bound the double sum by a weighted quadratic form in `√D`.
  have hsumA :
      (∑ i ∈ J, ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖)
        ≤
      ∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hGram i hi j hj

  -- Bound the weighted quadratic form using `2ab ≤ a^2 + b^2` and the row-sum bound.
  have hquad :
      (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j))
        ≤
      C * ∑ i ∈ J, D i := by
    -- First, symmetrize using `√D_i √D_j ≤ (D_i + D_j)/2`.
    have hstep :
        (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j))
          ≤
        (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * ((D i + D j) / 2)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      have hDi : 0 ≤ D i := hD i hi
      have hDj : 0 ≤ D j := hD j hj
      have hsqrt :
          Real.sqrt (D i) * Real.sqrt (D j) ≤ (D i + D j) / 2 :=
        mul_sqrt_mul_sqrt_le_add_div_two hDi hDj
      have hnonneg : 0 ≤ a (Nat.dist i j) := ha (Nat.dist i j)
      -- Multiply by `a(dist i j) ≥ 0`.
      have := mul_le_mul_of_nonneg_left hsqrt hnonneg
      -- Reassociate products.
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    -- Now expand and use the row-sum bound.
    have hstep' :
        (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * ((D i + D j) / 2))
          ≤
        C * ∑ i ∈ J, D i := by
      -- A “column sum” bound follows from symmetry of `Nat.dist`.
      have hCol : ∀ j ∈ J, (∑ i ∈ J, a (Nat.dist i j)) ≤ C := by
        intro j hj
        have :
            (∑ i ∈ J, a (Nat.dist i j)) = ∑ i ∈ J, a (Nat.dist j i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [Nat.dist_comm] using (rfl : a (Nat.dist i j) = a (Nat.dist j i))
        simpa [this] using hRow j hj

      -- Algebraic decomposition of the symmetrized term.
      have hdecomp :
          (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * ((D i + D j) / 2))
            =
          (∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            + (∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹))) := by
        -- Termwise: `a * ((D i + D j)/2) = D i * (a/2) + D j * (a/2)`.
        simp [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          mul_assoc, mul_left_comm, mul_comm]

      -- Apply the row-sum and column-sum bounds to the two pieces.
      have hrow1 :
          (∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) := by
        -- For each fixed `i`, factor out `D i` and use the row-sum bound on `∑ a(dist i j)`.
        have hterm :
            (∑ i ∈ J, D i * (∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              ≤
            ∑ i ∈ J, D i * (C * ((2 : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hDi : 0 ≤ D i := hD i hi
          have hrowi : (∑ j ∈ J, a (Nat.dist i j)) ≤ C := hRow i hi
          have hrowi' :
              (∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)) ≤ C * ((2 : ℝ)⁻¹) := by
            have hhalf_nonneg : 0 ≤ ((2 : ℝ)⁻¹) := by
              exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)
            have hmul := mul_le_mul_of_nonneg_right hrowi hhalf_nonneg
            -- Rewrite `(∑ a) * (2⁻¹)` as `∑ a * (2⁻¹)`.
            have hs :
                (∑ j ∈ J, a (Nat.dist i j)) * ((2 : ℝ)⁻¹)
                  =
                ∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹) := by
              simpa using (Finset.sum_mul J (fun j => a (Nat.dist i j)) ((2 : ℝ)⁻¹))
            simpa [hs] using hmul
          -- Now multiply by `D i ≥ 0`.
          have := mul_le_mul_of_nonneg_left hrowi' hDi
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this
        -- Convert the LHS to a double sum and the RHS to a product.
        have hsL :
            (∑ i ∈ J, D i * (∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              =
            ∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        have hsR :
            (∑ i ∈ J, D i * (C * ((2 : ℝ)⁻¹))) = (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) := by
          simpa using (Finset.sum_mul J (fun i => D i) (C * ((2 : ℝ)⁻¹))).symm
        simpa [hsL, hsR] using hterm

      have hrow2 :
          (∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ j ∈ J, D j) * (C * ((2 : ℝ)⁻¹)) := by
        -- Same argument, using the column-sum bound.
        have hterm :
            (∑ j ∈ J, D j * (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              ≤
            ∑ j ∈ J, D j * (C * ((2 : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hDj : 0 ≤ D j := hD j hj
          have hcolj : (∑ i ∈ J, a (Nat.dist i j)) ≤ C := hCol j hj
          have hcolj' :
              (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)) ≤ C * ((2 : ℝ)⁻¹) := by
            have hhalf_nonneg : 0 ≤ ((2 : ℝ)⁻¹) := by
              exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)
            have hmul := mul_le_mul_of_nonneg_right hcolj hhalf_nonneg
            have hs :
                (∑ i ∈ J, a (Nat.dist i j)) * ((2 : ℝ)⁻¹)
                  =
                ∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹) := by
              simpa using (Finset.sum_mul J (fun i => a (Nat.dist i j)) ((2 : ℝ)⁻¹))
            simpa [hs] using hmul
          have := mul_le_mul_of_nonneg_left hcolj' hDj
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this
        have hsL0 :
            (∑ j ∈ J, D j * (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              =
            ∑ j ∈ J, ∑ i ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        have hsL :
            (∑ j ∈ J, D j * (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              =
            ∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
          have hswap :
              (∑ j ∈ J, ∑ i ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
                =
              ∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
            simpa using
              (Finset.sum_comm (s := J) (t := J)
                (f := fun j i => D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹))))
          exact hsL0.trans hswap
        have hsR :
            (∑ j ∈ J, D j * (C * ((2 : ℝ)⁻¹))) = (∑ j ∈ J, D j) * (C * ((2 : ℝ)⁻¹)) := by
          simpa using (Finset.sum_mul J (fun j => D j) (C * ((2 : ℝ)⁻¹))).symm
        simpa [hsL, hsR] using hterm

      have hsumEq : (∑ j ∈ J, D j) = ∑ i ∈ J, D i := rfl

      -- Combine the two bounds and simplify.
      have hsum :
          (∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              + (∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) + (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) := by
        -- rewrite the second RHS sum `∑ j D j` as `∑ i D i`
        nlinarith [hrow1, hrow2, hsumEq]

      have hsimp :
          (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) + (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹))
            =
          C * ∑ i ∈ J, D i := by
        ring

      -- Apply the decomposition and the combined bound.
      simpa [hdecomp, hsimp, add_assoc, add_left_comm, add_comm] using hsum

    exact le_trans hstep (le_trans hstep' (le_rfl))

  -- Finish.
  exact le_trans hsumGram (le_trans hsumA hquad)

end

end Goldbach.Cert.MajorArcModules.Q0MinorInterzone
