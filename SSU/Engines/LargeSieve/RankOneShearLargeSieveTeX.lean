import SSU.Engines.LargeSieve.RankOneShearLargeSieve

/-!
TeX-friendly corollaries of `RankOneShearLargeSieve`.

This file replaces the opaque MV constant `LS.C` by the explicit polylog expression

`N + (1/|t|) * (1 + log R)`

provided by `MV.finiteLargeSieve_of_distBound_C_le_one_add_log`.

It is intended as a small step toward `05b_SSU.tex` Step 3/4 bounds, where the large-sieve
constant is tracked in this “(length) + (frequency spacing)^{-1} * (1+log diameter)” form.
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace RankOneShear

open Complex

/-!
## Packaging: bound in terms of the 2D `ℓ²` energy on a rank-one box

The TeX statements (Step 3/4) are phrased with the coefficient energy `∑_{T'} |F|²` on a box
`T' ⊂ ℤ×ℤ`.  For *rank-one* arrays `F(u,v) = β(u) α(v)` on a product set, the energy factors
exactly as a product of 1D energies.

This section records the exact factorization and a convenient corollary of
`norm_rankOneSignal_sq_le_one_add_log` with the RHS rewritten as `C * boxEnergy`.
-/

/-- 2D `ℓ²` energy of the rank-one array `F(u,v) := β(u) α(v)` on the product set
`J × {a, a+1, ..., a+(N-1)}` (encoded with `Fin N`). -/
def boxEnergy (J : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) : ℝ :=
  ∑ u ∈ J, ∑ k ∈ (Finset.univ : Finset (Fin N)), ‖β u * α (a + (k : ℕ))‖ ^ 2

theorem boxEnergy_eq
    (J : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    boxEnergy J a N α β
      =
    (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  unfold boxEnergy
  -- Factor the norm on each term, then pull the `α`-energy out of the `u`-sum.
  have hterm (u : ℤ) :
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖β u * α (a + (k : ℕ))‖ ^ 2)
        =
      (‖β u‖ ^ 2) * (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
    -- `‖β*α‖^2 = ‖β‖^2 * ‖α‖^2` termwise.
    have :
        (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖β u * α (a + (k : ℕ))‖ ^ 2)
          =
        ∑ k ∈ (Finset.univ : Finset (Fin N)),
          (‖β u‖ ^ 2) * (‖α (a + (k : ℕ))‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [norm_mul, mul_pow]
    -- Pull out the constant factor `‖β u‖^2`.
    simpa [this, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  calc
    (∑ u ∈ J, ∑ k ∈ (Finset.univ : Finset (Fin N)), ‖β u * α (a + (k : ℕ))‖ ^ 2)
        =
      ∑ u ∈ J, (‖β u‖ ^ 2) * (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        simpa using hterm u
    _ =
      (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
        -- pull the constant inner energy out of the `u`-sum
        simpa using
          (Finset.sum_mul (s := J) (f := fun u : ℤ => ‖β u‖ ^ 2)
            (a := ∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2)).symm
    _ = _ := by
        ring

theorem norm_rankOneSignal_sq_le_one_add_log
    (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (t : ℝ) (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖∑ u ∈ J,
        β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * SSU.Engines.TypeII.e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
      ≤
    (∑ u ∈ J, ‖β u‖ ^ 2) *
      ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  -- Start from the MV bound with the raw Crow constant.
  have hMV :=
    norm_rankOneSignal_sq_le_MV (J := J) (R := R) (hDist := hDist)
      (t := t) (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β)
  -- Replace `LS.C` by the explicit polylog bound.
  have hC :
      (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
          (hDist := hDist) (ht := by simpa using ht) (ht0 := by simpa using neg_ne_zero.2 ht0)).C
        ≤
      (N : ℝ) + (1 / |t|) * (1 + Real.log R) := by
    -- Use the general bound, and simplify `|-t| = |t|`.
    have h :=
      MV.finiteLargeSieve_of_distBound_C_le_one_add_log
        (J := J) (N := N) (t := -t) (R := R) (hDist := hDist)
        (ht := by simpa using ht) (ht0 := by simpa using neg_ne_zero.2 ht0)
    simpa [abs_neg] using h
  have hβ_nonneg : 0 ≤ (∑ u ∈ J, ‖β u‖ ^ 2 : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro u hu
    positivity
  -- Multiply the `LS.C` bound into the MV inequality.
  have hmul :
      (∑ u ∈ J, ‖β u‖ ^ 2) *
          (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
              (hDist := hDist) (ht := by simpa using ht)
              (ht0 := by simpa using neg_ne_zero.2 ht0)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2)
        ≤
      (∑ u ∈ J, ‖β u‖ ^ 2) * ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
    have hCmul :
        (∑ u ∈ J, ‖β u‖ ^ 2) *
            (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
                (hDist := hDist) (ht := by simpa using ht)
                (ht0 := by simpa using neg_ne_zero.2 ht0)).C
          ≤
        (∑ u ∈ J, ‖β u‖ ^ 2) * ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) := by
      exact mul_le_mul_of_nonneg_left hC hβ_nonneg
    -- Finish by multiplying on the right by the nonnegative coefficient energy.
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · simpa [mul_assoc] using hCmul
    · positivity
  exact hMV.trans hmul

theorem norm_rankOneSignal_sq_le_one_add_log_boxEnergy
    (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (t : ℝ) (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖∑ u ∈ J,
        β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * SSU.Engines.TypeII.e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) * boxEnergy J a N α β := by
  classical
  have h :=
    norm_rankOneSignal_sq_le_one_add_log
      (J := J) (R := R) (hDist := hDist) (t := t) (ht := ht) (ht0 := ht0)
      (a := a) (N := N) (α := α) (β := β)
  -- Rewrite the RHS product of energies as `boxEnergy`.
  have hE := (boxEnergy_eq (J := J) (a := a) (N := N) (α := α) (β := β))
  -- `h` has `Eβ * C * Eα`; commute to `C * (Eβ*Eα)` then use `boxEnergy_eq`.
  -- (All factors are nonnegative reals, so commutation is safe.)
  -- First rewrite and then `simpa`.
  have :
      (∑ u ∈ J, ‖β u‖ ^ 2) *
          ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2)
        =
      ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) * boxEnergy J a N α β := by
    -- Use `boxEnergy_eq` and `ring`.
    -- `boxEnergy_eq` gives `boxEnergy = Eβ * Eα`.
    -- Move `C` to the front.
    calc
      (∑ u ∈ J, ‖β u‖ ^ 2) *
            ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
            (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2)
          =
        ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
          ((∑ u ∈ J, ‖β u‖ ^ 2) *
            (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2)) := by
          ring
      _ = ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) * boxEnergy J a N α β := by
          simpa [hE] using rfl
  exact h.trans_eq this

end RankOneShear

end
end LargeSieve
end Engines
end SSU
