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

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace RankOneShear

open Complex
open SSU.Engines.TypeII

/-!
## “Swapped” rank-one bound (interval on the coefficient side)

This is the TeX Step 3/4 Cauchy–Schwarz move in the *other* direction:

* apply Cauchy–Schwarz in the **interval variable** (`v`), and
* apply MV large sieve to the resulting **sum of squares** of exponential sums in the other
  variable (`u`), assuming `u` runs over an interval.

Compared to `norm_rankOneSignal_sq_le_one_add_log`, the polylog constant depends on the *length of
the `u`-interval* rather than the length of the `v`-interval.  This is convenient when one wants a
TeX-like “(outer length) + (frequency spacing)^{-1}” loss in the outer variable.
-/

/-- A TeX-friendly bound obtained by Cauchy–Schwarz in the `v`-interval and MV on the `u`-interval.

This is a “rank-one only” helper lemma: it does not address the fully general matrix-coefficient
case in TeX Step 3/4, but it is a useful intermediate building block for the rank-one Type–II
model. -/
theorem norm_rankOneSignal_sq_le_one_add_log_swap_interval
    (A B : ℤ) (hAB : A ≤ B)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (R : ℕ)
    (hDist :
      ∀ i ∈ (Finset.Icc a (a + (N : ℤ) - 1)), ∀ j ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        SSU.Hilbert.distZ i j ≤ R)
    (t : ℝ) (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0) :
    ‖∑ u ∈ (Finset.Icc A B),
        β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
      ≤
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), ‖α v‖ ^ 2) *
      (((B + 1 - A).toNat : ℝ) + (1 / |t|) * (1 + Real.log R)) *
      (∑ u ∈ (Finset.Icc A B), ‖β u‖ ^ 2) := by
  classical
  let uIcc : Finset ℤ := Finset.Icc A B
  let vIcc : Finset ℤ := Finset.Icc a (a + (N : ℤ) - 1)

  -- Coefficient interval length: `Nu = (B+1-A).toNat`.
  let Nu : ℕ := (B + 1 - A).toNat
  have hNu_pos : 0 ≤ (B + 1 - A) := by linarith
  have hNu_cast : (Nu : ℤ) = (B + 1 - A) := by
    -- `toNat` is exact under nonnegativity.
    simpa [Nu, Int.toNat_of_nonneg hNu_pos]
  have hub : A + (Nu : ℤ) - 1 = B := by
    -- `A + (B+1-A) - 1 = B`.
    -- Use `hNu_cast` to remove the `toNat`.
    linarith [hNu_cast]
  have hIcc_u : (Finset.Icc A (A + (Nu : ℤ) - 1)) = uIcc := by
    simp [uIcc, hub]

  -- Swap the order of summation, and commute the phase to match the MV interface.
  have hswap :
      (∑ u ∈ uIcc,
          β u * (∑ v ∈ vIcc, α v * e (t * (u : ℝ) * (v : ℝ))))
        =
      (∑ v ∈ vIcc,
          α v * (∑ u ∈ uIcc, β u * e (t * (v : ℝ) * (u : ℝ)))) := by
    classical
    calc
      (∑ u ∈ uIcc,
          β u * (∑ v ∈ vIcc, α v * e (t * (u : ℝ) * (v : ℝ))))
          =
        ∑ u ∈ uIcc, ∑ v ∈ vIcc, β u * (α v * e (t * (u : ℝ) * (v : ℝ))) := by
          simp [Finset.mul_sum, mul_assoc]
      _ =
        ∑ v ∈ vIcc, ∑ u ∈ uIcc, β u * (α v * e (t * (u : ℝ) * (v : ℝ))) := by
          exact Finset.sum_comm
      _ =
        ∑ v ∈ vIcc, α v * (∑ u ∈ uIcc, β u * e (t * (v : ℝ) * (u : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

  -- Apply the existing TeX-friendly MV corollary with roles swapped:
  -- outer index set = `vIcc`, inner interval = `uIcc`.
  have hMV :=
    norm_rankOneSignal_sq_le_one_add_log
      (J := vIcc) (R := R) (hDist := hDist)
      (t := t) (ht := ht) (ht0 := ht0)
      (a := A) (N := Nu) (α := β) (β := α)

  -- Convert the `Fin Nu` energy to the `Icc A B` energy.
  have hβ_energy :
      (∑ k ∈ (Finset.univ : Finset (Fin Nu)), ‖β (A + (k : ℕ))‖ ^ 2)
        =
      (∑ u ∈ uIcc, ‖β u‖ ^ 2) := by
    classical
    -- First rewrite the `Fin` sum as a `range` sum.
    have hFin :
        (∑ k ∈ (Finset.univ : Finset (Fin Nu)), ‖β (A + (k : ℕ))‖ ^ 2)
          =
        ∑ n ∈ Finset.range Nu, ‖β (A + n)‖ ^ 2 := by
      -- Remove the membership binder, then use `Fin.sum_univ_eq_sum_range`.
      have h1 :
          (∑ k ∈ (Finset.univ : Finset (Fin Nu)), ‖β (A + (k : ℕ))‖ ^ 2)
            =
          ∑ k : Fin Nu, ‖β (A + (k : ℕ))‖ ^ 2 := by
        simp
      have h2 :
          (∑ k : Fin Nu, ‖β (A + (k : ℕ))‖ ^ 2)
            =
          ∑ n ∈ Finset.range Nu, ‖β (A + n)‖ ^ 2 := by
        -- `Fin.sum_univ_eq_sum_range` expects a function on `ℕ` (using the coercion `Fin Nu → ℕ`).
        simpa using (Fin.sum_univ_eq_sum_range (fun n : ℕ => ‖β (A + n)‖ ^ 2) Nu)
      exact h1.trans h2
    -- Rewrite the `Icc` sum as a `range` sum.
    have hIcc :
        (∑ u ∈ (Finset.Icc A (A + (Nu : ℤ) - 1)), ‖β u‖ ^ 2)
          =
        ∑ n ∈ Finset.range Nu, ‖β (A + n)‖ ^ 2 := by
      have hNat : ((A + (Nu : ℤ) - 1 + 1 - A)).toNat = Nu := by simp
      simpa [MV.sum_Icc_eq_sum_range, hNat, add_assoc, add_left_comm, add_comm] using
        (MV.sum_Icc_eq_sum_range (a := A) (b := A + (Nu : ℤ) - 1) (f := fun u : ℤ => ‖β u‖ ^ 2))
    simpa [hIcc_u] using (hFin.trans hIcc.symm)

  have hMain :
      ‖∑ v ∈ vIcc,
          α v * (∑ u ∈ uIcc, β u * e (t * (v : ℝ) * (u : ℝ)))‖ ^ 2
        ≤
      (∑ v ∈ vIcc, ‖α v‖ ^ 2) *
        ((Nu : ℝ) + (1 / |t|) * (1 + Real.log R)) *
        (∑ u ∈ uIcc, ‖β u‖ ^ 2) := by
    have hMV' :
        ‖∑ v ∈ vIcc,
            α v * (∑ u ∈ (Finset.Icc A (A + (Nu : ℤ) - 1)),
              β u * e (t * (v : ℝ) * (u : ℝ)))‖ ^ 2
          ≤
        (∑ v ∈ vIcc, ‖α v‖ ^ 2) *
          ((Nu : ℝ) + (1 / |t|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin Nu)), ‖β (A + (k : ℕ))‖ ^ 2) := by
      simpa [vIcc] using hMV
    simpa [hIcc_u, hβ_energy] using hMV'

  -- Finish by swapping the finite sums.
  calc
    ‖∑ u ∈ uIcc,
        β u * (∑ v ∈ vIcc, α v * e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
        =
      ‖∑ v ∈ vIcc,
          α v * (∑ u ∈ uIcc, β u * e (t * (v : ℝ) * (u : ℝ)))‖ ^ 2 := by
        simpa [hswap]
    _ ≤
      (∑ v ∈ vIcc, ‖α v‖ ^ 2) *
        ((Nu : ℝ) + (1 / |t|) * (1 + Real.log R)) *
        (∑ u ∈ uIcc, ‖β u‖ ^ 2) := hMain
    _ = _ := by
        simp [uIcc, vIcc, Nu]

end RankOneShear

end
end LargeSieve
end Engines
end SSU
