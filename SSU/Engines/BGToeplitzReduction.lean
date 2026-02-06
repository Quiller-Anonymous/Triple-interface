import SSU.Engines.TypeIIToeplitz

/-!
05_BG.tex (BG) — Toeplitz Type–II reduction helper.

This file packages a TeX-faithful intermediate target for the Toeplitz Type–II reduction:

* Define a tube coefficient array on lattice points `p = (d,n)` as `F(p) = α_d β_n W(p)`.
* Define the aggregated product coefficients `A_k := ∑_{dn=k} F(d,n)` (TeX Eq. (5.2)).
* Treat the TeX Toeplitz quadratic form
    `∑_{k,k'} A_{k'} * conj(A_k) * K(k' - k)`
  as the *authoritative* “group-by-product” expression.

Then the deterministic lemma in `SSU.Engines.BGToeplitz` converts this `k,k'`-sum into the
`tubeFormProd` used by `SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd`.

This isolates what remains to be proved in applications:
an identity of the form `⟪T_i f, T_j f⟫ = (k,k')-Toeplitz form`.
-/

namespace SSU
namespace Engines
namespace BGToeplitzReduction

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz

namespace TeX

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A TeX-style Type–II coefficient factorization on tube lattice points `(d,n)`. -/
structure CoeffFactorization where
  tube : Finset TubePoint
  /-- Coefficients `α_d` (depends on the application; may depend on `f,i,j`). -/
  α : H → ℤ → ℤ → ℤ → ℂ
  /-- Coefficients `β_n` (depends on the application; may depend on `f,i,j`). -/
  β : H → ℤ → ℤ → ℤ → ℂ
  /-- Cutoff/weight `W(d,n)` (TeX: `W(d/D,n/N)`). -/
  W : TubePoint → ℂ

namespace CoeffFactorization

variable (C : CoeffFactorization (H := H))

open SSU.Engines.TypeII.ProductToeplitz

/-- Tube coefficient array `F(d,n) = α_d β_n W(d,n)` on `TubePoint = (d,n)`. -/
noncomputable def F (f : H) (i j : ℤ) : TubePoint → ℂ :=
  fun p => (C.α f i j p.1) * (C.β f i j p.2) * (C.W p)

/-- Aggregated product coefficients `A_k := ∑_{dn=k} F(d,n)` (TeX Eq. (5.2)). -/
noncomputable def A (f : H) (i j k : ℤ) : ℂ :=
  SSU.Engines.TypeII.ProductToeplitz.coeffByProd C.tube (C.F f i j) k

-- The constructor in `TypeIIToeplitz` uses `tubeFormProd`, so this is the expression we provide
-- applications when they are proving the reduction identity.
noncomputable def toeplitzForm (K : ℤ → ℝ) (f : H) (i j : ℤ) : ℂ :=
  SSU.Engines.TypeII.ProductToeplitz.tubeFormProd K C.tube (C.F f i j)

/-!
### TeX Toeplitz quadratic form

05_BG.tex line 37 uses the “group by product” expression

`∑_{k,k'} A_{k'} * conj(A_k) * K(k' - k)`.

This is deterministically equivalent to `tubeFormProd` once the kernel is even (as in BG).
-/

/-- The TeX `k,k'` Toeplitz form (05_BG.tex line 37). -/
noncomputable def toeplitzFormTeX (K : ℤ → ℝ) (f : H) (i j : ℤ) : ℂ :=
  ∑ k ∈ C.tube.image prod, ∑ k' ∈ C.tube.image prod,
    (C.A f i j k') * star (C.A f i j k) * (K (k' - k))

theorem toeplitzForm_eq_sum_image_prod (K : ℤ → ℝ) (f : H) (i j : ℤ) :
    C.toeplitzForm K f i j =
      ∑ k ∈ C.tube.image prod, ∑ k' ∈ C.tube.image prod,
        (C.A f i j k) * (K (k' - k)) * star (C.A f i j k') := by
  -- This is exactly `ProductToeplitz.tubeFormProd_eq_sum_image_prod`, specialized to `F := C.F f i j`.
  simpa [CoeffFactorization.toeplitzForm, CoeffFactorization.A, CoeffFactorization.F] using
    (SSU.Engines.TypeII.ProductToeplitz.tubeFormProd_eq_sum_image_prod
      (K := K) (T := C.tube) (F := C.F f i j))

theorem toeplitzFormTeX_eq_toeplitzForm
    (K : ℤ → ℝ) (hK : ∀ t : ℤ, K (-t) = K t) (f : H) (i j : ℤ) :
    C.toeplitzFormTeX K f i j = C.toeplitzForm K f i j := by
  classical
  -- Expand the RHS as the “direct” grouped-by-product sum, then show the TeX-ordered sum agrees
  -- by reindexing `(k,k') ↦ (k',k)` and using evenness of `K`.
  have h2 := (C.toeplitzForm_eq_sum_image_prod (K := K) f i j)
  -- Unfold the TeX form on the LHS and the grouped form on the RHS.
  simp [CoeffFactorization.toeplitzFormTeX]
  rw [h2]
  -- Abbreviations for the product-index set and the aggregated coefficients.
  let S : Finset ℤ := C.tube.image prod
  have hS : C.tube.image prod = S := by
    rfl
  -- Rewrite both double sums as sums over `S × S`.
  have hL' :
      (∑ kk ∈ S.product S, (C.A f i j kk.2) * star (C.A f i j kk.1) * (K (kk.2 - kk.1)))
        =
      ∑ k ∈ S, ∑ k' ∈ S, (C.A f i j k') * star (C.A f i j k) * (K (k' - k)) := by
    simpa [Finset.sum_product, mul_assoc, mul_left_comm, mul_comm]
  have hR' :
      (∑ kk ∈ S.product S, (C.A f i j kk.1) * (K (kk.2 - kk.1)) * star (C.A f i j kk.2))
        =
      ∑ k ∈ S, ∑ k' ∈ S, (C.A f i j k) * (K (k' - k)) * star (C.A f i j k') := by
    simpa [Finset.sum_product, mul_assoc, mul_left_comm, mul_comm]
  -- Replace both sides by sums over `S.product S`.
  -- First rewrite the goal’s finsets in terms of `S`.
  simp [hS] at *
  rw [← hL', ← hR']
  -- Now it is a deterministic reindexing of a single sum over `S × S`.
  -- Use `Finset.sum_bij` with the involution `swap : (k,k') ↦ (k',k)`.
  refine Finset.sum_bij
      (s := S.product S) (t := S.product S)
      (f := fun kk => (C.A f i j kk.2) * star (C.A f i j kk.1) * (K (kk.2 - kk.1)))
      (g := fun kk => (C.A f i j kk.1) * (K (kk.2 - kk.1)) * star (C.A f i j kk.2))
      (i := fun kk _ => (kk.2, kk.1))
      (hi := ?_) (i_inj := ?_) (i_surj := ?_) (h := ?_)
  · intro kk hkk
    rcases Finset.mem_product.mp hkk with ⟨hk1, hk2⟩
    exact Finset.mem_product.mpr ⟨hk2, hk1⟩
  · intro a ha b hb hab
    -- `swap a = swap b` implies `a = b`.
    cases a with
    | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
        cases hab
        rfl
  · intro kk hkk
    -- Surjectivity: take `swap kk` as preimage.
    refine ⟨(kk.2, kk.1), ?_, rfl⟩
    rcases Finset.mem_product.mp hkk with ⟨hk1, hk2⟩
    exact Finset.mem_product.mpr ⟨hk2, hk1⟩
  · intro kk hkk
    -- Compare the term at `kk` with the target term at `swap kk`.
    -- Use evenness to replace `K (kk.1 - kk.2)` by `K (kk.2 - kk.1)`.
    have hK' : K (kk.1 - kk.2) = K (kk.2 - kk.1) := by
      have : -(kk.2 - kk.1) = kk.1 - kk.2 := by abel
      simpa [this] using (hK (kk.2 - kk.1))
    -- Unfold `i` and simplify.
    simp [hK', mul_assoc, mul_left_comm, mul_comm]

end CoeffFactorization

/--
Constructor: build a `ReductionToTubeFormProd` once the application proves the TeX toeplitz-form
identity for Gram entries, plus an energy comparison for the coefficient array.

This is the *TeX-faithful interface* for the Toeplitz Type–II reduction: the only real work is
proving `inner_eq_toeplitzForm`.
-/
noncomputable def mkReductionToTubeFormProd
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)}
    (X Hpar : ℝ) (K : ℤ → ℝ)
    (C : CoeffFactorization (H := H))
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_toeplitzForm :
      ∀ f : H, ∀ i ∈ J, ∀ j ∈ J,
        inner ℂ (T i f) (T j f) = C.toeplitzForm K f i j)
    (energy_le :
      ∀ f : H, ∀ i ∈ J, ∀ j ∈ J,
        tubeEnergy C.tube (C.F f i j) ≤ Cenergy * ‖T i f‖ * ‖T j f‖) :
    ReductionToTubeFormProd (H := H) (J := J) (T := T) X Hpar K C.tube :=
by
  classical
  refine
    { Cenergy := Cenergy
      Cenergy_nonneg := Cenergy_nonneg
      F := fun f i j => C.F f i j
      inner_eq := ?_
      energy_le := ?_ }
  · intro f i hi j hj
    -- Replace by the TeX toeplitz-form identity, then convert toeplitz-form to `tubeFormProd`.
    have h1 : inner ℂ (T i f) (T j f) = C.toeplitzForm K f i j :=
      inner_eq_toeplitzForm f i hi j hj
    simpa [CoeffFactorization.toeplitzForm] using h1
  · intro f i hi j hj
    simpa using energy_le f i hi j hj

end TeX

end

end BGToeplitzReduction
end Engines
end SSU
