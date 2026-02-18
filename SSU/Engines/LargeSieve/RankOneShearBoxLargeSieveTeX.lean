import SSU.Engines.LargeSieve.TypeIIShearSumTeX
import SSU.Engines.LargeSieve.RankOneShearLargeSieveTeX

/-!
TeX Step 3/4 large-sieve bound for a **rank-one shear box**.

This is the clean “first real” analytic lemma for the large-sieve stage:

* we work directly with the TeX shear sum `shearSum`,
* we assume coefficients factor as `F(u,v) = β(u) α(v)` on a product set
  `J × {a, a+1, ..., a+(N-1)}`,
* we apply the proved Montgomery–Vaughan large sieve (packaged in
  `RankOneShearLargeSieveTeX`) to obtain a TeX-friendly polylog bound, and
* we rewrite the RHS in terms of the 2D `ℓ²` energy `boxEnergy`.

This lemma is meant to be used **before** any tube restriction: restricting support can only
decrease the energy.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

namespace RankOneShearBox

open SSU.Engines.LargeSieve.RankOneShear

/-- Outer-`u` Montgomery–Vaughan constant for the symmetric dyadic shear box used in TeX Step 3/4. -/
def outerUConst (q : ℤ) (X ξ : ℝ) (U D : ℕ) : ℝ :=
  (D : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log (2 * U))

/-- Outer-`v` Montgomery–Vaughan constant for the symmetric dyadic shear box used in TeX Step 3/4. -/
def outerVConst (q : ℤ) (X ξ : ℝ) (U D : ℕ) : ℝ :=
  ((2 * U + 1 : ℕ) : ℝ) +
    (1 / |(ξ / ((q : ℝ) * X))|) *
      (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))

/-- The rank-one shear box set `J × Icc(a, a+N-1)` as a finset of shear points. -/
def box (J : Finset ℤ) (a : ℤ) (N : ℕ) : Finset ShearPoint :=
  J.product (Finset.Icc a (a + (N : ℤ) - 1))

@[simp] theorem mem_box_iff (J : Finset ℤ) (a : ℤ) (N : ℕ) (uv : ShearPoint) :
    uv ∈ box J a N ↔ uv.1 ∈ J ∧ uv.2 ∈ (Finset.Icc a (a + (N : ℤ) - 1)) := by
  simp [box]

/-!
### Support restriction (box ⇒ smaller box)

This is the deterministic “tube by restriction” move:
if we want to sum only over a subset `J' ⊆ J` of the `u`-indices, we can keep the larger
product set `box J a N` but replace the outer weight `β` by `β' := 1_{J'} · β`.

This preserves the rank-one structure `F(u,v)=β'(u)α(v)` and makes later specializations to
tube-support (e.g. `u ∈ [-U,U]`) painless.
-/

def βrestrict (J' : Finset ℤ) (β : ℤ → ℂ) : ℤ → ℂ :=
  fun u => if u ∈ J' then β u else 0

theorem βrestrict_eq_of_mem {J' : Finset ℤ} {β : ℤ → ℂ} {u : ℤ} (hu : u ∈ J') :
    βrestrict J' β u = β u := by
  simp [βrestrict, hu]

theorem βrestrict_eq_zero_of_not_mem {J' : Finset ℤ} {β : ℤ → ℂ} {u : ℤ} (hu : u ∉ J') :
    βrestrict J' β u = 0 := by
  simp [βrestrict, hu]

/-- On a rank-one shear box, `shearSum` is exactly the rank-one signal sum used by MV. -/
theorem shearSum_eq_rankOneSignal
    (q : ℤ) (X ξ : ℝ) (J : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    shearSum q X ξ (box J a N) (fun uv => β uv.1 * α uv.2)
      =
    ∑ u ∈ J,
      β u *
        (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
  classical
  -- Expand the product finset sum and pull out the outer factor `β u`.
  have hphase (u v : ℤ) :
      SSU.Engines.TypeII.e (ξ * ((u : ℝ) * (v : ℝ)) / ((q : ℝ) * X))
        =
      SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ)) := by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite `shearSum` on the product set as an iterated sum.
  unfold shearSum box
  -- Outer/inner sums over `J × I`.
  simp [Finset.sum_product]
  -- Now factor `β u` out of the inner sum and rewrite the phase using `hphase`.
  refine Finset.sum_congr rfl ?_
  intro u hu
  -- Rewrite the phase inside the `e` factor, pointwise in `v`, and reassociate the products so
  -- we can pull out the constant `β u`.
  have hrew :
      (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          β u * α v * SSU.Engines.TypeII.e (ξ * (u : ℝ) * (v : ℝ) / ((q : ℝ) * X)))
        =
      ∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          β u * (α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    -- reassociate `β u * α v * e(…)` into `β u * (α v * e(…))` and rewrite the phase
    simp [mul_assoc, hphase u v]
  calc
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        β u * α v * SSU.Engines.TypeII.e (ξ * (u : ℝ) * (v : ℝ) / ((q : ℝ) * X)))
        =
      ∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        β u * (α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := hrew
    _ =
      β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
      -- Pull out the constant factor `β u` using `Finset.mul_sum`.
      simpa [Finset.mul_sum] using
        (Finset.mul_sum (a := β u)
          (s := (Finset.Icc a (a + (N : ℤ) - 1)))
          (f := fun v : ℤ =>
            α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ)))).symm

theorem shearSum_box_eq_shearSum_box_of_left_restrict
    (q : ℤ) (X ξ : ℝ) (J J' : Finset ℤ) (hsub : J' ⊆ J) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    shearSum q X ξ (box J a N) (fun uv => (βrestrict J' β) uv.1 * α uv.2)
      =
    shearSum q X ξ (box J' a N) (fun uv => β uv.1 * α uv.2) := by
  classical
  -- Rewrite both sides as rank-one signals.
  have hL :=
    shearSum_eq_rankOneSignal (q := q) (X := X) (ξ := ξ) (J := J) (a := a) (N := N)
      (α := α) (β := βrestrict J' β)
  have hR :=
    shearSum_eq_rankOneSignal (q := q) (X := X) (ξ := ξ) (J := J') (a := a) (N := N)
      (α := α) (β := β)
  -- Reduce to a `Finset.sum_subset` argument on the outer `u`-sum.
  have hsum :
      (∑ u ∈ J',
          (βrestrict J' β u) *
              (∑ v ∈ Finset.Icc a (a + (N : ℤ) - 1),
                α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))))
        =
      ∑ u ∈ J,
          (βrestrict J' β u) *
              (∑ v ∈ Finset.Icc a (a + (N : ℤ) - 1),
                α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
    -- `sum_subset` is oriented as `∑_{u∈J'} = ∑_{u∈J}` (since the summand vanishes off `J'`).
    have hzero :
        ∀ u ∈ J, u ∉ J' →
          (βrestrict J' β u) *
              (∑ v ∈ Finset.Icc a (a + (N : ℤ) - 1),
                α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) = 0 := by
      intro u huJ huJ'
      simp [βrestrict_eq_zero_of_not_mem (u := u) (J' := J') (β := β) huJ']
    exact
      Finset.sum_subset hsub (by
        intro u huJ huJ'
        exact hzero u huJ huJ')
  have hsum' :
      (∑ u ∈ J, (βrestrict J' β u) *
          (∑ v ∈ Finset.Icc a (a + (N : ℤ) - 1),
            α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))))
        =
      ∑ u ∈ J', β u *
          (∑ v ∈ Finset.Icc a (a + (N : ℤ) - 1),
            α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
    -- Use the previous identity and simplify `βrestrict = β` on `J'`.
    refine hsum.symm.trans ?_
    refine Finset.sum_congr rfl ?_
    intro u hu
    simp [βrestrict_eq_of_mem (u := u) (J' := J') (β := β) hu]
  -- Transport back.
  simpa [hL, hR] using hsum'

theorem boxEnergy_left_restrict_eq
    (J J' : Finset ℤ) (hsub : J' ⊆ J) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α (βrestrict J' β)
      =
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β := by
  classical
  unfold SSU.Engines.LargeSieve.RankOneShear.boxEnergy
  -- `sum_subset` is oriented as `∑_{u∈J'} = ∑_{u∈J}`.
  have hzero :
      ∀ u ∈ J, u ∉ J' →
        (∑ k ∈ (Finset.univ : Finset (Fin N)),
            ‖(βrestrict J' β u) * α (a + (k : ℕ))‖ ^ 2) = 0 := by
    intro u huJ huJ'
    have hβ : βrestrict J' β u = 0 :=
      βrestrict_eq_zero_of_not_mem (u := u) (J' := J') (β := β) huJ'
    simp [hβ]
  have hsubset :
      (∑ u ∈ J', ∑ k ∈ (Finset.univ : Finset (Fin N)),
          ‖(βrestrict J' β u) * α (a + (k : ℕ))‖ ^ 2)
        =
      ∑ u ∈ J, ∑ k ∈ (Finset.univ : Finset (Fin N)),
          ‖(βrestrict J' β u) * α (a + (k : ℕ))‖ ^ 2 :=
    Finset.sum_subset hsub (by
      intro u huJ huJ'
      exact hzero u huJ huJ')
  -- Now simplify `βrestrict = β` on `J'`.
  refine hsubset.symm.trans ?_
  refine Finset.sum_congr rfl ?_
  intro u hu
  simp [βrestrict_eq_of_mem (u := u) (J' := J') (β := β) hu]

/-- MV large-sieve bound for the TeX shear sum on a rank-one box, with RHS written as `boxEnergy`. -/
theorem norm_shearSum_sq_le_one_add_log_boxEnergy
    (q : ℤ) (X ξ : ℝ) (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / ((q : ℝ) * X))| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box J a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log R)) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α β := by
  classical
  -- Rewrite `shearSum` as the MV-ready rank-one signal.
  have hrew :=
    shearSum_eq_rankOneSignal (q := q) (X := X) (ξ := ξ) (J := J) (a := a) (N := N)
      (α := α) (β := β)
  -- Apply the MV bound in box-energy form.
  have hMV :=
    SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log_boxEnergy
      (J := J) (R := R) (hDist := hDist)
      (t := (ξ / ((q : ℝ) * X))) (ht := ht) (ht0 := ht0)
      (a := a) (N := N) (α := α) (β := β)
  simpa [hrew] using hMV

/-- Convenience specialization of `norm_shearSum_sq_le_one_add_log_boxEnergy` to an interval
`J = Icc A B`, using the deterministic diameter bound `distZ ≤ toNat (B-A)`. -/
theorem norm_shearSum_sq_le_one_add_log_boxEnergy_Icc
    (q : ℤ) (X ξ : ℝ) (A B : ℤ)
    (ht : |(ξ / ((q : ℝ) * X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box (Finset.Icc A B) a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β := by
  classical
  have hDist :
      ∀ i ∈ (Finset.Icc A B), ∀ j ∈ (Finset.Icc A B),
        SSU.Hilbert.distZ i j ≤ Int.toNat (B - A) := by
    intro i hi j hj
    exact SSU.Hilbert.distZ_le_toNat_sub_of_mem_Icc (A := A) (B := B) (i := i) (j := j) hi hj
  simpa using
    (norm_shearSum_sq_le_one_add_log_boxEnergy
      (q := q) (X := X) (ξ := ξ) (J := Finset.Icc A B) (R := Int.toNat (B - A))
      (hDist := hDist) (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β))

/--
Tube-by-restriction corollary (deterministic):
apply the MV bound on a larger outer set `J` with `β` restricted to a subset `J' ⊆ J`.

This is the exact move used to specialize a box estimate to a tube estimate by shrinking the
`u`-support (without breaking the rank-one form `F(u,v) = β(u)α(v)`).
-/
theorem norm_shearSum_sq_le_one_add_log_boxEnergy_of_left_restrict
    (q : ℤ) (X ξ : ℝ) (J J' : Finset ℤ) (hsub : J' ⊆ J) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / ((q : ℝ) * X))| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box J' a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log R)) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β := by
  classical
  have hmain :=
    norm_shearSum_sq_le_one_add_log_boxEnergy
      (q := q) (X := X) (ξ := ξ) (J := J) (R := R) (hDist := hDist)
      (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := βrestrict J' β)
  -- rewrite LHS using the restriction identity
  have hshear :
      shearSum q X ξ (box J a N) (fun uv => (βrestrict J' β) uv.1 * α uv.2)
        =
      shearSum q X ξ (box J' a N) (fun uv => β uv.1 * α uv.2) :=
    shearSum_box_eq_shearSum_box_of_left_restrict
      (q := q) (X := X) (ξ := ξ) (J := J) (J' := J') (hsub := hsub) (a := a) (N := N)
      (α := α) (β := β)
  -- rewrite RHS energy using the restriction identity
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α (βrestrict J' β)
        =
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β :=
    boxEnergy_left_restrict_eq
      (J := J) (J' := J') (hsub := hsub) (a := a) (N := N) (α := α) (β := β)
  -- transport across both rewrites
  simpa [hshear, hE] using hmain

/-!
### A TeX-faithful dyadic-box specialization

TeX typically uses `u ∈ [-U,U]` and `v ∈ (D,2D]`.  On integers, we encode `(D,2D]` as
`Icc (D+1) (2D)`, i.e. `a := D+1` and `N := D`.

This lemma is just a convenience wrapper around `norm_shearSum_sq_le_one_add_log_boxEnergy_Icc`.
-/

theorem norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic
    (q : ℤ) (X ξ : ℝ) (U D : ℕ)
    (ht : |(ξ / ((q : ℝ) * X))| * (2 * U : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
        (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((D : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log (2 * U))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
        ((D : ℤ) + 1) D α β := by
  classical
  -- Apply the interval version with `A = -U`, `B = U` and note `toNat (B-A) = 2U`.
  have htoNat : ((U : ℤ) + (U : ℤ)).toNat = 2 * U := by
    -- First, `toNat (U+U) = U+U`, then rewrite `U+U` as `2*U`.
    -- (`simp` knows `toNat (ofNat n) = n` for nonnegative integers.)
    have htoNat' : ((U : ℤ) + (U : ℤ)).toNat = U + U := by
      -- Use injectivity of `Int.ofNat` and `Int.toNat_of_nonneg`.
      apply Int.ofNat.inj
      have hnonneg : 0 ≤ (U : ℤ) + (U : ℤ) := by
        -- `U+U ≥ 0`.
        exact_mod_cast (Nat.zero_le (U + U))
      -- `Int.ofNat (Int.toNat z) = z` for `z ≥ 0`, and `z = ofNat (U+U)` here.
      calc
        (Int.ofNat (((U : ℤ) + (U : ℤ)).toNat)) = (U : ℤ) + (U : ℤ) := Int.toNat_of_nonneg hnonneg
        _ = (Int.ofNat (U + U) : ℤ) := by simp
    simpa [two_mul] using htoNat'
  -- Now dispatch to the Icc lemma.
  have h :=
    norm_shearSum_sq_le_one_add_log_boxEnergy_Icc
      (q := q) (X := X) (ξ := ξ) (A := (-(U : ℤ))) (B := (U : ℤ))
      (ht := by simpa [htoNat] using ht) (ht0 := ht0)
      (a := ((D : ℤ) + 1)) (N := D) (α := α) (β := β)
  -- `simp` rewrites `Int.toNat (B-A)` to `2*U` using `htoNat`.
  simpa [htoNat] using h

/-!
### Swapped-dimension dyadic specialization

Same underlying MV lemma, but with the *frequency* set taken to be the dyadic `v`-range
`(D,2D] = Icc(D+1,2D)`, and the coefficient interval taken to be the symmetric `u`-range
`[-U,U] = Icc(-U,U)` (encoded as `a := -U`, `N := 2U+1`).

This is the “outer-v” analogue of `norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic`.
-/

theorem norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic_swap
    (q : ℤ) (X ξ : ℝ) (U D : ℕ)
    (ht :
      |(ξ / ((q : ℝ) * X))| *
          (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box (Finset.Icc ((D : ℤ) + 1) (2 * D : ℤ)) (-(U : ℤ)) (2 * U + 1))
        (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((2 * U + 1 : ℝ) +
          (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc ((D : ℤ) + 1) (2 * D : ℤ))
        (-(U : ℤ)) (2 * U + 1) α β := by
  classical
  -- Directly apply the interval lemma with `J = Icc(D+1,2D)` and `I = Icc(-U,U)`.
  simpa using
    (norm_shearSum_sq_le_one_add_log_boxEnergy_Icc
      (q := q) (X := X) (ξ := ξ) (A := ((D : ℤ) + 1)) (B := (2 * D : ℤ))
      (ht := ht) (ht0 := ht0)
      (a := (-(U : ℤ))) (N := (2 * U + 1)) (α := α) (β := β))

/-!
### Energy on a shear box

This is a small deterministic helper: it relates the literal `ℓ²` energy on the product finset
`box J a N` to the packaged `RankOneShear.boxEnergy` definition (which uses `Fin N` indexing).
-/

private theorem sum_Icc_eq_sum_univ_Fin (a : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), f v)
      =
    ∑ k ∈ (Finset.univ : Finset (Fin N)), f (a + (k : ℕ)) := by
  classical
  -- First rewrite the `Icc` sum as a `range` sum.
  have hNat : ((a + (N : ℤ) - 1 + 1 - a)).toNat = N := by simp
  have hIcc :
      (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), f v)
        =
      ∑ n ∈ Finset.range N, f (a + n) := by
    simpa [SSU.Engines.LargeSieve.MV.sum_Icc_eq_sum_range, hNat, add_assoc, add_left_comm, add_comm] using
      (SSU.Engines.LargeSieve.MV.sum_Icc_eq_sum_range (a := a) (b := a + (N : ℤ) - 1) (f := f))
  -- Convert `range N` to `Fin N`.
  let g : Fin N → ℝ := fun k => f (a + (k : ℕ))
  have hRange :
      (∑ n ∈ Finset.range N, f (a + n)) = ∑ k : Fin N, g k := by
    -- `sum_fin_eq_sum_range` gives a `range` sum with an `if`; simplify it on `range N`.
    have h0 := (Finset.sum_fin_eq_sum_range (n := N) (c := g))
    have h1 :
        (∑ k : Fin N, g k) = ∑ x ∈ Finset.range N, f (a + x) := by
      refine h0.trans ?_
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxlt : x < N := Finset.mem_range.1 hx
      simp [g, hxlt]
    exact h1.symm
  have huniv : (∑ k ∈ (Finset.univ : Finset (Fin N)), g k) = ∑ k : Fin N, g k := by simp
  -- Finish.
  calc
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), f v)
        = ∑ n ∈ Finset.range N, f (a + n) := hIcc
    _ = ∑ k : Fin N, g k := hRange
    _ = ∑ k ∈ (Finset.univ : Finset (Fin N)), g k := by simpa [huniv]
    _ = ∑ k ∈ (Finset.univ : Finset (Fin N)), f (a + (k : ℕ)) := by simp [g]

theorem sum_norm_sq_on_box_eq_boxEnergy
    (J : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    (∑ uv ∈ box J a N, ‖β uv.1 * α uv.2‖ ^ 2)
      =
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α β := by
  classical
  unfold SSU.Engines.LargeSieve.RankOneShear.boxEnergy box
  -- Expand the product sum and rewrite the `Icc`-energy using `Fin N`.
  simp [Finset.sum_product, sum_Icc_eq_sum_univ_Fin (a := a) (N := N),
    mul_assoc, mul_left_comm, mul_comm]

/-- MV large-sieve bound for the TeX shear sum on a rank-one box, with RHS written as the literal
`ℓ²` energy `∑_{(u,v)∈box} ‖β(u)α(v)‖²` (instead of `boxEnergy`). -/
theorem norm_shearSum_sq_le_one_add_log_sum_norm_sq_on_box
    (q : ℤ) (X ξ : ℝ) (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / ((q : ℝ) * X))| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box J a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log R)) *
      (∑ uv ∈ box J a N, ‖β uv.1 * α uv.2‖ ^ 2) := by
  have h :=
    norm_shearSum_sq_le_one_add_log_boxEnergy
      (q := q) (X := X) (ξ := ξ) (J := J) (R := R) (hDist := hDist)
      (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β)
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α β
        =
      (∑ uv ∈ box J a N, ‖β uv.1 * α uv.2‖ ^ 2) :=
    (sum_norm_sq_on_box_eq_boxEnergy (J := J) (a := a) (N := N) (α := α) (β := β)).symm
  simpa [hE] using h

/-- Tube-by-restriction version of `norm_shearSum_sq_le_one_add_log_sum_norm_sq_on_box`. -/
theorem norm_shearSum_sq_le_one_add_log_sum_norm_sq_on_box_of_left_restrict
    (q : ℤ) (X ξ : ℝ) (J J' : Finset ℤ) (hsub : J' ⊆ J) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / ((q : ℝ) * X))| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box J' a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log R)) *
      (∑ uv ∈ box J' a N, ‖β uv.1 * α uv.2‖ ^ 2) := by
  have h :=
    norm_shearSum_sq_le_one_add_log_boxEnergy_of_left_restrict
      (q := q) (X := X) (ξ := ξ) (J := J) (J' := J') (hsub := hsub) (R := R) (hDist := hDist)
      (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β)
  have hE :
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J' a N α β
        =
      (∑ uv ∈ box J' a N, ‖β uv.1 * α uv.2‖ ^ 2) :=
    (sum_norm_sq_on_box_eq_boxEnergy (J := J') (a := a) (N := N) (α := α) (β := β)).symm
  simpa [hE] using h

/-!
### Step 5 (rank-one box): geometric mean of the two one-dimensional bounds

For later `ξ`-integration, TeX combines the “outer-`u`” and “outer-`v`” large-sieve losses by a
geometric mean.  In Lean we record the same move for the rank-one shear box model.
-/

/-- “Outer-`v`” analogue of `norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic` obtained by applying
`RankOneShear.norm_rankOneSignal_sq_le_one_add_log_swap_interval` to the rank-one signal. -/
theorem norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic_outerV
    (q : ℤ) (X ξ : ℝ) (U D : ℕ)
    (ht :
      |(ξ / ((q : ℝ) * X))| *
          (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
        (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    (((2 * U + 1 : ℕ) : ℝ) +
          (1 / |(ξ / ((q : ℝ) * X))|) *
            (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
        ((D : ℤ) + 1) D α β := by
  classical
  -- Rewrite `shearSum` as the rank-one signal sum over `u` and `v`.
  have hrew :=
    shearSum_eq_rankOneSignal (q := q) (X := X) (ξ := ξ)
      (J := Finset.Icc (-(U : ℤ)) (U : ℤ)) (a := ((D : ℤ) + 1)) (N := D) (α := α) (β := β)

  -- Deterministic diameter bound on the `v`-interval `Icc(D+1, (D+1)+D-1)` (= `Icc(D+1,2D)`).
  have hB : (((D : ℤ) + 1) + (D : ℤ) - 1) = (2 * D : ℤ) := by
    linarith
  have hDistV :
      ∀ i ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)),
        ∀ j ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)),
          SSU.Hilbert.distZ i j ≤ Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)) := by
    intro i hi j hj
    have hi' : i ∈ (Finset.Icc ((D : ℤ) + 1) (2 * D : ℤ)) := by
      simpa [hB] using hi
    have hj' : j ∈ (Finset.Icc ((D : ℤ) + 1) (2 * D : ℤ)) := by
      simpa [hB] using hj
    exact
      SSU.Hilbert.distZ_le_toNat_sub_of_mem_Icc
        (A := ((D : ℤ) + 1)) (B := (2 * D : ℤ)) (i := i) (j := j) hi' hj'

  -- The `u`-interval is nonempty (used only for the `toNat` bookkeeping).
  have hAB : (-(U : ℤ)) ≤ (U : ℤ) := by
    have h0 : (0 : ℤ) ≤ (U : ℤ) := by exact_mod_cast (Nat.zero_le U)
    linarith

  -- Apply the swapped rank-one bound to the rank-one signal.
  have hswap :=
    SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log_swap_interval
      (A := (-(U : ℤ))) (B := (U : ℤ)) (hAB := hAB)
      (a := ((D : ℤ) + 1)) (N := D) (α := α) (β := β)
      (R := Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))) (hDist := hDistV)
      (t := (ξ / ((q : ℝ) * X))) (ht := ht) (ht0 := ht0)

  -- Rewrite the RHS product of 1D energies as `boxEnergy`.
  have hα_energy :
      (∑ v ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)), ‖α v‖ ^ 2)
        =
      ∑ k ∈ (Finset.univ : Finset (Fin D)), ‖α (((D : ℤ) + 1) + (k : ℕ))‖ ^ 2 := by
    simpa using (sum_Icc_eq_sum_univ_Fin (a := ((D : ℤ) + 1)) (N := D) (f := fun v : ℤ => ‖α v‖ ^ 2))

  have hE :
      (∑ v ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)), ‖α v‖ ^ 2) *
          (∑ u ∈ (Finset.Icc (-(U : ℤ)) (U : ℤ)), ‖β u‖ ^ 2)
        =
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
        ((D : ℤ) + 1) D α β := by
    have hbox :=
      (SSU.Engines.LargeSieve.RankOneShear.boxEnergy_eq
        (J := Finset.Icc (-(U : ℤ)) (U : ℤ)) (a := ((D : ℤ) + 1)) (N := D) (α := α) (β := β))
    -- `boxEnergy` uses the `Fin D` energy for the `v`-variable, so rewrite the `Icc` sum by
    -- `hα_energy` and commute factors.
    calc
      (∑ v ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)), ‖α v‖ ^ 2) *
            (∑ u ∈ (Finset.Icc (-(U : ℤ)) (U : ℤ)), ‖β u‖ ^ 2)
          =
        (∑ k ∈ (Finset.univ : Finset (Fin D)), ‖α (((D : ℤ) + 1) + (k : ℕ))‖ ^ 2) *
            (∑ u ∈ (Finset.Icc (-(U : ℤ)) (U : ℤ)), ‖β u‖ ^ 2) := by
          simp [hα_energy]
      _ =
        (∑ u ∈ (Finset.Icc (-(U : ℤ)) (U : ℤ)), ‖β u‖ ^ 2) *
          (∑ k ∈ (Finset.univ : Finset (Fin D)), ‖α (((D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
      _ = SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
            ((D : ℤ) + 1) D α β := by
          simpa using hbox.symm

  have hNu : ((U : ℤ) + 1 - (-(U : ℤ))).toNat = 2 * U + 1 := by
    -- `simp` reduces to a `toNat` identity; prove it by casting to `ℤ`.
    apply Int.ofNat.inj
    have hn : (0 : ℤ) ≤ (U : ℤ) + 1 + (U : ℤ) := by positivity
    -- `toNat` is inverse to coercion on nonnegative integers.
    calc
      (((U : ℤ) + 1 - (-(U : ℤ))).toNat : ℤ)
          = (((U : ℤ) + 1 + (U : ℤ)).toNat : ℤ) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (U : ℤ) + 1 + (U : ℤ) := by
              simpa using (Int.toNat_of_nonneg hn)
      _ = (2 * U + 1 : ℤ) := by
              norm_cast
              ring

  -- Transport the swapped MV bound across `hrew`, then rewrite the energy product as `boxEnergy`.
  have hx :
      ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
          (fun uv => β uv.1 * α uv.2)‖ ^ 2
        ≤
      (∑ v ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)), ‖α v‖ ^ 2) *
        ((((U : ℤ) + 1 - (-(U : ℤ))).toNat : ℝ) +
            (1 / |(ξ / ((q : ℝ) * X))|) *
              (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) *
          (∑ u ∈ Finset.Icc (-(U : ℤ)) (U : ℤ), ‖β u‖ ^ 2) := by
    simpa [hrew] using hswap

  -- Now rewrite the RHS as `Cv * boxEnergy`.
  calc
    ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
        (fun uv => β uv.1 * α uv.2)‖ ^ 2
        ≤
      (∑ v ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)), ‖α v‖ ^ 2) *
        ((((U : ℤ) + 1 - (-(U : ℤ))).toNat : ℝ) +
            (1 / |(ξ / ((q : ℝ) * X))|) *
              (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) *
          (∑ u ∈ Finset.Icc (-(U : ℤ)) (U : ℤ), ‖β u‖ ^ 2) := hx
    _ =
      (↑(2 * U + 1) +
            (1 / |(ξ / ((q : ℝ) * X))|) *
              (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) *
        SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
          ((D : ℤ) + 1) D α β := by
      -- Avoid `simp` cancellation lemmas (`mul_eq_mul_*_iff`) by rewriting in two steps.
      set vE :=
        ∑ v ∈ (Finset.Icc ((D : ℤ) + 1) (((D : ℤ) + 1) + (D : ℤ) - 1)), ‖α v‖ ^ 2
      set uE := ∑ u ∈ Finset.Icc (-(U : ℤ)) (U : ℤ), ‖β u‖ ^ 2
      set C : ℝ :=
        (((U : ℤ) + 1 - (-(U : ℤ))).toNat : ℝ) +
          (1 / |(ξ / ((q : ℝ) * X))|) *
            (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))
      have hC :
          C =
            (↑(2 * U + 1) +
              (1 / |(ξ / ((q : ℝ) * X))|) *
                (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) := by
        dsimp [C]
        rw [hNu]
      -- Rewrite `vE * C * uE` to `C * boxEnergy`, then use `hC` to match the target constant.
      have hmain :
          vE * C * uE =
            (↑(2 * U + 1) +
                    (1 / |(ξ / ((q : ℝ) * X))|) *
                      (1 + Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))))) *
              SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
                ((D : ℤ) + 1) D α β := by
        -- First, pull `C` out front and rewrite the energy product using `hE`.
        have h1 :
            vE * C * uE =
              C *
                SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
                  ((D : ℤ) + 1) D α β := by
          calc
            vE * C * uE = C * (vE * uE) := by
              ac_rfl
            _ = C *
                SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
                  ((D : ℤ) + 1) D α β := by
              simpa [vE, uE] using congrArg (fun t => C * t) hE
        -- Now rewrite `C` using `hC`.
        simpa [hC, mul_assoc] using h1
      -- Discharge the goal by unfolding abbreviations on the LHS.
      simpa [vE, uE, C, mul_assoc] using hmain

/-- TeX-style Step 5 bound on the symmetric dyadic shear box, by geometric mean of
`norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic` (outer-`u`) and
`norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic_outerV` (outer-`v`). -/
theorem norm_shearSum_sq_le_geomMean_boxEnergy_symmDyadic
    (q : ℤ) (X ξ : ℝ) (U D : ℕ)
    (htu : |(ξ / ((q : ℝ) * X))| * (2 * U : ℝ) ≤ (1 / 2 : ℝ))
    (htv :
      |(ξ / ((q : ℝ) * X))| *
          (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
        (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    Real.sqrt (outerUConst q X ξ U D * outerVConst q X ξ U D)
        *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
          ((D : ℤ) + 1) D α β := by
  classical
  set E :=
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc (-(U : ℤ)) (U : ℤ))
      ((D : ℤ) + 1) D α β
  have hOuterU :=
    norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic
      (q := q) (X := X) (ξ := ξ) (U := U) (D := D) (ht := htu) (ht0 := ht0) (α := α) (β := β)
  have hOuterV :=
    norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic_outerV
      (q := q) (X := X) (ξ := ξ) (U := U) (D := D) (ht := htv) (ht0 := ht0) (α := α) (β := β)
  -- Both are bounds by `C * E`.
  have hU' :
      ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
          (fun uv => β uv.1 * α uv.2)‖ ^ 2
        ≤
      outerUConst q X ξ U D * E := by
    simpa [E, outerUConst] using hOuterU
  have hV' :
      ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
          (fun uv => β uv.1 * α uv.2)‖ ^ 2
        ≤
      outerVConst q X ξ U D * E := by
    simpa [E, outerVConst] using hOuterV

  -- Geometric mean: `x ≤ a` and `x ≤ b` ⇒ `x ≤ sqrt (a*b)`, then simplify.
  set x :=
    ‖shearSum q X ξ (box (Finset.Icc (-(U : ℤ)) (U : ℤ)) ((D : ℤ) + 1) D)
        (fun uv => β uv.1 * α uv.2)‖ ^ 2
  set Cu : ℝ := outerUConst q X ξ U D
  set Cv : ℝ := outerVConst q X ξ U D

  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have ha : x ≤ Cu * E := by simpa [x, Cu, E] using hU'
  have hb : x ≤ Cv * E := by simpa [x, Cv, E] using hV'
  have ha0 : 0 ≤ Cu * E := le_trans hx0 ha
  have hx2 : x ^ 2 ≤ (Cu * E) * (Cv * E) := by
    have := mul_le_mul ha hb hx0 ha0
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  have hx_sqrt : x ≤ Real.sqrt ((Cu * E) * (Cv * E)) :=
    Real.le_sqrt_of_sq_le hx2

  -- Simplify `sqrt ((Cu*E)*(Cv*E)) = sqrt (Cu*Cv) * E`.
  have hE0 : 0 ≤ E := by
    -- `boxEnergy` is a sum of squares.
    unfold E SSU.Engines.LargeSieve.RankOneShear.boxEnergy
    refine Finset.sum_nonneg ?_
    intro u hu
    refine Finset.sum_nonneg ?_
    intro k hk
    positivity
  have hCu0 : 0 ≤ Cu := by
    have hlog : 0 ≤ Real.log (2 * (U : ℝ)) := by
      simpa [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using (Real.log_natCast_nonneg (2 * U))
    have htinv : 0 ≤ (1 / |(ξ / ((q : ℝ) * X))|) := by positivity
    -- Unfold `Cu` and discharge by positivity.
    dsimp [Cu, outerUConst]
    nlinarith [hlog, htinv]
  have hCv0 : 0 ≤ Cv := by
    have hlog : 0 ≤ Real.log (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1))) :=
      Real.log_natCast_nonneg (Int.toNat ((2 * D : ℤ) - ((D : ℤ) + 1)))
    have htinv : 0 ≤ (1 / |(ξ / ((q : ℝ) * X))|) := by positivity
    dsimp [Cv, outerVConst]
    nlinarith [hlog, htinv]
  have hCuCv0 : 0 ≤ Cu * Cv := mul_nonneg hCu0 hCv0

  have hsqrt :
      Real.sqrt ((Cu * E) * (Cv * E)) = Real.sqrt (Cu * Cv) * E := by
    -- Rearrange into `(Cu*Cv) * (E*E)` and split the sqrt.
    calc
      Real.sqrt ((Cu * E) * (Cv * E))
          = Real.sqrt ((Cu * Cv) * (E * E)) := by
              have hmul : (Cu * E) * (Cv * E) = (Cu * Cv) * (E * E) := by ring
              simpa [hmul]
      _ = Real.sqrt (Cu * Cv) * Real.sqrt (E * E) := by
              simpa [mul_assoc] using (Real.sqrt_mul hCuCv0 (E * E))
      _ = Real.sqrt (Cu * Cv) * E := by
              simp [Real.sqrt_mul_self hE0, mul_assoc]

  -- Finish.
  have : x ≤ Real.sqrt (Cu * Cv) * E := by
    simpa [hsqrt] using hx_sqrt
  -- Expand `Cu`, `Cv` and `E` to match the statement.
  simpa [x, Cu, Cv, E, outerUConst, outerVConst, mul_assoc, mul_left_comm, mul_comm] using this

end RankOneShearBox

end

end LargeSieve
end TypeII
end Engines
end SSU
