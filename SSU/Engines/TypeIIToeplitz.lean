import SSU.Engines.TypeII

/-!
Type-II (Toeplitz-in-product) bridge layer.

This file packages the TeX “group by product” rewrite (k = d n, kernel in k'-k) as a parallel
single-tube SSU statement, and provides a bridge to the SSU heart (`Interzone.GramHypothesis`).

It is intentionally *parallel* to the determinant-style `SSU.SingleTube` statement:
the skew form `d'n - d n'` and the Toeplitz form `d'n' - d n` are different shifts, and different
applications may want one or the other.
-/

namespace SSU
namespace Engines
namespace TypeIIToeplitz

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Engines.TypeII

namespace PT

open SSU.Engines.TypeII.ProductToeplitz

abbrev prod := SSU.Engines.TypeII.ProductToeplitz.prod
abbrev prodSum := SSU.Engines.TypeII.ProductToeplitz.prodSum
abbrev coeffByProd := SSU.Engines.TypeII.ProductToeplitz.coeffByProd
abbrev prodSum_eq_sum_image_prod := SSU.Engines.TypeII.ProductToeplitz.prodSum_eq_sum_image_prod
abbrev tubeFormProd := SSU.Engines.TypeII.ProductToeplitz.tubeFormProd
abbrev tubeFormProd_eq := SSU.Engines.TypeII.ProductToeplitz.tubeFormProd_eq

end PT

/-!
## Toeplitz single-tube statement

The TeX “Toeplitzization” after grouping by the product variable `k = d n` yields a quadratic form
whose kernel depends on `k' - k`. We record the resulting inequality in the same shape as
`SSU.SingleTubeSSUStatement`, but for the Toeplitz product-shift form.
-/

def ToeplitzTubeSSUStatement (X H : ℝ) (K : ℤ → ℝ) (T : Finset TubePoint) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : TubePoint → ℂ,
      ‖PT.tubeFormProd K T F‖ ≤ C * Real.sqrt (H / X) * (tubeEnergy T F)

/-!
## Step 3–4 interface (Toeplitz sum version)

This mirrors `Step34LargeSieve`, but for the product-grouped oscillatory sum

`S(ξ) = ∑_{p∈T} F(p) e(ξ * (d n) / X)`.
-/

structure Step34ProdSum (X H : ℝ) (T : Finset TubePoint) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, |ξ| ≤ (1 / H) →
      ∀ F : TubePoint → ℂ,
        ‖PT.prodSum X ξ T F‖ ^ 2 ≤ C * Real.sqrt (H / X) * (tubeEnergy T F)

namespace Step34ProdSum

/--
Trivial (non–number-theoretic) Step 3–4 bound for `prodSum` by Cauchy–Schwarz.

This is only scaffolding: the constant scales like `card(T)`.
-/
def trivial (X H : ℝ) (T : Finset TubePoint) (hX : 0 < X) (hH : 0 < H) : Step34ProdSum X H T where
  C := (T.card : ℝ) * Real.sqrt (X / H)
  C_nonneg := by
    have : 0 ≤ (T.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact mul_nonneg this (by positivity)
  bound := by
    classical
    intro ξ _hξ F
    -- Triangle inequality + `‖e(·)‖ = 1`.
    have hnorm :
        ‖PT.prodSum X ξ T F‖ ≤ ∑ p ∈ T, ‖F p‖ := by
      have h1 :
          ‖PT.prodSum X ξ T F‖
            ≤
          ∑ p ∈ T, ‖F p * e (ξ * (PT.prod p : ℝ) / X)‖ := by
        simpa [PT.prodSum] using
          (norm_sum_le T (fun p => F p * e (ξ * (PT.prod p : ℝ) / X)))
      have h2 :
          (∑ p ∈ T, ‖F p * e (ξ * (PT.prod p : ℝ) / X)‖) =
            ∑ p ∈ T, ‖F p‖ := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        have he : ‖e (ξ * (PT.prod p : ℝ) / X)‖ = 1 := by
          simpa using (norm_e (ξ * (PT.prod p : ℝ) / X))
        simpa [norm_mul, he, mul_assoc]
      exact h2 ▸ h1
    have hsq1 :
        ‖PT.prodSum X ξ T F‖ ^ 2 ≤ (Finset.sum T (fun p => ‖F p‖)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hnorm 2
    have hsq2 :
        (Finset.sum T (fun p => ‖F p‖)) ^ 2 ≤ (T.card : ℝ) * Finset.sum T (fun p => ‖F p‖ ^ 2) := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := T) (f := fun p => ‖F p‖))
    have hsq :
        ‖PT.prodSum X ξ T F‖ ^ 2 ≤ (T.card : ℝ) * tubeEnergy T F := by
      simpa [tubeEnergy] using (le_trans hsq1 hsq2)
    -- Convert to `C * sqrt(H/X)`.
    have hx0 : X ≠ 0 := ne_of_gt hX
    have hH0 : H ≠ 0 := ne_of_gt hH
    have hmul_sqrt :
        Real.sqrt (X / H) * Real.sqrt (H / X) = 1 := by
      have hpos1 : 0 ≤ X / H := by
        have : 0 < X / H := div_pos hX hH
        exact le_of_lt this
      calc
        Real.sqrt (X / H) * Real.sqrt (H / X)
            = Real.sqrt ((X / H) * (H / X)) := (Real.sqrt_mul hpos1 (H / X)).symm
        _ = Real.sqrt (1 : ℝ) := by
              congr 1
              field_simp [hx0, hH0]
        _ = 1 := by simp
    have hC :
        ((T.card : ℝ) * Real.sqrt (X / H)) * Real.sqrt (H / X) = (T.card : ℝ) := by
      calc
        ((T.card : ℝ) * Real.sqrt (X / H)) * Real.sqrt (H / X)
            = (T.card : ℝ) * (Real.sqrt (X / H) * Real.sqrt (H / X)) := by ring
        _ = (T.card : ℝ) := by simp [hmul_sqrt]
    simpa [mul_assoc, hC] using hsq

end Step34ProdSum

/-!
## Step 2 + Step 3–4 ⇒ Toeplitz single-tube inequality (planned)

For the Toeplitz-in-product packaging, TeX Step 2 is the deterministic identity
`ProductToeplitz.tubeFormProd_eq`. The corresponding lemma turning a `Step34ProdSum` bound into a
`ToeplitzTubeSSUStatement` is proved here; it is the Toeplitz analogue of
`singleTubeSSUStatement_of_step2ToTubeForm`.
-/

namespace ToeplitzTubeSSUStatement

open MeasureTheory

private lemma star_e (x : ℝ) : star (e x) = e (-x) := by
  -- Reuse the already-proved lemma about `conj (e x)` from `SSU.Engines.TypeII`.
  simpa using (SSU.Engines.TypeII.AdmissibleKernel.conj_e x)

theorem of_step2KernelRep (X H : ℝ) (K : ℤ → ℝ) (T : Finset TubePoint)
    (h2 : Step2KernelRep X H K) (h34 : Step34ProdSum X H T)
    (hX : 0 < X) (hH : 0 < H) (hKhat : IntegrableOn h2.Khat (Set.Icc (-(1 / H)) (1 / H))) :
    ToeplitzTubeSSUStatement X H K T := by
  classical
  let s : Set ℝ := SSU.Engines.TypeII.ProductToeplitz.s H
  have hKhat' : IntegrableOn h2.Khat s := by
    simpa [s, SSU.Engines.TypeII.ProductToeplitz.s] using hKhat
  refine ⟨h34.C * (∫ ξ in s, h2.Khat ξ), ?_, ?_⟩
  · -- Nonnegativity of the constant.
    have hK : 0 ≤ ∫ ξ in s, h2.Khat ξ := by
      refine integral_nonneg_of_ae ?_
      exact ae_of_all _ (fun ξ => h2.Khat_nonneg ξ)
    exact mul_nonneg h34.C_nonneg hK
  · intro F
    -- TeX Step 2: rewrite the Toeplitz tube form as an integral against `Khat`.
    have htube :
        PT.tubeFormProd K T F =
          (∫ ξ in s,
              ((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))) := by
      -- `PT.tubeFormProd_eq` is the proved deterministic insertion identity.
      simpa [s] using
        (PT.tubeFormProd_eq (X := X) (H := H) (K := K) (hK := h2) (T := T) (F := F) hH hKhat')

    -- First bound the norm of the integral by the integral of the norm.
    have hnormInt :
        ‖PT.tubeFormProd K T F‖
          ≤
        ∫ ξ in s,
          ‖((h2.Khat ξ : ℝ) : ℂ) *
              ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖ := by
      -- Use the Bochner inequality `‖∫ f‖ ≤ ∫ ‖f‖` on the restricted measure.
      let g : ℝ → ℂ :=
        fun ξ : ℝ =>
          ((h2.Khat ξ : ℝ) : ℂ) *
            ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
              (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))
      calc
        ‖PT.tubeFormProd K T F‖ = ‖∫ ξ in s, g ξ‖ := by simpa [htube, g]
        _ ≤ ∫ ξ in s, ‖g ξ‖ := by
              simpa [MeasureTheory.integral] using
                (MeasureTheory.norm_integral_le_integral_norm
                  (μ := (volume : Measure ℝ).restrict s) (f := g))
        _ = _ := by simp [g]

    -- Pointwise control of the integrand norm via the Step 3–4 bound.
    have hpoint :
        (fun ξ : ℝ =>
            ‖((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖)
          ≤ᵐ[(volume : Measure ℝ).restrict s]
        fun ξ : ℝ =>
            (h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := by
      have hs : MeasurableSet s := by
        dsimp [s]
        measurability
      filter_upwards [ae_restrict_mem hs] with ξ hξ
      have hξabs : |ξ| ≤ (1 / H) := by
        have hle : -(1 / H) ≤ ξ ∧ ξ ≤ (1 / H) := by
          simpa [s, Set.mem_Icc] using hξ
        exact abs_le.2 hle
      have hS :
          ‖PT.prodSum X (-ξ) T F‖ ^ 2
            ≤ h34.C * Real.sqrt (H / X) * tubeEnergy T F := by
        -- Apply the Step 3–4 bound at `-ξ` (the set is symmetric).
        have : |(-ξ)| ≤ (1 / H) := by simpa [abs_neg] using hξabs
        exact h34.bound (-ξ) this F
      -- Relate the integrand to `prodSum X (-ξ)`.
      have hsumP :
          (∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X)))
            =
          PT.prodSum X (-ξ) T F := by
        -- Expand `prodSum` and compare terms pointwise.
        classical
        -- `prodSum X (-ξ) T F = ∑ p ∈ T, F p * e ((-ξ) * prod(p) / X)`.
        dsimp [PT.prodSum, SSU.Engines.TypeII.ProductToeplitz.prodSum]
        refine Finset.sum_congr rfl ?_
        intro p hp
        have harg : -(ξ * (PT.prod p : ℝ) / X) = (-ξ) * (PT.prod p : ℝ) / X := by
          -- Rewrite division as multiplication by `X⁻¹` and reassociate.
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        simp [harg]
      have hsumQ :
          (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))
            =
          star (PT.prodSum X (-ξ) T F) := by
        classical
        -- Expand `prodSum` and compute conjugation termwise.
        dsimp [PT.prodSum, SSU.Engines.TypeII.ProductToeplitz.prodSum]
        have hrhs :
            star (∑ q ∈ T, F q * e ((-ξ) * (PT.prod q : ℝ) / X))
              =
            ∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X) := by
          -- Push `star` inside the finite sum, then use `star_e`.
          -- Include `mul_comm` to present terms as `star(F q) * e(...)`.
          simp [star_sum, star_mul, star_e, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        simpa using hrhs.symm
      have hprodNorm :
          ‖(∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
              (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))‖
            =
          ‖PT.prodSum X (-ξ) T F‖ ^ 2 := by
        -- The product is `S * star S`, whose norm is `‖S‖^2`.
        have hSstar :
            ‖PT.prodSum X (-ξ) T F * star (PT.prodSum X (-ξ) T F)‖
              =
            ‖PT.prodSum X (-ξ) T F‖ ^ 2 := by
          calc
            ‖PT.prodSum X (-ξ) T F * star (PT.prodSum X (-ξ) T F)‖
                =
              ‖PT.prodSum X (-ξ) T F‖ * ‖star (PT.prodSum X (-ξ) T F)‖ := by
                simpa using norm_mul (PT.prodSum X (-ξ) T F) (star (PT.prodSum X (-ξ) T F))
            _ = ‖PT.prodSum X (-ξ) T F‖ * ‖PT.prodSum X (-ξ) T F‖ := by
                simp
            _ = ‖PT.prodSum X (-ξ) T F‖ ^ 2 := by
                simp [pow_two, mul_assoc]
        -- Rewrite the goal into `‖S * star S‖ = ‖S‖^2` and apply `hSstar`.
        -- We use `rw` rather than `simp` to avoid rewriting `‖a*b‖` into `‖a‖*‖b‖`.
        -- (That simp rewrite is correct, but makes the match fragile.)
        have : ‖(∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))‖
                =
              ‖PT.prodSum X (-ξ) T F * star (PT.prodSum X (-ξ) T F)‖ := by
          -- Rewrite the two factors.
          rw [hsumP, hsumQ]
        -- Finish by chaining with `hSstar`.
        exact this.trans hSstar
      -- Now bound the norm of the full integrand.
      have hK0 : 0 ≤ h2.Khat ξ := h2.Khat_nonneg ξ
      have hstep :
          ‖((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖
            ≤ (h2.Khat ξ) * (‖PT.prodSum X (-ξ) T F‖ ^ 2) := by
        -- Pull the real scalar out of the norm, without expanding the inner product norm.
        have houter :
            ‖((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖
              =
            ‖((h2.Khat ξ : ℝ) : ℂ)‖ *
              ‖(∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))‖ := by
          simpa using
            (norm_mul
              ((h2.Khat ξ : ℝ) : ℂ)
              ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))))
        -- Now rewrite `‖(Khat : ℂ)‖ = |Khat|` and apply `hprodNorm`.
        have hn :
            ‖((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖
              =
            (h2.Khat ξ) * (‖PT.prodSum X (-ξ) T F‖ ^ 2) := by
          -- Rewrite using `houter`, then use `hprodNorm`.
          have hscalar : ‖((h2.Khat ξ : ℝ) : ℂ)‖ = |h2.Khat ξ| := by
            simpa [RCLike.norm_ofReal]
          calc
            ‖((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖
                =
              ‖((h2.Khat ξ : ℝ) : ℂ)‖ *
                ‖(∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))‖ := houter
            _ = |h2.Khat ξ| *
                ‖(∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X))‖ := by
                  -- Avoid `simp`: it may rewrite `‖a*b‖` into `‖a‖*‖b‖`.
                  rw [hscalar]
            _ = |h2.Khat ξ| * (‖PT.prodSum X (-ξ) T F‖ ^ 2) := by
                  -- Rewrite the inner norm using `hprodNorm`.
                  rw [hprodNorm]
            _ = (h2.Khat ξ) * (‖PT.prodSum X (-ξ) T F‖ ^ 2) := by
                  simp [abs_of_nonneg hK0]
        exact (le_of_eq hn)
      have hstep' :
          (h2.Khat ξ) * (‖PT.prodSum X (-ξ) T F‖ ^ 2)
            ≤
          (h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := by
        exact mul_le_mul_of_nonneg_left hS hK0
      exact le_trans hstep hstep'

    have hgi :
        Integrable (fun ξ : ℝ =>
          (h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F))
          ((volume : Measure ℝ).restrict s) := by
      -- A constant multiple of an integrable function.
      simpa [IntegrableOn, s] using
        (hKhat'.mul_const (h34.C * Real.sqrt (H / X) * tubeEnergy T F))

    have hmono :
        (∫ ξ in s,
            ‖((h2.Khat ξ : ℝ) : ℂ) *
                ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                  (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖)
          ≤
        ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := by
      refine integral_mono_of_nonneg ?_ hgi hpoint
      exact ae_of_all _ (fun ξ => by
        positivity)

    have hconst :
        (∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F))
          =
        (∫ ξ in s, h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := by
      simpa [s] using
        (MeasureTheory.integral_mul_const
          (μ := (volume : Measure ℝ).restrict s)
          (r := (h34.C * Real.sqrt (H / X) * tubeEnergy T F))
          (f := fun ξ : ℝ => h2.Khat ξ))

    have hfinal :
        ‖PT.tubeFormProd K T F‖
          ≤ (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (H / X) * tubeEnergy T F := by
      have h1 :
          ‖PT.tubeFormProd K T F‖
            ≤ ∫ ξ in s,
              ‖((h2.Khat ξ : ℝ) : ℂ) *
                  ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                    (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖ := hnormInt
      have h2' :
          (∫ ξ in s,
              ‖((h2.Khat ξ : ℝ) : ℂ) *
                  ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                    (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖)
            ≤
          (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (H / X) * tubeEnergy T F := by
        -- `∫ ‖integrand‖ ≤ ∫ Khat * const = (∫ Khat) * const`.
        have hmono' :
            (∫ ξ in s,
                ‖((h2.Khat ξ : ℝ) : ℂ) *
                    ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                      (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖)
              ≤
            (∫ ξ in s, h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := by
          calc
            (∫ ξ in s,
                ‖((h2.Khat ξ : ℝ) : ℂ) *
                    ((∑ p ∈ T, F p * e (-(ξ * (PT.prod p : ℝ) / X))) *
                      (∑ q ∈ T, (star (F q)) * e (ξ * (PT.prod q : ℝ) / X)))‖)
                ≤ ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := hmono
            _ = (∫ ξ in s, h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F) := by
                simpa [hconst]
        have hreassoc :
            (∫ ξ in s, h2.Khat ξ) * (h34.C * Real.sqrt (H / X) * tubeEnergy T F)
              =
            (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (H / X) * tubeEnergy T F := by
          ac_rfl
        simpa [hreassoc] using hmono'
      exact le_trans h1 h2'
    -- Now rewrite to the advertised `C * sqrt(H/X)` form.
    have hswap :
        (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (H / X) * tubeEnergy T F
          =
        (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (H / X) * tubeEnergy T F := rfl
    simpa [hswap, s] using hfinal

end ToeplitzTubeSSUStatement

/-!
## Bridge to the SSU heart (GramHypothesis)

This mirrors `ReductionToTubeForm`/`gramHypothesis_of_singleTube` but for the Toeplitz tube form.
-/

structure ReductionToTubeFormProd
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (J : Finset ℤ) (T : ℤ → (H →L[ℂ] H))
    (X Hpar : ℝ) (K : ℤ → ℝ) (tube : Finset TubePoint) where
  Cenergy : ℝ
  Cenergy_nonneg : 0 ≤ Cenergy
  F : H → ℤ → ℤ → TubePoint → ℂ
  inner_eq :
    ∀ f : H, ∀ i ∈ J, ∀ j ∈ J,
      inner ℂ (T i f) (T j f) = PT.tubeFormProd K tube (F f i j)
  energy_le :
    ∀ f : H, ∀ i ∈ J, ∀ j ∈ J,
      tubeEnergy tube (F f i j) ≤ Cenergy * ‖T i f‖ * ‖T j f‖

namespace ReductionToTubeFormProd

open SSU.Engines.TypeII.ProductToeplitz

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)}
    {X Hpar : ℝ} {K : ℤ → ℝ} {tube : Finset TubePoint}

/--
Scale a reduction by a constant complex scalar on the operator side.

If `T' i := c • T i`, then we can keep the same energy constant `Cenergy` and scale the tube
coefficients `F` by `c` to preserve the exact Gram identification.
-/
noncomputable def mulConst (c : ℂ)
    (R : ReductionToTubeFormProd (J := J) (T := T) X Hpar K tube) :
    ReductionToTubeFormProd (J := J) (T := fun i => c • T i) X Hpar K tube :=
by
  classical
  refine
    { Cenergy := R.Cenergy
      Cenergy_nonneg := R.Cenergy_nonneg
      F := fun f i j p => c * R.F f i j p
      inner_eq := ?_
      energy_le := ?_ }
  · intro f i hi j hj
    -- `⟪c • Ti f, c • Tj f⟫ = (c * star c) * ⟪Ti f, Tj f⟫`.
    have hinner :
        inner ℂ ((c • T i) f) ((c • T j) f) = (c * star c) * inner ℂ (T i f) (T j f) := by
      -- `inner_smul_left` / `inner_smul_right` for complex inner products.
      -- We normalize to the `c * star c` form.
      simp [mul_assoc, mul_left_comm, mul_comm]
    -- Replace the inner product by the tube form from `R`, then use scaling of `tubeFormProd`.
    calc
      inner ℂ ((c • T i) f) ((c • T j) f)
          = (c * star c) * PT.tubeFormProd K tube (R.F f i j) := by
              simpa [R.inner_eq (f := f) (i := i) hi (j := j) hj] using hinner
      _ = PT.tubeFormProd K tube (fun p => c * R.F f i j p) := by
              simpa using
                (SSU.Engines.TypeII.ProductToeplitz.tubeFormProd_mul_const
                  (K := K) (T := tube) (c := c) (F := R.F f i j)).symm
      _ = PT.tubeFormProd K tube (fun p => c * R.F f i j p) := rfl
  · intro f i hi j hj
    -- Use the tube-energy scaling lemma, then the original energy bound, then norm scaling.
    have hE :
        tubeEnergy tube (fun p => c * R.F f i j p) = (‖c‖ ^ 2) * tubeEnergy tube (R.F f i j) := by
      simpa using (SSU.tubeEnergy_mul_const (T := tube) (c := c) (F := R.F f i j))
    have hR : tubeEnergy tube (R.F f i j) ≤ R.Cenergy * ‖T i f‖ * ‖T j f‖ :=
      R.energy_le (f := f) (i := i) hi (j := j) hj
    -- Scale both sides by `‖c‖^2 ≥ 0`.
    have hscale :
        (‖c‖ ^ 2) * tubeEnergy tube (R.F f i j)
          ≤ (‖c‖ ^ 2) * (R.Cenergy * ‖T i f‖ * ‖T j f‖) := by
      have hc : 0 ≤ (‖c‖ ^ 2 : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hR hc
    -- Rewrite the RHS norms: `‖(c • T i) f‖ = ‖c‖ * ‖T i f‖`.
    have hnorm :
        (‖c‖ ^ 2) * (R.Cenergy * ‖T i f‖ * ‖T j f‖)
          = R.Cenergy * ‖(c • T i) f‖ * ‖(c • T j) f‖ := by
      -- `‖c•x‖ = ‖c‖‖x‖` in a normed space over `ℂ`.
      simp [norm_smul, mul_assoc, mul_left_comm, mul_comm, pow_two]
    -- Put it together.
    calc
      tubeEnergy tube (fun p => c * R.F f i j p)
          = (‖c‖ ^ 2) * tubeEnergy tube (R.F f i j) := by simpa [hE]
      _ ≤ (‖c‖ ^ 2) * (R.Cenergy * ‖T i f‖ * ‖T j f‖) := hscale
      _ = R.Cenergy * ‖(c • T i) f‖ * ‖(c • T j) f‖ := hnorm

end ReductionToTubeFormProd

noncomputable def gramHypothesis_of_toeplitzSingleTube
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)}
    {X Hpar : ℝ} {K : ℤ → ℝ} {tube : Finset TubePoint}
    (hSSU : ToeplitzTubeSSUStatement X Hpar K tube)
    (R : ReductionToTubeFormProd (J := J) (T := T) X Hpar K tube) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  classical
  let C : ℝ := Classical.choose hSSU
  have hCspec :
      0 ≤ C ∧
        ∀ F : TubePoint → ℂ,
          ‖PT.tubeFormProd K tube F‖ ≤ C * Real.sqrt (Hpar / X) * tubeEnergy tube F :=
    Classical.choose_spec hSSU
  have hC0 : 0 ≤ C := hCspec.1
  have hC :
      ∀ F : TubePoint → ℂ,
        ‖PT.tubeFormProd K tube F‖ ≤ C * Real.sqrt (Hpar / X) * tubeEnergy tube F :=
    hCspec.2
  let cTot : ℝ := C * Real.sqrt (Hpar / X) * R.Cenergy
  have hcTot : 0 ≤ cTot := by
    have hsqrt : 0 ≤ Real.sqrt (Hpar / X) := by positivity
    exact mul_nonneg (mul_nonneg hC0 hsqrt) R.Cenergy_nonneg
  refine { a := fun _ => Real.toNNReal cTot, gram := ?_ }
  intro f i hi j hj
  have hId : ‖inner ℂ (T i f) (T j f)‖ = ‖PT.tubeFormProd K tube (R.F f i j)‖ := by
    simpa [R.inner_eq (f := f) (i := i) hi (j := j) hj]
  have hTube :
      ‖PT.tubeFormProd K tube (R.F f i j)‖
        ≤ C * Real.sqrt (Hpar / X) * tubeEnergy tube (R.F f i j) :=
    hC (R.F f i j)
  have hEnergy :
      tubeEnergy tube (R.F f i j) ≤ R.Cenergy * ‖T i f‖ * ‖T j f‖ :=
    R.energy_le (f := f) (i := i) hi (j := j) hj
  have hmul :
      C * Real.sqrt (Hpar / X) * tubeEnergy tube (R.F f i j)
        ≤ C * Real.sqrt (Hpar / X) * (R.Cenergy * ‖T i f‖ * ‖T j f‖) := by
    have hfac : 0 ≤ C * Real.sqrt (Hpar / X) := by
      have : 0 ≤ Real.sqrt (Hpar / X) := by positivity
      exact mul_nonneg hC0 this
    exact mul_le_mul_of_nonneg_left hEnergy hfac
  have hcomb :
      ‖inner ℂ (T i f) (T j f)‖ ≤ cTot * ‖T i f‖ * ‖T j f‖ := by
    have :
        ‖inner ℂ (T i f) (T j f)‖
          ≤ C * Real.sqrt (Hpar / X) * (R.Cenergy * ‖T i f‖ * ‖T j f‖) := by
      exact le_trans (by simpa [hId] using hTube) hmul
    simpa [cTot, mul_assoc, mul_left_comm, mul_comm] using this
  have ha : ((Real.toNNReal cTot : NNReal) : ℝ) = cTot := by
    simpa using (Real.coe_toNNReal cTot hcTot)
  simpa [ha, hcTot, mul_assoc, mul_left_comm, mul_comm] using hcomb

noncomputable def gramHypothesis_of_step2KernelRep
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)}
    {X Hpar : ℝ} {K : ℤ → ℝ} {tube : Finset TubePoint}
    (h2 : Step2KernelRep X Hpar K) (h34 : Step34ProdSum X Hpar tube)
    (hX : 0 < X) (hH : 0 < Hpar) (hKhat : IntegrableOn h2.Khat (Set.Icc (-(1 / Hpar)) (1 / Hpar)))
    (R : ReductionToTubeFormProd (J := J) (T := T) X Hpar K tube) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  classical
  have hSSU : ToeplitzTubeSSUStatement X Hpar K tube :=
    ToeplitzTubeSSUStatement.of_step2KernelRep X Hpar K tube h2 h34 hX hH hKhat
  exact gramHypothesis_of_toeplitzSingleTube (J := J) (T := T) (X := X) (Hpar := Hpar) (K := K)
    (tube := tube) hSSU R

end

end TypeIIToeplitz
end Engines
end SSU
