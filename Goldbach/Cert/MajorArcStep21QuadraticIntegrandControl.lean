import Goldbach.Cert.MajorArcStep20BankExpSumApprox

/-!
Major arcs (Step 21, sigma-agnostic): quadratic/product bookkeeping for bank exponential sums.

Step 20 gives a major-arc approximation for the **bank** exponential sum at a point `α = a/q + β`:
`‖S(β) - M(β)‖ ≤ E(β)`.

In the correlation integral, the integrand is quadratic in these sums (a product of two shifted
frequencies), so we need a purely algebraic upgrade that controls
`‖S₁ * S₂ - M₁ * M₂‖` in terms of `‖Sᵢ - Mᵢ‖`.
-/

namespace Goldbach.Cert
namespace MajorArcStep21QuadraticIntegrandControl

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep20BankExpSumApprox

noncomputable section

private lemma norm_mul_sub_mul_le_of_norm_sub_le
    {S₁ S₂ M₁ M₂ : ℂ} {E₁ E₂ : ℝ}
    (h₁ : ‖S₁ - M₁‖ ≤ E₁) (h₂ : ‖S₂ - M₂‖ ≤ E₂) :
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  have hE₁ : 0 ≤ E₁ := le_trans (norm_nonneg _) h₁
  have hE₂ : 0 ≤ E₂ := le_trans (norm_nonneg _) h₂

  -- Expand the product difference into a sum of three error terms.
  have hdecomp :
      S₁ * S₂ - M₁ * M₂ =
        (S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂ + M₁ * (S₂ - M₂) := by
    ring
  rw [hdecomp]

  -- Triangle inequality, then bound each term using `h₁` and `h₂`.
  have htri :
      ‖(S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂ + M₁ * (S₂ - M₂)‖
        ≤
      ‖(S₁ - M₁) * (S₂ - M₂)‖ + ‖(S₁ - M₁) * M₂‖ + ‖M₁ * (S₂ - M₂)‖ := by
    -- `‖(x+y)+z‖ ≤ (‖x‖+‖y‖)+‖z‖`.
    have hxy :
        ‖(S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂‖
          ≤
        ‖(S₁ - M₁) * (S₂ - M₂)‖ + ‖(S₁ - M₁) * M₂‖ := by
      simpa using norm_add_le ((S₁ - M₁) * (S₂ - M₂)) ((S₁ - M₁) * M₂)
    calc
      ‖(S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂ + M₁ * (S₂ - M₂)‖
          =
        ‖((S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂) + M₁ * (S₂ - M₂)‖ := by
          simp [add_assoc]
      _ ≤ ‖(S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂‖ + ‖M₁ * (S₂ - M₂)‖ := by
          exact norm_add_le _ _
      _ ≤ (‖(S₁ - M₁) * (S₂ - M₂)‖ + ‖(S₁ - M₁) * M₂‖) + ‖M₁ * (S₂ - M₂)‖ := by
          exact add_le_add_right hxy _
      _ = ‖(S₁ - M₁) * (S₂ - M₂)‖ + ‖(S₁ - M₁) * M₂‖ + ‖M₁ * (S₂ - M₂)‖ := by
          ring

  refine le_trans htri ?_

  have h₁₂ :
      ‖(S₁ - M₁) * (S₂ - M₂)‖ ≤ E₁ * E₂ := by
    have hmul : ‖(S₁ - M₁) * (S₂ - M₂)‖ = ‖S₁ - M₁‖ * ‖S₂ - M₂‖ := by
      simpa [norm_mul] using (norm_mul (S₁ - M₁) (S₂ - M₂))
    -- `‖S₁-M₁‖*‖S₂-M₂‖ ≤ E₁*E₂`.
    have hprod :
        ‖S₁ - M₁‖ * ‖S₂ - M₂‖ ≤ E₁ * E₂ :=
      mul_le_mul h₁ h₂ (norm_nonneg _) hE₁
    simpa [hmul] using hprod

  have h₁M₂ :
      ‖(S₁ - M₁) * M₂‖ ≤ E₁ * ‖M₂‖ := by
    have hmul : ‖(S₁ - M₁) * M₂‖ = ‖S₁ - M₁‖ * ‖M₂‖ := by
      simpa [norm_mul] using (norm_mul (S₁ - M₁) M₂)
    have hprod : ‖S₁ - M₁‖ * ‖M₂‖ ≤ E₁ * ‖M₂‖ :=
      mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
    simpa [hmul] using hprod

  have hM₁₂ :
      ‖M₁ * (S₂ - M₂)‖ ≤ ‖M₁‖ * E₂ := by
    have hmul : ‖M₁ * (S₂ - M₂)‖ = ‖M₁‖ * ‖S₂ - M₂‖ := by
      simpa [norm_mul] using (norm_mul M₁ (S₂ - M₂))
    have hprod : ‖M₁‖ * ‖S₂ - M₂‖ ≤ ‖M₁‖ * E₂ :=
      mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
    simpa [hmul] using hprod

  -- Combine the three termwise bounds.
  exact add_le_add (add_le_add h₁₂ h₁M₂) hM₁₂

/--
Given Step 20 bounds for two bank exponential sums (at possibly different real offsets `β₁,β₂`),
bound the resulting quadratic/product error.

This is purely algebraic, but phrased in the major-arc notation that will be used when inserting
the major-arc approximation into the Step 12 shifted-frequency integrand.
-/
theorem norm_bankSum_mul_sub_muMainTerm_mul_le_of_PsiBound
    {q a : ℕ}
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β₁ β₂ : ℝ} (hβ₁ : |2 * Real.pi * β₁| ≤ 1) (hβ₂ : |2 * Real.pi * β₂| ≤ 1) :
    let V₁ : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β₁ n
    let V₂ : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β₂ n
    let S₁ : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₁ + ((a : ℝ) / (q : ℝ))) n
    let S₂ : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₂ + ((a : ℝ) / (q : ℝ))) n
    let M₁ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₁
    let M₂ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₂
    let E₁ : ℝ :=
      (q : ℝ) *
          ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
            * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β₁|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    let E₂ : ℝ :=
      (q : ℝ) *
          ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
            * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β₂|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  classical
  intro V₁ V₂ S₁ S₂ M₁ M₂ E₁ E₂

  have hS₁ : ‖S₁ - M₁‖ ≤ E₁ := by
    simpa [V₁, S₁, M₁, E₁] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApprox.norm_bankSum_sub_muMainTerm_le_of_PsiBound
        (q := q) (a := a) (A := A) (hpsi := hpsi)
        (L := L) (U := U) hLU hL hL3 hq ha hqlog (β := β₁) hβ₁)
  have hS₂ : ‖S₂ - M₂‖ ≤ E₂ := by
    simpa [V₂, S₂, M₂, E₂] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApprox.norm_bankSum_sub_muMainTerm_le_of_PsiBound
        (q := q) (a := a) (A := A) (hpsi := hpsi)
        (L := L) (U := U) hLU hL hL3 hq ha hqlog (β := β₂) hβ₂)

  exact norm_mul_sub_mul_le_of_norm_sub_le (S₁ := S₁) (S₂ := S₂) (M₁ := M₁) (M₂ := M₂)
    (E₁ := E₁) (E₂ := E₂) hS₁ hS₂

end

end MajorArcStep21QuadraticIntegrandControl
end Goldbach.Cert

