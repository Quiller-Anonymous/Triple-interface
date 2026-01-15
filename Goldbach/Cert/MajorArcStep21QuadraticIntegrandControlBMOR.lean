import Goldbach.Cert.MajorArcStep21QuadraticIntegrandControl
import Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR

/-!
Major arcs (Step 21, BMOR-effective variant): quadratic integrand control.

This mirrors `Goldbach.Cert.MajorArcStep21QuadraticIntegrandControl.norm_bankSum_mul_sub_muMainTerm_mul_le_of_PsiBound`,
but uses the BMOR-effective bank exponential-sum bound from Step 20.
-/

namespace Goldbach.Cert
namespace MajorArcStep21QuadraticIntegrandControlBMOR

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.ExplicitPNTinAP_BMOR

noncomputable section

private lemma norm_mul_sub_mul_le_of_norm_sub_le
    {S₁ S₂ M₁ M₂ : ℂ} {E₁ E₂ : ℝ}
    (h₁ : ‖S₁ - M₁‖ ≤ E₁) (h₂ : ‖S₂ - M₂‖ ≤ E₂) :
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  have hE₁ : 0 ≤ E₁ := le_trans (norm_nonneg _) h₁
  have hE₂ : 0 ≤ E₂ := le_trans (norm_nonneg _) h₂

  have hdecomp :
      S₁ * S₂ - M₁ * M₂ =
        (S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂ + M₁ * (S₂ - M₂) := by
    ring
  rw [hdecomp]

  have htri :
      ‖(S₁ - M₁) * (S₂ - M₂) + (S₁ - M₁) * M₂ + M₁ * (S₂ - M₂)‖
        ≤
      ‖(S₁ - M₁) * (S₂ - M₂)‖ + ‖(S₁ - M₁) * M₂‖ + ‖M₁ * (S₂ - M₂)‖ := by
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

  exact add_le_add (add_le_add h₁₂ h₁M₂) hM₁₂

theorem norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
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
          ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₁|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    let E₂ : ℝ :=
      (q : ℝ) *
          ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₂|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  classical
  intro V₁ V₂ S₁ S₂ M₁ M₂ E₁ E₂

  have hS₁ : ‖S₁ - M₁‖ ≤ E₁ := by
    simpa [V₁, S₁, M₁, E₁] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR.norm_bankSum_sub_muMainTerm_le_of_BMOR
        (q := q) (a := a) (L := L) (U := U) hLU hL hXmin hq ha hqQ0 (β := β₁) hβ₁)
  have hS₂ : ‖S₂ - M₂‖ ≤ E₂ := by
    simpa [V₂, S₂, M₂, E₂] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR.norm_bankSum_sub_muMainTerm_le_of_BMOR
        (q := q) (a := a) (L := L) (U := U) hLU hL hXmin hq ha hqQ0 (β := β₂) hβ₂)

  exact norm_mul_sub_mul_le_of_norm_sub_le (S₁ := S₁) (S₂ := S₂) (M₁ := M₁) (M₂ := M₂)
    (E₁ := E₁) (E₂ := E₂) hS₁ hS₂

/--
Variant of `norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR` with no `Xmin ≤ L-1` cutoff.

This uses the coarse fallback bound from Step 20 (constant `210`), so it is intended only as a
certificate-friendly “no low-end cutoff” option.
-/
theorem norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL2 : 2 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
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
          (((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₁|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    let E₂ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₂|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  classical
  intro V₁ V₂ S₁ S₂ M₁ M₂ E₁ E₂

  have hS₁ : ‖S₁ - M₁‖ ≤ E₁ := by
    simpa [V₁, S₁, M₁, E₁] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR.norm_bankSum_sub_muMainTerm_le_of_BMOR210
        (q := q) (a := a) (L := L) (U := U) hLU hL hL2 hq ha hqQ0 (β := β₁) hβ₁)
  have hS₂ : ‖S₂ - M₂‖ ≤ E₂ := by
    simpa [V₂, S₂, M₂, E₂] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR.norm_bankSum_sub_muMainTerm_le_of_BMOR210
        (q := q) (a := a) (L := L) (U := U) hLU hL hL2 hq ha hqQ0 (β := β₂) hβ₂)

  exact norm_mul_sub_mul_le_of_norm_sub_le (S₁ := S₁) (S₂ := S₂) (M₁ := M₁) (M₂ := M₂)
    (E₁ := E₁) (E₂ := E₂) hS₁ hS₂

/-!
### Variant with different coprime numerators

The proof of Step 21 is purely “apply Step 20 twice + a product-error lemma”, and does not require
the two exponential sums to share the same numerator `a` (only the same modulus `q`).

This variant is convenient when rewriting `α ± β` around *different* rationals with the same
denominator `q` (e.g. after a coprime-preserving rational approximation of `β` and `1-β`).
-/

theorem norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'
    {q a₁ a₂ : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL2 : 2 ≤ (L - 1))
    (hq : 1 ≤ q) (ha₁ : Nat.Coprime a₁ q) (ha₂ : Nat.Coprime a₂ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {β₁ β₂ : ℝ} (hβ₁ : |2 * Real.pi * β₁| ≤ 1) (hβ₂ : |2 * Real.pi * β₂| ≤ 1) :
    let V₁ : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β₁ n
    let V₂ : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β₂ n
    let S₁ : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₁ + ((a₁ : ℝ) / (q : ℝ))) n
    let S₂ : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₂ + ((a₂ : ℝ) / (q : ℝ))) n
    let M₁ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₁
    let M₂ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₂
    let E₁ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₁|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    let E₂ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₂|))))
        +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2))
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  classical
  intro V₁ V₂ S₁ S₂ M₁ M₂ E₁ E₂

  have hS₁ : ‖S₁ - M₁‖ ≤ E₁ := by
    simpa [V₁, S₁, M₁, E₁] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR.norm_bankSum_sub_muMainTerm_le_of_BMOR210
        (q := q) (a := a₁) (L := L) (U := U) hLU hL hL2 hq ha₁ hqQ0 (β := β₁) hβ₁)
  have hS₂ : ‖S₂ - M₂‖ ≤ E₂ := by
    simpa [V₂, S₂, M₂, E₂] using
      (Goldbach.Cert.MajorArcStep20BankExpSumApproxBMOR.norm_bankSum_sub_muMainTerm_le_of_BMOR210
        (q := q) (a := a₂) (L := L) (U := U) hLU hL hL2 hq ha₂ hqQ0 (β := β₂) hβ₂)

  exact norm_mul_sub_mul_le_of_norm_sub_le (S₁ := S₁) (S₂ := S₂) (M₁ := M₁) (M₂ := M₂)
    (E₁ := E₁) (E₂ := E₂) hS₁ hS₂

end

end MajorArcStep21QuadraticIntegrandControlBMOR
end Goldbach.Cert
