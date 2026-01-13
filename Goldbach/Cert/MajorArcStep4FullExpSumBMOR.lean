import Goldbach.Cert.MajorArcStep4FullExpSum
import Goldbach.Cert.MajorArcStep3MajorArcDecompMuBMOR

/-!
Major arcs (Step 4, BMOR-effective variant): full exponential-sum estimate.

This mirrors `Goldbach.Cert.MajorArcStep4FullExpSum.norm_fullExpSum_sub_muMainTerm_le_of_PsiBound`,
but replaces the coprime-residue bound (Step 3) with the BMOR-effective version.

The bound for the non-coprime residue contribution is unchanged (it is elementary and does not use
any prime distribution input).
-/

namespace Goldbach.Cert
namespace MajorArcStep4FullExpSumBMOR

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.ExplicitPNTinAP_BMOR

noncomputable section

theorem norm_fullExpSum_sub_muMainTerm_le_of_BMOR
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
  classical
  intro V
  let Rcop : Finset ℕ := (Finset.range q).filter (fun r => Nat.Coprime r q)
  let Rbad : Finset ℕ := (Finset.range q).filter (fun r => ¬ Nat.Coprime r q)
  let Sres (r : ℕ) : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1),
      (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n

  have hdecomp :
      (∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
        =
      ∑ r ∈ Finset.range q,
        e ((a : ℝ) * (r : ℝ) / q) * Sres r := by
    simpa [Sres, mul_assoc, mul_left_comm, mul_comm] using
      (Goldbach.Cert.MajorArcStep2MajorArcDecomp.sum_Ico_LambdaVM_mul_gExp_mul_e_eq_sum_range_residue
        (q := q) (a := a) hq (β := β) (L := L) (U := U))

  have hsplit :
      (∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        =
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        +
      (∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r) := by
    have :=
      (Finset.sum_filter_add_sum_filter_not (s := Finset.range q)
        (p := fun r : ℕ => Nat.Coprime r q)
        (f := fun r : ℕ => e ((a : ℝ) * (r : ℝ) / q) * Sres r))
    simpa [Rcop, Rbad, add_comm, add_left_comm, add_assoc] using this.symm

  have hcop_bound :=
    (Goldbach.Cert.MajorArcStep3MajorArcDecompMuBMOR.norm_sum_coprimeResidues_sub_muMainTerm_le_of_BMOR
      (q := q) (a := a) (L := L) (U := U) hLU hL hXmin hq ha hqQ0 (β := β) hβ)

  have hbad_bound :
      ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
        ≤
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
    have h0 :
        ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
          ≤
        ∑ n ∈ Finset.Ico L (U + 1),
          (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0) := by
      simpa [Rbad, Sres] using
        (Goldbach.Cert.MajorArcStep4FullExpSum.norm_badResiduePart_le_sum_bad_vonMangoldt
          (q := q) (a := a) hq (L := L) (U := U) (β := β))
    have h1 :=
      (Goldbach.Cert.MajorArcStep4FullExpSum.sum_Ico_bad_vonMangoldt_le
        (q := q) hq (L := L) (U := U) hLU)
    exact le_trans h0 h1

  have htri :
      ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        +
      ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
    -- same proof as the `PsiBound` version
    let main : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V
    have hsplit_sub :
        (∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main
          =
        ((∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main)
          +
        (∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r) := by
      simp [main, hsplit, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]
    have hnorm :
        ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
          ≤
        ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
          +
        ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
      calc
        ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
            =
          ‖((∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main)
              + (∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r)‖ := by
            simpa [hsplit_sub]
        _ ≤
          ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
            +
          ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
            exact norm_add_le _ _
    simpa [main] using hnorm

  have hmain :
      ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
    have htri' :
        ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
          ≤
        ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
          +
        ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := htri
    calc
      ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
          ≤
        ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
              - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
            +
          ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := htri'
      _ ≤
        (q : ℝ) *
          ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
          +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
          have := add_le_add hcop_bound hbad_bound
          simpa [add_assoc, add_left_comm, add_comm] using this

  -- Replace the residue-decomposed LHS by the original sum.
  simpa [hdecomp] using hmain

end

end MajorArcStep4FullExpSumBMOR
end Goldbach.Cert
