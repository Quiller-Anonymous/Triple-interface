import Goldbach.Cert.MajorArcStep5ExpSumApproxBMOR
import Goldbach.Cert.MajorArcStep19PrimePowerDisposal

/-!
Major arcs (Step 20, BMOR-effective variant): major-arc approximation for bank prime-only sums.

This mirrors `Goldbach.Cert.MajorArcStep20BankExpSumApprox.norm_bankSum_sub_muMainTerm_le_of_PsiBound`,
but uses the BMOR-effective Step 5 bound for the von Mangoldt sum.

The prime-power contamination estimate (Step 19) is unchanged.
-/

namespace Goldbach.Cert
namespace MajorArcStep20BankExpSumApproxBMOR

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.ExplicitPNTinAP_BMOR
open Goldbach.Cert.MajorArcStep19PrimePowerDisposal

noncomputable section

theorem norm_bankSum_sub_muMainTerm_le_of_BMOR
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + ((a : ℝ) / (q : ℝ))) n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
      (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
  classical
  intro V
  have hVM :=
    Goldbach.Cert.MajorArcStep5ExpSumApproxBMOR.norm_expSum_sub_muMainTerm_le_of_BMOR
      (q := q) (a := a) (L := L) (U := U) hLU hL hXmin hq ha hqQ0 (β := β) hβ
  have hDiff :=
    (Goldbach.Cert.MajorArcStep19PrimePowerDisposal.norm_sum_ΛVM_sub_bankΛ_gExp_le
      (L := L) (U := U) (β := (β + ((a : ℝ) / (q : ℝ)))))
  set SB : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1), (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
  set SVM : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1),
      (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
  set C : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1),
      ((Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ))
        * gExp (β + (a : ℝ) / (q : ℝ)) n

  have hrewrite : SVM = SB + C := by
    subst SB SVM C
    have hterm :
        ∀ n : ℕ,
          (ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            =
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            +
          ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)) * gExp (β + (a : ℝ) / (q : ℝ)) n := by
      intro n
      have hsplit :
          (ΛVM n : ℂ)
            =
          (Goldbach.BG_Bank.Λ n : ℂ) + ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      calc
        (ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            =
          ((Goldbach.BG_Bank.Λ n : ℂ) + ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)))
            * gExp (β + (a : ℝ) / (q : ℝ)) n := by
              exact
                congrArg (fun z : ℂ => z * gExp (β + (a : ℝ) / (q : ℝ)) n) hsplit
        _ =
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            +
          ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)) * gExp (β + (a : ℝ) / (q : ℝ)) n := by
              simpa using
                (add_mul
                  (Goldbach.BG_Bank.Λ n : ℂ)
                  ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ))
                  (gExp (β + (a : ℝ) / (q : ℝ)) n))
    have hsum :
        (∑ n ∈ Finset.Ico L (U + 1), (ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n)
          =
        ∑ n ∈ Finset.Ico L (U + 1),
          ((Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            +
            ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)) * gExp (β + (a : ℝ) / (q : ℝ)) n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      simpa using hterm n
    rw [hsum]
    simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

  have hC_norm :
      ‖C‖ ≤ (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
    simpa [C] using hDiff

  -- Triangle inequality: `‖(SVM - main) - C‖ ≤ ‖SVM - main‖ + ‖C‖`.
  have hTri :
      ‖SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      ‖SVM - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖ + ‖C‖ := by
    have hSB : SB = SVM - C := by
      have := congrArg (fun t : ℂ => t - C) hrewrite
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
    have hSub :
        SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V
          =
        (SVM - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V) - C := by
      simp [hSB, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hSub]
    exact norm_sub_le _ _

  -- Put everything together.
  have hmain :
      ‖SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
      (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
    -- substitute Step 5 bound for `SVM` and the Step 19 bound for `C`.
    have := add_le_add hVM hC_norm
    exact le_trans hTri (by simpa [add_assoc, add_left_comm, add_comm] using this)

  -- Replace `SB` by the statement's bank sum and finish.
  simpa [SB] using hmain

end

end MajorArcStep20BankExpSumApproxBMOR
end Goldbach.Cert
