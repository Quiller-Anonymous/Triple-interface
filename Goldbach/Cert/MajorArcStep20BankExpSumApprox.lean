import Goldbach.Cert.MajorArcStep5ExpSumApprox
import Goldbach.Cert.MajorArcStep19PrimePowerDisposal

/-!
Major arcs (Step 20, sigma-agnostic): major-arc approximation for bank prime-only exponential sums.

Step 5 gives a major-arc approximation for von Mangoldt-weighted sums:

`∑ ΛVM(n) e((β + a/q)n) ≈ (μ(q)/φ(q)) * ∑ e(β n)`.

The Goldbach bank weight is prime-only (`BG_Bank.Λ`), differing from `ΛVM` only on prime powers.
Step 19 supplies a crude bound on the resulting contamination term.

This file combines Steps 5 and 19 via the triangle inequality to obtain a major-arc approximation
for the bank exponential sum with the same main term.
-/

namespace Goldbach.Cert
namespace MajorArcStep20BankExpSumApprox

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep5ExpSumApprox
open Goldbach.Cert.MajorArcStep19PrimePowerDisposal

noncomputable section

/--
Bank (prime-only) major-arc approximation on an interval, derived from Step 5 (`ΛVM`) plus
Step 19 (prime-power disposal).
-/
theorem norm_bankSum_sub_muMainTerm_le_of_PsiBound
    {q a : ℕ}
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + ((a : ℝ) / (q : ℝ))) n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
      (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
  classical
  intro V
  -- Step 5 gives the `ΛVM` version of the same approximation.
  have hVM :=
    Goldbach.Cert.MajorArcStep5ExpSumApprox.norm_expSum_sub_muMainTerm_le_of_PsiBound
      (q := q) (a := a) (A := A) (hpsi := hpsi)
      (L := L) (U := U) hLU hL hL3 hq ha hqlog (β := β) hβ
  -- Step 19 bounds the difference between `ΛVM` and the bank weight.
  have hDiff :=
    (Goldbach.Cert.MajorArcStep19PrimePowerDisposal.norm_sum_ΛVM_sub_bankΛ_gExp_le
      (L := L) (U := U) (β := (β + ((a : ℝ) / (q : ℝ))))) -- gExp at the same frequency
  -- Name the three sums (bank, von Mangoldt, contamination).
  set SB : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1), (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
  set SVM : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1),
      (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
  set C : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1),
      ((Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ))
        * gExp (β + (a : ℝ) / (q : ℝ)) n

  have hrewrite :
      SVM = SB + C := by
    -- Expand definitions and use `Finset.sum_add_distrib` after a pointwise decomposition.
    subst SB SVM C
    -- Pointwise decomposition:
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
        -- `x = y + (x-y)`.
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      -- Multiply by `gExp` and distribute.
      calc
        (ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            =
          ((Goldbach.BG_Bank.Λ n : ℂ) + ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)))
            * gExp (β + (a : ℝ) / (q : ℝ)) n := by
              -- Use `congrArg` to avoid rewriting the RHS occurrence of `ΛVM n`.
              exact
                congrArg (fun z : ℂ => z * gExp (β + (a : ℝ) / (q : ℝ)) n) hsplit
        _ =
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
            +
          ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ)) * gExp (β + (a : ℝ) / (q : ℝ)) n := by
              -- Pure ring-like distribution: `(x+y)*z = x*z + y*z`.
              simpa using
                (add_mul
                  (Goldbach.BG_Bank.Λ n : ℂ)
                  ((ΛVM n : ℂ) - (Goldbach.BG_Bank.Λ n : ℂ))
                  (gExp (β + (a : ℝ) / (q : ℝ)) n))

    -- Apply `hterm` under the sum, then split using `sum_add_distrib`.
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
    simpa [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

  -- Triangle inequality: `‖(SVM - main) - C‖ ≤ ‖SVM - main‖ + ‖C‖`.
  have hTri :
      ‖SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      ‖SVM - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖ + ‖C‖ := by
    -- rewrite `SB` as `SVM - C` using `hrewrite`, then apply `norm_sub_le`.
    have hSB : SB = SVM - C := by
      -- from `SVM = SB + C` we get `SB = SVM - C`
      have := congrArg (fun t : ℂ => t - C) hrewrite
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
    -- now `SB - main = (SVM - main) - C`
    have hSub :
        SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V
          =
        (SVM - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V) - C := by
      -- substitute `SB = SVM - C` and rearrange.
      simp [hSB, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    -- Apply `‖x - y‖ ≤ ‖x‖ + ‖y‖`.
    rw [hSub]
    exact norm_sub_le _ _

  -- Combine Step 5 bound with contamination bound.
  have hFinal :
      ‖SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      (q : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
      (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
    -- `hVM` bounds the `ΛVM` term, and `hDiff` bounds the contamination.
    have hDiff' :
        ‖C‖
          ≤ (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
      -- `C` is the same sum as in Step 19, up to rewriting `↑(x-y)` as `↑x-↑y`.
      have hC :
          C =
          ∑ n ∈ Finset.Ico L (U + 1),
            ((Goldbach.Cert.SiegelWalfisz.ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ)
              * gExp (β + (a : ℝ) / (q : ℝ)) n := by
        subst C
        refine Finset.sum_congr rfl ?_
        intro n hn
        -- unfold the real-to-complex cast of a difference
        simp [sub_eq_add_neg, add_mul, mul_assoc]
      -- Apply the Step 19 bound and rewrite by `hC`.
      simpa [hC] using hDiff
    -- Combine via triangle inequality + bounds.
    calc
      ‖SB - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
          ≤ ‖SVM - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖ + ‖C‖ := hTri
      _ ≤
        ( (q : ℝ) *
            ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
              * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
          +
          (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) )
          + (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
          exact add_le_add hVM hDiff'
      _ = _ := by ring

  -- Unfold `SB`/`SVM`/`C` back into the statement.
  simpa [SB] using hFinal

end

end MajorArcStep20BankExpSumApprox
end Goldbach.Cert
