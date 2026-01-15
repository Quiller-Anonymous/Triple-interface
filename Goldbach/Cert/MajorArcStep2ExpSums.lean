import Goldbach.Cert.SiegelWalfiszAxioms
import Goldbach.Cert.SiegelWalfiszWeightedComplex
import Goldbach.Cert.MajorArcExponentialPrelude
import Mathlib.Algebra.BigOperators.Intervals

/-!
Major arcs (Step 2, preparatory): exponential sums in arithmetic progressions on short intervals.

This file is sigma-agnostic. It packages a lemma of the form:

`SW(ψ) ⇒` a bound for
`∑_{n ∈ [L,U], n≡a[q]} ΛVM(n) e(β n)` vs `(1/φ(q)) * ∑_{n ∈ [L,U]} e(β n)`,

where `e(x) = exp(2π i x)` and the bound is uniform in `β` on a small-arc regime
`|2πβ| ≤ 1` (sufficient for major-arc widths once `X` is large).
-/

namespace Goldbach.Cert
namespace MajorArcStep2ExpSums

open scoped BigOperators

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SiegelWalfiszWeighted
open Goldbach.Cert.MajorArcExponential

noncomputable section

variable (q a : ℕ)

/-- The additive character weight `n ↦ e(β n)` (as a function on `ℕ`). -/
noncomputable def gExp (β : ℝ) (n : ℕ) : ℂ :=
  e (β * (n : ℝ))

lemma norm_gExp (β : ℝ) (n : ℕ) : ‖gExp β n‖ = 1 := by
  simp [gExp, norm_e]

lemma norm_gExp_succ_sub_gExp_le (β : ℝ) (n : ℕ) (hβ : |2 * Real.pi * β| ≤ 1) :
    ‖gExp β (n + 1) - gExp β n‖ ≤ 4 * Real.pi * |β| := by
  -- Apply the `e` Lipschitz bound with `x = β(n+1)` and `y = βn`.
  have hxy : |2 * Real.pi * ((β * ((n + 1 : ℕ) : ℝ)) - (β * (n : ℝ)))| ≤ 1 := by
    -- the inner difference is just `β`
    simpa [mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using hβ
  have habs : |β * ((n : ℝ) + 1) - β * (n : ℝ)| = |β| := by
    have hdiff : β * ((n : ℝ) + 1) - β * (n : ℝ) = β := by nlinarith
    simp [hdiff]
  have h :=
    (norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one (x := β * ((n + 1 : ℕ) : ℝ)) (y := β * (n : ℝ))
      hxy)
  -- `simp` rewrites `((n+1:ℕ):ℝ)` to `(n:ℝ)+1`, so `habs` applies.
  simpa [gExp, habs] using h

/--
Main Step-2 lemma: a SW(ψ)-derived AP exponential sum bound on an interval.

This is obtained by applying the complex SW-weighted interval lemma to a modified weight that
vanishes at `L-1`, so no boundary hypothesis is needed.
-/
theorem norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_PsiBound
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
            * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
      ≤
      (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
        * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
  classical
  -- Modify the weight so it vanishes at `L-1`.
  let g0 : ℕ → ℂ :=
    fun n => if n = L - 1 then 0 else gExp β n
  have hg0 : g0 (L - 1) = 0 := by simp [g0]

  -- On the target interval, `g0 = gExp` since `n ≠ L-1`.
  have hg0_eq_on_Ico :
      ∀ {n : ℕ}, n ∈ Finset.Ico L (U + 1) → g0 n = gExp β n := by
    intro n hn
    have hnL : L ≤ n := (Finset.mem_Ico.mp hn).1
    have hLm1_lt_L : (L - 1) < L := Nat.pred_lt (Nat.ne_of_gt hL)
    have hne : n ≠ L - 1 := by
      exact ne_of_gt (lt_of_lt_of_le hLm1_lt_L hnL)
    simp [g0, hne]

  have hsum_weight :
      (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * g0 n)
        =
      (∑ n ∈ Finset.Ico L (U + 1),
          (aTerm (q := q) (a := a) n : ℂ) * gExp β n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [hg0_eq_on_Ico hn]

  have hsum_main :
      (∑ n ∈ Finset.Ico L (U + 1), g0 n)
        =
      (∑ n ∈ Finset.Ico L (U + 1), gExp β n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact hg0_eq_on_Ico hn

  -- Bound the variation term for `g0` over `Ico (L-1) U`.
  have hsum_diff :
      (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
        ≤ (1 : ℝ) + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
    -- Split off the single boundary jump at `n = L-1`; on the interior we get the Lipschitz bound
    -- `‖e(β(n+1)) - e(βn)‖ ≤ 4π|β|`.
    have hLm1_lt_L : (L - 1) < L := Nat.pred_lt (Nat.ne_of_gt hL)
    have hLm1_lt_U : L - 1 < U := lt_of_lt_of_le hLm1_lt_L hLU
    have hsub : L - 1 + 1 = L := Nat.sub_add_cancel (Nat.succ_le_of_lt hL)
    have hIco : insert (L - 1) (Finset.Ico L U) = Finset.Ico (L - 1) U := by
      simpa [hsub] using
        (Finset.insert_Ico_succ_left_eq_Ico (a := L - 1) (b := U) hLm1_lt_U)
    have hnot : (L - 1) ∉ Finset.Ico L U := by
      have : ¬ L ≤ L - 1 := Nat.not_le_of_gt hLm1_lt_L
      simp [Finset.mem_Ico, this]
    have hneL : (L : ℕ) ≠ L - 1 := ne_of_gt hLm1_lt_L

    have hboundary : ‖g0 (L - 1 + 1) - g0 (L - 1)‖ = 1 := by
      -- `g0(L-1)=0`, `g0(L)=gExp(L)`, and `‖gExp(L)‖ = 1`.
      simp [g0, hneL, hg0, hsub, norm_gExp]

    have hdiff_interior :
        ∀ {n : ℕ}, n ∈ Finset.Ico L U → ‖g0 (n + 1) - g0 n‖ ≤ 4 * Real.pi * |β| := by
      intro n hn
      have hnL : L ≤ n := (Finset.mem_Ico.mp hn).1
      have hne0 : n ≠ L - 1 := by
        exact ne_of_gt (lt_of_lt_of_le hLm1_lt_L hnL)
      have hne1 : (n + 1 : ℕ) ≠ L - 1 := by
        have hn_ge : (L - 1) ≤ n := le_trans (Nat.le_of_lt hLm1_lt_L) hnL
        have : (L - 1) < n + 1 := lt_of_le_of_lt hn_ge (Nat.lt_succ_self n)
        exact ne_of_gt this
      have hcore :
          ‖g0 (n + 1) - g0 n‖ = ‖gExp β (n + 1) - gExp β n‖ := by
        simp [g0, hne0, hne1]
      have hLip :
          ‖gExp β (n + 1) - gExp β n‖ ≤ 4 * Real.pi * |β| :=
        norm_gExp_succ_sub_gExp_le (β := β) n hβ
      simpa [hcore] using hLip

    have hsum_interior :
        (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖)
          ≤ ((U - L : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
      have hle :
          (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖)
            ≤ ∑ n ∈ Finset.Ico L U, (4 * Real.pi * |β|) := by
        refine Finset.sum_le_sum ?_
        intro n hn
        exact hdiff_interior (n := n) hn
      have hcardNat : (Finset.Ico L U).card = U - L := by simp
      have hcard :
          ((Finset.Ico L U).card : ℝ) = ((U - L : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      calc
        (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖)
            ≤ ∑ n ∈ Finset.Ico L U, (4 * Real.pi * |β|) := hle
        _ = ((Finset.Ico L U).card : ℝ) * (4 * Real.pi * |β|) := by
              simp
        _ = ((U - L : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
              simp

    have hnonneg : 0 ≤ 4 * Real.pi * |β| := by
      have h4 : 0 ≤ (4 : ℝ) := by norm_num
      exact mul_nonneg (mul_nonneg h4 (le_of_lt Real.pi_pos)) (abs_nonneg β)

    have hsub_le : (U - L) ≤ (U - (L - 1)) := by
      exact Nat.sub_le_sub_left (Nat.pred_le L) U
    have hsub_le' : ((U - L : ℕ) : ℝ) ≤ ((U - (L - 1) : ℕ) : ℝ) := by
      exact_mod_cast hsub_le

    have hsum_interior' :
        (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖)
          ≤ ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
      exact le_trans hsum_interior (by
        exact mul_le_mul_of_nonneg_right hsub_le' hnonneg)

    calc
      (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
          = (∑ n ∈ insert (L - 1) (Finset.Ico L U), ‖g0 (n + 1) - g0 n‖) := by
              simp [hIco]
      _ = ‖g0 (L - 1 + 1) - g0 (L - 1)‖
            + (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖) := by
              simp [Finset.sum_insert, hnot]
      _ ≤ (1 : ℝ) + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
              -- Use `hboundary` and `hsum_interior'`.
              have := add_le_add (le_of_eq hboundary) hsum_interior'
              simpa [hboundary] using this

  have hU_ne : (U : ℕ) ≠ L - 1 := by
    have hLm1_lt_L : (L - 1) < L := Nat.pred_lt (Nat.ne_of_gt hL)
    exact Nat.ne_of_gt (lt_of_lt_of_le hLm1_lt_L hLU)
  have hnorm_g0U : ‖g0 U‖ = 1 := by
    simpa [g0, hU_ne] using (norm_gExp (β := β) (n := U))

  -- Apply the complex SW-weighted interval lemma to `g0`.
  have hSW :=
    SiegelWalfiszWeighted.norm_weightedSum_Ico_sub_mainTerm_le_of_PsiBound (q := q) (a := a)
      (hpsi := hpsi) (g := g0) (L := L) (U := U)
      hLU hL hL3 hq hcop hqlog hg0

  -- Rewrite the LHS back to the desired `gExp`, and bound the RHS using `hsum_diff`.
  have hSW' :
      ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
        ≤
        (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖))) := by
    simpa [hsum_weight, hsum_main] using hSW

  calc
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
            * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
        ≤
        (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖))) := hSW'
    _ ≤
        (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
        have hinner :
            (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)))
              ≤ 2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)) := by
          have : ‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
                  ≤ 2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
            have := add_le_add (le_of_eq hnorm_g0U) hsum_diff
            nlinarith
          nlinarith
        exact mul_le_mul_of_nonneg_left hinner (by
          -- the outer factor is nonnegative
          have hlog_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
            have h2 : (2 : ℕ) ≤ (L - 1 : ℕ) := le_trans (by decide : (2 : ℕ) ≤ 3) hL3
            have h2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast h2
            have h1 : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2'
            exact Real.log_pos h1
          have hpow_pos : 0 < (Real.log ((L - 1 : ℕ) : ℝ)) ^ A := pow_pos hlog_pos A
          have hmul_nonneg : 0 ≤ hpsi.C * (U : ℝ) := by
            exact mul_nonneg hpsi.C_nonneg (by positivity)
          exact div_nonneg hmul_nonneg (le_of_lt hpow_pos))

end

end MajorArcStep2ExpSums
end Goldbach.Cert
