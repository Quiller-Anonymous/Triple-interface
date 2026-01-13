import Goldbach.Cert.MajorArcStep2ExpSums
import Goldbach.Cert.SiegelWalfiszWeightedComplexAbsE
import Goldbach.Cert.ExplicitPNTinAP_BMOR_Consequences

/-!
Major arcs (Step 2, BMOR-effective variant): exponential sums in AP from an **explicit** ψ-bound.

This is a “turnkey-certificate oriented” variant of `MajorArcStep2ExpSums`:
instead of consuming an *ineffective* `PsiBound A` with the side condition `q ≤ (log x)^A`,
we assume the explicit PNT-in-AP estimate from BMOR (as an axiom in
`Goldbach.Cert.ExplicitPNTinAP_BMOR`) and derive the same kind of major-arc exponential-sum bound
for *fixed* moduli `q ≤ Q0 = 30000` and `x ≥ 10^6`.

This file is sigma-agnostic; it only produces Step-2 type exponential sum bounds.
-/

namespace Goldbach.Cert
namespace MajorArcStep2ExpSumsBMOR

open scoped BigOperators

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SiegelWalfiszWeighted
open Goldbach.Cert.ExplicitPNTinAP_BMOR
open Goldbach.Cert.ExplicitPNTinAP_BMOR.Consequences
open Goldbach.Cert.MajorArcStep2ExpSums

noncomputable section

variable {q a : ℕ}

/--
BMOR-effective Step-2 bound on an interval:

`∑_{n∈Ico L (U+1), n≡a[q]} ΛVM(n) e(β n)` is close to `(1/φ(q)) * ∑ e(β n)`,
with an explicit error using the BMOR constant `Cψ` and `log (L-1)` (no `q ≤ (log x)^A` side condition).

We keep the same “small arc” condition `|2πβ| ≤ 1` as the existing Step-2 lemma.
-/
theorem norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_BMOR
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0) (hcop : Nat.Coprime a q)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
            * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
      ≤
      (Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
        * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))) := by
  classical
  -- Modify the weight so it vanishes at `L-1` (as in the `PsiBound` proof).
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

  -- Bound `‖g0 U‖ = 1`.
  have hU_ne : (U : ℕ) ≠ L - 1 := by
    have hLm1_lt_L : (L - 1) < L := Nat.pred_lt (Nat.ne_of_gt hL)
    exact Nat.ne_of_gt (lt_of_lt_of_le hLm1_lt_L hLU)
  have hnorm_g0U : ‖g0 U‖ = 1 := by
    simpa [g0, hU_ne] using (MajorArcStep2ExpSums.norm_gExp (β := β) (n := U))

  -- Bound the variation term for `g0` over `Ico (L-1) U`.
  have hdiff_bound :
      ∀ {n : ℕ}, n ∈ Finset.Ico (L - 1) U →
        ‖g0 (n + 1) - g0 n‖ ≤ (1 : ℝ) + (4 * Real.pi * |β|) := by
    intro n hn
    by_cases hcase : n = L - 1
    · subst hcase
      -- boundary jump: `g0(L) - g0(L-1) = gExp(L) - 0`
      have hLm1_lt_L : (L - 1) < L := Nat.pred_lt (Nat.ne_of_gt hL)
      have hneL : (L : ℕ) ≠ L - 1 := ne_of_gt hLm1_lt_L
      have hsub : L - 1 + 1 = L := Nat.sub_add_cancel (Nat.succ_le_of_lt hL)
      have hnorm : ‖gExp β L‖ = 1 := MajorArcStep2ExpSums.norm_gExp (β := β) (n := L)
      have hnonneg : 0 ≤ 4 * Real.pi * |β| := by
        have h4 : 0 ≤ (4 : ℝ) := by norm_num
        exact mul_nonneg (mul_nonneg h4 (le_of_lt Real.pi_pos)) (abs_nonneg β)
      have : ‖g0 (L - 1 + 1) - g0 (L - 1)‖ ≤ (1 : ℝ) + (4 * Real.pi * |β|) := by
        have : (1 : ℝ) ≤ (1 : ℝ) + (4 * Real.pi * |β|) := by linarith
        simpa [g0, hneL, hg0, hsub, hnorm] using this
      simpa [hsub] using this
    · -- interior: both endpoints are `gExp`, so use the `e` Lipschitz bound.
      have hne1 : (n + 1 : ℕ) ≠ L - 1 := by
        have hn_ge : (L - 1) ≤ n := (Finset.mem_Ico.mp hn).1
        have : (L - 1) < n + 1 := lt_of_le_of_lt hn_ge (Nat.lt_succ_self n)
        exact ne_of_gt this
      have hne0 : n ≠ L - 1 := hcase
      have hcore : ‖g0 (n + 1) - g0 n‖ = ‖gExp β (n + 1) - gExp β n‖ := by
        simp [g0, hne1, hne0]
      have hLip : ‖gExp β (n + 1) - gExp β n‖ ≤ 4 * Real.pi * |β| :=
        MajorArcStep2ExpSums.norm_gExp_succ_sub_gExp_le (β := β) n hβ
      exact le_trans (by simpa [hcore] using hLip) (by nlinarith)

  have hsum_diff :
      (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
        ≤ ((U - (L - 1) : ℕ) : ℝ) * ((1 : ℝ) + (4 * Real.pi * |β|)) := by
    have hle :
        (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
          ≤ ∑ n ∈ Finset.Ico (L - 1) U, ((1 : ℝ) + (4 * Real.pi * |β|)) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact hdiff_bound (n := n) hn
    have hcardNat : (Finset.Ico (L - 1) U).card = U - (L - 1) := by
      simp
    have hcard : ((Finset.Ico (L - 1) U).card : ℝ) = ((U - (L - 1) : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    calc
      (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
          ≤ ∑ n ∈ Finset.Ico (L - 1) U, ((1 : ℝ) + (4 * Real.pi * |β|)) := hle
      _ = ((Finset.Ico (L - 1) U).card : ℝ) * ((1 : ℝ) + (4 * Real.pi * |β|)) := by
            simp [mul_add]
      _ = ((U - (L - 1) : ℕ) : ℝ) * ((1 : ℝ) + (4 * Real.pi * |β|)) := by
            simp [hcard]

  -- Uniform bound on `|E x|` for `x ∈ [L-1, U]` from BMOR.
  have hE_uniform :
      ∀ {x : ℕ}, x ∈ Finset.Icc (L - 1) U →
        |E (q := q) (a := a) x|
          ≤ Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by
    intro x hx
    have hXmin' : Xmin ≤ (L - 1) := hXmin
    have hx' :
        |E (q := q) (a := a) x| ≤ Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by
      -- Apply the interval-uniform BMOR consequence with `X := L-1`.
      have hx'' :=
        (abs_E_le_uniform_on_Icc_Q0 (q := q) (a := a)
          (X := (L - 1)) (U := U) (hX := hXmin') hq hqQ0 hcop (x := x) ?_)
      · simpa using hx''
      · -- `x ∈ Icc (L-1) U` as required.
        simpa using hx
    exact hx'

  -- Apply the complex absE-weighted lemma to `g0`.
  have hSW :=
    SiegelWalfiszWeighted.norm_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform (q := q) (a := a)
      (g := g0) (L := L) (U := U)
      hLU hL hg0
      (M := Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ)) hE_uniform

  -- Rewrite back to `gExp` and simplify the RHS using `hsum_diff`.
  have hSW' :
      ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
        ≤ (Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖))) := by
    simpa [hsum_weight, hsum_main] using hSW

  calc
    ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
        ≤ (Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖))) := hSW'
    _ ≤ (Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))) := by
      have hinner :
          (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)))
            ≤ 2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)) := by
        have : ‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
                ≤ 1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|) := by
          have := add_le_add (le_of_eq hnorm_g0U) hsum_diff
          simpa [mul_add] using this
        nlinarith
      have hcoef_nonneg :
          0 ≤ Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by
        have hlog_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
          -- `L - 1 ≥ 10^6 ≥ 2`
          have hX2 : (2 : ℕ) ≤ (L - 1) := le_trans (by
            norm_num [Xmin]) hXmin
          have hX2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast hX2
          have h1X : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hX2'
          exact Real.log_pos h1X
        have hC : 0 ≤ Cψ := Cψ_nonneg
        exact div_nonneg (mul_nonneg hC (by positivity)) (le_of_lt hlog_pos)
      exact mul_le_mul_of_nonneg_left hinner hcoef_nonneg
    _ = (Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))) := by
      rfl

end

end MajorArcStep2ExpSumsBMOR
end Goldbach.Cert
