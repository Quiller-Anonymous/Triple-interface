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
        * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
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
      simp [g0, hneL, hg0, hsub, MajorArcStep2ExpSums.norm_gExp]

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
      have hLip : ‖gExp β (n + 1) - gExp β n‖ ≤ 4 * Real.pi * |β| :=
        MajorArcStep2ExpSums.norm_gExp_succ_sub_gExp_le (β := β) n hβ
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
      have hcard : ((Finset.Ico L U).card : ℝ) = ((U - L : ℕ) : ℝ) := by
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
              have := add_le_add (le_of_eq hboundary) hsum_interior'
              simpa [hboundary] using this

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
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
      have hinner :
          (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)))
            ≤ 2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)) := by
        have : ‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
                ≤ 2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
          have := add_le_add (le_of_eq hnorm_g0U) hsum_diff
          nlinarith
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
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
      rfl

/--
Variant of `norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_BMOR` with no `Xmin ≤ L-1` cutoff.

This uses the very weak uniform envelope
`|E(x)| ≤ 210 * x / log x` (valid for all `x ≥ 2`) to remove the `Xmin` side condition.

It is intended only as a certificate-friendly fallback when one wants to avoid low-end cutoffs in
later reductions.
-/
theorem norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_BMOR210
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL2 : 2 ≤ (L - 1))
    (hq : 1 ≤ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0) (hcop : Nat.Coprime a q)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
            * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
      ≤
      ((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
        * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
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
  have hsum_diff :
      (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
        ≤ (1 : ℝ) + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
    -- Same proof as the `Cψ`-version: split off the boundary jump and use Lipschitz on the interior.
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
      simp [g0, hneL, hg0, hsub, MajorArcStep2ExpSums.norm_gExp]

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
      have hrewrite : g0 (n + 1) - g0 n = gExp β (n + 1) - gExp β n := by
        simp [g0, hne0, hne1]
      -- Lipschitz bound for `gExp`.
      simpa [hrewrite] using
        (MajorArcStep2ExpSums.norm_gExp_succ_sub_gExp_le (β := β) (n := n) hβ)

    have hsum_interior :
        (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖)
          ≤ ((U - L : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
      have :=
        Finset.sum_le_sum (fun n hn => hdiff_interior (n := n) hn)
      -- Turn the constant sum into `card * constant`.
      have hcard : (Finset.Ico L U).card = U - L := by
        simpa using (Finset.card_Ico L U)
      have hconst :
          (∑ _n ∈ Finset.Ico L U, (4 * Real.pi * |β| : ℝ))
            =
          ((U - L : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
        simp [hcard, mul_assoc, mul_left_comm, mul_comm]
      exact le_trans this (by simpa [hconst])

    have hsub_le : (U - L : ℕ) ≤ (U - (L - 1) : ℕ) := by
      -- `U - L ≤ U - (L-1)` since `L-1 ≤ L`.
      exact Nat.sub_le_sub_left (Nat.pred_le _) U
    have hsum_interior' :
        (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖)
          ≤ ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
      have hnonneg : 0 ≤ (4 * Real.pi * |β|) := by
        have : 0 ≤ (4 : ℝ) := by norm_num
        exact mul_nonneg (mul_nonneg this (le_of_lt Real.pi_pos)) (abs_nonneg β)
      exact le_trans hsum_interior (by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsub_le) hnonneg)

    calc
      (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
          = (∑ n ∈ insert (L - 1) (Finset.Ico L U), ‖g0 (n + 1) - g0 n‖) := by
              simp [hIco]
      _ = ‖g0 (L - 1 + 1) - g0 (L - 1)‖
            + (∑ n ∈ Finset.Ico L U, ‖g0 (n + 1) - g0 n‖) := by
              simp [Finset.sum_insert, hnot]
      _ ≤ (1 : ℝ) + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
              have := add_le_add (le_of_eq hboundary) hsum_interior'
              simpa [hboundary] using this

  -- Uniform bound on `|E x|` for `x ∈ [L-1, U]` from the coarse `210 * x/log x` envelope.
  have hE_uniform :
      ∀ {x : ℕ}, x ∈ Finset.Icc (L - 1) U →
        |E (q := q) (a := a) x|
          ≤ (210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by
    intro x hx
    have hxX : L - 1 ≤ x := (Finset.mem_Icc.mp hx).1
    have hxU : x ≤ U := (Finset.mem_Icc.mp hx).2
    have hx2' : 2 ≤ x := le_trans hL2 hxX
    have hqQ : q ≤ Qmax :=
      le_trans hqQ0 (Q0_le_Qmax : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) ≤ Qmax)
    have hpoint := abs_E_le_210_of_two_le (q := q) (a := a) (x := x) hx2' hq hqQ hcop

    have hlogL_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
      have hL2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast hL2
      have h1 : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hL2'
      exact Real.log_pos h1
    have hlogx_pos : 0 < Real.log (x : ℝ) := by
      have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2'
      have h1 : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hx2R
      exact Real.log_pos h1
    have hlog_mono : Real.log ((L - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
      have hLpos : 0 < ((L - 1 : ℕ) : ℝ) := by
        have : 0 < (L - 1 : ℕ) := lt_of_lt_of_le (Nat.succ_pos 1) hL2
        exact_mod_cast this
      exact Real.log_le_log hLpos (by exact_mod_cast hxX)
    have hinv :
        (Real.log (x : ℝ))⁻¹ ≤ (Real.log ((L - 1 : ℕ) : ℝ))⁻¹ :=
      (inv_le_inv₀ hlogx_pos hlogL_pos).2 hlog_mono
    have hxU_real : (x : ℝ) ≤ (U : ℝ) := by exact_mod_cast hxU
    have hdiv :
        (x : ℝ) / Real.log (x : ℝ) ≤ (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by
      calc
        (x : ℝ) / Real.log (x : ℝ) = (x : ℝ) * (Real.log (x : ℝ))⁻¹ := by simp [div_eq_mul_inv]
        _ ≤ (U : ℝ) * (Real.log (x : ℝ))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hxU_real (by positivity)
        _ ≤ (U : ℝ) * (Real.log ((L - 1 : ℕ) : ℝ))⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by simp [div_eq_mul_inv]
    have hC_nonneg : 0 ≤ (210 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_left hdiv hC_nonneg
    exact le_trans hpoint (by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this)

  -- Apply the complex absE-weighted lemma to `g0`.
  have hSW :=
    SiegelWalfiszWeighted.norm_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform (q := q) (a := a)
      (g := g0) (L := L) (U := U)
      hLU hL hg0
      (M := (210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ)) hE_uniform

  -- Rewrite back to `gExp` and simplify the RHS using `hsum_diff`.
  have hSW' :
      ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
        ≤ ((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖))) := by
    simpa [hsum_weight, hsum_main] using hSW

  calc
    ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * gExp β n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), gExp β n)‖
        ≤ ((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖))) := hSW'
    _ ≤ ((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
      have hinner :
          (2 * (‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)))
            ≤ 2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)) := by
        have : ‖g0 U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g0 (n + 1) - g0 n‖)
                ≤ 2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
          have := add_le_add (le_of_eq hnorm_g0U) hsum_diff
          nlinarith
        nlinarith
      have hcoef_nonneg :
          0 ≤ (210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) := by
        have hlog_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
          have hL2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast hL2
          have h1 : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hL2'
          exact Real.log_pos h1
        exact div_nonneg (mul_nonneg (by norm_num) (by positivity)) (le_of_lt hlog_pos)
      exact mul_le_mul_of_nonneg_left hinner hcoef_nonneg
    _ = ((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := rfl

end

end MajorArcStep2ExpSumsBMOR
end Goldbach.Cert
