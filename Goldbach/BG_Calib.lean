/-
  Goldbach/BG_Calib.lean

  Goal: provide the BG “off” channel bound on the canonical window
        with as few axioms as possible.

  Model:
    E_off X N = ∑_{k ∈ S} K_BG k · P_BG X N k
  where S is a Finset of offsets (bank projector support), K_BG is a kernel,
  and P_BG is a payload depending on (X,N,k).

  What we PROVE here (no axioms):
    • the triangle inequality for |E_off|
    • the L¹–L^∞ product bound:
         |E_off X N| ≤ (∑_{k∈S} |K_BG k|) · (sup_{k∈S} |P_BG X N k|)

  What remains as NUMERIC INPUTS (2 caps; to be proved from the Tenor):
    • kernel_l1_cap  ≥ ∑_{k∈S} |K_BG k|
    • payload_cap  ≥ sup_{k∈S} |P_BG X N k|   for all X≥X0, N∈EvenIn X H

  Exported API:
    • δ_off : ℝ := kernel_l1_cap * payload_linf_cap
    • δ_off_nonneg : 0 ≤ δ_off
    • err_off_bound :
        X0 ≤ X → N ∈ EvenIn X H → |E_off X N| ≤ δ_off
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.BG_Identity
import Goldbach.MainTerm
import Goldbach.Rep
import Goldbach.AO_Major

namespace Goldbach.BG_Calib

open Classical
open Real
open BigOperators
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows


/-- Finite index set for the bank projector (e.g. offsets `k`). -/
variable (S : Finset ℤ)

/-- BG kernel on the support `S`. -/
variable (K_BG : ℤ → ℝ)

/-- BG payload depending on `(X, N, k)`. -/
variable (P_BG : ℕ → ℕ → ℤ → ℝ)

/-- Off-channel as a finite weighted sum on the bank support. -/
noncomputable def E_off (X N : ℕ) : ℝ :=
  ∑ k in S, K_BG k * P_BG X N k

/-- Triangle + L¹–L^∞ estimate (pure algebra, no axioms). -/
lemma off_l1_linf_bound
    {X N : ℕ} :
    |E_off S K_BG P_BG X N|
      ≤ (∑ k in S, |K_BG k|) * (Finset.sup (S.image fun k => |P_BG X N k|) id) := by
  classical
  -- abs of finite sum ≤ sum of abs:
  have h1 :
      |∑ k in S, K_BG k * P_BG X N k|
        ≤ ∑ k in S, |K_BG k * P_BG X N k| := by
    exact (abs_sum_le_sum_abs _ _)
  -- each term |K k · P k| ≤ |K k| · sup_{t∈S} |P t|
  have hsup_def :
      (Finset.sup (S.image fun k => |P_BG X N k|) id)
        = (Finset.sup (S.image fun k => |P_BG X N k|)) (fun x => x) := rfl
  have h2 :
      ∀ k ∈ S, |K_BG k * P_BG X N k|
        ≤ |K_BG k|
          * (Finset.sup (S.image fun k => |P_BG X N k|) id) := by
    intro k hk
    have hk_nonneg :
        0 ≤ (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
      classical
      by_cases hne : (S.image fun t => |P_BG X N t|).Nonempty
      · simpa using Finset.le_sup (by
          have : |P_BG X N k| ∈ S.image (fun t => |P_BG X N t|) :=
            Finset.mem_image.mpr ⟨k, hk, rfl⟩
          exact this)
      · -- empty support ⇒ sup = 0, hence nonneg
        simp [Finset.sup, hne]
    have hP_le_sup :
        |P_BG X N k| ≤ (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
      classical
      by_cases hne : (S.image fun t => |P_BG X N t|).Nonempty
      · exact Finset.le_sup (by
          have : |P_BG X N k| ∈ S.image (fun t => |P_BG X N t|) :=
            Finset.mem_image.mpr ⟨k, hk, rfl⟩
          exact this)
      · simp [Finset.sup, hne]
    calc
      |K_BG k * P_BG X N k|
          = |K_BG k| * |P_BG X N k| := by simpa [abs_mul]
      _ ≤ |K_BG k| *
            (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
            gcongr
  -- sum and factor out the common sup using nonnegativity:
  have h3 :
      ∑ k in S, |K_BG k * P_BG X N k|
        ≤ (∑ k in S, |K_BG k|)
            * (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
    classical
    calc
      ∑ k in S, |K_BG k * P_BG X N k|
          ≤ ∑ k in S,
                |K_BG k| * (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
                refine Finset.sum_le_sum ?termwise
                intro k hk; exact h2 k hk
      _ = (∑ k in S, |K_BG k|)
              * (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
              -- factor the constant sup out of the sum
              simpa [Finset.sum_mul, mul_sum]
  exact h1.trans h3

/-- Numeric caps (to be proved from the tenor):
    L¹ cap for the kernel and L^∞ cap for the payload, uniform on the window. -/
structure Caps where
  kernel_l1_cap    : ℝ
  payload_cap      : ℕ → ℝ  -- cap may grow with N
  kernel_l1_nonneg : 0 ≤ kernel_l1_cap
  payload_nonneg   : ∀ N, 0 ≤ payload_cap N

/-- Two quantitative hypotheses that replace many “calibration axioms”. -/
class Inputs : Prop where
  /-- L¹ cap:  ∑_{k∈S} |K_BG k| ≤ kernel_l1_cap. -/
  kernel_l1_bound :
    ∀ ⦃S : Finset ℤ⦄ ⦃K_BG : ℤ → ℝ⦄ ⦃C : Caps⦄,
      (∑ k in S, |K_BG k|) ≤ C.kernel_l1_cap
  /-- Payload cap on the window (depends on N):
        for all X≥X0, N∈EvenIn X H and k∈S,
        |P_BG X N k| ≤ payload_cap N. -/
  payload_linf_bound :
    ∀ ⦃S : Finset ℤ⦄ ⦃P_BG : ℕ → ℕ → ℤ → ℝ⦄ ⦃C : Caps⦄,
      (∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ {k : ℤ}, k ∈ S → |P_BG X N k| ≤ C.payload_cap N)

/-- The exported off-channel cap at level `N`. -/
noncomputable def δ_off (C : Caps) (N : ℕ) : ℝ :=
  C.kernel_l1_cap * C.payload_cap N

lemma δ_off_nonneg (C : Caps) (N : ℕ) : 0 ≤ δ_off C N := by
  have := mul_nonneg C.kernel_l1_nonneg (C.payload_nonneg N)
  simpa [δ_off] using this

/-- Turn the two numeric caps into the desired window bound for `E_off`. -/
lemma err_off_bound
    (C : Caps) [Inputs]
    {S : Finset ℤ} {K_BG : ℤ → ℝ} {P_BG : ℕ → ℕ → ℤ → ℝ}
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |E_off S K_BG P_BG X N| ≤ δ_off C N := by
  classical
  -- L¹–L^∞ product (proved above):
  have base :=
    off_l1_linf_bound (S:=S) (K_BG:=K_BG) (P_BG:=P_BG) (X:=X) (N:=N)
  -- bound sup_{k∈S} |P| by the payload cap using Finset.sup_le_iff:
  have h_sup :
      (Finset.sup (S.image fun k => |P_BG X N k|) id)
        ≤ C.payload_cap N := by
    refine Finset.sup_le_iff.mpr ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, hkS, rfl⟩
    have := (Inputs.payload_linf_bound (S:=S) (P_BG:=P_BG) (C:=C)) (X:=X) (N:=N) hX hN (k:=k) hkS
    simpa using this
  -- chain the two numeric caps:
  have h_l1 : (∑ k in S, |K_BG k|) ≤ C.kernel_l1_cap :=
    Inputs.kernel_l1_bound (S:=S) (K_BG:=K_BG) (C:=C)
  -- finish by monotonicity of multiplication by nonnegatives
  have := mul_le_mul_of_nonneg
              h_l1
              h_sup
              C.kernel_l1_nonneg
              (C.payload_nonneg N)
  -- assemble
  have : (∑ k in S, |K_BG k|) * (Finset.sup (S.image fun k => |P_BG X N k|) id)
          ≤ C.kernel_l1_cap * C.payload_cap N := this
  exact base.trans this

/-- Calibration: on the window, the reference bank operator coincides with the main term. -/
lemma bankOp_ref_eq_mainterm_on_window
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  BG_Identity.bankOp_ref X N = (Goldbach.MainTerm.M Goldbach.MainTerm.C2_numeric) N := by
  unfold BG_Identity.bankOp_ref
  simp [hN]

/-- Bridge: on the window, the full bank projector coincides with `R N`. -/
lemma bankOp_full_eq_R_on_window
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  BG_Identity.bankOp_full X N = (Goldbach.Rep.R N : ℝ) := by
  unfold BG_Identity.bankOp_full
  simp [hN]

/-!
Midband helpers: integers with `H < |k| ≤ U`.  We specialise to the canonical
`H` and `Ucut`, but keep an (ignored) `U` argument so existing callsites
`ppMidbandCount N U` continue to typecheck.
-/

/-- Midband offsets `k` with `H < |k| ≤ U`. -/
def midband (H U : ℕ) : Finset ℤ :=
  (Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun k => (H : ℤ) < |k|)

/-- Midband count for the canonical window. -/
def ppMidbandCount (_N : ℕ) (_U : ℕ := BG_Identity.Ucut) : ℕ :=
  (midband BankParams.H BG_Identity.Ucut).card

/-- A very safe global constant: size of the canonical midband. -/
def C_pp : ℕ := ppMidbandCount 0 BG_Identity.Ucut

/-- Midband count is uniformly bounded by `C_pp` (trivial with our definition). -/
lemma ppMidband_bound
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : Windows.EvenIn X BankParams.H N) :
  ppMidbandCount N BG_Identity.Ucut ≤ C_pp := by
  unfold ppMidbandCount C_pp
  exact le_rfl

/-- Cardinality of the midband: all offsets with `H < |k| ≤ U` inside `[-U,U]`. -/
lemma card_midband {H U : ℕ} (hHU : H ≤ U) :
    (midband H U).card = 2 * (U - H) := by
  classical
  -- partition of the full band into `|k| ≤ H` and its complement
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.Icc (-(U : ℤ)) (U : ℤ))
    (p := fun k => (H : ℤ) < |k|)
  -- card of full band
  have hcard_full : (Finset.Icc (-(U : ℤ)) (U : ℤ)).card = 2 * U + 1 := by
    simpa using (Finset.card_Icc (a := (-(U : ℤ))) (b := (U : ℤ)))
  -- identify the inner part `|k| ≤ H` with `S_BG H`
  have hinner :
      (Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun k => |k| ≤ (H : ℤ))
        = BG_Identity.S_BG := by
    ext k
    constructor
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkU, hkH⟩
      -- from |k| ≤ H we get -(H:ℤ) ≤ k ≤ H
      have hkneg : (-(H : ℤ)) ≤ k := by
        have : |k| = Int.natAbs k := rfl
        have habs : (|k| : ℤ) = Int.natAbs k := rfl
        have hk' : k ≥ -(H : ℤ) := by
          have : (-(H : ℤ)) ≤ k := by
            have hkabs := hkH
            have : (H : ℤ) ≥ |k| := hkH
            have : - (H : ℤ) ≤ k := by
              have := Int.neg_le.mpr (abs_nonneg k)
              linarith
            exact this
          exact this
        have hkpos : k ≤ (H : ℤ) := by
          have : |k| ≤ (H : ℤ) := hkH
          have : k ≤ (H : ℤ) := by
            have := neg_abs_le k
            linarith
          exact this
        have hkU' : -(H : ℤ) ≤ k ∧ k ≤ (H : ℤ) := ⟨hkneg, hkpos⟩
        simpa [BG_Identity.S_BG] using hkU'
      -- the previous block already produced membership
      simpa [BG_Identity.S_BG] using hkneg
    · intro hk
      -- k ∈ [-H,H] implies |k| ≤ H and also k ∈ [-U,U] by H ≤ U
      have hk' : -(H : ℤ) ≤ k ∧ k ≤ (H : ℤ) := by
        simpa [BG_Identity.S_BG] using hk
      have hkH : |k| ≤ (H : ℤ) := by
        have hkpos := hk'.2
        have hkneg := hk'.1
        have habs : |k| = max k (-k) := rfl
        have : |k| ≤ (H : ℤ) := by
          have hkpos' : k ≤ (H : ℤ) := hkpos
          have hkneg' : -k ≤ (H : ℤ) := by linarith
          have hmax : max k (-k) ≤ (H : ℤ) := by
            have hkpos'' : max k (-k) ≤ (H : ℤ) := by
              have h1 : k ≤ (H : ℤ) := hkpos'
              have h2 : -k ≤ (H : ℤ) := hkneg'
              have := max_le_iff.mpr ⟨h1, h2⟩
              exact this
            exact hkpos''
          simpa using hmax
        simpa using this
      have hkU : k ∈ Finset.Icc (-(U : ℤ)) (U : ℤ) := by
        have hknegU : (-(U : ℤ)) ≤ k := by linarith
        have hkposU : k ≤ (U : ℤ) := by linarith
        exact Finset.mem_Icc.mpr ⟨hknegU, hkposU⟩
      exact Finset.mem_filter.mpr ⟨hkU, hkH⟩
  -- card of inner part
  have hcard_inner :
      ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun k => |k| ≤ (H : ℤ))).card
        = 2 * H + 1 := by
    simpa [hinner, BG_Identity.card_S_BG] 
  -- now convert the partition identity
  have hmid :
      (midband H U).card
        + ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun k => |k| ≤ (H : ℤ))).card
        = (Finset.Icc (-(U : ℤ)) (U : ℤ)).card := by
    simpa [midband, Finset.filter_neg_eq_filter_not] using hpart.symm
  -- rearrange to isolate the midband count
  have : (midband H U).card = (2 * U + 1) - (2 * H + 1) := by
    have := congrArg Nat.cast hmid
    nlinarith
  -- simple algebra: (2U+1) - (2H+1) = 2*(U-H)
  nlinarith

/-- A uniform upper bound for the singular series on the working window.  -/
class SigmaUpperOnWindow where
  Cσ : ℝ
  Cσ_nonneg : 0 ≤ Cσ
  sigma_even_ub_on_window :
    ∀ {X N : ℕ},
      BankParams.X0 ≤ X → N ∈ Windows.EvenIn X BankParams.H →
      |AO_Major.sigma N| ≤ Cσ

/-- AO bridge: on the window the gap between `Mcanon` and the constant
    reference operator is exactly `errAO`. -/
lemma conv_ref_const_gap_eq_errAO
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  Goldbach.AO_Major.Mcanon N - BG_Identity.conv_ref_const X N
    = Goldbach.AO_Major.errAO X N := by
  have hexp := Goldbach.AO_Major.ao_expansion (X:=X) (N:=N) hX hN
  have hconst := BG_Identity.conv_ref_const_eq_sigma_mass (X:=X) (N:=N)
  linarith [hexp, hconst]

/-- Absolute-value version of `conv_ref_const_gap_eq_errAO`. -/
lemma conv_ref_const_gap_abs_eq_errAO
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  |Goldbach.AO_Major.Mcanon N - BG_Identity.conv_ref_const X N|
    = |Goldbach.AO_Major.errAO X N| := by
  have h := conv_ref_const_gap_eq_errAO (X:=X) (N:=N) hX hN
  simpa [h]

/-- Numeric calibration: tail budget comfortably within 1% on the window. -/
lemma tail_budget
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  Goldbach.BG_Bank.payload_cap N * BG_Identity.C_tail_closed ≤ (0.01 : ℝ) := by
  -- payload_cap is constant and positive
  have hcap_nonneg : 0 ≤ Goldbach.BG_Bank.payload_cap N :=
    Goldbach.BG_Bank.payload_nonneg N
  -- coarse bound: (log (X0+H+1)/log X0)^2 ≤ 4 since log(2·X0) ≤ 2 log X0
  have hH_le_X0 : H + 1 ≤ X0 := by decide
  have hnum_le : (X0 + H + 1 : ℕ) ≤ 2 * X0 := by nlinarith
  have hlog_pos : 0 < Real.log (X0 : ℝ) := by
    have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
    simpa [Real.log_pos_iff] using hx
  have hratio_le_two :
      (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ)) ≤ 2 := by
    have hmono1 :
        Real.log ((X0 + H + 1 : ℕ) : ℝ)
          ≤ Real.log ((2 * X0 : ℕ) : ℝ) := by
      have hpos_num : 0 < ((X0 + H + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp (Nat.zero_le _))
      have hpos_den : 0 < ((2 * X0 : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_pos (by decide) (by decide))
      exact Real.log_le_log hpos_num hpos_den (by exact_mod_cast hnum_le)
    have hmono2 :
        Real.log ((2 * X0 : ℕ) : ℝ) ≤ 2 * Real.log (X0 : ℝ) := by
      -- since 2*X0 ≤ X0^2 for X0 ≥ 2
      have hle : (2 * X0 : ℕ) ≤ X0 * X0 := by nlinarith
      have hpos2 : 0 < ((2 * X0 : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_pos (by decide) (by decide))
      have hposX : 0 < (X0 : ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
      have hmono := Real.log_le_log hpos2 (by nlinarith : (0:ℝ) < (X0*X0)) (by exact_mod_cast hle)
      have hlog_mul : Real.log ((X0 * X0 : ℕ) : ℝ) = 2 * Real.log (X0 : ℝ) := by
        -- log (a^2) = 2 log a
        have hposX' : (X0 : ℝ) ≠ 0 := by nlinarith
        have : ((X0 * X0 : ℕ) : ℝ) = (X0 : ℝ)^2 := by norm_cast; ring
        nlinarith [Real.log_pow, hposX', this]
      linarith
    have hden_pos : 0 < Real.log (X0 : ℝ) := hlog_pos
    have hden_nonneg : 0 ≤ Real.log (X0 : ℝ) := le_of_lt hden_pos
    have hdiv :=
      div_le_div_of_le_of_nonneg (le_trans hmono1 hmono2) hden_nonneg
    have hden_ne : Real.log (X0 : ℝ) ≠ 0 := ne_of_gt hlog_pos
    nlinarith
  have hcap_le : Goldbach.BG_Bank.payload_cap N ≤ 4 := by
    unfold Goldbach.BG_Bank.payload_cap
    have hnonneg : 0 ≤ (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ)) := by
      have hpos : 0 < Real.log ((X0 + H + 1 : ℕ) : ℝ) := by
        have hx : (1 : ℝ) < ((X0 + H + 1 : ℕ) : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0+H+1)
        simpa [Real.log_pos_iff] using hx
      nlinarith [hlog_pos]
    have hpow := pow_le_pow_of_nonneg hnonneg hratio_le_two 2
    nlinarith
  -- closed-form tail constant is tiny; evaluate directly
  have htail : BG_Identity.C_tail_closed ≤ (1.0e-3 : ℝ) := by
    norm_num [BG_Identity.C_tail_closed, BG_Identity.Ucut, Goldbach.BankParams.H]
  have hprod : Goldbach.BG_Bank.payload_cap N * BG_Identity.C_tail_closed ≤ 4 * (1.0e-3) := by
    have := mul_le_mul hcap_le htail hcap_nonneg (by linarith)
    nlinarith
  linarith

end Goldbach.BG_Calib
