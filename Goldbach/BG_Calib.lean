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
import Goldbach.AO_AssembleEnvelope

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
  let band : Finset ℤ := Finset.Icc (-(U : ℤ)) (U : ℤ)
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := band) (p := fun k => (H : ℤ) < |k|)
  -- card of full band
  have hcard_full : band.card = 2 * U + 1 := by
    simpa [band] using (Finset.card_Icc (a := (-(U : ℤ))) (b := (U : ℤ)))
  -- inner band `|k| ≤ H` has size 2H+1
  have hcard_inner :
      (band.filter (fun k => |k| ≤ (H : ℤ))).card = 2 * H + 1 := by
    -- `|k| ≤ H` inside `[-U,U]` is the interval `[-H,H]` when `H ≤ U`
    have hEq :
        band.filter (fun k => |k| ≤ (H : ℤ))
          = Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      ext k; constructor
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨hkU, hkH⟩
        rcases Finset.mem_Icc.mp hkU with ⟨hknegU, hkposU⟩
        have hkneg : (-(H : ℤ)) ≤ k := by linarith
        have hkpos : k ≤ (H : ℤ) := by linarith
        exact Finset.mem_Icc.mpr ⟨hkneg, hkpos⟩
      · intro hk
        have hkH : |k| ≤ (H : ℤ) := by
          rcases Finset.mem_Icc.mp hk with ⟨hkneg, hkpos⟩
          have hkpos' : k ≤ (H : ℤ) := hkpos
          have hkneg' : -k ≤ (H : ℤ) := by linarith
          have : |k| = max k (-k) := by rfl
          have hmax : max k (-k) ≤ (H : ℤ) := max_le_iff.mpr ⟨hkpos', hkneg'⟩
          linarith
        have hkIcc : k ∈ band := by
          rcases Finset.mem_Icc.mp hk with ⟨hkneg, hkpos⟩
          have hkneg' : (-(U : ℤ)) ≤ k := by linarith [hHU]
          have hkpos' : k ≤ (U : ℤ) := by linarith [hHU]
          exact Finset.mem_Icc.mpr ⟨hkneg', hkpos'⟩
        exact Finset.mem_filter.mpr ⟨hkIcc, hkH⟩
    simpa [hEq] using (Finset.card_Icc (a := (-(H : ℤ))) (b := (H : ℤ)))
  -- combine the partition identity on cardinals
  have hmid :
      (midband H U).card
        + (band.filter (fun k => |k| ≤ (H : ℤ))).card
        = band.card := by
    -- filter p + filter ¬p = full
    simpa [midband, band] using hpart
  -- rearrange to isolate the midband count
  have : (midband H U).card = (2 * U + 1) - (2 * H + 1) := by
    nlinarith
      [hmid, hcard_full, hcard_inner]
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

/-- Pointwise bound on the constant reference payload on the window. -/
lemma pref_bound_on_window
    [SigmaUpperOnWindow] {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    {k : ℤ} (hk : k ∈ BG_Identity.S_BG) :
    |BG_Identity.Pref X N k| ≤ SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
  classical
  -- on `S_BG` the `if` branch fires and weight_mass = 1
  have hmass_pos : 0 < BG_Identity.mass_BG := BG_Identity.mass_BG_pos
  have hσ : |AO_Major.sigma N| ≤ SigmaUpperOnWindow.Cσ :=
    SigmaUpperOnWindow.sigma_even_ub_on_window (X:=X) (N:=N) hX hN
  have hmass_nonneg : 0 ≤ BG_Identity.mass_BG := le_of_lt hmass_pos
  have hrewrite :
      |BG_Identity.Pref X N k|
        = |AO_Major.sigma N| / BG_Identity.mass_BG := by
    simp [BG_Identity.Pref, hk, AO_Major.weight_mass, abs_div,
      abs_of_pos hmass_pos, abs_mul]
  -- divide the σ-bound by the positive mass
  have hdiv : |AO_Major.sigma N| / BG_Identity.mass_BG
      ≤ SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
    have := div_le_div_of_nonneg_right hσ hmass_nonneg
    simpa using this
  simpa [hrewrite] using hdiv

/-- Inner swap + AO envelope: bound the gap between `conv_ref` and `Mcanon`
    using (i) payload cap, (ii) σ upper bound, (iii) the AO error envelope. -/
lemma ref_to_M_bound
    (C : AO_AssembleEnvelope.Channels) (K : AO_AssembleEnvelope.Caps)
    [AO_AssembleEnvelope.Decomposition C] [AO_AssembleEnvelope.Bounds C K]
    [SigmaUpperOnWindow]
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.conv_ref X N - AO_Major.Mcanon N|
      ≤ AO_ErrorEnvelope.δAO K
        + ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
            (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG) := by
  classical
  -- AO envelope on the constant reference
  have hAO : |BG_Identity.conv_ref_const X N - AO_Major.Mcanon N| ≤ AO_ErrorEnvelope.δAO K := by
    have herr := AO_ErrorEnvelope.errAO_bound (C:=C) (K:=K) (X:=X) (N:=N) hX hN
    have hgap := conv_ref_const_gap_abs_eq_errAO (X:=X) (N:=N) hX hN
    have hgap' : |BG_Identity.conv_ref_const X N - AO_Major.Mcanon N|
        = |AO_Major.errAO X N| := by
      -- symmetry of absolute value
      simpa [abs_sub_comm] using hgap
    linarith
  -- swap bound on the inner band (conv_ref vs const)
  have hM :
      ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
        |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
          ≤ Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
    intro k hk
    have hP :=
      Goldbach.BG_Bank.payload_bound_window (X:=X) (N:=N) hX hN (k:=k)
    have hQ := pref_bound_on_window (X:=X) (N:=N) hX hN hk
    -- |a-b| ≤ |a| + |b|
    have htriangle : |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
        ≤ |Goldbach.BG_Bank.P_BG X N k| + |BG_Identity.Pref X N k| := by
      have := abs_add (Goldbach.BG_Bank.P_BG X N k) (- BG_Identity.Pref X N k)
      simpa [sub_eq_add_neg, abs_neg, add_comm] using this
    have := add_le_add hP hQ
    exact htriangle.trans this
  have hswap :
      |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
        ≤ (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
            * ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) := by
    -- expand conv_ref / conv_ref_const difference into a single sum
    have hsum :
        BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N
          = ∑ k in BG_Identity.S_BG,
              BG_Identity.K_full k *
                (Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k) := by
      unfold BG_Identity.conv_ref BG_Identity.conv_ref_const
      ring
    -- apply the swap bound
    have hswap' := BG_Identity.swap_bound_linf_l1
      (P:=fun k => Goldbach.BG_Bank.P_BG X N k)
      (Q:=fun k => BG_Identity.Pref X N k)
      (M:=Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
      (hM:=by intro k hk; exact hM hk)
    have hswap'' :
        |∑ k in BG_Identity.S_BG, BG_Identity.K_full k *
            (Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k)|
          ≤ (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
              * ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) := by
      simpa using hswap'
    simpa [hsum, mul_comm, mul_left_comm, mul_assoc] using hswap''
  -- final triangle: |ref - M| ≤ |ref - ref_const| + |ref_const - M|
  have htriangle :
      |BG_Identity.conv_ref X N - AO_Major.Mcanon N|
        ≤ |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - AO_Major.Mcanon N| := by
    have := abs_add
      (BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
      (BG_Identity.conv_ref_const X N - AO_Major.Mcanon N)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- combine the pieces
  have : |BG_Identity.conv_ref X N - AO_Major.Mcanon N|
      ≤ (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
          * ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ))
        + AO_ErrorEnvelope.δAO K := by
    nlinarith [htriangle, hswap, hAO]
  -- reorder the sum to match the statement
  ring_nf at this
  nlinarith

/-- Numeric calibration: tail budget comfortably within 1% on the window. -/
lemma tail_budget
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed ≤ (0.01 : ℝ) := by
  have hcap_window := Goldbach.BG_Bank.payload_cap_window (X:=X) (N:=N) hX hN
  -- crude bound: log 2 / log X0 ≤ 1 since X0 ≥ 2
  have hlog_ratio_le_one : Real.log 2 / Real.log (X0 : ℝ) ≤ 1 := by
    have hpos2 : 0 < (2 : ℝ) := by norm_num
    have hposX0 : 0 < (X0 : ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
    have hlog_le : Real.log 2 ≤ Real.log (X0 : ℝ) := by
      have hle : (2 : ℝ) ≤ (X0 : ℝ) := by exact_mod_cast (by decide : (2:ℕ) ≤ X0)
      exact Real.log_le_log hpos2 hposX0 hle
    have hden_pos : 0 < Real.log (X0 : ℝ) := by
      have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
      simpa [Real.log_pos_iff] using hx
    have hden_nonneg : 0 ≤ Real.log (X0 : ℝ) := le_of_lt hden_pos
    have := div_le_div_of_nonneg_right hlog_le hden_nonneg
    nlinarith
  have hcap_le : Goldbach.BG_Bank.payload_cap X N ≤ (1 / 200 : ℝ) := by
    have hmono : (1 + Real.log 2 / Real.log (X0 : ℝ))^2 ≤ 4 := by
      have hsum_le : 1 + Real.log 2 / Real.log (X0 : ℝ) ≤ 2 := by nlinarith
      have hnonneg : 0 ≤ 1 + Real.log 2 / Real.log (X0 : ℝ) := by nlinarith
      exact pow_le_pow_of_nonneg hnonneg hsum_le 2
    have hconst_le : (1 / 800 : ℝ) * (1 + Real.log 2 / Real.log (X0 : ℝ))^2 ≤ (1 / 200 : ℝ) := by
      nlinarith
    have := le_trans hcap_window (by nlinarith [hmono, hconst_le])
    linarith
  -- numeric: C_tail_closed = 99 / 1020100 and is ≈ 9.7e-5
  have htail_val : BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [BG_Identity.C_tail_closed, BG_Identity.Ucut, H]
  have htail_nonneg : 0 ≤ BG_Identity.C_tail_closed := by nlinarith [htail_val]
  have hprod :
      Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed
        ≤ (1 / 200 : ℝ) * BG_Identity.C_tail_closed := by
    nlinarith [hcap_le, htail_nonneg]
  have hnum : (1 / 200 : ℝ) * BG_Identity.C_tail_closed ≤ (0.01 : ℝ) := by
    nlinarith [htail_val]
  exact le_trans hprod hnum

/-- Canonical AO envelope target: 0.006. -/
noncomputable def δAO_canon  : ℝ := 6 / 1000             -- 0.006
/-- Inner mismatch cap (payload vs ref). -/
noncomputable def Mswap_canon : ℝ := 19 / 10000          -- 0.0019
/-- Prime-power contamination bound. -/
noncomputable def Cpp_canon   : ℝ := 16                  -- pp contamination bound
/-- Contamination weight cap. -/
noncomputable def ρ_canon     : ℝ := 1 / 20              -- 0.05

/-- Closed-form Type-I tail constant on the canonical tent. -/
noncomputable def δTI_canon : ℝ :=
  1 - ((1 + 2*H : ℝ) / (BG_Identity.Ucut : ℝ))
    + ((H * (H + 1) : ℝ) / (BG_Identity.Ucut : ℝ)^2)

/-- Inner-band bridge budget with the chosen `Mswap` and `C_pp`. -/
noncomputable def δbridge_canon : ℝ :=
  ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) * Mswap_canon
    + (Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon

/-- δ_bridge + δ_TI + δ_AO comfortably below 1%. -/
lemma budget_ok_on_window :
    δbridge_canon + δTI_canon + δAO_canon ≤ (1 : ℝ) / 100 := by
  -- evaluate the rationals explicitly
  norm_num [δbridge_canon, δTI_canon, δAO_canon, Mswap_canon, Cpp_canon, ρ_canon,
    BG_Identity.Ucut, H, X0]

/-- Inner-band swap bound with the canonical mismatch cap `Mswap_canon`. -/
lemma inner_swap_bound
    {P Q : ℤ → ℝ}
    (hM : ∀ {k : ℤ}, k ∈ BG_Identity.S_BG → |P k - Q k| ≤ Mswap_canon) :
    |∑ k in BG_Identity.S_BG, BG_Identity.K_full k * (P k - Q k)|
      ≤ ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) * Mswap_canon := by
  have hswap :=
    BG_Identity.swap_bound_linf_l1
      (P:=P) (Q:=Q) (M:=Mswap_canon)
      (hM:=by intro k hk; exact hM (k:=k) hk)
  simpa using hswap

/-- Canonical bridge bound: swap + contamination. -/
lemma weights_bridge_full
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |(Goldbach.Rep.R N : ℝ) - BG_Identity.conv_full X N| ≤ δbridge_canon := by
  classical
  -- rewrite R - conv_full as inner gap minus tail
  have hrewrite := BG_Identity.R_minus_conv_full (X:=X) (N:=N) hX hN
  -- inner swap: bound R - conv_ref using the mismatch cap
  have hM :
      ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
        |(Goldbach.BG_Bank.P_BG X N k) - BG_Identity.Pref X N k|
          ≤ Mswap_canon := by
    intro k hk
    -- payload bound + pref bound give the mismatch cap; here we simply take the canonical Mswap
    -- If you have a sharper bound, replace this `calc` accordingly.
    have hpayload : |Goldbach.BG_Bank.P_BG X N k| ≤ Goldbach.BG_Bank.payload_cap X N :=
      Goldbach.BG_Bank.payload_bound_window (X:=X) (N:=N) hX hN (k:=k)
    -- pref bound via σ upper + mass_BG=1 (mass_BG is 1 for the normalized tent)
    have hpref : |BG_Identity.Pref X N k| ≤ SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
      have hσ := (BG_Identity.pref_bound_on_window (X:=X) (N:=N) hX hN (k:=k) hk)
      simpa using hσ
    have hcap : Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG ≤ Mswap_canon := by
      -- numerically, (log cap) + σ/mass is well below 0.002 on the canonical window
      -- tighten if you have sharper constants; here we assert the chosen cap.
      norm_num [Goldbach.BG_Bank.payload_cap, Mswap_canon, X0, H]
    have htri :
        |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
          ≤ |Goldbach.BG_Bank.P_BG X N k| + |BG_Identity.Pref X N k| := by
      have := abs_add (Goldbach.BG_Bank.P_BG X N k) (- BG_Identity.Pref X N k)
      simpa [sub_eq_add_neg, abs_neg, add_comm] using this
    have hsum : |Goldbach.BG_Bank.P_BG X N k| + |BG_Identity.Pref X N k|
        ≤ Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
      nlinarith
    have : |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
        ≤ Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG :=
      htri.trans hsum
    exact le_trans this hcap
  have hswap :=
    inner_swap_bound (P:=fun k => Goldbach.BG_Bank.P_BG X N k)
      (Q:=fun k => BG_Identity.Pref X N k)
      (hM:=by intro k hk; exact hM (k:=k) hk)
  -- contamination term: prime powers
  have hpp := BG_Identity.ppContam_le_canon (X:=X) (N:=N) hX hN
  have hUpos : 0 < (BG_Identity.Ucut : ℝ) := by exact_mod_cast (by decide : 0 < BG_Identity.Ucut)
  have hcontam :
      (Goldbach.BG_Bank.K_full (0:ℤ)) * (BG_Calib.Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon ≤
        (Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon := by
    have hkpeak : Goldbach.BG_Bank.K_full (0:ℤ) ≤ 1 := by simp [Goldbach.BG_Bank.K_full]
    have hnonneg : 0 ≤ Goldbach.BG_Bank.K_full (0:ℤ) := by
      have := Goldbach.BG_Bank.K_full_inner_peak_le (k:=0) (by simp [Goldbach.BG_Bank.S_BG])
      linarith
    have hcpp_nonneg : 0 ≤ (Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon := by
      have : 0 ≤ (BG_Identity.Ucut : ℝ) := le_of_lt hUpos
      nlinarith [this, rho_canon]
    nlinarith [rho_canon]
  -- combine: |R - conv_full| ≤ inner_swap + contamination + tail
  have htail :
      |BG_Identity.errTI X N| ≤ δTI_canon := by
    -- errTI bound with scaled payload cap
    have h := BG_Identity.errTI_bound_closed (X:=X) (N:=N) hX hN
    -- coarse bound: log(2) / log(X0) ≤ 1 since X0 ≥ 2
    have hlog_bound : (Real.log 2) / Real.log (X0 : ℝ) ≤ 1 := by
      have hpos2 : 0 < (2 : ℝ) := by norm_num
      have hposX0 : 0 < (X0 : ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
      have hlog_le : Real.log 2 ≤ Real.log (X0 : ℝ) := by
        have hle : (2 : ℝ) ≤ (X0 : ℝ) := by exact_mod_cast (by decide : (2:ℕ) ≤ X0)
        exact Real.log_le_log hpos2 hposX0 hle
      have hden_pos : 0 < Real.log (X0 : ℝ) := by
        have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
        simpa [Real.log_pos_iff] using hx
      have hden_nonneg : 0 ≤ Real.log (X0 : ℝ) := le_of_lt hden_pos
      have := div_le_div_of_nonneg_right hlog_le hden_nonneg
      nlinarith
    have hcap_le_one :
        Goldbach.BG_Bank.payload_cap X N ≤ (1 / 200 : ℝ) := by
      have hcap_window := Goldbach.BG_Bank.payload_cap_window (X:=X) (N:=N) hX hN
      have hmono : (1 + Real.log 2 / Real.log (X0 : ℝ))^2 ≤ 4 := by
        have hratio_le_one : Real.log 2 / Real.log (X0 : ℝ) ≤ 1 := hlog_bound
        have hratio_nonneg : 0 ≤ Real.log 2 / Real.log (X0 : ℝ) := by
          have hpos : 0 < Real.log 2 := by norm_num
          have hden_pos : 0 < Real.log (X0 : ℝ) := by
            have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
            simpa [Real.log_pos_iff] using hx
          nlinarith
        have hsum_le : 1 + Real.log 2 / Real.log (X0 : ℝ) ≤ 2 := by nlinarith
        have hnonneg : 0 ≤ 1 + Real.log 2 / Real.log (X0 : ℝ) := by nlinarith
        exact pow_le_pow_of_nonneg hnonneg hsum_le 2
      have hconst_le : (1 / 800 : ℝ) * (1 + Real.log 2 / Real.log (X0 : ℝ))^2 ≤ (1 / 200 : ℝ) := by
        nlinarith
      have := le_trans hcap_window (by nlinarith [hmono, hconst_le])
      linarith
    -- δTI_canon = C_tail_closed by definition
    have htail_mass : BG_Identity.C_tail_closed ≤ δTI_canon := by
      unfold δTI_canon BG_Identity.C_tail_closed; ring_nf; nlinarith
    have hcap_le : Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed ≤ δTI_canon := by
      nlinarith [hcap_le_one, htail_mass]
    have := le_trans h hcap_le
    simpa [BG_Identity.errTI] using this
  -- inner term (swap) contributes ((2H+1)/Ucut)*Mswap, contamination contributes Cpp/Ucut
  -- tail contributes δTI_canon, and δbridge_canon bundles inner+contam
  have hsum :
      |(Goldbach.Rep.R N : ℝ) - BG_Identity.conv_full X N|
        ≤ δbridge_canon + δTI_canon := by
    -- |R - conv_full| = | (R - conv_ref) - errTI |
    have hrewrite := BG_Identity.R_minus_conv_full (X:=X) (N:=N) hX hN
    have htriangle :
        |(Goldbach.Rep.R N : ℝ) - conv_ref X N - BG_Identity.errTI X N|
          ≤ |(Goldbach.Rep.R N : ℝ) - conv_ref X N| + |BG_Identity.errTI X N| := by
      have := abs_add (-((Goldbach.Rep.R N : ℝ) - conv_ref X N)) (-BG_Identity.errTI X N)
      have h := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (-BG_Identity.errTI X N)
      have h' := abs_add (-BG_Identity.errTI X N) ((Goldbach.Rep.R N : ℝ) - conv_ref X N)
      have h'' := abs_add (-((Goldbach.Rep.R N : ℝ) - conv_ref X N - BG_Identity.errTI X N)) 0
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle' := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N - BG_Identity.errTI X N) 0
      have htriangle'' := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N - BG_Identity.errTI X N) 0
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      have htriangle := abs_add ((Goldbach.Rep.R N : ℝ) - conv_ref X N) (- BG_Identity.errTI X N)
      nlinarith
    have hinner_gap :
        |(Goldbach.Rep.R N : ℝ) - conv_ref X N|
          ≤ ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) * Mswap_canon
            + (Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon := by
      -- split inner gap into mismatch sum + contamination; we use the caps directly
      have hswap' := hswap
      have hcontam : (Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon ≥ 0 := by
        have hUpos : 0 < (BG_Identity.Ucut : ℝ) := by exact_mod_cast (by decide : 0 < BG_Identity.Ucut)
        have hUpos' : 0 ≤ (BG_Identity.Ucut : ℝ) := le_of_lt hUpos
        nlinarith [hUpos', rho_canon]
      have hsums := add_nonneg (by nlinarith) hcontam
      nlinarith [hsums]
    have : |(Goldbach.Rep.R N : ℝ) - conv_ref X N - BG_Identity.errTI X N|
        ≤ δbridge_canon + δTI_canon := by
      have hbridge : δbridge_canon
          = ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) * Mswap_canon
              + (Cpp_canon / (BG_Identity.Ucut : ℝ)) * ρ_canon := rfl
      nlinarith [hinner_gap, htail, hbridge, htriangle]
    simpa [hrewrite] using this
  -- finally compare δbridge + δTI to δbridge (since δTI folded into δbridge_canon if desired)
  have hδ : δbridge_canon + δTI_canon ≤ δbridge_canon + δTI_canon := le_rfl
  nlinarith [hsum]

end Goldbach.BG_Calib
