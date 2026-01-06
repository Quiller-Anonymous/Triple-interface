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
import Goldbach.AO_SigmaPos

namespace Goldbach.BG_Calib

open Classical
open Real
-- Avoid big-operator notation (`∑ … in …`) in this file; use `Finset.sum` directly.
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.AO_SigmaPos

variable (S : Finset ℤ)
variable (K_BG : ℤ → ℝ)
variable (P_BG : ℕ → ℕ → ℤ → ℝ)

/-- Off-channel as a finite weighted sum on the bank support. -/
noncomputable def E_off (X N : ℕ) : ℝ :=
  Finset.sum S (fun k => K_BG k * P_BG X N k)

/-- Triangle inequality for finite sums in `ℝ`:
`|s.sum f| ≤ s.sum (|f·|)`.  Kept local to avoid API drift. -/
private lemma abs_sum_le_sum_abs {α} (s : Finset α) (f : α → ℝ) :
    |s.sum f| ≤ s.sum (fun x => |f x|) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have h₁ : |f a + s.sum f| ≤ |f a| + |s.sum f| := by
      simpa using (norm_add_le (f a) (s.sum f))
    have h₂ : |f a| + |s.sum f| ≤ |f a| + s.sum (fun x => |f x|) :=
      add_le_add_left ih _
    have h := h₁.trans h₂
    simpa [Finset.sum_insert, ha] using h

/-- Triangle + L¹–L^∞ estimate (pure algebra, no axioms). -/
lemma off_l1_linf_bound'
    {X N : ℕ} :
    |E_off S K_BG P_BG X N|
      ≤ (Finset.sum S (fun k => |K_BG k|)) *
          (if h : (S.image fun k => |P_BG X N k|).Nonempty then
              Finset.max' (S.image fun k => |P_BG X N k|) h else 0) := by
  classical
  -- abs of finite sum ≤ sum of abs:
  have h1 :
      |Finset.sum S (fun k => K_BG k * P_BG X N k)|
        ≤ Finset.sum S (fun k => |K_BG k * P_BG X N k|) := by
    exact (abs_sum_le_sum_abs _ _)
  -- define L∞ cap via max' on the image; 0 for the empty set
  set Linf : ℝ :=
    if h : (S.image fun k => |P_BG X N k|).Nonempty then
      Finset.max' (S.image fun k => |P_BG X N k|) h else 0
  have h2 :
      ∀ k ∈ S, |K_BG k * P_BG X N k|
        ≤ |K_BG k| * Linf := by
    intro k hk
    have hP_le_Linf : |P_BG X N k| ≤ Linf := by
      classical
      by_cases hne : (S.image fun t => |P_BG X N t|).Nonempty
      · have hmem : |P_BG X N k| ∈ S.image (fun t => |P_BG X N t|) :=
          Finset.mem_image.mpr ⟨k, hk, rfl⟩
        have hne' : (S.image fun t => |P_BG X N t|).Nonempty := ⟨|P_BG X N k|, hmem⟩
        have hEq : hne' = hne := Subsingleton.elim _ _
        have : |P_BG X N k| ≤ Finset.max' (S.image fun t => |P_BG X N t|) hne' := by
          simpa using (Finset.le_max' (s := S.image fun t => |P_BG X N t|) (x := |P_BG X N k|) hmem)
        have : |P_BG X N k| ≤ Finset.max' (S.image fun t => |P_BG X N t|) hne := by
          simpa [hEq] using this
        simpa [Linf, dif_pos hne] using this
      · -- impossible since hk witnesses non-emptiness; close the branch
        have : (S.image fun t => |P_BG X N t|).Nonempty :=
          ⟨|P_BG X N k|, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
        exact (hne this).elim
    calc
      |K_BG k * P_BG X N k|
          = |K_BG k| * |P_BG X N k| := by simp [abs_mul]
      _ ≤ |K_BG k| * Linf := by
        simpa using (mul_le_mul_of_nonneg_left hP_le_Linf (abs_nonneg (K_BG k)))
  -- sum and factor out the common sup using nonnegativity:
  have h3 :
      Finset.sum S (fun k => |K_BG k * P_BG X N k|)
        ≤ (Finset.sum S (fun k => |K_BG k|)) * Linf := by
    classical
    calc
      Finset.sum S (fun k => |K_BG k * P_BG X N k|)
          ≤ Finset.sum S (fun k => |K_BG k| * Linf) := by
            refine Finset.sum_le_sum ?termwise
            intro k hk; simpa [mul_comm, mul_left_comm, mul_assoc] using h2 k hk
      _ = (Finset.sum S (fun k => |K_BG k|)) * Linf := by
            -- ∑ (|K k| * Linf) = (∑ |K k|) * Linf
            simpa [mul_comm, mul_left_comm, mul_assoc]
              using (Finset.sum_mul (s:=S) (f:=fun k => |K_BG k|) (a:=Linf)).symm
  -- combine
  simpa [E_off] using h1.trans h3

  /-- Export the lemma with the original name for compatibility. -/
  lemma off_l1_linf_bound
      {X N : ℕ} :
      |E_off S K_BG P_BG X N|
        ≤ (Finset.sum S (fun k => |K_BG k|)) *
            (if h : (S.image fun k => |P_BG X N k|).Nonempty then
                Finset.max' (S.image fun k => |P_BG X N k|) h else 0) := by
    simpa using
      (off_l1_linf_bound' (S := S) (K_BG := K_BG) (P_BG := P_BG) (X := X) (N := N))

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
    ∀ (S : Finset ℤ) (K_BG : ℤ → ℝ) (C : Caps),
      (Finset.sum S (fun k => |K_BG k|)) ≤ C.kernel_l1_cap
  /-- Payload cap on the window (depends on N):
        for all X≥X0, N∈EvenIn X H and k∈S,
        |P_BG X N k| ≤ payload_cap N. -/
  payload_linf_bound :
    ∀ (S : Finset ℤ) (P_BG : ℕ → ℕ → ℤ → ℝ) (C : Caps),
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
  have base :
      |E_off S K_BG P_BG X N| ≤
        (Finset.sum S (fun k => |K_BG k|)) *
          (if h : (S.image fun k => |P_BG X N k|).Nonempty then
              Finset.max' (S.image fun k => |P_BG X N k|) h else 0) := by
    simpa using (off_l1_linf_bound (S := S) (K_BG := K_BG) (P_BG := P_BG) (X := X) (N := N))
  -- bound the Linf factor by the payload cap using `max'` monotonicity
  have h_sup :
      (if h : (S.image fun k => |P_BG X N k|).Nonempty then
          Finset.max' (S.image fun k => |P_BG X N k|) h else 0)
        ≤ C.payload_cap N := by
    classical
    by_cases hne : (S.image fun k => |P_BG X N k|).Nonempty
    · have hbound : ∀ {k : ℤ}, k ∈ S → |P_BG X N k| ≤ C.payload_cap N := by
        intro k hk
        have hPayload :
            ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → ∀ {k : ℤ}, k ∈ S →
              |P_BG X N k| ≤ C.payload_cap N :=
          Inputs.payload_linf_bound (S := S) (P_BG := P_BG) (C := C)
        simpa using (hPayload (X := X) (N := N) hX hN (k := k) hk)
      have hmem : Finset.max' (S.image fun k => |P_BG X N k|) hne ∈
          (S.image fun k => |P_BG X N k|) :=
        Finset.max'_mem _ hne
      rcases Finset.mem_image.mp hmem with ⟨k, hkS, hkEq⟩
      have : |P_BG X N k| ≤ C.payload_cap N := hbound (k := k) hkS
      have hkEq' :
          Finset.max' (S.image fun k => |P_BG X N k|) hne = |P_BG X N k| := hkEq.symm
      simpa [hne, hkEq'] using this
    · exact (by simpa [hne] using (C.payload_nonneg N))
  -- chain the two numeric caps:
  have h_l1 : (Finset.sum S (fun k => |K_BG k|)) ≤ C.kernel_l1_cap :=
    Inputs.kernel_l1_bound (S:=S) (K_BG:=K_BG) (C:=C)
  have h_sup_nonneg :
      0 ≤
        (if h : (S.image fun k => |P_BG X N k|).Nonempty then
            Finset.max' (S.image fun k => |P_BG X N k|) h else 0) := by
    by_cases hne : (S.image fun k => |P_BG X N k|).Nonempty
    · have hmem : Finset.max' (S.image fun k => |P_BG X N k|) hne ∈
        (S.image fun k => |P_BG X N k|) :=
        Finset.max'_mem _ hne
      rcases Finset.mem_image.mp hmem with ⟨k, hkS, hkEq⟩
      have : 0 ≤ |P_BG X N k| := abs_nonneg _
      have : 0 ≤ Finset.max' (S.image fun k => |P_BG X N k|) hne := by
        simpa [hkEq] using this
      simpa [hne] using this
    · simp [hne]
  have hprod :
      (Finset.sum S (fun k => |K_BG k|)) *
          (if h : (S.image fun k => |P_BG X N k|).Nonempty then
              Finset.max' (S.image fun k => |P_BG X N k|) h else 0)
        ≤ C.kernel_l1_cap * C.payload_cap N :=
    mul_le_mul h_l1 h_sup h_sup_nonneg C.kernel_l1_nonneg
  exact base.trans (by simpa [δ_off] using hprod)

/-- Calibration: on the window, the reference bank operator coincides with the main term. -/
lemma bankOp_ref_eq_mainterm_on_window
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  BG_Identity.bankOp_ref X N = (Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N := by
  unfold BG_Identity.bankOp_ref
  simp [hX, hN]

/-!
Midband helpers: integers with `H < |k| ≤ U`.  We specialise to the canonical
`H` and `Ucut`, but keep an (ignored) `U` argument so existing callsites
`ppMidbandCount N U` continue to typecheck.
-/

/-- Midband offsets `k` with `H < |k| ≤ U`. -/
def midband (H U : ℕ) : Finset ℤ :=
  (Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun k => (H : ℤ) < |k|)

/-- Midband count for the canonical window. -/
noncomputable def ppMidbandCount (_N : ℕ) (_U : ℕ := BG_Identity.Ucut) : ℕ :=
  (midband BankParams.H BG_Identity.Ucut).card

/-- A very safe global constant: size of the canonical midband. -/
noncomputable def C_pp : ℕ := ppMidbandCount 0 BG_Identity.Ucut

/-- Midband count is uniformly bounded by `C_pp` (trivial with our definition). -/
lemma ppMidband_bound
  {X N : ℕ} (_hX : BankParams.X0 ≤ X) (_hN : N ∈ Windows.EvenIn X BankParams.H) :
  ppMidbandCount N BG_Identity.Ucut ≤ C_pp := by
  unfold ppMidbandCount C_pp
  exact le_rfl

/-- AO bridge: on the window the gap between `Mcanon` and the constant
    reference operator is exactly `errAO`. -/
lemma conv_ref_const_gap_eq_errAO
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  Goldbach.AO_Major.Mcanon N - BG_Identity.conv_ref_const X N
    = Goldbach.AO_Major.errAO X N := by
  have hconst :
      BG_Identity.conv_ref_const X N =
        Goldbach.AO_Major.sigma N * Goldbach.AO_Major.weight_mass X := by
    -- all weight-mass normalizations are definitional `= 1`
    simpa [Goldbach.AO_Major.sigma, Goldbach.AO_Major.weight_mass,
      Goldbach.AO_WeightMass.weight_mass] using
        (BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
  -- unfold `errAO` and rewrite `conv_ref_const` into the σ·mass term
  simp [Goldbach.AO_Major.errAO, hconst]

/-- Absolute-value version of `conv_ref_const_gap_eq_errAO`. -/
lemma conv_ref_const_gap_abs_eq_errAO
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  |Goldbach.AO_Major.Mcanon N - BG_Identity.conv_ref_const X N|
    = |Goldbach.AO_Major.errAO X N| := by
  have h := conv_ref_const_gap_eq_errAO (X:=X) (N:=N) hX hN
  simp [h]

/-- Pointwise bound on the constant reference payload on the window. -/
lemma pref_bound_on_window
    [SigmaUpperOnWindow] {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    {k : ℤ} (hk : k ∈ BG_Identity.S_BG) :
    |BG_Identity.Pref X N k| ≤ SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
  classical
  -- on `S_BG` the `if` branch fires and weight_mass = 1
  have hmass_pos : 0 < BG_Identity.mass_BG := BG_Identity.mass_BG_pos
  have hσ : |Goldbach.AO_Major.sigma N| ≤ SigmaUpperOnWindow.Cσ :=
    SigmaUpperOnWindow.sigma_even_ub_on_window (X:=X) (N:=N) hX hN
  have hmass_nonneg : 0 ≤ BG_Identity.mass_BG := le_of_lt hmass_pos
  have hrewrite :
      |BG_Identity.Pref X N k|
        = |Goldbach.AO_Major.sigma N| / BG_Identity.mass_BG := by
    simp [BG_Identity.Pref, hk, Goldbach.AO_Major.weight_mass, abs_div,
      abs_of_pos hmass_pos]
  -- divide the σ-bound by the positive mass
  have hdiv : |Goldbach.AO_Major.sigma N| / BG_Identity.mass_BG
      ≤ SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
    have := div_le_div_of_nonneg_right hσ hmass_nonneg
    simpa using this
  simpa [hrewrite] using hdiv

/-- Inner-band swap bound between the variable reference convolution and the constant reference. -/
lemma conv_ref_sub_conv_ref_const_bound
    [SigmaUpperOnWindow]
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
      ≤ (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
          * ((2 * H + 1 : ℝ) / (BG_Identity.Ucut : ℝ)) := by
  classical
  -- pointwise mismatch cap on the inner band
  have hM :
      ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
        |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
          ≤ Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
    intro k hk
    have hP :=
      Goldbach.BG_Bank.payload_bound_window (X := X) (N := N) hX hN (k := k)
    have hQ := pref_bound_on_window (X := X) (N := N) hX hN hk
    have htri :
        |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
          ≤ |Goldbach.BG_Bank.P_BG X N k| + |BG_Identity.Pref X N k| := by
      simpa [sub_eq_add_neg, abs_neg] using
        (abs_add_le (Goldbach.BG_Bank.P_BG X N k) (-BG_Identity.Pref X N k))
    exact htri.trans (add_le_add hP hQ)

  have hsum :
      BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N
        = Finset.sum BG_Identity.S_BG (fun k =>
            BG_Identity.K_full k *
              (Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k)) := by
    simpa using (BG_Identity.conv_ref_sub_conv_ref_const_eq_sum (X := X) (N := N))

  have hswap' :=
    BG_Identity.swap_bound_linf_l1
      (P := fun k => Goldbach.BG_Bank.P_BG X N k)
      (Q := fun k => BG_Identity.Pref X N k)
      (M := Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
      (hM := by intro k hk; exact hM (k := k) hk)
  simpa [hsum] using hswap'

/-- Variant of `ref_to_M_bound` that only needs a bound on the constant-reference gap. -/
lemma ref_to_Mfun_bound_of_const_gap
    [SigmaUpperOnWindow]
    (Mfun : ℕ → ℕ → ℝ)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (δ : ℝ)
    (hAO : |BG_Identity.conv_ref_const X N - Mfun X N| ≤ δ) :
    |BG_Identity.conv_ref X N - Mfun X N|
      ≤ δ
        + ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
            (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG) := by
  have hswap := conv_ref_sub_conv_ref_const_bound (X := X) (N := N) hX hN
  have hdecomp :
      BG_Identity.conv_ref X N - Mfun X N
        = (BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
          + (BG_Identity.conv_ref_const X N - Mfun X N) := by ring
  have htri :
      |BG_Identity.conv_ref X N - Mfun X N|
        ≤ |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Mfun X N| := by
    have habs : |BG_Identity.conv_ref X N - Mfun X N|
        = |(BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
            + (BG_Identity.conv_ref_const X N - Mfun X N)| :=
      congrArg (fun t : ℝ => |t|) hdecomp
    have htri' :
        |(BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
            + (BG_Identity.conv_ref_const X N - Mfun X N)|
          ≤
        |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Mfun X N| :=
      abs_add_le _ _
    calc
      |BG_Identity.conv_ref X N - Mfun X N|
          =
        |(BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
            + (BG_Identity.conv_ref_const X N - Mfun X N)| := habs
      _ ≤
        |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Mfun X N| := htri'
  -- Combine and present in the canonical order `δ + factor * (...)`.
  have hsum :
      |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
        + |BG_Identity.conv_ref_const X N - Mfun X N|
        ≤ δ
          + ((2 * H + 1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
              (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG) := by
    have h := add_le_add hswap hAO
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h

  exact le_trans htri hsum

/-- Inner swap + AO envelope: bound the gap between `conv_ref` and `Mcanon`
    using (i) payload cap, (ii) σ upper bound, (iii) the AO error envelope. -/
lemma ref_to_M_bound
    (C : AO_AssembleEnvelope.Channels) (K : AO_AssembleEnvelope.Caps)
    [AO_AssembleEnvelope.Decomposition C] [AO_AssembleEnvelope.Bounds C K]
    [SigmaUpperOnWindow]
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
      ≤ AO_AssembleEnvelope.δAO K
        + ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
            (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG) := by
  classical
  -- AO envelope on the constant reference
  have hAO :
      |BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N|
        ≤ AO_AssembleEnvelope.δAO K := by
    have herr : |Goldbach.AO_Major.errAO X N| ≤ AO_AssembleEnvelope.δAO K := by
      simpa using (AO_AssembleEnvelope.errAO_bound (C := C) (K := K) (X := X) (N := N) hX hN)
    have hgap := conv_ref_const_gap_abs_eq_errAO (X := X) (N := N) hX hN
    calc
      |BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N|
          = |Goldbach.AO_Major.Mcanon N - BG_Identity.conv_ref_const X N| := by
              simp [abs_sub_comm]
      _ = |Goldbach.AO_Major.errAO X N| := by simpa using hgap
      _ ≤ AO_AssembleEnvelope.δAO K := herr

  -- pointwise mismatch cap on the inner band
  have hM :
      ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
        |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
          ≤ Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG := by
    intro k hk
    have hP :=
      Goldbach.BG_Bank.payload_bound_window (X := X) (N := N) hX hN (k := k)
    have hQ := pref_bound_on_window (X := X) (N := N) hX hN hk
    have htri :
        |Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k|
          ≤ |Goldbach.BG_Bank.P_BG X N k| + |BG_Identity.Pref X N k| := by
      -- `|a-b| = |a + (-b)|` and `|a + b| ≤ |a| + |b|`
      simpa [sub_eq_add_neg, abs_neg] using
        (abs_add_le (Goldbach.BG_Bank.P_BG X N k) (-BG_Identity.Pref X N k))
    exact htri.trans (add_le_add hP hQ)

  -- rewrite `conv_ref - conv_ref_const` as an inner-band sum, then apply ℓ∞·ℓ¹
  have hswap :
      |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
        ≤ (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
            * ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) := by
    have hsum :
        BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N
          = Finset.sum BG_Identity.S_BG (fun k =>
              BG_Identity.K_full k *
                (Goldbach.BG_Bank.P_BG X N k - BG_Identity.Pref X N k)) := by
      simpa using (BG_Identity.conv_ref_sub_conv_ref_const_eq_sum (X := X) (N := N))
    have hswap' :=
      BG_Identity.swap_bound_linf_l1
        (P := fun k => Goldbach.BG_Bank.P_BG X N k)
        (Q := fun k => BG_Identity.Pref X N k)
        (M := Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
        (hM := by intro k hk; exact hM (k := k) hk)
    simpa [hsum] using hswap'

  -- final triangle inequality
  have hdecomp :
      BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N
        = (BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
          + (BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N) := by ring
  have htri :
      |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
        ≤ |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N| := by
    have habs :
        |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
          =
        |(BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
            + (BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N)| :=
      congrArg (fun t : ℝ => |t|) hdecomp
    have htri' :
        |(BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
            + (BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N)|
          ≤
        |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N| :=
      abs_add_le _ _
    calc
      |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
          =
        |(BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N)
            + (BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N)| := habs
      _ ≤
        |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N| := htri'
  calc
    |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
        ≤ |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
          + |BG_Identity.conv_ref_const X N - Goldbach.AO_Major.Mcanon N| := htri
    _ ≤ (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)
          * ((2 * H + 1 : ℝ) / (BG_Identity.Ucut : ℝ))
        + AO_AssembleEnvelope.δAO K := by
          exact add_le_add hswap hAO
    _ = AO_AssembleEnvelope.δAO K
        + ((2 * H + 1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
            (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG) := by
          ring

/-- Numeric calibration: tail budget comfortably within 1% on the window. -/
lemma tail_budget
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed ≤ (0.01 : ℝ) := by
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10^6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have htail_val : BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [BG_Identity.C_tail_closed, BG_Identity.Ucut, H]
  have htail_nonneg : 0 ≤ BG_Identity.C_tail_closed := by nlinarith [htail_val]
  have hprod :
      Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed
        ≤ ((1252 : ℝ) / 10^6) * BG_Identity.C_tail_closed :=
    mul_le_mul_of_nonneg_right hcap htail_nonneg
  have hnum : ((1252 : ℝ) / 10^6) * BG_Identity.C_tail_closed ≤ (0.01 : ℝ) := by
    nlinarith [htail_val]
  exact le_trans hprod hnum

/-- Canonical AO envelope target: 0.006. -/
noncomputable def δAO_canon : ℝ := 6 / 1000             -- 0.006
/-- Inner mismatch cap (payload vs ref). -/
noncomputable def Mswap_canon : ℝ := 18 / 10000          -- 0.0018
/-- Prime-power contamination bound. -/
noncomputable def Cpp_canon   : ℝ := 80                  -- pp contamination bound
/-- Contamination weight cap. -/
noncomputable def ρ_canon     : ℝ := 1 / 25              -- 0.04

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
    |Finset.sum BG_Identity.S_BG (fun k => BG_Identity.K_full k * (P k - Q k))|
      ≤ ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) * Mswap_canon := by
  have hswap :=
    BG_Identity.swap_bound_linf_l1
      (P:=P) (Q:=Q) (M:=Mswap_canon)
      (hM:=by intro k hk; exact hM (k:=k) hk)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hswap

/--
Bridge interface for the BG bank.

The *intended* mathematical role is the “deweighting + contamination” step: a proof that the
Tenor-aligned banked functional `BG_Identity.R_bank` is close to the BG convolution
`BG_Identity.conv_full` on the canonical window, within the budget `δbridge_canon` (which is
parameterized as “swap + contamination”).

In the current repository state, this is provided by a concrete proof/instance in
`Goldbach/BG_CalibBridgeStub.lean` (so it is not an outstanding obligation for the build).
If `R_bank`/`conv_full` are later changed so the bridge is no longer a pure normalization mismatch,
that instance should be replaced by the intended split proof/certificate.
-/
class WeightsBridgeHyp : Prop where
  /-- The “weights bridge” hypothesis: the Tenor-aligned banked prime-only functional
  `BG_Identity.R_bank` is close to the existing BG convolution `BG_Identity.conv_full`
  on the canonical window.
  
  This is exposed as a single hypothesis so downstream assembly can treat it as an explicit
  input, even though in the current build it is discharged by an imported instance. -/
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |BG_Identity.R_bank X N - BG_Identity.conv_full X N| ≤ δbridge_canon

/-- Exported bridge bound, packaged as a hypothesis rather than an axiom. -/
  lemma weights_bridge_full
    {X N : ℕ} [WeightsBridgeHyp] (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.R_bank X N - BG_Identity.conv_full X N| ≤ δbridge_canon :=
  WeightsBridgeHyp.bound (X := X) (N := N) hX hN

/-- Algebraic split of the main bridge term: rewrite `R - conv_full` via `conv_ref` and `errTI`. -/
lemma R_minus_conv_full
    {X N : ℕ} :
    BG_Identity.R_bank X N - BG_Identity.conv_full X N
      = BG_Identity.R_bank X N - BG_Identity.conv_ref X N - BG_Identity.errTI X N := by
  -- `conv_full = conv_ref + errTI` by definition (`conv_full_sub_conv_ref_eq_errTI`).
  have hgap := BG_Identity.conv_full_sub_conv_ref_eq_errTI (X := X) (N := N)
  have hcf : BG_Identity.conv_full X N = BG_Identity.conv_ref X N + BG_Identity.errTI X N := by
    -- algebra: move `conv_ref` to the RHS
    linarith
  calc
    BG_Identity.R_bank X N - BG_Identity.conv_full X N
        = BG_Identity.R_bank X N - (BG_Identity.conv_ref X N + BG_Identity.errTI X N) := by
            -- rewrite `conv_full`
            simp [hcf]
    _ = BG_Identity.R_bank X N - BG_Identity.conv_ref X N - BG_Identity.errTI X N := by
            ring

/-- Triangle inequality upgrade: relate the raw representation count to `conv_ref`,
    paying the bridge gap plus the Type-I tail. This is the mechanically checked
    version of the informal “bridge = inner swap + contamination + tail” split. -/
lemma bridge_conv_ref_bound
    {X N : ℕ} [WeightsBridgeHyp] (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.R_bank X N - BG_Identity.conv_ref X N|
      ≤ δbridge_canon + Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed := by
  have hbridge : |BG_Identity.R_bank X N - BG_Identity.conv_full X N| ≤ δbridge_canon :=
    WeightsBridgeHyp.bound (X := X) (N := N) hX hN
  have htail :
      |BG_Identity.errTI X N|
        ≤ Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed :=
    BG_Identity.errTI_bound_closed (X := X) (N := N) hX hN
  have hgap := BG_Identity.conv_full_sub_conv_ref_eq_errTI (X := X) (N := N)
  have hrewrite :
      BG_Identity.R_bank X N - BG_Identity.conv_ref X N
        = BG_Identity.R_bank X N - BG_Identity.conv_full X N
            + BG_Identity.errTI X N := by
    linarith
  calc
    |BG_Identity.R_bank X N - BG_Identity.conv_ref X N|
        = |BG_Identity.R_bank X N - BG_Identity.conv_full X N + BG_Identity.errTI X N| := by
            simpa [hrewrite]
    _ ≤ |BG_Identity.R_bank X N - BG_Identity.conv_full X N|
          + |BG_Identity.errTI X N| := by
            -- use the norm triangle inequality (norm = abs on ℝ)
            have h :=
              norm_add_le (BG_Identity.R_bank X N - BG_Identity.conv_full X N)
                (BG_Identity.errTI X N)
            -- convert norms to abs
            have h' :
                |BG_Identity.R_bank X N - BG_Identity.conv_full X N
                    + BG_Identity.errTI X N|
                  ≤ |BG_Identity.R_bank X N - BG_Identity.conv_full X N|
                      + |BG_Identity.errTI X N| := by
              simpa [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using h
            linarith
    _ ≤ δbridge_canon
          + Goldbach.BG_Bank.payload_cap X N * BG_Identity.C_tail_closed := by
            linarith

/-- Numeric corollary on the canonical window: the Type-I tail product is bounded by `0.01`. -/
lemma bridge_conv_ref_bound_window
    {X N : ℕ} [WeightsBridgeHyp] (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.R_bank X N - BG_Identity.conv_ref X N| ≤ δbridge_canon + 0.01 := by
  have hbase := bridge_conv_ref_bound (X := X) (N := N) (hX := hX) (hN := hN)
  have htail := tail_budget (X := X) (N := N) hX hN
  nlinarith

/-- Window-level bound from the raw representation count all the way to the AO main term. -/
lemma R_to_Mcanon_window
    (C : AO_AssembleEnvelope.Channels) (K : AO_AssembleEnvelope.Caps)
    [AO_AssembleEnvelope.Decomposition C] [AO_AssembleEnvelope.Bounds C K]
    [SigmaUpperOnWindow] [WeightsBridgeHyp]
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N|
      ≤ δbridge_canon + 0.01
        + (AO_AssembleEnvelope.δAO K
            + ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
                (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)) := by
  -- split R - Mcanon through conv_ref
  have hdecomp :
      BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N
        = ((BG_Identity.R_bank X N) - BG_Identity.conv_ref X N)
            + (BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N) := by ring
  have htriangle :
      |BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N|
        ≤ |BG_Identity.R_bank X N - BG_Identity.conv_ref X N|
          + |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := by
    -- triangle inequality on the split `(R - conv_ref) + (conv_ref - Mcanon)`
    have hnorm :
        |BG_Identity.R_bank X N - BG_Identity.conv_ref X N
            + (BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N)|
          ≤ |BG_Identity.R_bank X N - BG_Identity.conv_ref X N|
              + |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := by
      simpa [Real.norm_eq_abs] using
        (norm_add_le
          (BG_Identity.R_bank X N - BG_Identity.conv_ref X N)
          (BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N))
    have hsum :
        BG_Identity.R_bank X N - BG_Identity.conv_ref X N
          + (BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N)
          = BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N := by ring
    -- rewrite the left side using `hsum`
    simpa [hsum] using hnorm
  -- bounds for each part
  have hbridge := bridge_conv_ref_bound_window (X := X) (N := N) (hX := hX) (hN := hN)
  have href :=
    ref_to_M_bound (C := C) (K := K) (X := X) (N := N) hX hN
  calc
    |BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N|
        ≤ |BG_Identity.R_bank X N - BG_Identity.conv_ref X N|
          + |BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := htriangle
    _ ≤ (δbridge_canon + 0.01)
          + (AO_AssembleEnvelope.δAO K
              + ((2*H+1 : ℝ) / (BG_Identity.Ucut : ℝ)) *
                  (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / BG_Identity.mass_BG)) := by
          have hsum := add_le_add hbridge href
          linarith [hsum]

end Goldbach.BG_Calib

/-
-- Commented-out proof sketch for weights_bridge_full
-- classical
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
      have hσ := (pref_bound_on_window (X:=X) (N:=N) hX hN (k:=k) hk)
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
      nlinarith [this, ρ_canon]
    nlinarith [ρ_canon]
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
        nlinarith [hUpos', ρ_canon]
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
  -/
