import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.BG_Calib
import Goldbach.ParallelTenorFunX

/-!
Scratchpad: a repo-faithful “contract” around the FunX major-arc objects.

This file is intentionally low-tech: it only records bounds that follow from the *current*
discrete definitions (`K_full`, `P_BG`, `payload_cap`, …) and does **not** use any analytic
number theory (Siegel–Walfisz, major-arc asymptotics, certificates, …).

It is meant to be a safe place to:
- pin the exact normalization/mass factors that are already provable in Lean, and
- surface what can (and cannot) be discharged from the existing combinatorial inequalities.
-/

namespace Goldbach.Cert
namespace MajorArcContractScratch

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

/-!
## A clean, unconditional upper bound for `RΛ_smooth`

On the canonical window, we can bound `RΛ_smooth` purely from:
- the per-offset cap `|P_BG| ≤ payload_cap`, and
- the ℓ¹ mass bound on `K_full` over `S_BG`.
-/

lemma abs_conv_ref_le_payload_cap_mul_l1
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref X N|
      ≤ Goldbach.BG_Bank.payload_cap X N
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
  classical
  have href :
      Goldbach.BG_Identity.conv_ref X N =
        Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
          Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.K_full k) :=
    Goldbach.BG_Identity.conv_ref_eq_sum_S_BG (X := X) (N := N)

  have hCap :
      ∀ k ∈ Goldbach.BG_Identity.S_BG,
        |Goldbach.BG_Bank.P_BG X N k| ≤ Goldbach.BG_Bank.payload_cap X N := by
    intro k _hk
    exact Goldbach.BG_Bank.payload_bound_window (X := X) (N := N) hX hN (k := k)

  have hsum :=
    Goldbach.BG_Identity.abs_sum_mul_le_cap_sum_abs
      (s := Goldbach.BG_Identity.S_BG)
      (a := fun k : ℤ => Goldbach.BG_Bank.P_BG X N k)
      (b := fun k : ℤ => Goldbach.BG_Identity.K_full k)
      (C := Goldbach.BG_Bank.payload_cap X N)
      hCap

  have hL1 :
      Finset.sum Goldbach.BG_Identity.S_BG (fun k => |Goldbach.BG_Identity.K_full k|)
        ≤ (2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) :=
    Goldbach.BG_Identity.sum_abs_K_full_inner_le

  have hcap_nonneg : 0 ≤ Goldbach.BG_Bank.payload_cap X N :=
    Goldbach.BG_Bank.payload_nonneg X N

  have hmul :
      Goldbach.BG_Bank.payload_cap X N
            * Finset.sum Goldbach.BG_Identity.S_BG (fun k => |Goldbach.BG_Identity.K_full k|)
        ≤ Goldbach.BG_Bank.payload_cap X N
            * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) :=
    mul_le_mul_of_nonneg_left hL1 hcap_nonneg

  -- rewrite `conv_ref` and finish
  simpa [href] using le_trans hsum hmul

lemma abs_RΛ_smooth_le_payload_cap_mul_l1
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N|
      ≤ Goldbach.BG_Bank.payload_cap X N
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
  have href :
      Goldbach.BG_Identity.conv_ref X N =
        Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N := by
    simpa using (Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth (X := X) (N := N))
  -- swap sides to use the previous lemma
  have h := abs_conv_ref_le_payload_cap_mul_l1 (X := X) (N := N) hX hN
  simpa [href] using h

/-!
## A window-uniform bound by the *canonical* major-arc cap

This shows: irrespective of any σ-model, the current `RΛ_smooth` is already bounded above by
the same numeric cap `δ_major_canon` used elsewhere in the project (because `payload_cap` is
numerically dominated by `Mswap_canon` on the window).
-/

lemma payload_cap_le_Mswap_canon_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.BG_Bank.payload_cap X N ≤ Goldbach.BG_Calib.Mswap_canon := by
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have hnum : (1252 : ℝ) / 10 ^ 6 ≤ Goldbach.BG_Calib.Mswap_canon := by
    -- `Mswap_canon = 18/10000 = 0.0018`
    norm_num [Goldbach.BG_Calib.Mswap_canon]
  exact le_trans hcap hnum

lemma abs_RΛ_smooth_le_δ_major_canon
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N|
      ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  have hRL := abs_RΛ_smooth_le_payload_cap_mul_l1 (X := X) (N := N) hX hN
  have hcap_le : Goldbach.BG_Bank.payload_cap X N ≤ Goldbach.BG_Calib.Mswap_canon :=
    payload_cap_le_Mswap_canon_on_window (X := X) (N := N) hX hN
  have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    positivity
  have hmul :
      Goldbach.BG_Bank.payload_cap X N
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
        ≤ Goldbach.BG_Calib.Mswap_canon
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) :=
    mul_le_mul_of_nonneg_right hcap_le hratio_nonneg
  have hδ :
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon =
        Goldbach.BG_Calib.Mswap_canon
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    -- `δ_major_canon` is defined as `((2H+1)/Ucut) * Mswap_canon`
    simp [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon, mul_comm]
  exact le_trans hRL (by simpa [hδ] using hmul)

/-!
## Sanity check: the *current* σ-model makes `InnerSwapOnWindow` unattainable

This is a purely definitional/numeric diagnostic: with
`Goldbach.AO_SigmaModel.sigma ≡ 0.05` and the present normalization of `conv_ref`,
the swap bound
`|conv_ref - conv_ref_const| ≤ δ_major_canon` cannot hold on the window.

This is **not** used by the pipeline; it’s here to prevent us from “chasing” a dead end.
-/

private lemma X0_even : Goldbach.Windows.IsEven X0 := by
  -- `X0 = 10^6`.
  simp [Goldbach.Windows.IsEven, Goldbach.BankParams.X0, X0]

private lemma X0_mem_EvenIn : X0 ∈ EvenIn X0 H :=
  Goldbach.Windows.mem_EvenIn_self (N := X0) (H := H) X0_even

private lemma conv_ref_const_eq_005 (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref_const X N = (0.05 : ℝ) := by
  -- `conv_ref_const = sigma * weight_mass` and `sigma ≡ sigma0 = 0.05`, `weight_mass = 1`.
  have := Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N)
  -- keep rewriting explicit to avoid simp loops
  simpa [Goldbach.AO_WeightMass.weight_mass, Goldbach.AO_SigmaModel.sigma,
    Goldbach.AO_SigmaModel.sigma0, Goldbach.AO_SigmaModel.c0, Goldbach.AO_SigmaModel.sigma_caps,
    Goldbach.AO_AssembleEnvelope.δAO] using this

private lemma abs_conv_ref_le_payload_cap_mul_inner_l1
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref X N|
      ≤ Goldbach.BG_Bank.payload_cap X N
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
  -- This is exactly `abs_conv_ref_le_payload_cap_mul_l1`.
  simpa using abs_conv_ref_le_payload_cap_mul_l1 (X := X) (N := N) hX hN

lemma not_innerSwapOnWindow_current_sigma_model :
    ¬ Goldbach.ParallelTenorFunX.InnerSwapOnWindow := by
  intro h
  -- Use the window point `(X,N) = (X0, X0)`.
  have hX : X0 ≤ X0 := le_rfl
  have hN : X0 ∈ EvenIn X0 H := X0_mem_EvenIn

  have hswap :=
    Goldbach.ParallelTenorFunX.InnerSwapOnWindow.bound (X := X0) (N := X0) hX hN

  -- Upper bound `|conv_ref|` by a uniform numeric expression.
  have hcap :
      Goldbach.BG_Bank.payload_cap X0 X0 ≤ (1252 : ℝ) / 10 ^ 6 := by
    simpa [Goldbach.BG_Bank.X0, Goldbach.BG_Bank.H] using
      (Goldbach.BG_Bank.payload_cap_window_num (X := X0) (N := X0) hX hN)

  have hconv :
      |Goldbach.BG_Identity.conv_ref X0 X0|
        ≤ ((1252 : ℝ) / 10 ^ 6) * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    have h0 :=
      abs_conv_ref_le_payload_cap_mul_inner_l1 (X := X0) (N := X0) hX hN
    have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      positivity
    -- multiply the payload cap bound through
    have :=
      mul_le_mul_of_nonneg_right hcap hratio_nonneg
    -- rewrite `a * b ≤ c * b` into the target
    nlinarith [h0, this]

  -- Lower bound `|conv_ref - conv_ref_const|` using the reverse triangle inequality.
  have htri :
      |Goldbach.BG_Identity.conv_ref_const X0 X0|
        ≤ |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0|
            + |Goldbach.BG_Identity.conv_ref X0 X0| := by
    -- `conv_ref_const = (conv_ref_const - conv_ref) + conv_ref`
    have h := abs_add_le (Goldbach.BG_Identity.conv_ref_const X0 X0 - Goldbach.BG_Identity.conv_ref X0 X0)
      (Goldbach.BG_Identity.conv_ref X0 X0)
    -- rewrite `|a+b|` to `|conv_ref_const|` and `|a|` to `|conv_ref - conv_ref_const|`
    have habs :
        |Goldbach.BG_Identity.conv_ref_const X0 X0 - Goldbach.BG_Identity.conv_ref X0 X0|
          = |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0| := by
      -- `c - r = -(r - c)` and `abs (-x) = abs x`.
      calc
        |Goldbach.BG_Identity.conv_ref_const X0 X0 - Goldbach.BG_Identity.conv_ref X0 X0|
            =
            |-(Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0)| := by
              congr 1; ring
        _ = |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0| := by
              simpa using (abs_neg (Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0))
    have hsum :
        (Goldbach.BG_Identity.conv_ref_const X0 X0 - Goldbach.BG_Identity.conv_ref X0 X0)
            + Goldbach.BG_Identity.conv_ref X0 X0
          = Goldbach.BG_Identity.conv_ref_const X0 X0 := by
      ring
    have h' :
        |Goldbach.BG_Identity.conv_ref_const X0 X0|
          ≤ |Goldbach.BG_Identity.conv_ref_const X0 X0 - Goldbach.BG_Identity.conv_ref X0 X0|
              + |Goldbach.BG_Identity.conv_ref X0 X0| := by
      simpa [hsum] using h
    simpa [habs] using h'

  have hrev :
      |Goldbach.BG_Identity.conv_ref_const X0 X0| - |Goldbach.BG_Identity.conv_ref X0 X0|
        ≤ |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0| := by
    linarith [htri]

  have hconst_abs :
      |Goldbach.BG_Identity.conv_ref_const X0 X0| = (0.05 : ℝ) := by
    have hconst : Goldbach.BG_Identity.conv_ref_const X0 X0 = (0.05 : ℝ) :=
      conv_ref_const_eq_005 (X := X0) (N := X0)
    have hnonneg : (0 : ℝ) ≤ (0.05 : ℝ) := by norm_num
    simpa [hconst, abs_of_nonneg hnonneg]

  have hdiff_ge :
      (0.05 : ℝ)
        - ((1252 : ℝ) / 10 ^ 6) * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
        ≤ |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0| := by
    have hsub :
        (0.05 : ℝ)
          - ((1252 : ℝ) / 10 ^ 6) * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
          ≤ (0.05 : ℝ) - |Goldbach.BG_Identity.conv_ref X0 X0| := by
      linarith [hconv]
    have hsub2 :
        (0.05 : ℝ) - |Goldbach.BG_Identity.conv_ref X0 X0|
          ≤ |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0| := by
      simpa [hconst_abs] using hrev
    exact le_trans hsub hsub2

  -- Numerically, the lower bound is *still* bigger than the canonical cap `δ_major_canon`.
  have hlt :
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
        <
        (0.05 : ℝ)
          - ((1252 : ℝ) / 10 ^ 6) * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    -- Everything is a rational expression in the pinned numerals once unfolded.
    norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon, Goldbach.BG_Calib.Mswap_canon,
      Goldbach.BankParams.H, Goldbach.BG_Identity.Ucut]

  have : Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
        < |Goldbach.BG_Identity.conv_ref X0 X0 - Goldbach.BG_Identity.conv_ref_const X0 X0| :=
    lt_of_lt_of_le hlt hdiff_ge

  exact (not_lt_of_ge hswap) this

end

end MajorArcContractScratch
end Goldbach.Cert
