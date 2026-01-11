import Goldbach.AO_Major
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_Models
import Goldbach.AO_KernelTail
import Goldbach.AO_MellinTrunc
import Goldbach.AO_SmoothLoss
import Goldbach.AO_OffDiag.TenorHypFunX
import Goldbach.AO_OffDiagFunX
import Goldbach.AO_Stages
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach.AO_InstantiateTenorFunX

open Goldbach
open Goldbach.AO_Models
open Goldbach.AO_Major
open Goldbach.AO_AssembleEnvelope
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.TenorHypFunX

/-!
Parallel AO instantiation that uses the `Q(X)`-refactored off-diagonal bound.

The other channels (`kernel/mellin/smooth`) remain as in the current pipeline; only `E_off`
is swapped out to use `TenorHypFunX.OffDiagHyp`.

Strategy 2 for the parallel track:
define a parallel `Mcanon` directly as the staged term `AO_Stages.M_off`, so no bespoke “wiring”
axiom is needed to relate it to `AO_Core.Mcanon`.
-/

/-- Canonical channel functions used in the assembled AO envelope. -/
noncomputable def channels (Hoff : OffDiagHyp) : Channels :=
{ E_kernel := Goldbach.AO_KernelTail.E_kernel
, E_mellin := Goldbach.AO_MellinTrunc.E_mellin
, E_smooth := Goldbach.AO_SmoothLoss.E_smooth
, E_off    := fun X N => Goldbach.AO_OffDiagFunX.E_off (TenorHypFunX.model Hoff) X N
}

/-- Parallel-track AO main term: the fully staged term (depends on `X`). -/
noncomputable def Mcanon (Hoff : OffDiagHyp) (X N : ℕ) : ℝ :=
  Goldbach.AO_Stages.M_off (channels Hoff) X N

/-- Parallel-track AO remainder: staged main term minus the baseline `sigma * weight_mass`. -/
noncomputable def errAO (Hoff : OffDiagHyp) (X N : ℕ) : ℝ :=
  Mcanon Hoff X N - Goldbach.AO_Stages.M_raw X N

/-- Canonical numeric caps, now parameterized by the off-diagonal hypothesis. -/
noncomputable def caps (Hoff : OffDiagHyp) : Caps :=
{ δ_kernel := ((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed
, δ_mellin := Goldbach.AO_MellinTrunc.δ_mellin_canon
, δ_smooth := (0.0008 : ℝ)
, δ_off    := Hoff.eps
, δ_kernel_nonneg := by
    have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by nlinarith [htail_val]
    have hconst : 0 ≤ ((1252 : ℝ) / 10^6) := by norm_num
    exact mul_nonneg hconst htail_nonneg
, δ_mellin_nonneg := Goldbach.AO_MellinTrunc.δ_mellin_nonneg
, δ_smooth_nonneg := by norm_num
, δ_off_nonneg    := Hoff.eps_nonneg
}

lemma errAO_decomp (Hoff : OffDiagHyp) (X N : ℕ) :
    errAO Hoff X N =
      (channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N
        + (channels Hoff).E_kernel X N + (channels Hoff).E_off X N := by
  simp [errAO, Mcanon, Goldbach.AO_Stages.M_off_sub_M_raw_eq_sum]

instance (Hoff : OffDiagHyp) : Bounds (channels Hoff) (caps Hoff) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X N hX hN
    have hX' : Goldbach.BG_Bank.X0 ≤ X := by simpa [Goldbach.BG_Bank.X0] using hX
    have hN' : N ∈ Goldbach.Windows.EvenIn X Goldbach.BG_Bank.H := by
      simpa [Goldbach.BG_Bank.H] using hN
    have hkernel :
        |Goldbach.AO_KernelTail.E_kernel X N|
          ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed := by
      simpa using (Goldbach.AO_KernelTail.E_kernel_bound (X := X) (N := N) hX' hN')
    have hcap :
        Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10^6 := by
      simpa [Goldbach.BG_Bank.X0, Goldbach.BG_Bank.H] using
        (Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX' hN')
    have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by nlinarith [htail_val]
    have hprod :
        Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed
          ≤ ((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed :=
      mul_le_mul_of_nonneg_right hcap htail_nonneg
    have : |(channels Hoff).E_kernel X N| ≤ (caps Hoff).δ_kernel := by
      simpa [channels, caps] using le_trans hkernel hprod
    simpa using this
  · intro X N hX hN
    have hmellin :
        |Goldbach.AO_MellinTrunc.E_mellin X N|
          ≤ Goldbach.AO_MellinTrunc.δ_mellin_canon :=
      Goldbach.AO_MellinTrunc.E_mellin_bound (X := X) (N := N) hX hN
    simpa [channels, caps] using hmellin
  · intro X N hX hN
    have hsmooth :
        |Goldbach.AO_SmoothLoss.E_smooth X N| ≤ (0.0008 : ℝ) := by
      have hX' : Goldbach.BG_Bank.X0 ≤ X := by simpa [Goldbach.BG_Bank.X0] using hX
      have hN' : N ∈ Goldbach.Windows.EvenIn X Goldbach.BG_Bank.H := by
        simpa [Goldbach.BG_Bank.H] using hN
      simpa using (Goldbach.AO_SmoothLoss.E_smooth_bound (X := X) (N := N) hX' hN')
    simpa [channels, caps] using hsmooth
  · intro X N hX hN
    have hoff :
        |Goldbach.AO_OffDiagFunX.E_off (TenorHypFunX.model Hoff) X N| ≤ Hoff.eps :=
      TenorHypFunX.E_off_bound (H := Hoff) (X := X) (N := N) hX hN
    simpa [channels, caps] using hoff

/-- Total AO cap for these caps. -/
noncomputable abbrev δAO (Hoff : OffDiagHyp) : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO (caps Hoff)

lemma δAO_nonneg (Hoff : OffDiagHyp) : 0 ≤ δAO Hoff := by
  simpa [δAO] using (Goldbach.AO_AssembleEnvelope.δAO_nonneg (caps Hoff))

/-- The assembled AO envelope bound in the `AO_Major` shape used downstream. -/
lemma errAO_bound (Hoff : OffDiagHyp)
    {X N : ℕ} (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    |errAO Hoff X N| ≤ δAO Hoff := by
  classical
  have hk := (Bounds.err_kernel_bound (C := channels Hoff) (K := caps Hoff)) hX hN
  have hm := (Bounds.err_mellin_bound (C := channels Hoff) (K := caps Hoff)) hX hN
  have hs := (Bounds.err_smooth_bound (C := channels Hoff) (K := caps Hoff)) hX hN
  have ho := (Bounds.err_off_bound (C := channels Hoff) (K := caps Hoff)) hX hN

  have tri :
      |(channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N
          + (channels Hoff).E_kernel X N + (channels Hoff).E_off X N|
        ≤ |(channels Hoff).E_smooth X N| + |(channels Hoff).E_mellin X N|
            + |(channels Hoff).E_kernel X N| + |(channels Hoff).E_off X N| := by
    have t3 :=
      abs_add_le ((channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N
        + (channels Hoff).E_kernel X N) ((channels Hoff).E_off X N)
    have t2 :=
      abs_add_le ((channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N)
        ((channels Hoff).E_kernel X N)
    have t1 := abs_add_le ((channels Hoff).E_smooth X N) ((channels Hoff).E_mellin X N)
    calc
      |(channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N
          + (channels Hoff).E_kernel X N + (channels Hoff).E_off X N|
          = |((channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N
              + (channels Hoff).E_kernel X N) + (channels Hoff).E_off X N| := by ring
      _ ≤ |(channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N
              + (channels Hoff).E_kernel X N| + |(channels Hoff).E_off X N| := t3
      _ ≤ (|(channels Hoff).E_smooth X N + (channels Hoff).E_mellin X N|
              + |(channels Hoff).E_kernel X N|) + |(channels Hoff).E_off X N| := by gcongr
      _ ≤ ((|(channels Hoff).E_smooth X N| + |(channels Hoff).E_mellin X N|)
              + |(channels Hoff).E_kernel X N|) + |(channels Hoff).E_off X N| := by gcongr
      _ = |(channels Hoff).E_smooth X N| + |(channels Hoff).E_mellin X N|
              + |(channels Hoff).E_kernel X N| + |(channels Hoff).E_off X N| := by ring

  have hdecomp := errAO_decomp (Hoff := Hoff) X N
  rw [hdecomp]
  refine le_trans tri ?_
  have hδ :
      (caps Hoff).δ_smooth + (caps Hoff).δ_mellin + (caps Hoff).δ_kernel + (caps Hoff).δ_off =
        δAO Hoff := by
    simp [δAO, Goldbach.AO_AssembleEnvelope.δAO]; ring
  calc
    |(channels Hoff).E_smooth X N| + |(channels Hoff).E_mellin X N|
          + |(channels Hoff).E_kernel X N| + |(channels Hoff).E_off X N|
        ≤ (caps Hoff).δ_smooth + (caps Hoff).δ_mellin + (caps Hoff).δ_kernel + (caps Hoff).δ_off := by
          gcongr
    _ = δAO Hoff := by simpa [hδ]

/-- Lower bound for the staged parallel-track main term on the canonical window. -/
lemma McanoN_lb_cAO (Hoff : OffDiagHyp) [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    {X N : ℕ} (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    Mcanon Hoff X N ≥ Goldbach.AO_Major.cAO (caps Hoff) := by
  have hX' : (10 ^ 6 : ℕ) ≤ X := by simpa [Goldbach.BankParams.X0] using hX
  have hN' : N ∈ Goldbach.Windows.EvenIn X (10 ^ 4) := by
    simpa [Goldbach.BankParams.H] using hN
  classical
  have hσ :
      Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin ≤ Goldbach.AO_SigmaPos.sigma N := by
    -- Use the windowed σ-lower input.
    simpa [Goldbach.AO_SigmaPos.sigma] using
      (Goldbach.AO_SigmaPos.SigmaLowerOnWindow.sigma_even_lb_on_window (X := X) (N := N) hX hN)

  have herr : |errAO Hoff X N| ≤ δAO Hoff := errAO_bound (Hoff := Hoff) (X := X) (N := N) hX hN
  have herr_lo : -(δAO Hoff) ≤ errAO Hoff X N := (abs_le.mp herr).1

  have hraw : Goldbach.AO_Stages.M_raw X N = Goldbach.AO_SigmaPos.sigma N := by
    simp [Goldbach.AO_Stages.M_raw, Goldbach.AO_SigmaPos.sigma, Goldbach.AO_Core.weight_mass]

  calc
    Mcanon Hoff X N
        = Goldbach.AO_Stages.M_raw X N + errAO Hoff X N := by
            -- `errAO = Mcanon - M_raw`
            ring_nf
            simp [errAO, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _   ≥ Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin + (-(δAO Hoff)) := by
            have hs0 :
                Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin ≤ Goldbach.AO_Stages.M_raw X N := by
              simpa [hraw] using hσ
            have hsum :
                Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin + (-(δAO Hoff))
                  ≤ Goldbach.AO_Stages.M_raw X N + errAO Hoff X N :=
              add_le_add hs0 herr_lo
            simpa [add_assoc, add_left_comm, add_comm] using hsum
    _   = Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin - δAO Hoff := by ring
    _   = Goldbach.AO_Major.cAO (caps Hoff) := by
            simp [Goldbach.AO_Major.cAO, δAO]

end Goldbach.AO_InstantiateTenorFunX
