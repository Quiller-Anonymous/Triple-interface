import Goldbach.AO_Major
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_ErrorEnvelope
import Goldbach.AO_Models
import Goldbach.AO_KernelTail
import Goldbach.AO_MellinTrunc
import Goldbach.AO_SmoothLoss
import Goldbach.AO_OffDiag
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach.AO_Instantiate
open Goldbach
open Goldbach.AO_Models
open Goldbach.AO_Major
open Goldbach.AO_AssembleEnvelope

/-- Canonical channel functions used in the assembled AO envelope. -/
noncomputable def channels : Channels :=
{ E_kernel := Goldbach.AO_KernelTail.E_kernel
, E_mellin := Goldbach.AO_MellinTrunc.E_mellin
, E_smooth := Goldbach.AO_SmoothLoss.E_smooth
, E_off    := Goldbach.AO_OffDiag.E_off
}

/-- Canonical numeric caps (edit the numbers to your current budget split). -/
noncomputable def caps : Caps :=
{ δ_kernel := ((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed
, δ_mellin := Goldbach.AO_MellinTrunc.δ_mellin_canon
, δ_smooth := (0.0008 : ℝ)
, δ_off    := (3e-4 : ℝ)
, δ_kernel_nonneg := by
    have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by nlinarith [htail_val]
    have hconst : 0 ≤ ((1252 : ℝ) / 10^6) := by norm_num
    exact mul_nonneg hconst htail_nonneg
, δ_mellin_nonneg := Goldbach.AO_MellinTrunc.δ_mellin_nonneg
, δ_smooth_nonneg := by norm_num
, δ_off_nonneg    := by norm_num
}

/-!
If you already have an axiom/lemma `errAO_decomp_api` elsewhere, keep it there.
You now use it to build the `Decomposition channels` instance.

If your `Decomposition` class has a *single* field, this `refine ⟨...⟩` works.
If it has a named field, replace `⟨...⟩` with `⟨errAO_decomp_api⟩` accordingly.
-/
axiom errAO_decomp_api :
  ∀ {X N : ℕ}, Goldbach.BankParams.X0 ≤ X →
      N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H →
    Goldbach.AO_Core.errAO X N
      = channels.E_smooth X N
      + channels.E_mellin X N
      + channels.E_kernel X N
      + channels.E_off X N

instance : Decomposition channels := by
  refine ⟨by
    intro X N hX hN
    simpa [channels] using (errAO_decomp_api (X := X) (N := N) hX hN)⟩

instance : Bounds channels caps := by
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
    have : |channels.E_kernel X N| ≤ caps.δ_kernel := by
      -- unfold `channels.E_kernel` and `caps.δ_kernel`, then apply the two-step bound
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
        |Goldbach.AO_OffDiag.E_off X N| ≤ (3e-4 : ℝ) :=
      Goldbach.AO_OffDiag.E_off_bound (X := X) (N := N) hX hN
    simpa [channels, caps] using hoff

/-- Total AO cap for the canonical caps. -/
noncomputable abbrev δAO : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO caps

lemma δAO_nonneg : 0 ≤ δAO := by
  simpa [δAO] using (Goldbach.AO_AssembleEnvelope.δAO_nonneg caps)

/-- The assembled AO envelope bound in the `AO_Major` shape used downstream. -/
lemma errAO_bound {X N : ℕ} (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    |Goldbach.AO_Major.errAO X N| ≤ δAO := by
  simpa [δAO, Goldbach.AO_Major.errAO, channels] using
    (Goldbach.AO_ErrorEnvelope.errAO_bound (C := channels) (K := caps) hX hN)

end Goldbach.AO_Instantiate
