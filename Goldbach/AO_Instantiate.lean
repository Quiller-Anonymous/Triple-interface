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
{ δ_kernel := (3e-3 : ℝ)
, δ_mellin := (18e-4 : ℝ)
, δ_smooth := (2e-3 : ℝ)
, δ_off    := (3e-4 : ℝ)
, δ_kernel_nonneg := by norm_num
, δ_mellin_nonneg := by norm_num
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
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    Goldbach.AO_ErrorCore.errAO channels X N
      = channels.E_kernel X N
      + channels.E_mellin X N
      + channels.E_smooth X N
      + channels.E_off X N

instance : Decomposition channels := by
  refine ⟨? _⟩
  intro X N hX hN
  simpa [channels] using (errAO_decomp_api (X := X) (N := N) hX hN)

/-- Total AO cap for the canonical caps. -/
noncomputable abbrev δAO : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO caps

lemma δAO_nonneg : 0 ≤ δAO := by
  simpa [δAO] using (Goldbach.AO_AssembleEnvelope.δAO_nonneg caps)

/-- The assembled AO envelope bound in the `AO_Major` shape used downstream. -/
lemma errAO_bound {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.AO_Major.errAO X N| ≤ δAO := by
  -- `AO_Major.errAO` should definitionaly be `AO_ErrorCore.errAO channels`
  -- or reducible to it; adjust simp list if needed.
  simpa [δAO, Goldbach.AO_Major.errAO, channels] using
    (Goldbach.AO_ErrorEnvelope.errAO_bound (C := channels) (K := caps) hX hN)

end Goldbach.AO_Instantiate
