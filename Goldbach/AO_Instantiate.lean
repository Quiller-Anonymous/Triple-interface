/-
  Goldbach/AO_Instantiate.lean
  Canonical AO envelope instantiation (names match AO_AssembleEnvelope).
-/
import Goldbach.AO_Major
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_ErrorEnvelope
import Goldbach.AO_KernelTail
import Goldbach.AO_MellinTrunc
import Goldbach.AO_SmoothLoss
import Goldbach.AO_OffDiag

namespace Goldbach.AO_Instantiate
open Goldbach

/-- Wire the four AO channels into the envelope record. -/
def channels : AO_AssembleEnvelope.Channels :=
{ E_kernel := AO_KernelTail.E_kernel,
  E_mellin := AO_MellinTrunc.E_mellin,
  E_smooth := AO_SmoothLoss.E_smooth,
  E_off    := AO_OffDiag.E_off }

/-- Canonical caps: split δAO_canon across the four channels. -/
noncomputable def caps : AO_AssembleEnvelope.Caps :=
{ δ_kernel := 0.0030, δ_mellin := 0.0018, δ_smooth := 0.0008, δ_off := 0.0004,
  δ_kernel_nonneg := by norm_num, δ_mellin_nonneg := by norm_num,
  δ_smooth_nonneg := by norm_num, δ_off_nonneg := by norm_num }

/-- Numeric bounds for the four channels on the window (using provided lemmas/axioms). -/
instance : AO_AssembleEnvelope.Bounds channels caps := by
  refine ⟨?k, ?m, ?s, ?o⟩
  · intro X N hX hN
    simpa [channels] using AO_KernelTail.E_kernel_bound (X:=X) (N:=N) hX hN
  · intro X N hX hN
    simpa [channels] using AO_MellinTrunc.E_mellin_bound (X:=X) (N:=N) hX hN
  · intro X N hX hN
    simpa [channels] using AO_SmoothLoss.E_smooth_bound (X:=X) (N:=N) hX hN
  · intro X N hX hN
    simpa [channels] using AO_OffDiag.E_off_bound (X:=X) (N:=N) hX hN

end Goldbach.AO_Instantiate
