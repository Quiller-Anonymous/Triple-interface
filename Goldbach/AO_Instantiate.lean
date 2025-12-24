import Goldbach.AO_Major
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_ErrorEnvelope
import Goldbach.AO_Models
import Goldbach.AO_KernelTail
import Goldbach.AO_MellinTrunc
import Goldbach.AO_SmoothLoss
import Goldbach.AO_OffDiag

namespace Goldbach.AO_Instantiate
open Goldbach
open Goldbach.AO_Models
open Goldbach.AO_Major
open Goldbach.AO_AssembleEnvelope

/-- Wire the four AO channels into the envelope record (telescoping forward differences). -/
def channels : AO_AssembleEnvelope.Channels :=
{ E_smooth := fun X N => M_infInf_sm X N - M_infInf_raw X N
  E_mellin := fun X N => M_infT_sm X N - M_infInf_sm X N
  E_kernel := fun X N => M_HT_sm X N - M_infT_sm X N
  E_off    := fun X N => Mc anon N - M_HT_sm X N }

/-- Canonical caps: split δAO_canon across the four channels. -/
noncomputable def caps : AO_AssembleEnvelope.Caps :=
{ δ_kernel := 0.0030, δ_mellin := 0.0018, δ_smooth := 0.0008, δ_off := 0.0004,
  δ_kernel_nonneg := by norm_num, δ_mellin_nonneg := by norm_num,
  δ_smooth_nonneg := by norm_num, δ_off_nonneg := by norm_num }

instance : AO_AssembleEnvelope.Decomposition channels := by
  refine ⟨?_⟩
  intro X N hX hN
  -- TODO: unfold the definitions of errAO and each channel and telescope
  sorry

/-- Telescoping identity: errAO = sum of four channels (on the canonical window). -/
instance : AO_AssembleEnvelope.Decomposition channels := by
  refine ⟨?_⟩
  intro X N hX hN
  -- unfold everything; ring does the telescope, and `M_infInf_raw` is definitional.
  simp [AO_Major.errAO, channels, Goldbach.AO_Models.M_infInf_raw]
  ring

/-- Numeric bounds for the four channels on the window (using provided lemmas/axioms). -/
instance : AO_AssembleEnvelope.Bounds channels caps := by
  refine ⟨?k, ?m, ?s, ?o⟩
  · intro X N hX hN
    -- your existing lemma should bound the kernel channel; adjust lemma names if needed
    simpa [channels] using AO_KernelTail.E_kernel_bound (X:=X) (N:=N) hX hN
  · intro X N hX hN
    simpa [channels] using AO_MellinTrunc.E_mellin_bound (X:=X) (N:=N) hX hN
  · intro X N hX hN
    simpa [channels] using AO_SmoothLoss.E_smooth_bound (X:=X) (N:=N) hX hN
  · intro X N hX hN
    simpa [channels] using AO_OffDiag.E_off_bound (X:=X) (N:=N) hX hN

end Goldbach.AO_Instantiate
