import Goldbach.AO_EnvelopeCore
import Goldbach.AO_KernelTail
import Goldbach.AO_MellinTrunc
import Goldbach.AO_SmoothLoss
import Goldbach.AO_OffDiag

namespace Goldbach.AO_CanonChannels

open Goldbach.AO_AssembleEnvelope

/-- Canonical channel functions used in the assembled AO envelope (main track). -/
noncomputable def channels : Channels :=
{ E_kernel := Goldbach.AO_KernelTail.E_kernel
, E_mellin := Goldbach.AO_MellinTrunc.E_mellin
, E_smooth := Goldbach.AO_SmoothLoss.E_smooth
, E_off    := Goldbach.AO_OffDiag.E_off
}

end Goldbach.AO_CanonChannels

