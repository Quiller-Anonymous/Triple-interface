import Goldbach.BankParams
import Goldbach.AO_SigmaModel
import Goldbach.AO_WeightMass
import Goldbach.AO_CanonChannels

namespace Goldbach.AO_Mcanon

open Goldbach.AO_AssembleEnvelope

/-!
Definition of the canonical AO main term `Mcanon`.

This is *not* an axiom: we define `Mcanon X N` to be the fully staged main term
for the main-track channel decomposition at scale `X`.
-/

/-- Canonical AO main term (main track). -/
noncomputable def Mcanon (X N : ℕ) : ℝ :=
  Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X
    + (Goldbach.AO_CanonChannels.channels.E_smooth X N
      + Goldbach.AO_CanonChannels.channels.E_mellin X N
      + Goldbach.AO_CanonChannels.channels.E_kernel X N
      + Goldbach.AO_CanonChannels.channels.E_off X N)

end Goldbach.AO_Mcanon
