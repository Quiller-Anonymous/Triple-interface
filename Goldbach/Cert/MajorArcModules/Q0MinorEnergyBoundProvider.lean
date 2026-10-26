import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
ε₁ seam provider for the turnkey `Q0` route.

The turnkey `Q0` route consumes the project-neutral energy interface
`Q0MinorEnergyBound Δ_canon 16`.

This file centralizes *how* we obtain that bound: the current provider uses the checked
`Q0MinorSSUFromCert.nonzeroModeEnergyBound` through the cap-16 conversion in
`Q0MinorEnergyFromLedgerCert`. It does not import or use the retired universal calibration seam in
`Q0MinorEnergyLedgerEngineAxiom`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- The ε₁ input used by `Q0TwoBoundsSpec`: energy bound with cap `16` on the canonical width. -/
abbrev q0Minor_energyBound16 :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound
      Δ_canon 16 :=
  energyBound16_of_ssuCertBound Q0MinorSSUFromCert.nonzeroModeEnergyBound

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider
