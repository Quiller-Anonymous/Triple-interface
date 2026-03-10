import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
ε₁ seam provider for the turnkey `Q0` route.

The turnkey `Q0` route consumes the project-neutral energy interface
`Q0MinorEnergyBound Δ_canon 16`.

This file centralizes *how* we obtain that bound:

- from a ledger-engine seam (`Q0MinorEnergyLedgerEngineAxiom`) plus the checked
  `Q0MinorLedgerCertData` cap-16 bridge (`Q0MinorEnergyFromLedgerCert`),
- with a stable output surface for downstream consumers.
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
