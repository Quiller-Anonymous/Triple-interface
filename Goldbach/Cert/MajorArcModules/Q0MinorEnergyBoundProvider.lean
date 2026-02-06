import Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundAxiom

/-!
ε₁ seam provider for the turnkey `Q0` route.

Polished-gold policy: the turnkey `Q0` route uses a project-neutral *energy bound* interface
`Q0MinorEnergyBound Δ_canon 16`.

This file centralizes *how* we obtain that bound:

- **Today (polished gold):** a single SSU/energy tool axiom in
  `Goldbach/Cert/MajorArcModules/Q0MinorEnergyBoundAxiom.lean`.
- **Later (stage (3) prep):** swap this provider to derive the same bound from the in-repo SSU /
  interzone machinery (still possibly assuming project-neutral SSU axioms), without changing
  downstream consumers.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundAxiom

noncomputable section

/-- The ε₁ input used by `Q0TwoBoundsSpec`: energy bound with cap `16` on the canonical width. -/
abbrev q0Minor_energyBound16 :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound
      Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 16 :=
  Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundAxiom.q0Minor_energyBound16

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider

