import Goldbach.Cert.MajorArcModules.All
import Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec
import Goldbach.Cert.MajorArcModules.Q0TwoBoundsPinnedAxioms

/-!
Fool’s-gold convenience import: turnkey `Q0` instantiation.

This file exists so we can build the turnkey `Q0` route *together with* the current pinned
assumption surface, while keeping the default `Goldbach.Cert.MajorArcModules.All` bundle
gold-grade.

It intentionally imports project-pinned axioms/budgets via `Q0TwoBoundsPinnedAxioms.lean`.
-/
