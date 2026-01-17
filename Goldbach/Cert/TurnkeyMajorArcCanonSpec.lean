import Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

/-!
Turnkey major-arc interface axiom (Strategy 2 / certificate-facing boundary).

This replaces the bespoke axiom `MajorArcEvalOnWindowCanonSpec.major_arc_eval_on_window_canon`
with the certificate-first interface `TurnkeyMajorArcCanon`.

Downstream code should consume the bound via `TurnkeyCanon`, so that this file can later be
replaced by an axiom-free construction (proved theorem or certificate-checked artifact) without
changing the pipeline wiring.
-/

namespace Goldbach.Cert.TurnkeyMajorArcCanonSpec

open Goldbach.Cert.MajorArcModules.TurnkeyCanon

noncomputable section

/-!
This is the single “turnkey major-arc” boundary.

Long-term goal: replace this axiom by a proved/certificate-checked construction producing an
inhabitant of `TurnkeyMajorArcCanon`.
-/
theorem turnkeyMajorArcCanon : TurnkeyMajorArcCanon :=
  Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.turnkeyMajorArcCanon

end

end Goldbach.Cert.TurnkeyMajorArcCanonSpec
