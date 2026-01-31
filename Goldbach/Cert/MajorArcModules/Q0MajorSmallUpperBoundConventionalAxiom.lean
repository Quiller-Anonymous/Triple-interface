import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec

/-!
Tool-axiom seam for ε₂-small (small-β) major-arc evaluation.

This is the project-neutral “conventional math” boundary: it asserts that, for a chosen pair
`(Δ,U)`, the small-β deviation quantity admits the uniform upper bound `≤ U`.

Pinned/certificate-facing files should *not* introduce axioms; instead they should import this
file and specialize it to their chosen parameters.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundConventionalAxiom

open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec

noncomputable section

axiom major_arc_small_beta_upperBound (Δ U : ℝ) :
  Q0MajorSmallUpperBound Δ U

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundConventionalAxiom

