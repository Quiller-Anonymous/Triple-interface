import Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Temporary conventional-math boundary for the ε₂-small (small-β) major-arc evaluation.

This file packages the (currently missing) global Step20–24 evaluation on `betaSmallSet` into a
single assumption, stated in the certificate-facing interface
`Q0MajorSmallUpperBoundSpec.Q0MajorSmallUpperBound`.

Long-term plan:
- replace this axiom by an assembled proof using the existing BMOR Step20/21 + Step24 machinery,
  and/or by a checker artifact producing the same upper bound `U`;
- keep the downstream plumbing (`Q0MajorSmallUpperBoundFromCert`) unchanged.

Note: this statement is “conventional” in *mathematical content* (a major-arc evaluation with an
explicit error bound), but the constant `U` is currently pinned to the generator-controlled budget
file `Q0MajorSmallCertData.lean` to match the turnkey Q0 route.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundTextbookAxiom

open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

noncomputable abbrev Us : ℝ := (Q0MajorSmallCertData.data.U : ℝ)

axiom major_arc_small_beta_upperBound :
  Q0MajorSmallUpperBound Δ_canon Us

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundTextbookAxiom

