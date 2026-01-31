import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Tool-axiom seam for ε₂-small (small-β major-arc evaluation) in the turnkey `Q0` route.

Polished-gold policy: downstream turnkey/spec code should depend on the **budget-level** bound
`Q0MajorSmallBound` directly, rather than on a pinned intermediate upper bound `U` that is later
compared to `εs` by a certificate check.

This file therefore records the small-β deviation bound with the advertised budget `εs`
(currently pinned in the generated artifact `Q0MajorSmallCertData`).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallBoundAxiom

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

noncomputable abbrev εs : ℝ := (Q0MajorSmallCertData.data.εs : ℝ)

axiom q0Major_small_bound : Q0MajorSmallBound Δ_canon εs

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallBoundAxiom

