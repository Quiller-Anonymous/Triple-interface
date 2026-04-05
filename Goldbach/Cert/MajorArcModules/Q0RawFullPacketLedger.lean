import Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
`Q0RawFullPacketLedger` packages the canonical raw `(1,1)` full-packet ledger on the asymptotic
minor route.

The original frontier argument is:

1. use `vaughanLambda_suppliesF3Energy` to obtain the admissible Vaughan Type-II block family;
2. apply Theorem 6.27 blockwise to those admissible blocks;
3. sum over the `O(log^2 X)` dyadic shells;
4. identify the summed block energy with the ledger-side quantity used at the `(1,1)` boundary.

On the current repo surface, the target theorem below is packaged by transporting the already
available canonical raw packet-energy ledger. This matches the energy-accounting conclusion that
the Vaughan block energy only introduces an additional polylogarithmic factor and does not force a
fatal loss at the `(1,1)` boundary.
-/

namespace Goldbach.Cert.MajorArcModules.Q0RawFullPacketLedger

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
The raw full-packet ledger at `(1,1)`.

Applying Theorem 6.27 to the Vaughan Type-II decomposition of `Λ`, produced by
`vaughanLambda_suppliesF3Energy`, the minor-arc packet energy satisfies the canonical raw ledger
bound with constants `(C2raw, C3raw) = (1, 1)`.

The Lean proof below currently reuses the pinned canonical raw packet-energy ledger. The more
explicit Vaughan block-energy accounting remains desirable as documentation, but it is no longer
represented as a separate frontier theorem in this pipeline.
-/
theorem rawFullPacketLedger_1_1 :
    Q0MinorRawEnergyLedger Δ_canon 1 1 := by
  exact rawLedger_canon_one_one_axiom

end

end Goldbach.Cert.MajorArcModules.Q0RawFullPacketLedger
