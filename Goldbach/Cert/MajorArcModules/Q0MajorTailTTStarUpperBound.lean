import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Stage 2 bridge: package the ε₂-large TT* k-support upper bound in a file that is
certificate-facing (i.e. it names `U := ...FromCert.U`), while keeping the Toeplitz-side
analytic proof internal.

This lets downstream turnkey/spec files depend on the *certificate interface* rather than the
historical Toeplitz "axiom" module name.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBound

open scoped BigOperators Interval

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

noncomputable section

theorem q0InnerMajor_full_ttstar_kSupport_upper :
    Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon U := by
  -- The Toeplitz-side proof is phrased in terms of `U_target := FromCert.U`.
  simpa [Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.U_target] using
    (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.innerMajorQ0_full_ttstar_kSupport_upperBound :
      Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.U_target)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBound
