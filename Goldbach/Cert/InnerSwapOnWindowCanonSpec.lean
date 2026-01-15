import Goldbach.ParallelTenorFunX
import Goldbach.Cert.InnerSwapTextbookRoute
import Goldbach.Cert.TurnkeyMajorArcCanonSpec

/-!
Canonical InnerSwap instance from the Strategy-2 major-arc axiom.

This is a small wiring module: it turns the project-facing major-arc statement on the textbook
objects (`RΛ_smooth`, `RΛ_model`) into the pipeline-facing `InnerSwapOnWindow` hypothesis.
-/

namespace Goldbach.Cert.InnerSwapOnWindowCanonSpec

open Goldbach
open Goldbach.Cert
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

instance : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  Goldbach.Cert.MajorArcModules.TurnkeyCanon.innerSwapOnWindow_of_turnkey
    Goldbach.Cert.TurnkeyMajorArcCanonSpec.turnkeyMajorArcCanon

end

end Goldbach.Cert.InnerSwapOnWindowCanonSpec
