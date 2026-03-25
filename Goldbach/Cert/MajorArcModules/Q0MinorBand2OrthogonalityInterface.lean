import Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface
import Goldbach.Cert.MajorArcModules.Q0MinorConcreteCalibration
import Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticRoute
import Goldbach.Cert.MajorArcModules.Q0Band2ShellOrthogonalityProof

/-!
`Q0MinorBand2OrthogonalityInterface` isolates the current structural frontier on the minor side.

After the Vaughan/F3 packet layer is organized, the remaining structural theorem consumed by the
concrete `(4,2,3,3)` route is exactly `Band2ShellOrthogonality Δ_canon`.

This file does not claim to prove that theorem. It packages the statement and records its immediate
downstream consequences so collaborators can target one precise analytic input.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorBand2OrthogonalityInterface

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge
open Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticRoute
open Goldbach.Cert.MajorArcModules.Q0Band2ShellOrthogonalityProof
open Goldbach.Cert.MajorArcModules.Q0MinorConcreteCalibration
open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Open structural frontier: the canonical dyadic shells are orthogonal once their shell distance is
at least `2`.

Intended provenance:

* single-sum Vaughan Type-II decomposition of `Λ`;
* admissible F3 block packaging from `Q0VaughanAdmissibility`;
* packet orthogonality / SSU assembly from Theorem 6.27;
* Farey-spacing / large-sieve geometry upgrading packet separation to shell orthogonality.
-/
axiom band2ShellOrthogonality_canon :
    Band2ShellOrthogonality Δ_canon

/--
Once band-2 shell orthogonality is supplied, the concrete calibrated `(4,2,3,3)` route reduces
the remaining minor side to square-function control `K = 3` and the raw `(1,1)` packet ledger.
-/
theorem ledgerEngine_canon_of_band2Interface_square3_raw1
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger.Q0MinorEnergyLedgerEngine
      Δ_canon
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C2
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C3 := by
  exact ledgerEngine_canon_of_band2_square3_raw1 band2ShellOrthogonality_canon hSq hRaw

/--
Energy-bound corollary of the previous theorem.
-/
theorem energyBound16_canon_of_band2Interface_square3_raw1
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 := by
  exact energyBound16_canon_of_band2_square3_raw1 band2ShellOrthogonality_canon hSq hRaw

/--
Variant using the current pinned raw `(1,1)` axiom.

This makes the dependency picture explicit:
after the concrete calibration discharge, only band-2 shell orthogonality and square-function
control with `K = 3` remain on the short route.
-/
theorem energyBound16_canon_of_band2Interface_square3_raw_axiom
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 := by
  exact energyBound16_canon_of_band2_square3_raw1
    band2ShellOrthogonality_canon hSq rawLedger_canon_one_one_axiom

/--
Asymptotic corollary of the band-2 interface on the raw `(1,1)` route.

This is the paper-facing replacement for the old finite-threshold calibration story: once the
structural band-2 input, square-function control, and raw packet ledger are supplied, the closure
envelope is eventually below any prescribed tolerance in the polylogarithmic regime.
-/
theorem asymptoticCalibrationTarget_of_band2Interface_square3_raw1
    {A : ℕ} {γ ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.AsymptoticCalibrationTarget
      A γ (asymptoticRouteC2 1) (asymptoticRouteC3 1) ε := by
  exact
    asymptoticCalibrationTarget_of_band2_square3_raw1
      (A := A) (γ := γ) (ε := ε)
      hA hγ0 hγhalf hε band2ShellOrthogonality_canon hSq hRaw

/--
Variant using the current pinned raw `(1,1)` packet-energy axiom.
-/
theorem asymptoticCalibrationTarget_of_band2Interface_square3_raw_axiom
    {A : ℕ} {γ ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3) :
    Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration.AsymptoticCalibrationTarget
      A γ (asymptoticRouteC2 1) (asymptoticRouteC3 1) ε := by
  exact
    asymptoticCalibrationTarget_of_band2Interface_square3_raw1
      (A := A) (γ := γ) (ε := ε)
      hA hγ0 hγhalf hε hSq rawLedger_canon_one_one_axiom

/--
Paper-facing asymptotic corollary of Proposition 6.18.

This is the honest asymptotic replacement for the earlier exact band-2 shell-orthogonality wish:
the overlap factor from Proposition 6.18 is harmless in the polylogarithmic regime, so the
band-2 and square-function spans are closed asymptotically. What remains open is the raw
full-packet ledger.
-/
theorem prop618_supplies_asymptoticCalibrationTarget_raw_frontier
    {A : ℕ} {γ ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε) :
    ∃ C_2 : ℝ, C_2 > 0 ∧
      Prop618AsymptoticCalibrationTarget A γ C_2 1 ε := by
  exact prop618_supplies_asymptotic_band2_square
    (A := A) (γ := γ) (ε := ε) hA hγ0 hγhalf hε

end

end Goldbach.Cert.MajorArcModules.Q0MinorBand2OrthogonalityInterface
