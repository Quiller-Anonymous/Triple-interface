import Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration
import Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
`Q0MinorAsymptoticRoute` is the paper-facing companion to the fixed-cap workbench route.

The concrete route

* band-2 shell orthogonality,
* square-function control,
* raw full-packet ledger,

still produces the same dyadic polynomial witness `(C, p) = (4, 2)`. The difference is that
instead of calibrating against the repo's pinned finite caps `C2`, `C3`, we feed the resulting
fixed constants into the asymptotic polylogarithmic envelope proved in
`Q0MinorAsymptoticCalibration`.

This matches the paper's architecture: for fixed `A ≥ 10` and `0 < γ < 1/2`, the closure
envelope eventually falls below any prescribed tolerance.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticRoute

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration
open Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- The asymptotic closure constant contributed by the `H/X` part of the `(4,2)` route. -/
def asymptoticRouteC2 (C2raw : ℝ) : ℝ :=
  CrowOf (aPoly 4 2) * (3 * C2raw)

/-- The asymptotic closure constant contributed by the `1 / (H Q0²)` part of the `(4,2)` route. -/
def asymptoticRouteC3 (C3raw : ℝ) : ℝ :=
  CrowOf (aPoly 4 2) * (3 * C3raw)

lemma asymptoticRouteC2_nonneg {C2raw : ℝ} (hC2raw : 0 ≤ C2raw) :
    0 ≤ asymptoticRouteC2 C2raw := by
  have hCrow : 0 ≤ CrowOf (aPoly 4 2) := by
    exact CrowOf_nonneg (a := aPoly 4 2) (aPoly_nonneg (C := 4) (p := 2) (by norm_num))
  exact mul_nonneg hCrow (mul_nonneg (by norm_num) hC2raw)

lemma asymptoticRouteC3_nonneg {C3raw : ℝ} (hC3raw : 0 ≤ C3raw) :
    0 ≤ asymptoticRouteC3 C3raw := by
  have hCrow : 0 ≤ CrowOf (aPoly 4 2) := by
    exact CrowOf_nonneg (a := aPoly 4 2) (aPoly_nonneg (C := 4) (p := 2) (by norm_num))
  exact mul_nonneg hCrow (mul_nonneg (by norm_num) hC3raw)

/--
Generalized dyadic polynomial witness from the band-2/square/raw route with arbitrary fixed
raw-ledger constants.
-/
theorem dyadicGramDecayPoly_canon_of_band2_square_and_raw
    {C2raw C3raw : ℝ}
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon C2raw C3raw) :
    Q0MinorDyadicGramDecayPoly Δ_canon 4 2 (3 * C2raw) (3 * C3raw) := by
  have hDiag :
      Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget.Q0MinorDiagonalLedger
        Δ_canon (3 * C2raw) (3 * C3raw) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (diagonalLedger_of_squareFunction_and_raw
        (Δ := Δ_canon) (K := 3) (C2raw := C2raw) (C3raw := C3raw) hSq hRaw)
  exact
    dyadicGramDecayPoly_of_band2_and_diagonal
      (Δ := Δ_canon) (C2 := 3 * C2raw) (C3 := 3 * C3raw) hBand hDiag

/--
Paper-facing asymptotic calibration target produced by the band-2/square/raw route.

The proof uses the route only to identify the fixed constants carried by the dyadic polynomial
witness. Once those constants are fixed, `Q0MinorAsymptoticCalibration` gives the eventual
`X₀(A,γ)` threshold.
-/
theorem asymptoticCalibrationTarget_of_band2_square_and_raw
    {A : ℕ} {γ ε C2raw C3raw : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε)
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon C2raw C3raw) :
    AsymptoticCalibrationTarget
      A γ (asymptoticRouteC2 C2raw) (asymptoticRouteC3 C3raw) ε := by
  let _ :=
    dyadicGramDecayPoly_canon_of_band2_square_and_raw
      (C2raw := C2raw) (C3raw := C3raw) hBand hSq hRaw
  exact
    asymptoticCalibrationTarget_of_polylog_regime
      (A := A) (γ := γ)
      (C2 := asymptoticRouteC2 C2raw) (C3 := asymptoticRouteC3 C3raw) (ε := ε)
      hA hγ0 hγhalf
      (asymptoticRouteC2_nonneg hRaw.C2_nonneg)
      (asymptoticRouteC3_nonneg hRaw.C3_nonneg)
      hε

/--
Specialization of the asymptotic route to the raw `(1,1)` packet-energy ledger.
-/
theorem asymptoticCalibrationTarget_of_band2_square3_raw1
    {A : ℕ} {γ ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε)
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    AsymptoticCalibrationTarget
      A γ (asymptoticRouteC2 1) (asymptoticRouteC3 1) ε := by
  exact
    asymptoticCalibrationTarget_of_band2_square_and_raw
      (A := A) (γ := γ) (ε := ε) (C2raw := 1) (C3raw := 1)
      hA hγ0 hγhalf hε hBand hSq hRaw

/--
Vaughan-aware wrapper for the asymptotic route.

The single-sum Vaughan/F3 supply is now a theorem rather than an axiom. The present route still
keeps the global raw-packet ledger as a separate theorem-shaped boundary, so this wrapper records
that the Vaughan assembly layer is available alongside the band-2/square/raw inputs.
-/
theorem asymptoticCalibrationTarget_of_vaughan_band2_square3_raw1
    {A : ℕ} {γ ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hε : 0 < ε)
    (X U V : ℕ)
    (_hVaughan : ∃ blocks : Finset (AdmissibleF3Block X),
      isVaughanTypeIIBlockFamily X U V blocks)
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    AsymptoticCalibrationTarget
      A γ (asymptoticRouteC2 1) (asymptoticRouteC3 1) ε := by
  exact
    asymptoticCalibrationTarget_of_band2_square3_raw1
      (A := A) (γ := γ) (ε := ε)
      hA hγ0 hγhalf hε hBand hSq hRaw

end

end Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticRoute
