import Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge
import Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
`Q0MinorRawEnergyLedgerRoute` isolates the “short path” suggested in the handoff notes:

1. a square-function control from dyadic packet energies to full minor packet energy;
2. a raw full minor packet ledger;
3. immediate derivation of `Q0MinorDiagonalLedger`.

This file is bookkeeping only. It does not prove either analytic input.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge
open Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- The full `Q0`-minor packet in `ℓ²(EvenIn X H)`. -/
def minorPacket (X : ℕ) (Δ : ℝ) : EuclideanSpace ℂ (EvenIn X H) :=
  WithLp.toLp (2 : ENNReal) (fun N : EvenIn X H => corr_integral_minor_Q0 X (N : ℕ) Δ)

/-- Squared `ℓ²` energy of the full `Q0`-minor packet. -/
def minorPacketEnergy (X : ℕ) (Δ : ℝ) : ℝ :=
  ‖minorPacket X Δ‖ ^ 2

/--
Raw full-packet minor-energy ledger target:
`‖corr_integral_minor_Q0(X,·,Δ)‖₂² ≤ C2*(H/X) + C3/(H*Q0²)`.
-/
structure Q0MinorRawEnergyLedger (Δ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      minorPacketEnergy X Δ
        ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)

/--
Pinned seam axiom for the remaining unsplit analytic theorem at `Δ = 1`:
`‖corr_integral_minor_Q0(X,·,1)‖₂² ≤ H/X + 1/(H*Q0²)`.
-/
axiom rawMinorPacketEnergy_canon :
  ∀ {X : ℕ}, X0 ≤ X →
    minorPacketEnergy X Δ_canon
      ≤ ((H : ℝ) / (X : ℝ)) + 1 / ((H : ℝ) * (Q0 : ℝ) ^ 2)

/--
Repackaging of `rawMinorPacketEnergy_canon` in ledger form with `(C2raw, C3raw) = (1, 1)`.
-/
theorem rawLedger_canon_one_one_axiom :
    Q0MinorRawEnergyLedger Δ_canon 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro X hX
  simpa [one_mul] using rawMinorPacketEnergy_canon (X := X) hX

/--
Square-function control from dyadic packet energies to the full packet energy.

For `K = 1`, this is the exact orthogonal decomposition identity.
For `K = 3`, it matches the three-fold-overlap route.
-/
structure Q0MinorSquareFunctionControl (Δ K : ℝ) : Prop where
  K_nonneg : 0 ≤ K
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j) ≤ K * minorPacketEnergy X Δ

/--
Square-function control + raw full-packet ledger ⇒ diagonal packet-energy ledger.
-/
theorem diagonalLedger_of_squareFunction_and_raw
    {Δ K C2raw C3raw : ℝ}
    (hSq : Q0MinorSquareFunctionControl Δ K)
    (hRaw : Q0MinorRawEnergyLedger Δ C2raw C3raw) :
    Q0MinorDiagonalLedger Δ (K * C2raw) (K * C3raw) := by
  refine ⟨mul_nonneg hSq.K_nonneg hRaw.C2_nonneg, mul_nonneg hSq.K_nonneg hRaw.C3_nonneg, ?_⟩
  intro X hX
  have hSqX :
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j) ≤ K * minorPacketEnergy X Δ :=
    hSq.bound (X := X) hX
  have hRawX :
      minorPacketEnergy X Δ
        ≤ C2raw * ((H : ℝ) / (X : ℝ)) + C3raw / ((H : ℝ) * (Q0 : ℝ) ^ 2) :=
    hRaw.bound (X := X) hX
  have hMul :
      K * minorPacketEnergy X Δ
        ≤
      K * (C2raw * ((H : ℝ) / (X : ℝ)) + C3raw / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hRawX hSq.K_nonneg
  have hMain :
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j)
        ≤
      K * (C2raw * ((H : ℝ) / (X : ℝ)) + C3raw / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :=
    le_trans hSqX hMul
  simpa [mul_add, mul_assoc, div_eq_mul_inv, mul_left_comm, mul_comm] using hMain

/--
Canonical corollary suggested in the handoff:
if one has square-function control with `K = 3` and raw full-packet ledger with `(C2raw,C3raw)=(1,1)`,
then `Q0MinorDiagonalLedger Δ_canon 3 3`.
-/
theorem diagonalLedger_canon_three_of_square3_and_raw1
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    Q0MinorDiagonalLedger Δ_canon 3 3 := by
  simpa using
    (diagonalLedger_of_squareFunction_and_raw
      (Δ := Δ_canon) (K := 3) (C2raw := 1) (C3raw := 1) hSq hRaw)

/--
If square-function control with `K = 3` is available, the pinned raw-energy axiom gives
`Q0MinorDiagonalLedger Δ_canon 3 3` immediately.
-/
theorem diagonalLedger_canon_three_of_square3_and_raw_axiom
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3) :
    Q0MinorDiagonalLedger Δ_canon 3 3 :=
  diagonalLedger_canon_three_of_square3_and_raw1 hSq rawLedger_canon_one_one_axiom

/--
Combining the previous corollary with the already-implemented band-2 bridge yields the canonical
dyadic polynomial payload `(C,p,C2raw,C3raw) = (4,2,3,3)`.
-/
theorem dyadicGramDecayPoly_canon_of_band2_square3_raw1
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1) :
    Q0MinorDyadicGramDecayPoly Δ_canon 4 2 3 3 := by
  exact
    dyadicGramDecayPoly_canon_of_band2_and_diagonal3 hBand
      (diagonalLedger_canon_three_of_square3_and_raw1 hSq hRaw)

/--
Turnkey closure for the suggestion-box route:

* band-2 shell orthogonality,
* square-function control with `K = 3`,
* raw full-packet bound with `(C2raw, C3raw) = (1, 1)`,
* numeric calibration against certified caps `C2`, `C3`.
-/
theorem ledgerEngine_canon_of_band2_square3_raw1_and_calibration
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hSq : Q0MinorSquareFunctionControl Δ_canon 3)
    (hRaw : Q0MinorRawEnergyLedger Δ_canon 1 1)
    (hC2cal :
      (CrowOf (aPoly 4 2)) * (3 : ℝ)
        ≤ Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C2)
    (hC3cal :
      (CrowOf (aPoly 4 2)) * (3 : ℝ)
        ≤ Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C3) :
    Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger.Q0MinorEnergyLedgerEngine
      Δ_canon
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C2
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C3 := by
  exact
    ledgerEngine_canon_of_band2_diagonal3_and_calibration
      hBand
      (diagonalLedger_canon_three_of_square3_and_raw1 hSq hRaw)
      hC2cal hC3cal

end

end Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
