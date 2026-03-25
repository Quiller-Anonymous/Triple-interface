import Goldbach.Cert.MajorArcModules.Q0MinorCalibrationHandoff
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
`Q0MinorConcreteCalibration` discharges the numeric calibration step for the existing
suggestion-box route `(C,p,C2raw,C3raw) = (4,2,3,3)`.

This does **not** prove the analytic inputs of that route:

* band-2 shell orthogonality,
* square-function control with `K = 3`,
* raw full-packet ledger with `(1,1)`.

What it does prove is that once those analytic inputs are supplied, the Crow calibration
inequalities are automatic. So for this concrete route, calibration is no longer the obstruction.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorConcreteCalibration

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge
open Goldbach.Cert.MajorArcModules.Q0MinorCalibrationHandoff
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

noncomputable section

/--
A deliberately coarse but sufficient Crow bound for the concrete decay profile `aPoly 4 2`.

The proof only uses the textbook inverse-square summation bound.
-/
theorem crow_aPoly_four_two_le_twenty :
    CrowOf (aPoly 4 2) ≤ 20 := by
  let f1 : ℕ → ℝ := fun m => 1 / ((m : ℝ) ^ 2)
  let f2 : ℕ → ℝ := fun d => 1 / (((d + 2 : ℕ) : ℝ) ^ 2)
  have hsum_range_shift1 : ∀ n : ℕ,
      (Finset.range n).sum (fun d => f1 (d + 1)) ≤ 2 := by
    intro n
    have hIooIco : Finset.Ioo 0 (n + 1) = Finset.Ico 1 (n + 1) := by
      ext m
      constructor <;> intro h <;>
        simp only [Finset.mem_Ioo, Finset.mem_Ico] at h ⊢ <;> omega
    calc
      (Finset.range n).sum (fun d => f1 (d + 1))
          = ∑ m ∈ Finset.Ico 1 (n + 1), f1 m := by
              simpa [f1, add_comm] using
                (Finset.sum_Ico_eq_sum_range (f := f1) 1 (n + 1)).symm
      _ = ∑ m ∈ Finset.Ioo 0 (n + 1), f1 m := by rw [hIooIco]
      _ ≤ 2 / ((0 : ℝ) + 1) := by
            simpa [f1] using (sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1))
      _ = 2 := by norm_num
  have hsummable_shift1 : Summable (fun d : ℕ => f1 (d + 1)) := by
    simpa [f1] using
      ((_root_.summable_nat_add_iff 1 (f := f1)).2
        ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)))
  have htsum_shift1_le : (∑' d : ℕ, f1 (d + 1)) ≤ 2 := by
    exact
      Real.tsum_le_of_sum_range_le
        (fun d => by simp [f1]; positivity)
        (by simpa using hsum_range_shift1)
  have hpointwise : ∀ d : ℕ, f2 d ≤ f1 (d + 1) := by
    intro d
    have h1 : 0 < (((d + 1 : ℕ) : ℝ) ^ 2) := by positivity
    have hle : (((d + 1 : ℕ) : ℝ) ^ 2) ≤ (((d + 2 : ℕ) : ℝ) ^ 2) := by
      nlinarith [show ((d + 1 : ℕ) : ℝ) ≤ ((d + 2 : ℕ) : ℝ) by
        exact_mod_cast Nat.le_succ (d + 1)]
    simpa [f1, f2] using (one_div_le_one_div_of_le h1 hle)
  have hsummable_shift2 : Summable f2 := by
    simpa [f1, f2, add_assoc, add_comm, add_left_comm] using
      ((_root_.summable_nat_add_iff 2 (f := f1)).2
        ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)))
  have htsum_shift2_le' : (∑' d : ℕ, f2 d) ≤ ∑' d : ℕ, f1 (d + 1) := by
    exact hsummable_shift2.tsum_le_tsum hpointwise hsummable_shift1
  have htsum_shift2_le : (∑' d : ℕ, f2 d) ≤ 2 := by
    exact le_trans htsum_shift2_le' htsum_shift1_le
  have hscaled : (∑' d : ℕ, 4 / (((d + 2 : ℕ) : ℝ) ^ 2)) ≤ 8 := by
    have hbase :
        (∑' d : ℕ, 4 / (((d + 2 : ℕ) : ℝ) ^ 2)) = 4 * (∑' d : ℕ, f2 d) := by
      simpa [f2, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_add_one_eq_two] using
        (tsum_mul_left (a := (4 : ℝ)) (f := f2))
    rw [hbase]
    nlinarith
  have hCrow :
      CrowOf (aPoly 4 2) = 4 + 2 * (∑' d : ℕ, 4 / (((d + 2 : ℕ) : ℝ) ^ 2)) := by
    simp [CrowOf, aPoly, div_eq_mul_inv, add_comm, add_left_comm, one_add_one_eq_two]
  rw [hCrow]
  nlinarith

/-- Concrete calibration inequality against the certified `C2` cap. -/
theorem crow_aPoly_four_two_three_le_C2 :
    (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ C2 := by
  have hMul : (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ 60 := by
    nlinarith [crow_aPoly_four_two_le_twenty]
  have hCap : (60 : ℝ) ≤ C2 := by
    norm_num [C2, Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data]
  exact le_trans hMul hCap

/-- Concrete calibration inequality against the certified `C3` cap. -/
theorem crow_aPoly_four_two_three_le_C3 :
    (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ C3 := by
  have hMul : (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ 60 := by
    nlinarith [crow_aPoly_four_two_le_twenty]
  have hCap : (60 : ℝ) ≤ C3 := by
    norm_num [C3, Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data]
  exact le_trans hMul hCap

/-- The concrete `(4,2,3,3)` route already satisfies the calibration target. -/
theorem calibrationTarget_four_two_three_three :
    CalibrationTarget 4 2 3 3 :=
  ⟨crow_aPoly_four_two_three_le_C2, crow_aPoly_four_two_three_le_C3⟩

/--
For the suggestion-box route, calibration is automatic: only the analytic inputs remain.
-/
theorem ledgerEngine_canon_of_band2_square3_raw1
    (hBand :
      Band2ShellOrthogonality Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon)
    (hSq :
      Q0MinorSquareFunctionControl Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 3)
    (hRaw :
      Q0MinorRawEnergyLedger Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 1 1) :
    Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger.Q0MinorEnergyLedgerEngine
      Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C2
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C3 := by
  have hCal : CalibrationTarget 4 2 3 3 := calibrationTarget_four_two_three_three
  have hDiag :=
    Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute.diagonalLedger_canon_three_of_square3_and_raw1
      hSq hRaw
  have hDy :
      Q0MinorDyadicGramDecayPoly Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 4 2 3 3 :=
    Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge.dyadicGramDecayPoly_canon_of_band2_and_diagonal3
      hBand hDiag
  have h :
      Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger.Q0MinorEnergyLedgerEngine
        Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon
        Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C2
        Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C3 :=
    ledgerEngine_of_dyadicPoly_and_calibration hDy hCal
  exact h

/-- Energy-bound corollary of the previous concrete calibrated route. -/
theorem energyBound16_canon_of_band2_square3_raw1
    (hBand :
      Band2ShellOrthogonality Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon)
    (hSq :
      Q0MinorSquareFunctionControl Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 3)
    (hRaw :
      Q0MinorRawEnergyLedger Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 1 1) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound
      Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon 16 :=
  energyBound16_of_ledger_engine (ledgerEngine_canon_of_band2_square3_raw1 hBand hSq hRaw)

end

end Goldbach.Cert.MajorArcModules.Q0MinorConcreteCalibration
