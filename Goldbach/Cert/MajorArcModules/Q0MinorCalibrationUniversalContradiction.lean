import Goldbach.Cert.MajorArcModules.Q0MinorCalibration
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms

/-!
# Audit of the retired universal Q0 calibration claim

The legacy calibration seam asserted `Q0MinorCalibrationBounds` for every tuple satisfying
`Q0MinorDyadicGramDecayPoly`. This file does not reintroduce that axiom. Instead it names the old
claim as a proposition and proves that it contradicts the existing dyadic-existence axiom.

The contradiction is monotonic. Starting from any dyadic witness, increase the Gram constant by
one and the raw diagonal constant by 161. Both are upper-bound constants, so the enlarged tuple is
still a dyadic witness. Its Crow factor is at least one and its raw constant is at least 161, while
the fixed certificate cap is 160.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorCalibrationUniversalContradiction

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorCalibration
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Exact proposition formerly asserted by `ssu_minor_energy_calibration`. -/
def LegacyUniversalCalibration : Prop :=
  ∀ {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ},
    Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw →
      Q0MinorCalibrationBounds C p C2raw C3raw

private theorem enlarge_dyadic_witness
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw) :
    Q0MinorDyadicGramDecayPoly Δ_canon (C + 1) p (C2raw + 161) C3raw := by
  refine
    { C_nonneg := by linarith [hDy.C_nonneg]
      p_gt_one := hDy.p_gt_one
      C2_nonneg := by linarith [hDy.C2_nonneg]
      C3_nonneg := hDy.C3_nonneg
      gram_bound := ?_
      sumD_bound := ?_ }
  · intro X hX i hi j hj
    have hold := hDy.gram_bound (X := X) hX i hi j hj
    have hden : 0 < (((Nat.dist i j : ℝ) + 1) ^ p) := by positivity
    have ha : aPoly C p (Nat.dist i j) ≤ aPoly (C + 1) p (Nat.dist i j) := by
      unfold aPoly
      exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
    calc
      ‖inner ℂ (dyadicV X Δ_canon i) (dyadicV X Δ_canon j)‖
          ≤ aPoly C p (Nat.dist i j) * Real.sqrt (dyadicD X Δ_canon i) *
              Real.sqrt (dyadicD X Δ_canon j) := hold
      _ ≤ aPoly (C + 1) p (Nat.dist i j) * Real.sqrt (dyadicD X Δ_canon i) *
              Real.sqrt (dyadicD X Δ_canon j) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · intro X hX
    have hold := hDy.sumD_bound (X := X) hX
    have hscale : 0 ≤ (H : ℝ) / (X : ℝ) := by positivity
    calc
      ∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ_canon j
          ≤ C2raw * ((H : ℝ) / (X : ℝ)) +
              C3raw / ((H : ℝ) *
                (Q0MinorInterzoneDyadicConventionalAxioms.Q0 : ℝ) ^ 2) := hold
      _ ≤ (C2raw + 161) * ((H : ℝ) / (X : ℝ)) +
              C3raw / ((H : ℝ) *
                (Q0MinorInterzoneDyadicConventionalAxioms.Q0 : ℝ) ^ 2) := by
            nlinarith

private theorem one_le_enlarged_crow
    {C : ℝ} {p : ℕ} (hC : 0 ≤ C) :
    1 ≤ CrowOf (aPoly (C + 1) p) := by
  have hnonneg : ∀ d : ℕ, 0 ≤ aPoly (C + 1) p d :=
    aPoly_nonneg (C := C + 1) (p := p) (by linarith)
  have htail : 0 ≤ ∑' d : ℕ, aPoly (C + 1) p (d + 1) :=
    tsum_nonneg (fun d => hnonneg (d + 1))
  calc
    (1 : ℝ) ≤ C + 1 := by linarith
    _ = aPoly (C + 1) p 0 := by simp [aPoly]
    _ ≤ CrowOf (aPoly (C + 1) p) := by
      unfold CrowOf
      linarith

/-- The retired universal calibration claim is inconsistent with dyadic witness existence. -/
theorem legacy_universal_calibration_inconsistent
    (hUniversal : LegacyUniversalCalibration) : False := by
  rcases q0MinorDyadicGramDecayPoly_exists (Δ := Δ_canon) with
    ⟨C, p, C2raw, C3raw, hDy⟩
  have hDy' := enlarge_dyadic_witness hDy
  have hCal := hUniversal hDy'
  have hCrow : 1 ≤ CrowOf (aPoly (C + 1) p) :=
    one_le_enlarged_crow hDy.C_nonneg
  have hRaw : (161 : ℝ) ≤ C2raw + 161 := by linarith [hDy.C2_nonneg]
  have hProduct :
      (161 : ℝ) ≤ CrowOf (aPoly (C + 1) p) * (C2raw + 161) := by
    calc
      (161 : ℝ) = 1 * 161 := by ring
      _ ≤ CrowOf (aPoly (C + 1) p) * (C2raw + 161) := by
        exact mul_le_mul hCrow hRaw (by norm_num) (by linarith)
  have hCap := hCal.hC2cal
  norm_num [Q0MinorEnergyFromLedgerCert.C2,
    Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data] at hCap
  linarith

end

end Goldbach.Cert.MajorArcModules.Q0MinorCalibrationUniversalContradiction
