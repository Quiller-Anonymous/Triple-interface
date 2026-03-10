import Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
import Mathlib.Tactic

/-!
`Q0MinorBand2Bridge` packages a convenient conditional route:

If dyadic shells are orthogonal beyond distance `1` (`dist ≥ 2`) and a diagonal ledger bound is
available, then the TT* polynomial target follows with explicit constants `C = 4`, `p = 2`.

This isolates exactly the part of the `Suggestion Box` argument that is deterministic Hilbert-space
bookkeeping (Cauchy + distance split), without claiming the shell-orthogonality hypothesis itself.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Banded shell-orthogonality hypothesis: dyadic packets are orthogonal once shell distance is at
least `2`. -/
def Band2ShellOrthogonality (Δ : ℝ) : Prop :=
  ∀ {X : ℕ}, X0 ≤ X →
    ∀ i ∈ (JX X : Finset ℕ), ∀ j ∈ (JX X : Finset ℕ),
      2 ≤ Nat.dist i j →
        inner ℂ (dyadicV X Δ i) (dyadicV X Δ j) = 0

/--
`dist ≥ 2` orthogonality + diagonal ledger ⇒ TT* polynomial target with explicit constants
`(C, p) = (4, 2)`.
-/
theorem ttstarPolyDecay_of_band2_and_diagonal
    {Δ C2 C3 : ℝ}
    (hBand : Band2ShellOrthogonality Δ)
    (hDiag : Q0MinorDiagonalLedger Δ C2 C3) :
    Q0MinorTTStarPolyDecay Δ 4 2 C2 C3 := by
  refine ⟨by norm_num, by norm_num, hDiag.C2_nonneg, hDiag.C3_nonneg, ?_, hDiag.sumD_bound⟩
  intro X hX i hi j hj
  have hsqrt_i : Real.sqrt (dyadicD X Δ i) = ‖dyadicV X Δ i‖ := by
    simp [dyadicD]
  have hsqrt_j : Real.sqrt (dyadicD X Δ j) = ‖dyadicV X Δ j‖ := by
    simp [dyadicD]
  by_cases hfar : 2 ≤ Nat.dist i j
  · have hinner0 : inner ℂ (dyadicV X Δ i) (dyadicV X Δ j) = 0 :=
      hBand (X := X) hX i hi j hj hfar
    have hRHS_nonneg :
        0 ≤ aPoly 4 2 (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j) := by
      exact mul_nonneg (mul_nonneg (aPoly_nonneg (C := 4) (p := 2) (by norm_num) _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hInner :
        ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖
          ≤ aPoly 4 2 (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j) := by
      simpa [hinner0] using hRHS_nonneg
    simpa [inner_dyadicV_eq_dyadicGramSum] using hInner
  · have hnear : Nat.dist i j ≤ 1 := by omega
    have hfactor : 1 ≤ aPoly 4 2 (Nat.dist i j) := by
      interval_cases hdist : Nat.dist i j
      · norm_num [aPoly]
      · norm_num [aPoly]
    let t : ℝ := Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j)
    have hinner_le_t :
        ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖ ≤ t := by
      have hcs :
          ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖
            ≤ ‖dyadicV X Δ i‖ * ‖dyadicV X Δ j‖ :=
        norm_inner_le_norm _ _
      simpa [t, hsqrt_i, hsqrt_j] using hcs
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hscale : t ≤ aPoly 4 2 (Nat.dist i j) * t := by
      have := mul_le_mul_of_nonneg_right hfactor ht_nonneg
      simpa [one_mul] using this
    have hInner :
        ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖
          ≤ aPoly 4 2 (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j) := by
      have : ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖ ≤ aPoly 4 2 (Nat.dist i j) * t :=
        le_trans hinner_le_t hscale
      simpa [t, mul_assoc] using this
    simpa [inner_dyadicV_eq_dyadicGramSum] using hInner

/-- Band-2 orthogonality + diagonal ledger also gives the Goldbach-native dyadic polynomial
Gram-decay interface, with explicit `(C, p) = (4, 2)`. -/
theorem dyadicGramDecayPoly_of_band2_and_diagonal
    {Δ C2 C3 : ℝ}
    (hBand : Band2ShellOrthogonality Δ)
    (hDiag : Q0MinorDiagonalLedger Δ C2 C3) :
    Q0MinorDyadicGramDecayPoly Δ 4 2 C2 C3 :=
  to_Q0MinorDyadicGramDecayPoly (ttstarPolyDecay_of_band2_and_diagonal (Δ := Δ) hBand hDiag)

/--
Canonical instantiation of the previous theorem at `Δ = 1`, with the raw ledger constants
`C2raw = 3`, `C3raw = 3` used in the suggestion proof.
-/
theorem dyadicGramDecayPoly_canon_of_band2_and_diagonal3
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hDiag : Q0MinorDiagonalLedger Δ_canon 3 3) :
    Q0MinorDyadicGramDecayPoly Δ_canon 4 2 3 3 :=
  dyadicGramDecayPoly_of_band2_and_diagonal (Δ := Δ_canon) (C2 := 3) (C3 := 3) hBand hDiag

/--
Final bridge wrapper:
if band-2 shell orthogonality and the raw `3,3` diagonal ledger are proved analytically, then the
only remaining input is the two calibration inequalities against the certified constants.
-/
def calibratedDyadicGramDecayPoly_canon_of_band2_diagonal3_and_calibration
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hDiag : Q0MinorDiagonalLedger Δ_canon 3 3)
    (hC2cal : (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ C2)
    (hC3cal : (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ C3) :
    CalibratedDyadicGramDecayPoly :=
  ⟨4, 2, 3, 3, dyadicGramDecayPoly_canon_of_band2_and_diagonal3 hBand hDiag, hC2cal, hC3cal⟩

/-- Turnkey-facing ledger engine from the band-2 route plus calibration. -/
theorem ledgerEngine_canon_of_band2_diagonal3_and_calibration
    (hBand : Band2ShellOrthogonality Δ_canon)
    (hDiag : Q0MinorDiagonalLedger Δ_canon 3 3)
    (hC2cal : (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ C2)
    (hC3cal : (CrowOf (aPoly 4 2)) * (3 : ℝ) ≤ C3) :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
  ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
    (calibratedDyadicGramDecayPoly_canon_of_band2_diagonal3_and_calibration
      hBand hDiag hC2cal hC3cal)

end

end Goldbach.Cert.MajorArcModules.Q0MinorBand2Bridge
