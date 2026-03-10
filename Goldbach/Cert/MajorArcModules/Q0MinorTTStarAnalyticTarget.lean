import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar
import Goldbach.Cert.MajorArcModules.Q0MinorSSUTarget

/-!
`Q0MinorTTStarAnalyticTarget` isolates the *post-TT** analytic payload for `ε₁`.

The deterministic pieces are already in-repo:

* dyadic packets `dyadicV`, `dyadicD`;
* TT* expansion `inner_dyadicV_eq_dyadicGramSum`;
* SSU-facing reduction from packet Gram/diag bounds to the Goldbach bridge target.

What remains is therefore the analytic proof of:

* a polynomial bound for the TT* Gram sum `dyadicGramSum`;
* the diagonal ledger bound `∑ dyadicD`.

This file packages exactly that interface and proves that it is sufficient to discharge the
current `ε₁` SSU bridge, up to the final numeric Crow calibration.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
TT* analytic target for the `ε₁` seam:

prove a polynomial bound for the explicit Gram sum, and prove the diagonal packet-energy ledger.
-/
structure Q0MinorTTStarPolyDecay
    (Δ : ℝ) (C : ℝ) (p : ℕ) (C2 C3 : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  p_gt_one : 1 < p
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  gramSum_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ i ∈ (JX X : Finset ℕ), ∀ j ∈ (JX X : Finset ℕ),
        ‖dyadicGramSum (X := X) (Δ := Δ) i j‖
          ≤ aPoly C p (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j)
  sumD_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j)
        ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) ^ 2)

/--
TT* Gram-sum control immediately upgrades to the Goldbach-native dyadic Gram-decay interface,
because `inner_dyadicV_eq_dyadicGramSum` is already proved.
-/
theorem to_Q0MinorDyadicGramDecayPoly
    {Δ : ℝ} {C : ℝ} {p : ℕ} {C2 C3 : ℝ}
    (h : Q0MinorTTStarPolyDecay Δ C p C2 C3) :
    Q0MinorDyadicGramDecayPoly Δ C p C2 C3 := by
  refine ⟨h.C_nonneg, h.p_gt_one, h.C2_nonneg, h.C3_nonneg, ?_, ?_⟩
  · intro X hX i hi j hj
    have hGram :=
      h.gramSum_bound (X := X) hX i hi j hj
    simpa [inner_dyadicV_eq_dyadicGramSum] using hGram
  · intro X hX
    simpa using h.sumD_bound (X := X) hX

/--
At the canonical width `Δ_canon`, TT* analytic control plus numeric calibration discharges the
current SSU bridge target exactly.
-/
def calibratedDyadicGramDecayPoly_of_ttstar
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (h : Q0MinorTTStarPolyDecay Δ_canon C p C2raw C3raw)
    (hC2cal : (CrowOf (aPoly C p)) * C2raw ≤ Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C2)
    (hC3cal : (CrowOf (aPoly C p)) * C3raw ≤ Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert.C3) :
    CalibratedDyadicGramDecayPoly := by
  refine ⟨C, p, C2raw, C3raw, ?_, hC2cal, hC3cal⟩
  exact to_Q0MinorDyadicGramDecayPoly h

end

end Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget
