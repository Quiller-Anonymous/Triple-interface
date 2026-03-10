import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
import Goldbach.Cert.MajorArcModules.Q0MinorCalibration
import Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
import Goldbach.Cert.MajorArcModules.Q0MinorToeplitzTarget
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Tool-axiom seam for ε₁ (minor / Q0-complement) in the turnkey `Q0` route.

This isolates the remaining analytic input needed by the *certificate glue*
`Q0MinorEnergyFromLedgerCert`, at the calibrated dyadic-bridge layer.

Polished-gold policy: this should eventually be discharged in-repo from the SSU/interzone
lever-bundle machinery (possibly still assuming project-neutral SSU tool axioms).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.Q0MinorCalibration
open Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorToeplitzTarget
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Concrete constants and dyadic polynomial-decay proof at `Δ_canon`. -/
structure DyadicPolyWitness where
  C : ℝ
  p : ℕ
  C2raw : ℝ
  C3raw : ℝ
  hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw

/-- Concrete constants and diagonal ledger proof at `Δ_canon`. -/
structure DiagonalLedgerWitness where
  C2raw : ℝ
  C3raw : ℝ
  hDiag : Q0MinorDiagonalLedger Δ_canon C2raw C3raw

/--
Project-neutral dyadic polynomial Gram-decay witness at `Δ_canon`.

This comes from the conventional dyadic existence axiom, and provides the raw constants and
packet-decay estimates used in Steps 1 and 2.
-/
noncomputable def ssu_minor_energy_dyadic_polyWitness :
    DyadicPolyWitness := by
  let hEx := q0MinorDyadicGramDecayPoly_exists (Δ := Δ_canon)
  let C : ℝ := Classical.choose hEx
  let hEx1 : ∃ p : ℕ, ∃ C2raw : ℝ, ∃ C3raw : ℝ,
      Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw := Classical.choose_spec hEx
  let p : ℕ := Classical.choose hEx1
  let hEx2 : ∃ C2raw : ℝ, ∃ C3raw : ℝ,
      Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw := Classical.choose_spec hEx1
  let C2raw : ℝ := Classical.choose hEx2
  let hEx3 : ∃ C3raw : ℝ,
      Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw := Classical.choose_spec hEx2
  let C3raw : ℝ := Classical.choose hEx3
  let hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw := Classical.choose_spec hEx3
  exact ⟨C, p, C2raw, C3raw, hDy⟩

/--
Step 3 seam (numeric calibration):
connect the Step-1/Step-2 constants to certified caps `C2,C3`.
-/
axiom ssu_minor_energy_calibration
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw) :
    Q0MinorCalibrationBounds C p C2raw C3raw

/--
Derived TT* package from Step-1 and Step-2 seam witnesses.
-/
theorem ssu_minor_energy_ttstar_polyDecay :
    ∃ (C : ℝ) (p : ℕ) (C2raw C3raw : ℝ),
      Q0MinorTTStarAnalyticTarget.Q0MinorTTStarPolyDecay Δ_canon C p C2raw C3raw := by
  let w := ssu_minor_energy_dyadic_polyWitness
  let C : ℝ := w.C
  let p : ℕ := w.p
  let C2raw : ℝ := w.C2raw
  let C3raw : ℝ := w.C3raw
  let hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw := w.hDy
  refine ⟨C, p, C2raw, C3raw, ?_⟩
  refine ⟨hDy.C_nonneg, hDy.p_gt_one, hDy.C2_nonneg, hDy.C3_nonneg, ?_, hDy.sumD_bound⟩
  intro X hX i hi j hj
  have hInner := hDy.gram_bound (X := X) hX i hi j hj
  simpa [Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar.inner_dyadicV_eq_dyadicGramSum]
    using hInner

/--
Remaining bridge witness, now derived from explicit Step-1/2/3 seam obligations.
-/
noncomputable def ssu_minor_energy_calibratedDyadicGramDecayPoly :
    CalibratedDyadicGramDecayPoly := by
  let w := ssu_minor_energy_dyadic_polyWitness
  let C : ℝ := w.C
  let p : ℕ := w.p
  let C2raw : ℝ := w.C2raw
  let C3raw : ℝ := w.C3raw
  let hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw := w.hDy
  have hTT :
      Q0MinorTTStarAnalyticTarget.Q0MinorTTStarPolyDecay Δ_canon C p C2raw C3raw :=
    by
      refine ⟨hDy.C_nonneg, hDy.p_gt_one, hDy.C2_nonneg, hDy.C3_nonneg, ?_, hDy.sumD_bound⟩
      intro X hX i hi j hj
      have hInner := hDy.gram_bound (X := X) hX i hi j hj
      simpa [Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar.inner_dyadicV_eq_dyadicGramSum]
        using hInner
  have hCal : Q0MinorCalibrationBounds C p C2raw C3raw :=
    ssu_minor_energy_calibration hDy
  exact calibratedDyadicGramDecayPoly_of_ttstar_and_calibration hTT hCal

/--
The turnkey-facing ledger engine, derived deterministically from the calibrated bridge witness.
-/
theorem ssu_minor_energy_ledger_engine :
  Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
  ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
    ssu_minor_energy_calibratedDyadicGramDecayPoly

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom
