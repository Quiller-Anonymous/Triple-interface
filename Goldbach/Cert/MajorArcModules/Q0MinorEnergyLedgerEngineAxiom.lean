import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
import Goldbach.Cert.MajorArcModules.Q0MinorCalibration
import Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
import Goldbach.Cert.MajorArcModules.Q0MinorToeplitzTarget
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Legacy calibration seam for ε₁ (minor / Q0-complement) in the turnkey `Q0` route.

This file formerly asserted calibration for every tuple satisfying
`Q0MinorDyadicGramDecayPoly`. That quantifier is inconsistent with the monotonicity of an
upper-bound witness: enlarging its constants preserves the dyadic bounds but eventually violates
the fixed calibration caps. The universal axiom has therefore been removed.

The surviving declarations make calibration an explicit input for the particular witness chosen
below. This module is retained at its old import path for compatibility; it is not an active Route A
closure provider.
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
noncomputable def ssu_minor_energy_calibratedDyadicGramDecayPoly
    (hCalibration :
      Q0MinorCalibrationBounds
        ssu_minor_energy_dyadic_polyWitness.C
        ssu_minor_energy_dyadic_polyWitness.p
        ssu_minor_energy_dyadic_polyWitness.C2raw
        ssu_minor_energy_dyadic_polyWitness.C3raw) :
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
  have hCal : Q0MinorCalibrationBounds C p C2raw C3raw := by
    simpa [w, C, p, C2raw, C3raw] using hCalibration
  exact calibratedDyadicGramDecayPoly_of_ttstar_and_calibration hTT hCal

/--
The turnkey-facing ledger engine, derived deterministically from the calibrated bridge witness.
-/
theorem ssu_minor_energy_ledger_engine :
    Q0MinorCalibrationBounds
        ssu_minor_energy_dyadic_polyWitness.C
        ssu_minor_energy_dyadic_polyWitness.p
        ssu_minor_energy_dyadic_polyWitness.C2raw
        ssu_minor_energy_dyadic_polyWitness.C3raw →
      Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
  fun hCalibration =>
  ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
    (ssu_minor_energy_calibratedDyadicGramDecayPoly hCalibration)

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom
