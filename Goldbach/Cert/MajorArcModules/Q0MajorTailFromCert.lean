import Goldbach.Cert.MajorArcModules.Q0MajorTailCertData
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar

/-!
Convenience wrapper: instantiate the ε₂ large-β tail bound from the generated ℚ certificate.

This file exposes the certified constants as `ℝ` and provides a one-line “if you give me the
analytic inner bound, the large-β tail is discharged” lemma.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert

open Goldbach.Cert.MajorArcModules.Q0MajorTailCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailCertData
open Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar

noncomputable section

noncomputable abbrev M2 : ℝ := (data.M2 : ℝ)
noncomputable abbrev εl : ℝ := (data.εl : ℝ)

theorem q0MajorLargeBound_of_innerMajorQ0_energy
    {Δ : ℝ} (hInner : Q0InnerMajorLargeBetaEnergyBound Δ M2) :
    Q0MajorLargeBound Δ εl :=
  Data.q0MajorLargeBound_of_innerMajorQ0_energy_of_valid (Δ := Δ) (d := data) hInner data_valid

theorem q0MajorLargeBound_of_innerMajorQ0_ttstar
    {Δ : ℝ} (hInner : Q0InnerMajorLargeBetaTTStarBound Δ M2) :
    Q0MajorLargeBound Δ εl :=
  q0MajorLargeBound_of_innerMajorQ0_energy (Δ := Δ) (hInner := hInner.to_energyBound)

theorem q0MajorLargeBound_of_innerMajorQ0_full_ttstar
    {Δ : ℝ} (hInner : Q0InnerMajorFullTTStarBound Δ M2) :
    Q0MajorLargeBound Δ εl :=
  q0MajorLargeBound_of_innerMajorQ0_ttstar (Δ := Δ) (hInner := hInner.to_tailTTStarBound)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert
