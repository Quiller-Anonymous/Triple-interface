import Goldbach.Cert.MajorArcInputsFunX

/-!
Derivations for the major-arc bound (FunX track).

Step 4.2 in the “hard step” plan: connect the orthodox input interface
`Goldbach.Cert.MajorArcInputsFunX` to the target major-arc bound shape
`Goldbach.Cert.MajorArcAxiomsFunX.MajorArcPowerSaving`.

At this stage, the derivation is just interface plumbing (no analytic work yet): we expose
the power-saving statement carried by the interface in the exact form used by
`Goldbach.Cert.MajorArcAxiomsFunX`.
-/

namespace Goldbach.Cert.MajorArcDeriveFunX

open Goldbach.Cert

theorem majorArcPowerSaving_of_inputs
    (h : Goldbach.Cert.MajorArcInputsFunX.MajorArcCore) :
    Goldbach.Cert.MajorArcAxiomsFunX.MajorArcPowerSaving :=
  h.majorArc_powerSaving

theorem majorArcPowerSaving_of_inputs_withSW
    (h : Goldbach.Cert.MajorArcInputsFunX.MajorArcWithSW) :
    Goldbach.Cert.MajorArcAxiomsFunX.MajorArcPowerSaving :=
  h.majorArc_powerSaving

/-- Convenience: extract a single-exponent `C/(log X)^A` bound from the inputs. -/
theorem majorArcBound_of_inputs
    (A : ℕ) (h : Goldbach.Cert.MajorArcInputsFunX.MajorArcCore) :
    ∃ C : ℝ, 0 ≤ C ∧
      Goldbach.Cert.MajorArcAxiomsFunX.MajorArcBound
        (fun X => C / (Real.log (X : ℝ)) ^ A) :=
  Goldbach.Cert.MajorArcAxiomsFunX.majorArcBound_of_powerSaving A h.majorArc_powerSaving

end Goldbach.Cert.MajorArcDeriveFunX

