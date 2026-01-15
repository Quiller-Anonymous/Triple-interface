import Goldbach.Cert.MajorArcCalibrationFunX
import Goldbach.Cert.TurnkeyMajorArcCanonSpec

/-!
Major arcs: canonical calibration datum (legacy name, now derived from the turnkey boundary).

Historically this file packaged a pinned power-saving calibration with an internal axiom
`majorArcBound_canon`.  The project is moving to a “turnkey” boundary instead:
`TurnkeyMajorArcCanon` is the exact on-window statement the pipeline needs.

To avoid churning downstream imports, we keep the same exported name
`MajorArcCanonCalibrationFromPinned.canonCalibration`, but it is now constructed from the turnkey
interface by choosing the trivial power-saving parameters `A=0`, `C=δ_major_canon`.
-/

namespace Goldbach.Cert
namespace MajorArcCanonCalibrationFromPinned

open Goldbach.BankParams
open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcCalibrationFunX

noncomputable section

def A_canon : ℕ := 0
def C_canon : ℝ := δ_major_canon

lemma C_canon_nonneg : 0 ≤ C_canon := by
  norm_num [C_canon, δ_major_canon]

lemma majorArcBound_canon :
    MajorArcBound (fun X => C_canon / (Real.log (X : ℝ)) ^ A_canon) := by
  intro X N hX hN
  -- `C/(log X)^0 = C` and the turnkey axiom gives `|RΛ_smooth-RΛ_model| ≤ δ_major_canon`.
  simpa [A_canon, C_canon] using
    (Goldbach.Cert.TurnkeyMajorArcCanonSpec.turnkeyMajorArcCanon.major_arc_eval_on_window_canon
      (X := X) (N := N) hX hN)

lemma cal_at_X0_canon :
    C_canon / (Real.log (X0 : ℝ)) ^ A_canon ≤ δ_major_canon := by
  simp [A_canon, C_canon]

noncomputable def canonCalibration : CanonicalCalibration :=
  mkCanonicalCalibration
    (A := A_canon)
    (C := C_canon)
    C_canon_nonneg
    majorArcBound_canon
    cal_at_X0_canon

end

end MajorArcCanonCalibrationFromPinned
end Goldbach.Cert

