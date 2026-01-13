import Goldbach.Cert.MajorArcCalibrationFunX
import Goldbach.Cert.CanonLogBounds

/-!
Major arcs: canonical calibration certificate datum (pinned-window boundary).

This file is the single **project-specific** boundary for the canonical major-arc evaluation:
it provides a `CanonicalCalibration` datum that yields the pinned cap `δ_major_canon` on the pinned
window.

Intended replacement (gold-grade): prove/verify `canonCalibration` from explicit in-repo estimates
or from a checkable numerical certificate, and keep downstream imports unchanged.

-/

namespace Goldbach.Cert
namespace MajorArcCanonCalibrationFromPinned

open Goldbach.BankParams
open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcCalibrationFunX

noncomputable section

/-!
Canonical calibration datum for the pinned major-arc cap `δ_major_canon`.

This file packages a small “certificate interface”:

1. an explicit single-exponent major-arc bound `C/(log X)^A` on the window, and
2. a single numeric inequality at `X0` upgrading that bound to the pinned cap `δ_major_canon`
   (the monotonicity step is proved in `MajorArcCalibrationFunX.cal_from_X0`).

We fix a conservative explicit exponent/constant pair `(A_canon, C_canon)` and *prove* the
calibration inequality at `X0` from a coarse lower bound `10 ≤ log X0`.

The remaining missing piece is the analytic statement `majorArcBound_canon` at these explicit
parameters.
-/

def A_canon : ℕ := 7
def C_canon : ℝ := 100

lemma C_canon_nonneg : 0 ≤ C_canon := by
  norm_num [C_canon]

axiom majorArcBound_canon :
  MajorArcBound (fun X => C_canon / (Real.log (X : ℝ)) ^ A_canon)

lemma cal_at_X0_canon :
    C_canon / (Real.log (X0 : ℝ)) ^ A_canon ≤ δ_major_canon := by
  have hC : 0 ≤ C_canon := C_canon_nonneg
  have hlog : (10 : ℝ) ≤ Real.log (X0 : ℝ) := Goldbach.Cert.CanonLogBounds.ten_le_log_X0
  have h10pos : 0 < (10 : ℝ) := by norm_num
  have hpow_le : (10 : ℝ) ^ A_canon ≤ (Real.log (X0 : ℝ)) ^ A_canon :=
    pow_le_pow_left₀ (le_of_lt h10pos) hlog A_canon
  have hfrac_le :
      C_canon / (Real.log (X0 : ℝ)) ^ A_canon ≤ C_canon / (10 : ℝ) ^ A_canon :=
    div_le_div_of_nonneg_left hC (pow_pos h10pos _) hpow_le
  have hnum : C_canon / (10 : ℝ) ^ A_canon ≤ δ_major_canon := by
    -- `100 / 10^7 ≤ 6e-5`.
    norm_num [C_canon, A_canon, δ_major_canon]
  exact le_trans hfrac_le hnum

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
