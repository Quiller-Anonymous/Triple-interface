import Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncEnergyTarget
import Goldbach.Cert.MajorArcModules.Q0SigmaTruncUniformBudget
import Goldbach.Cert.MajorArcModules.C2RamanujanEulerProduct
import Goldbach.Cert.MajorArcModules.EvenWindowReindex
import Goldbach.Cert.MajorArcModules.NormalizedRealWindowEnergy

/-!
Uniform centered energy of the canonical fixed-`Q0` truncation.
The proof uses exact finite divisor moments and the discrepancy of integer divisibility
on an arbitrary interval. It does not use the generated certificate at `X0`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncUniform

open scoped BigOperators
open Goldbach.BankParams Goldbach.Windows
open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.AO_OffDiag.TailBlock
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncRawEnergy
open Goldbach.Cert.MajorArcModules.C2RamanujanEulerProduct
open Goldbach.Cert.MajorArcModules.EvenWindowReindex
open Goldbach.Cert.MajorArcModules.NormalizedRealWindowEnergy

/-- The normalized energy bound holds for every canonical window, not just at `X0`. -/
theorem centeredNormalizedSigmaTruncWindowEnergy_lt_1795
    {X : ℕ} (hX : X0 ≤ X) : centeredNormalizedSigmaTruncWindowEnergy X < 1795 := by
  have hc : (33 : ℝ) / 25 < 2 * ramanujanSeriesOnWindow.C.C2 := by
    have hC := ramanujanSeriesOnWindow_C2_gt_33_50
    linarith
  exact Q0SigmaTruncUniformBudget.normalized_truncation_energy_lt_1795 hX _ hc

/-- A uniform replacement for the pinned truncation-energy theorem. -/
theorem centeredNormalizedSigmaTruncWindowEnergyTarget_1795 :
    CenteredNormalizedSigmaTruncWindowEnergyTarget 1795 :=
  ⟨by norm_num, fun hX => (centeredNormalizedSigmaTruncWindowEnergy_lt_1795 hX).le⟩

end Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncUniform
