import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelPrefactor

/-!
Pointwise geometric Route A kernel comparison for the frozen witness `G_formula`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private lemma kernelMassNZEven_upper_routeA_nonneg (X : ℕ) :
    0 ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X := by
  have hcore_nonneg : 0 ≤ Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore := by
    rw [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCore_eq_collapsed]
    dsimp [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCoreCollapsed]
    positivity
  rw [Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA]
  positivity

private lemma kernelMassNZOdd_upper_routeA_nonneg (X : ℕ) :
    0 ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X := by
  have hcore_nonneg : 0 ≤ Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore := by
    rw [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCore_eq_collapsed]
    dsimp [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCoreCollapsed]
    positivity
  rw [Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA]
  positivity

noncomputable def kernelParityWindowPointwiseConst (X : ℕ) : ℝ :=
  Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
    + Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X

private noncomputable def rawParityKernelExpr (X : ℕ) : ℝ :=
  ‖uniformWindowNormalization X‖ ^ 4
    * ((Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
          * geometricWindowParityMassEvenConst)
        +
        (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
          * geometricWindowParityMassOddConst))

private noncomputable def scaledParityKernelExpr (X : ℕ) : ℝ :=
  ‖uniformWindowNormalization X‖ ^ 4
    * (kernelParityWindowPointwiseConst X
        * (geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst))

private lemma gFormulaCorePointwiseEnergy_le_rawParityKernelExpr
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    gFormulaCorePointwiseEnergy X N ≤ rawParityKernelExpr X := by
  simpa [rawParityKernelExpr] using gFormulaCorePointwiseEnergy_le_routeAWindowConst hX hN

private lemma rawParityKernelExpr_le_scaledParityKernelExpr
    {X : ℕ} :
    rawParityKernelExpr X ≤ scaledParityKernelExpr X := by
  have hEvenConst_nonneg : 0 ≤ geometricWindowParityMassEvenConst := by
    norm_num [geometricWindowParityMassEvenConst, H]
  have hOddConst_nonneg : 0 ≤ geometricWindowParityMassOddConst := by
    norm_num [geometricWindowParityMassOddConst, H]
  have hKernelEven_nonneg :
      0 ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X :=
    kernelMassNZEven_upper_routeA_nonneg X
  have hKernelOdd_nonneg :
      0 ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X :=
    kernelMassNZOdd_upper_routeA_nonneg X
  have hInner :
      (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
          * geometricWindowParityMassEvenConst)
        +
      (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
          * geometricWindowParityMassOddConst)
      ≤
      kernelParityWindowPointwiseConst X
        * (geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst) := by
    dsimp [kernelParityWindowPointwiseConst]
    nlinarith
  exact mul_le_mul_of_nonneg_left hInner (by positivity)

private lemma scaledParityKernelExpr_le_kernelParityWindowPointwiseConst
    {X : ℕ} (hX : X0 ≤ X) :
    scaledParityKernelExpr X ≤ kernelParityWindowPointwiseConst X := by
  have hKernelEven_nonneg :
      0 ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X :=
    kernelMassNZEven_upper_routeA_nonneg X
  have hKernelOdd_nonneg :
      0 ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X :=
    kernelMassNZOdd_upper_routeA_nonneg X
  have hPrefMul :
      ‖uniformWindowNormalization X‖ ^ 4
        * (geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst)
        * kernelParityWindowPointwiseConst X
      ≤
      kernelParityWindowPointwiseConst X := by
    have hPref := uniformWindowParityPrefactor_le_one (X := X) hX
    have hKernel_nonneg : 0 ≤ kernelParityWindowPointwiseConst X := by
      dsimp [kernelParityWindowPointwiseConst]
      exact add_nonneg hKernelEven_nonneg hKernelOdd_nonneg
    have :=
      mul_le_mul_of_nonneg_right hPref hKernel_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  simpa [scaledParityKernelExpr, mul_assoc, mul_left_comm, mul_comm] using hPrefMul

theorem gFormulaCorePointwiseEnergy_le_kernelParityWindowPointwiseConst
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    gFormulaCorePointwiseEnergy X N ≤ kernelParityWindowPointwiseConst X := by
  exact le_trans
    (gFormulaCorePointwiseEnergy_le_rawParityKernelExpr hX hN)
    (le_trans
      (rawParityKernelExpr_le_scaledParityKernelExpr (X := X))
      (scaledParityKernelExpr_le_kernelParityWindowPointwiseConst (X := X) hX))

end

end Q0MinorGFormulaRouteA
