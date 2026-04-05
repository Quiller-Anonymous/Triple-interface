import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelWindowLift

/-!
Constant-collapse wrapper for the geometric Route A kernel window bound.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private lemma sum_mem_const_eq_card_mul
    (s : Finset ℕ) (c : ℝ) :
    (∑ n ∈ s, c) = (s.card : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]

theorem gFormulaCoreWindowEnergy_le_kernelParityWindow
    {X : ℕ} (hX : X0 ≤ X) :
    gFormulaCoreWindowEnergy X
      ≤
    ((EvenIn X H).card : ℝ) * kernelParityWindowPointwiseConst X := by
  exact le_trans
    (gFormulaCoreWindowEnergy_le_sum_kernelParityWindowPointwiseConst (X := X) hX)
    (by simpa using (sum_mem_const_eq_card_mul (EvenIn X H) (kernelParityWindowPointwiseConst X)).le)

end

end Q0MinorGFormulaRouteA
