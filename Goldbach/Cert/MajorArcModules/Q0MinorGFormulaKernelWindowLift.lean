import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaKernelPointwise

/-!
Pure finite-sum lift of the pointwise geometric Route A kernel comparison.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private lemma sum_mem_le_sum_mem_of_pointwise_le
    (s : Finset ℕ) (f g : ℕ → ℝ)
    (hfg : ∀ n ∈ s, f n ≤ g n) :
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, g n := by
  refine Finset.sum_le_sum ?_
  intro n hn
  exact hfg n hn

theorem gFormulaCoreWindowEnergy_le_sum_kernelParityWindowPointwiseConst
    {X : ℕ} (hX : X0 ≤ X) :
    gFormulaCoreWindowEnergy X
      ≤
    ∑ N ∈ EvenIn X H, kernelParityWindowPointwiseConst X := by
  unfold gFormulaCoreWindowEnergy
  exact sum_mem_le_sum_mem_of_pointwise_le
    (EvenIn X H)
    (fun N => gFormulaCorePointwiseEnergy X N)
    (fun _ => kernelParityWindowPointwiseConst X)
    (fun N hN => gFormulaCorePointwiseEnergy_le_kernelParityWindowPointwiseConst hX hN)

end

end Q0MinorGFormulaRouteA
