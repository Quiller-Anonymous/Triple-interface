/-
  Goldbach/AO_KernelTail.lean
  Kernel tail (H → ∞) bound for the AO model.

  We *identify* the AO kernel tail with the bank type-I tail `errTI`:
    E_kernel X N := errTI X N
  and use the proved lemma `errTI_bound_closed`.
-/
import Goldbach.BG_Identity
import Goldbach.BG_Bank
import Goldbach.Windows

namespace Goldbach.AO_KernelTail

open Real Goldbach Goldbach.Windows

/-- AO kernel tail: we take it to be exactly the bank type-I tail. -/
noncomputable def E_kernel (X N : ℕ) : ℝ :=
  BG_Identity.errTI X N

lemma E_kernel_congr_X (X₁ X₂ N : ℕ) : E_kernel X₁ N = E_kernel X₂ N := by
  -- All `X`-dependence is syntactic (via `wX`) and cancels definitionally.
  simp [E_kernel, Goldbach.BG_Identity.errTI, Goldbach.BG_Bank.P_BG, Goldbach.BG_Bank.wX]

/-- **Kernel tail bound** (no axioms): closed-form tail mass × payload cap. -/
theorem E_kernel_bound
  {X N : ℕ} (hX : BG_Bank.X0 ≤ X) (hN : N ∈ EvenIn X BG_Bank.H) :
  |E_kernel X N| ≤ BG_Bank.payload_cap X N * BG_Identity.C_tail_closed := by
  -- This *is* your proved tail bound.
  simpa [E_kernel] using
    BG_Identity.errTI_bound_closed (X:=X) (N:=N) hX hN

end Goldbach.AO_KernelTail
