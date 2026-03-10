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
noncomputable def E_kernel (_X N : ℕ) : ℝ :=
  -- We pin the bank-scale parameter to `N` so that (on the AO main track) this term is
  -- definitionally independent of the ambient AO scale `X`.
  BG_Identity.errTI N N

lemma E_kernel_congr_X (X₁ X₂ N : ℕ) : E_kernel X₁ N = E_kernel X₂ N := by
  rfl

/-- **Kernel tail bound** (no axioms): closed-form tail mass × payload cap. -/
theorem E_kernel_bound
  {X N : ℕ} (hX : BG_Bank.X0 ≤ X) (hN : N ∈ EvenIn X BG_Bank.H) :
  |E_kernel X N| ≤ BG_Bank.payload_cap X N * BG_Identity.C_tail_closed := by
  -- Apply the bank tail bound at scale `X := N`, and then rewrite `payload_cap` (it ignores `X`).
  have hXN : BG_Bank.X0 ≤ N := by
    have hNX : X ≤ N := by
      -- Unpack `N ∈ EvenIn X H` as `∃ k ≤ H, N = X + k`.
      have hIn : N ∈ Goldbach.Windows.IccShift X BG_Bank.H := (Finset.mem_filter.mp hN).1
      rcases Finset.mem_image.mp hIn with ⟨k, hk, rfl⟩
      exact Nat.le_add_right X k
    exact le_trans hX hNX
  have hEven : Goldbach.Windows.IsEven N := (Finset.mem_filter.mp hN).2
  have hNmem : N ∈ EvenIn N BG_Bank.H :=
    Goldbach.Windows.mem_EvenIn_self (N := N) (H := BG_Bank.H) hEven
  simpa [E_kernel, BG_Bank.payload_cap] using
    (BG_Identity.errTI_bound_closed (X := N) (N := N) hXN hNmem)

theorem E_kernel_bound_relative
  {X N : ℕ} (hX : BG_Bank.X0 ≤ X) (hN : N ∈ EvenIn X BG_Bank.H) :
  |E_kernel X N|
    ≤ Goldbach.AO_WeightMass.weight_mass N
        * (BG_Bank.payload_cap X N * BG_Identity.C_tail_closed) := by
  have hXN : BG_Bank.X0 ≤ N := by
    have hNX : X ≤ N := by
      have hIn : N ∈ Goldbach.Windows.IccShift X BG_Bank.H := (Finset.mem_filter.mp hN).1
      rcases Finset.mem_image.mp hIn with ⟨k, hk, rfl⟩
      exact Nat.le_add_right X k
    exact le_trans hX hNX
  have hEven : Goldbach.Windows.IsEven N := (Finset.mem_filter.mp hN).2
  have hNmem : N ∈ EvenIn N BG_Bank.H :=
    Goldbach.Windows.mem_EvenIn_self (N := N) (H := BG_Bank.H) hEven
  simpa [E_kernel, BG_Bank.payload_cap, Goldbach.AO_WeightMass.weight_mass,
    mul_assoc, mul_left_comm, mul_comm] using
    (BG_Identity.errTI_bound_closed_wScale_sq (X := N) (N := N) hXN hNmem)

end Goldbach.AO_KernelTail
