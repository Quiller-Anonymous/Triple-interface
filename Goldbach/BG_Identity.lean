/-
  Goldbach/BG_Identity.lean  — axiom-free scaffold

  Purpose:
    Provide a *formal* decomposition of errAO into four channels on the window.
    For now we keep E_off as our BG_Calib off-term (which is 0 with the current
    K_BG and P_BG), and we choose the other three placeholders so that the identity
    is definitional (no axioms needed).

  Later:
    Replace E_kernel/E_mellin/E_smooth by your actual channels and keep E_off.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Major          -- errAO
import Goldbach.BG_Bank
import Goldbach.BG_Operator
import Goldbach.BG_Calib

namespace Goldbach.BG_Identity

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.BG_Bank
open Goldbach.BG_Operator
open Real
open BigOperators
open Classical

/-- Off-channel from the calibrator (uses S_BG, K_BG, P_BG). -/
noncomputable def E_off (X N : ℕ) : ℝ :=
  BG_Calib.E_off S_BG K_BG P_BG X N

/-- Temporary choices for the other channels so that the identity is rfl. -/
noncomputable def E_kernel (X N : ℕ) : ℝ := 0
noncomputable def E_mellin (X N : ℕ) : ℝ := 0
noncomputable def E_smooth (X N : ℕ) : ℝ := AO_Major.errAO X N - E_off X N

/-- On the canonical window, errAO decomposes into four channels (definitionally). -/
theorem errAO_decomp_window :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    AO_Major.errAO X N
      = E_kernel X N + E_mellin X N + E_smooth X N + E_off X N := by
  intro X N _hX _hN
  unfold E_kernel E_mellin E_smooth E_off
  simp [BG_Calib.E_off, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

end Goldbach.BG_Identity
