/-
  Goldbach/BG_Operator.lean  — axiom-free scaffold

  What this file provides now:
    • K_BG           : ℤ → ℝ      (BG kernel)
    • kernel_l1_cap  : ℝ
    • kernel_l1_nonneg
    • kernel_l1_bound  : ∑_{k∈S_BG} |K_BG k| ≤ kernel_l1_cap

  Temporary choice:
    K_BG ≡ 0, so the L¹ bound holds with cap 0. Replace with your Tenor kernel later.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.BG_Bank

namespace Goldbach.BG_Operator

open Goldbach
open Goldbach.BankParams
open Goldbach.BG_Bank
open Real
open BigOperators
open Classical

/-- BG kernel (temporary: zero; replace by the Tenor kernel later). -/
noncomputable def K_BG : ℤ → ℝ := fun _ => 0

/-- Temporary L¹ cap for the kernel. -/
noncomputable def kernel_l1_cap : ℝ := 0

lemma kernel_l1_nonneg : 0 ≤ kernel_l1_cap := by
  simp [kernel_l1_cap]

/-- Sum of |K_BG| on S_BG is bounded by the cap (trivial now since K_BG ≡ 0). -/
lemma kernel_l1_bound :
  (∑ k in S_BG, |K_BG k|) ≤ kernel_l1_cap := by
  simp [S_BG, K_BG, kernel_l1_cap]

end Goldbach.BG_Operator
