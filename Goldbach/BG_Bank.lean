/-
  Goldbach/BG_Bank.lean  — axiom-free scaffold

  What this file provides now:
    • S_BG  : Finset ℤ     (bank support)
    • P_BG  : ℕ → ℕ → ℤ → ℝ (BG payload)
    • payload_linf_cap, payload_linf_nonneg, payload_linf_bound  (proved)

  Temporary choice:
    P_BG ≡ 0, so |P_BG| ≤ 0 holds by simp. This keeps the file axiom-free.
    Later, replace `P_BG` with your Tenor payload and re-prove `payload_linf_bound`.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach.BG_Bank

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Real
open BigOperators
open Classical

/-- Canonical BG support (bank offsets). -/
noncomputable def S_BG : Finset ℤ :=
  Finset.Icc (-(H : ℤ)) (H : ℤ)

/-- BG payload (temporary: zero; replace by the Tenor formula later). -/
noncomputable def P_BG : ℕ → ℕ → ℤ → ℝ :=
  fun _X _N _k => 0

/-- A (temporary) L∞ cap for the payload. -/
noncomputable def payload_linf_cap : ℝ := 0

lemma payload_linf_nonneg : 0 ≤ payload_linf_cap := by
  simp [payload_linf_cap]

/-- Uniform pointwise bound on the canonical window: |P_BG X N k| ≤ payload_linf_cap.
    (Holds trivially now because P_BG ≡ 0.) -/
lemma payload_linf_bound :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    ∀ {k : ℤ}, k ∈ S_BG → |P_BG X N k| ≤ payload_linf_cap := by
  intro X N _hX _hN k _hk
  simp [P_BG, payload_linf_cap]

end Goldbach.BG_Bank
