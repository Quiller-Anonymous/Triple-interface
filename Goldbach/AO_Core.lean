/-
  Goldbach/AO_Core.lean
  Minimal, axiom-free core for AO objects shared across modules:
    • sigma   : ℕ → ℝ
    • Mcanon  : ℕ → ℝ
    • weight_mass : ℕ → ℝ  (normalized to 1.0)
    • errAO   : ℕ → ℕ → ℝ (algebraic remainder Mcanon − sigma*mass)

  This file stays *producer-only* to avoid import cycles.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.AO_SigmaModel

namespace Goldbach.AO_Core

open Real
open Goldbach
open Goldbach.Windows

/-- Singular series (σ-model). Positivity/estimates live in `AO_SigmaPos`. -/
noncomputable abbrev sigma : ℕ → ℝ := Goldbach.AO_SigmaModel.sigma

/-- Canonical AO main term (placeholder). -/
noncomputable def Mcanon : ℕ → ℝ := fun _ => 0

/-- Major-arc weight mass (ledger normalization = 1). -/
@[simp] def weight_mass (_X : ℕ) : ℝ := (1 : ℝ)

/-- AO error remainder: `Mcanon N - sigma N * weight_mass X`. -/
@[simp] noncomputable def errAO (X N : ℕ) : ℝ :=
  Mcanon N - sigma N * weight_mass X

end Goldbach.AO_Core
