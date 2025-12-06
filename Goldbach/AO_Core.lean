/-
  Goldbach/AO_Core.lean
  Minimal, axiom-free core for AO objects shared across modules:
    • sigma : ℕ → ℝ  (declared here)
    • weight_mass : ℕ → ℝ  (normalized to 1.0)
    • errAO : ℕ → ℕ → ℝ    (algebraic remainder Mcanon − sigma*mass)

  This file avoids importing any consumer so we can break dependency cycles.
-/
import Mathlib
import Goldbach.TenorCanon
import Goldbach.Windows

namespace Goldbach.AO_Core

open Real
open Goldbach
open Goldbach.Windows

/-- Singular series. Its positivity/estimates live elsewhere. -/
constant sigma : ℕ → ℝ

/-- Major-arc weight mass (ledger normalization = 1). -/
@[simp] def weight_mass (_X : ℕ) : ℝ := 1.0

/-- AO error remainder: `Mcanon N - sigma N * weight_mass X`. -/
@[simp] def errAO (X N : ℕ) : ℝ :=
  Goldbach.TenorCanon.Mcanon N - sigma N * weight_mass X

end Goldbach.AO_Core
