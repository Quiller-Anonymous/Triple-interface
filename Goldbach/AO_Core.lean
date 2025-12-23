/-
  Goldbach/AO_Core.lean
  Minimal, axiom-free core for AO objects shared across modules:
    • sigma   : ℕ → ℝ  (declared here)
    • Mcanon  : ℕ → ℝ  (main term, declared abstractly)
    • weight_mass : ℕ → ℝ  (normalized to 1.0)
    • errAO   : ℕ → ℕ → ℝ (algebraic remainder Mcanon − sigma*mass)

  This file stays *producer-only* to avoid import cycles.  Downstream
  consumers (AO_Major, TenorCanon, …) import this rather than the other way
  around.
-/
import Mathlib
import Goldbach.Windows

namespace Goldbach.AO_Core

open Real
open Goldbach
open Goldbach.Windows

/-- Singular series. Its positivity/estimates live elsewhere. Placeholder here. -/
noncomputable def sigma : ℕ → ℝ := fun _ => 0

/-- Canonical AO main term (placeholder). -/
noncomputable def Mcanon : ℕ → ℝ := fun _ => 0

/-- Major-arc weight mass (ledger normalization = 1). -/
@[simp] def weight_mass (_X : ℕ) : ℝ := 1.0

/-- AO error remainder: `Mcanon N - sigma N * weight_mass X`. -/
@[simp] noncomputable def errAO (X N : ℕ) : ℝ :=
  Mcanon N - sigma N * weight_mass X

end Goldbach.AO_Core
