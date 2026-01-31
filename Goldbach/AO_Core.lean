/-
  Goldbach/AO_Core.lean
  Minimal, axiom-free core for AO objects shared across modules:
    • sigma   : ℕ → ℝ
    • Mcanon  : ℕ → ℕ → ℝ
    • weight_mass : ℕ → ℝ  (aligned with bank `wX` scaling)
    • errAO   : ℕ → ℕ → ℝ (algebraic remainder Mcanon − sigma*mass)

  This file stays *producer-only* to avoid import cycles.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.AO_SigmaModel
import Goldbach.AO_Mcanon
import Goldbach.AO_WeightMass

namespace Goldbach.AO_Core

open Real
open Goldbach
open Goldbach.Windows

/-- Singular series (σ-model). Positivity/estimates live in `AO_SigmaPos`. -/
noncomputable abbrev sigma : ℕ → ℝ := Goldbach.AO_SigmaModel.sigma

/-- Canonical AO main term (main track). -/
noncomputable abbrev Mcanon : ℕ → ℕ → ℝ := Goldbach.AO_Mcanon.Mcanon

/-- Major-arc weight mass (aligned with `BG_Bank.wX` normalization). -/
@[simp] noncomputable def weight_mass (X : ℕ) : ℝ := Goldbach.AO_WeightMass.weight_mass X

/-- AO error remainder: `Mcanon N - sigma N * weight_mass X`. -/
@[simp] noncomputable def errAO (X N : ℕ) : ℝ :=
  Mcanon X N - sigma N * weight_mass X

end Goldbach.AO_Core
