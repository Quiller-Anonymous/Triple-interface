import SSU.Instances.FejerBankedPartition
import SSU.Torus.DyadicShells

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
Mirror of the “Setup and construction” block in `SupportingDocs/Goldbach tenor/sections/05b_SSU.tex`,
Subsection “Tube overlap for the Fejér-banked partition”.

This file provides a *definition-level* interface:

* a parent-arc index `ι` (TeX: `I`),
* tangential tapers `ϑ_I`,
* normal coordinates `ν_I`,
* short-axis bumps `χ_j` and shifts `t_{j,k}`,
* tube projectors `P_{U_{j,k}}(ξ) := ϑ_{I(k)}(ξ) * χ_j(ν_{I(k)}(ξ) - t_{j,k})`,
* tube sets `U_{j,k} := supp(P_{U_{j,k}})`.

The overlap bounds (Lemma `lem:bounded-mult-j` and Proposition `prop:tube-overlap`) are still
handled via hypotheses, packaged as `SSU.Instances.FejerBankedPartition.Data`.
-/

namespace SSU
namespace Instances
namespace FejerBankedConstruction

open scoped BigOperators ENNReal

open MeasureTheory
open SSU.Torus

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-!
## Setup

This is the minimal “construction data” matching the TeX definition `\eqref{eq:P_U_def}`.
-/

structure Setup (κ ι : Type*) [DecidableEq κ] where
  /-- The large parameter `X` from the notes (window length). -/
  X : ℝ
  /-- The short-shift bandwidth parameter `H` from the notes. -/
  H : ℝ
  /-- The dyadic shell indices used by the application (finite for the SSU engine). -/
  J : Finset ℤ
  /-- Tube indices available at each shell. -/
  K : ℤ → Finset κ
  /-- Parent arc index (TeX: `I(k)`). -/
  parent : κ → ι

  /-- Tangential tapers `ϑ_I : 𝕋 → ℝ`. -/
  ϑ : ι → UC → ℝ
  hϑ : ∀ I : ι, Measurable (ϑ I)
  ϑ_nonneg : ∀ I : ι, ∀ x : UC, 0 ≤ ϑ I x
  ϑ_le_one : ∀ I : ι, ∀ x : UC, ϑ I x ≤ 1

  /-- Signed normal coordinate to the arc `I` (TeX: `ν_I`). -/
  ν : ι → UC → ℝ
  hν : ∀ I : ι, Measurable (ν I)

  /-- Short-axis bumps `χ_j : ℝ → ℝ` (TeX: equation `\eqref{eq:chi_j}`). -/
  χ : ℤ → ℝ → ℝ
  hχ : ∀ j : ℤ, Measurable (χ j)
  χ_nonneg : ∀ j : ℤ, ∀ t : ℝ, 0 ≤ χ j t
  χ_le_one : ∀ j : ℤ, ∀ t : ℝ, χ j t ≤ 1

  /-- Tube shifts `t_{j,k}` (TeX: `t_{j,k} ∈ (2^{-j}/H)ℤ`). -/
  t : ℤ → κ → ℝ

  /-- Tube projectors `P_{U_{j,k}} : 𝕋 → ℝ`. -/
  P : ℤ → κ → UC → ℝ
  /-- Defining equation (TeX: `\eqref{eq:P_U_def}`). -/
  P_eq :
    ∀ j : ℤ, ∀ k : κ, ∀ x : UC,
      P j k x = (ϑ (parent k) x) * χ j (ν (parent k) x - t j k)

  /-- Fejér window multiplier `Φ_H` (frequency-side). -/
  Φ : UC → ℂ
  /-- `Φ_H ∈ L^∞`. -/
  hΦ : MemLp Φ (∞ : ℝ≥0∞) μ
  /-- A pointwise `L^∞` bound `‖Φ_H‖_∞ ≤ Φmax`. -/
  Φmax : ℝ
  Φmax_nonneg : 0 ≤ Φmax
  Φ_bound : ∀ x : UC, ‖Φ x‖ ≤ Φmax

  /-- Fixed-`j` overlap constant (TeX Lemma `lem:bounded-mult-j`, packaged). -/
  M : ℝ
  M_nonneg : 0 ≤ M
  fixed_j_overlap : ∀ j : ℤ, ∀ x : UC, (∑ k ∈ K j, P j k x) ≤ M

  /-- Global overlap constant (TeX Proposition `prop:tube-overlap`, packaged). -/
  ΛP : ℝ
  ΛP_nonneg : 0 ≤ ΛP
  global_overlap : ∀ x : UC, (∑ j ∈ J, ∑ k ∈ K j, P j k x) ≤ ΛP

namespace Setup

variable {κ ι : Type*} [DecidableEq κ] (S : Setup κ ι)

/-- Tube set `U_{j,k} := supp(P_{U_{j,k}})`. -/
noncomputable def U (j : ℤ) (k : κ) : Set UC :=
  Function.support (S.P j k)

theorem P_nonneg (j : ℤ) (k : κ) (x : UC) : 0 ≤ S.P j k x := by
  have hθ : 0 ≤ S.ϑ (S.parent k) x := S.ϑ_nonneg (S.parent k) x
  have hχ : 0 ≤ S.χ j (S.ν (S.parent k) x - S.t j k) := S.χ_nonneg j _
  -- Use the TeX defining equation `P = ϑ * χ`.
  simpa [S.P_eq j k x] using mul_nonneg hθ hχ

theorem P_le_one (j : ℤ) (k : κ) (x : UC) : S.P j k x ≤ 1 := by
  have hθ : S.ϑ (S.parent k) x ≤ 1 := S.ϑ_le_one (S.parent k) x
  have hχ : S.χ j (S.ν (S.parent k) x - S.t j k) ≤ 1 := S.χ_le_one j _
  have hmul :
      (S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)) ≤ 1 * 1 := by
    exact
      mul_le_mul hθ hχ (S.χ_nonneg j _) (by positivity : 0 ≤ (1 : ℝ))
  have hmul' :
      (S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)) ≤ (1 : ℝ) := by
    simpa using hmul
  simpa [S.P_eq j k x] using hmul'

theorem measurable_P (j : ℤ) (k : κ) : Measurable (S.P j k) := by
  have hχcomp :
      Measurable fun x : UC => S.χ j (S.ν (S.parent k) x - S.t j k) := by
    have hν' : Measurable fun x : UC => S.ν (S.parent k) x - S.t j k := by
      simpa using (S.hν (S.parent k)).sub_const (S.t j k)
    exact (S.hχ j).comp hν'
  have hmul : Measurable fun x : UC => (S.ϑ (S.parent k) x) * S.χ j (S.ν (S.parent k) x - S.t j k) := by
    exact (S.hϑ (S.parent k)).mul hχcomp
  have hPfun :
      (S.P j k) = fun x : UC => (S.ϑ (S.parent k) x) * S.χ j (S.ν (S.parent k) x - S.t j k) := by
    funext x
    simpa using (S.P_eq j k x)
  simpa [hPfun] using hmul

theorem memLp_P (j : ℤ) (k : κ) : MemLp (S.P j k) (∞ : ℝ≥0∞) μ := by
  -- `0 ≤ P ≤ 1` pointwise, so `‖P‖ ≤ 1` a.e.
  have hmeas : AEStronglyMeasurable (S.P j k) μ :=
    (S.measurable_P j k).aestronglyMeasurable
  refine MeasureTheory.memLp_top_of_bound hmeas (C := (1 : ℝ)) ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have h0 : 0 ≤ S.P j k x := S.P_nonneg j k x
  have h1 : S.P j k x ≤ 1 := S.P_le_one j k x
  -- Convert `0 ≤ P ≤ 1` to `‖P‖ ≤ 1`.
  have : ‖S.P j k x‖ ≤ (1 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  simpa using this

/-- Forget the extra construction data, keeping only the abstract `FejerBankedPartition.Data`. -/
noncomputable def toData : FejerBankedPartition.Data κ where
  X := S.X
  H := S.H
  J := S.J
  K := S.K
  P := S.P
  hP := fun j k => S.memLp_P j k
  P_nonneg := fun j k x => S.P_nonneg j k x
  P_le_one := fun j k x => S.P_le_one j k x
  Φ := S.Φ
  hΦ := S.hΦ
  Φmax := S.Φmax
  Φmax_nonneg := S.Φmax_nonneg
  Φ_bound := S.Φ_bound
  M := S.M
  M_nonneg := S.M_nonneg
  fixed_j_overlap := S.fixed_j_overlap
  ΛP := S.ΛP
  ΛP_nonneg := S.ΛP_nonneg
  global_overlap := S.global_overlap

end Setup

end

end FejerBankedConstruction
end Instances
end SSU
