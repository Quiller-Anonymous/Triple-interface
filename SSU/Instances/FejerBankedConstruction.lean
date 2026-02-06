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

  /--
  Additional dyadic-shell cut-off `δ_{j,I} : 𝕋 → ℝ`.

  This is the Lean-level hook for the TeX bookkeeping “`P_{U_{j,k}}` is supported in `𝓐 ∩ 𝒟_j`”.
  In simple instances one can take `δ ≡ 1`; in the “platinum” Fejér-banked instance we take `δ`
  to be the indicator of the normal-coordinate shell.
  -/
  δ : ℤ → ι → UC → ℝ
  hδ : ∀ j : ℤ, ∀ I : ι, Measurable (δ j I)
  δ_nonneg : ∀ j : ℤ, ∀ I : ι, ∀ x : UC, 0 ≤ δ j I x
  δ_le_one : ∀ j : ℤ, ∀ I : ι, ∀ x : UC, δ j I x ≤ 1

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
      P j k x =
        (δ j (parent k) x) * ((ϑ (parent k) x) * χ j (ν (parent k) x - t j k))

  /-- Fejér window multiplier `Φ_H` (frequency-side). -/
  Φ : UC → ℂ
  /-- Measurability of `Φ_H`. -/
  measurable_Φ : Measurable Φ
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
  have hδ : 0 ≤ S.δ j (S.parent k) x := S.δ_nonneg j (S.parent k) x
  have hθ : 0 ≤ S.ϑ (S.parent k) x := S.ϑ_nonneg (S.parent k) x
  have hχ : 0 ≤ S.χ j (S.ν (S.parent k) x - S.t j k) := S.χ_nonneg j _
  -- Use the defining equation `P = δ * (ϑ * χ)`.
  have : 0 ≤ (S.δ j (S.parent k) x) * ((S.ϑ (S.parent k) x) * S.χ j (S.ν (S.parent k) x - S.t j k)) :=
    mul_nonneg hδ (mul_nonneg hθ hχ)
  simpa [S.P_eq j k x] using this

theorem P_le_one (j : ℤ) (k : κ) (x : UC) : S.P j k x ≤ 1 := by
  have hδ : S.δ j (S.parent k) x ≤ 1 := S.δ_le_one j (S.parent k) x
  have hθ : S.ϑ (S.parent k) x ≤ 1 := S.ϑ_le_one (S.parent k) x
  have hχ : S.χ j (S.ν (S.parent k) x - S.t j k) ≤ 1 := S.χ_le_one j _
  have hδ0 : 0 ≤ S.δ j (S.parent k) x := S.δ_nonneg j (S.parent k) x
  have hθ0 : 0 ≤ S.ϑ (S.parent k) x := S.ϑ_nonneg (S.parent k) x
  have hχ0 : 0 ≤ S.χ j (S.ν (S.parent k) x - S.t j k) := S.χ_nonneg j _
  have hθχ_le : (S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)) ≤ (1 : ℝ) := by
    have hθχ : (S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)) ≤ 1 * 1 :=
      mul_le_mul hθ hχ hχ0 (by positivity : 0 ≤ (1 : ℝ))
    simpa using hθχ
  have hmul :
      (S.δ j (S.parent k) x) * ((S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)))
        ≤ (1 : ℝ) := by
    have hnθχ : 0 ≤ (S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)) :=
      mul_nonneg hθ0 hχ0
    have h' :
        (S.δ j (S.parent k) x) *
            ((S.ϑ (S.parent k) x) * (S.χ j (S.ν (S.parent k) x - S.t j k)))
          ≤ 1 * 1 :=
      mul_le_mul hδ hθχ_le hnθχ (by positivity : 0 ≤ (1 : ℝ))
    simpa using h'
  simpa [S.P_eq j k x, mul_assoc] using hmul

theorem measurable_P (j : ℤ) (k : κ) : Measurable (S.P j k) := by
  have hχcomp :
      Measurable fun x : UC => S.χ j (S.ν (S.parent k) x - S.t j k) := by
    have hν' : Measurable fun x : UC => S.ν (S.parent k) x - S.t j k := by
      simpa using (S.hν (S.parent k)).sub_const (S.t j k)
    exact (S.hχ j).comp hν'
  have hθχ :
      Measurable fun x : UC => (S.ϑ (S.parent k) x) * S.χ j (S.ν (S.parent k) x - S.t j k) := by
    exact (S.hϑ (S.parent k)).mul hχcomp
  have hmul :
      Measurable fun x : UC =>
        (S.δ j (S.parent k) x) * ((S.ϑ (S.parent k) x) * S.χ j (S.ν (S.parent k) x - S.t j k)) := by
    exact (S.hδ j (S.parent k)).mul hθχ
  have hPfun :
      (S.P j k) =
        fun x : UC =>
          (S.δ j (S.parent k) x) * ((S.ϑ (S.parent k) x) * S.χ j (S.ν (S.parent k) x - S.t j k)) := by
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
  measurable_P := fun j k => S.measurable_P j k
  hP := fun j k => S.memLp_P j k
  P_nonneg := fun j k x => S.P_nonneg j k x
  P_le_one := fun j k x => S.P_le_one j k x
  Φ := S.Φ
  measurable_Φ := S.measurable_Φ
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

/-!
## Coverage hypothesis (TeX `\eqref{eq:chi_j}`)

The TeX “covering by translates” property is conceptually a statement about the family of bumps
`χ_j` and the grid of shifts `t_{j,k}` along the normal coordinate `ν_I`.

For Lean, we package the *usable* form:

*on the core region where the tangential cutoff `ϑ_I` and shell cutoff `δ_{j,I}` equal `1`, the
finite translate sum is bounded below by a fixed constant.*

This is the right level of abstraction for proving the lower bound side of (T1) without hardcoding
the tent bump.
-/

namespace Coverage

variable {κ ι : Type*} [DecidableEq κ] (S : Setup κ ι)

/-- Translate-sum of `χ_j` along the `t_{j,k}` grid, restricted to a fixed parent arc `I`. -/
noncomputable def χSum (j : ℤ) (I : ι) (x : UC) : ℝ := by
  classical
  exact ∑ k ∈ S.K j, if S.parent k = I then S.χ j (S.ν I x - S.t j k) else 0

/-- Translate-sum of the projectors `P_{U_{j,k}}`, restricted to a fixed parent arc `I`. -/
noncomputable def PSum (j : ℤ) (I : ι) (x : UC) : ℝ := by
  classical
  exact ∑ k ∈ S.K j, if S.parent k = I then S.P j k x else 0

structure Hypothesis where
  /-- A uniform lower bound for the translate sum, on the core region. -/
  cLower : ℝ
  cLower_pos : 0 < cLower
  /--
  Coverage on the *core* region `δ_{j,I} = 1` and `ϑ_I = 1`.

  This matches the TeX usage: on `I° ∩ 𝒟_j` the tube projectors form a partition of unity
  up to constants.
  -/
  cover :
    ∀ j : ℤ, ∀ I : ι, ∀ x : UC, S.δ j I x = 1 → S.ϑ I x = 1 → cLower ≤ χSum S j I x

variable {κ ι : Type*} [DecidableEq κ] {S : Setup κ ι}

theorem PSum_eq_χSum_of_core (j : ℤ) (I : ι) (x : UC)
    (hδ : S.δ j I x = 1) (hϑ : S.ϑ I x = 1) :
    PSum S j I x = χSum S j I x := by
  classical
  -- Expand both sums and use the defining equation for `P`.
  unfold PSum χSum
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hparent : S.parent k = I
  · -- On the core region, `δ = 1` and `ϑ = 1`, so `P = χ`.
    have :
        S.P j k x = S.χ j (S.ν I x - S.t j k) := by
      have hPk : S.P j k x =
          (S.δ j I x) * ((S.ϑ I x) * S.χ j (S.ν I x - S.t j k)) := by
        simpa [hparent] using S.P_eq j k x
      -- Simplify using `δ = 1` and `ϑ = 1`.
      simpa [hPk, hδ, hϑ, mul_assoc, mul_left_comm, mul_comm]
    simp [hparent, this]
  · simp [hparent]

theorem PSum_ge_of_hypothesis (h : Hypothesis (S := S)) (j : ℤ) (I : ι) (x : UC)
    (hδ : S.δ j I x = 1) (hϑ : S.ϑ I x = 1) :
    h.cLower ≤ PSum S j I x := by
  -- Reduce to the translate sum of `χ` using `PSum_eq_χSum_of_core`.
  simpa [PSum_eq_χSum_of_core (S := S) (j := j) (I := I) (x := x) hδ hϑ] using
    (h.cover j I x hδ hϑ)

end Coverage

end

end FejerBankedConstruction
end Instances
end SSU
