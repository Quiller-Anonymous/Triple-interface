import SSU.Instances.FejerBankedConstruction
import SSU.Torus.Bank
import SSU.Torus.NormalCoord

import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
Frozen “platinum” analytic conventions for the Fejér-banked partition.

This file only fixes the **definitions** for the first SSU instance (χ_j, ϑ_I, Φ̂_H, and J).
The TeX overlap bounds (T1) and bank-dom can then be proved for these concrete definitions.
-/

namespace SSU
namespace Instances
namespace FejerBankedPlatinum

open scoped BigOperators ENNReal

open MeasureTheory
open SSU.Torus
open SSU.Torus.Bank
open Metric

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The dyadic shell cutoff `Jmax := ⌊log₂(ceil H)⌋` (Nat). -/
def Jmax (H : ℝ) : ℕ :=
  Nat.log 2 (Nat.ceil H)

/-- Shell index set `J = {0,…,Jmax}` as a `Finset ℤ`. -/
def J (H : ℝ) : Finset ℤ :=
  Finset.Icc (0 : ℤ) (Int.ofNat (Jmax H))

/-- Base tent bump `χBase(u) = max(0, 1 - |u|)`. -/
def χBase (u : ℝ) : ℝ :=
  max 0 (1 - |u|)

theorem χBase_nonneg (u : ℝ) : 0 ≤ χBase u := by
  simp [χBase]

theorem χBase_le_one (u : ℝ) : χBase u ≤ 1 := by
  have h1 : (1 - |u|) ≤ 1 := by linarith [abs_nonneg u]
  have h0 : (0 : ℝ) ≤ 1 := by norm_num
  exact (max_le_iff.2 ⟨h0, h1⟩)

theorem measurable_χBase : Measurable χBase := by
  -- `max` and `abs` preserve measurability.
  simpa [χBase] using (measurable_const.max (measurable_const.sub measurable_abs))

/-- Parameters for the frozen “platinum” Fejér-banked partition. -/
structure Params (Q : ℕ) where
  /-- The large parameter `X` from the notes (window length). -/
  X : ℝ
  hX : 0 < X
  /-- Short-shift scale parameter `H` (TeX). -/
  H : ℝ
  hH : 0 < H
  /-- Tube-shift truncation: at shell `j`, use `n ∈ [-N j, N j]`. -/
  N : ℤ → ℕ
  /-- Disjointness hypothesis `Q^2 ≪ H` (enough for disjoint major arcs at radius `cA/H`). -/
  hQH : ((Q : ℝ) ^ 2) ≤ H

namespace Params

variable {Q : ℕ} (P : Params Q)

abbrev ι : Type := RatCenter Q
abbrev κ : Type := (RatCenter Q) × ℤ

instance : DecidableEq (κ (Q := Q)) := by classical infer_instance

instance : Finite (ι (Q := Q)) := by
  classical
  let enc : RatCenter Q → (Fin (Q + 1) × Fin (Q + 1)) :=
    fun r =>
      (⟨r.q, Nat.lt_succ_of_le r.hqQ⟩,
        ⟨r.a, Nat.lt_succ_of_le (le_trans (Nat.le_of_lt r.ha) r.hqQ)⟩)
  refine Finite.of_injective enc ?_
  intro r s h
  have hq : r.q = s.q := congrArg (fun x => (x.1 : Fin (Q + 1)).1) h
  have ha : r.a = s.a := congrArg (fun x => (x.2 : Fin (Q + 1)).1) h
  cases r
  cases s
  cases hq
  cases ha
  simp

instance : Fintype (ι (Q := Q)) := Fintype.ofFinite (ι (Q := Q))

/-- The canonical shell set `J = {0,…,Jmax}`. -/
def J : Finset ℤ :=
  FejerBankedPlatinum.J P.H

/-- Tube step size in the normal coordinate: `2^{-j} / H`. -/
abbrev step (j : ℤ) : ℝ :=
  (2 : ℝ) ^ (-j) / P.H

theorem step_pos (j : ℤ) : 0 < P.step j := by
  have hpow : 0 < (2 : ℝ) ^ (-j) := by
    simpa using (zpow_pos (by norm_num : (0 : ℝ) < (2 : ℝ)) (-j))
  exact div_pos hpow P.hH

/-- Shift index set at shell `j`: integers `n ∈ [-N j, N j]`. -/
def shiftSet (j : ℤ) : Finset ℤ :=
  Finset.Icc (-Int.ofNat (P.N j)) (Int.ofNat (P.N j))

/-- Full tube index set at shell `j`: all arcs × all shift indices. -/
def K (j : ℤ) : Finset (κ (Q := Q)) :=
  (Finset.univ : Finset (RatCenter Q)).product (P.shiftSet j)

/-- Parent arc of a tube index. -/
def parent : (κ (Q := Q)) → RatCenter Q := Prod.fst

/-- Tangential taper `ϑ_I`: hard cutoff on the major arc `I`. -/
def ϑ (r : RatCenter Q) : UC → ℝ :=
  Set.indicator (majorArc (Q := Q) (H := P.H) (cA := cA) r) (fun _ => (1 : ℝ))

theorem measurable_ϑ (r : RatCenter Q) : Measurable (P.ϑ r) := by
  have hS : MeasurableSet (majorArc (Q := Q) (H := P.H) (cA := cA) r) :=
    (Metric.isClosed_closedBall).measurableSet
  simpa [Params.ϑ] using (measurable_const.indicator hS)

theorem ϑ_nonneg (r : RatCenter Q) (x : UC) : 0 ≤ P.ϑ r x := by
  by_cases hx : x ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r <;> simp [Params.ϑ, hx]

theorem ϑ_le_one (r : RatCenter Q) (x : UC) : P.ϑ r x ≤ 1 := by
  by_cases hx : x ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r <;> simp [Params.ϑ, hx]

/-- Normal coordinate `ν_I(ξ)` is the signed wrap-around difference to the arc center. -/
def ν (r : RatCenter Q) : UC → ℝ :=
  SSU.Torus.normalCoord r.center

theorem measurable_ν (r : RatCenter Q) : Measurable (Params.ν (Q := Q) r) := by
  simpa [Params.ν] using SSU.Torus.measurable_normalCoord (c := r.center)

/-- Short-axis bump `χ_j(t) = χBase(t / step j)`. -/
def χ (j : ℤ) : ℝ → ℝ :=
  fun t => χBase (t / P.step j)

theorem measurable_χ (j : ℤ) : Measurable (P.χ j) := by
  have hdiv : Measurable fun t : ℝ => t / P.step j := by
    simpa [div_eq_mul_inv] using (Measurable.mul_const measurable_id ((P.step j)⁻¹))
  exact measurable_χBase.comp hdiv

theorem χ_nonneg (j : ℤ) (t : ℝ) : 0 ≤ P.χ j t := by
  simpa [Params.χ] using χBase_nonneg (u := t / P.step j)

theorem χ_le_one (j : ℤ) (t : ℝ) : P.χ j t ≤ 1 := by
  simpa [Params.χ] using χBase_le_one (u := t / P.step j)

/-- Tube shift `t_{j,(r,n)} := n * step j`. -/
def t (j : ℤ) (k : κ (Q := Q)) : ℝ :=
  (k.2 : ℝ) * P.step j

/--
Dyadic shell in the **normal coordinate** (local version of TeX’s `𝒟_j`).

We use the signed wrap-around coordinate `ν_r(ξ) ∈ (-1/2,1/2]` and take the shell
`2^{-(j+1)}/H < |ν_r(ξ)| ≤ 2^{-j}/H`, i.e. `step (j+1) < |ν| ≤ step j`.

This is the missing “`P_{U_{j,k}}` is supported in `𝓐 ∩ 𝒟_j`” bookkeeping needed for the
TeX partition statement `∑_{j,k} P_{U_{j,k}} ≍ 1_𝓐`.
-/
def Dj (j : ℤ) (r : RatCenter Q) : Set UC :=
  {ξ : UC | P.step (j + 1) < |Params.ν (Q := Q) r ξ| ∧ |Params.ν (Q := Q) r ξ| ≤ P.step j}

/-- Shell cut-off `1_{𝒟_j}` (as an `ℝ`-valued indicator). -/
def shellCut (j : ℤ) (r : RatCenter Q) : UC → ℝ :=
  Set.indicator (P.Dj j r) (fun _ => (1 : ℝ))

theorem measurableSet_Dj (j : ℤ) (r : RatCenter Q) : MeasurableSet (P.Dj j r) := by
  -- `Dj` is defined by two inequalities on the measurable function `ξ ↦ |ν_r(ξ)|`.
  have hν : Measurable fun ξ : UC => Params.ν (Q := Q) r ξ := Params.measurable_ν (Q := Q) (r := r)
  have habs : Measurable fun ξ : UC => |Params.ν (Q := Q) r ξ| := hν.abs
  have hlt :
      MeasurableSet {ξ : UC | P.step (j + 1) < |Params.ν (Q := Q) r ξ|} :=
    measurableSet_lt measurable_const habs
  have hle :
      MeasurableSet {ξ : UC | |Params.ν (Q := Q) r ξ| ≤ P.step j} :=
    measurableSet_le habs measurable_const
  simpa [Params.Dj, Set.setOf_and] using hlt.inter hle

theorem measurable_shellCut (j : ℤ) (r : RatCenter Q) : Measurable (P.shellCut j r) := by
  have hS : MeasurableSet (P.Dj j r) := P.measurableSet_Dj (Q := Q) j r
  simpa [Params.shellCut] using (measurable_const.indicator hS)

theorem shellCut_nonneg (j : ℤ) (r : RatCenter Q) (x : UC) : 0 ≤ P.shellCut j r x := by
  by_cases hx : x ∈ P.Dj j r <;> simp [Params.shellCut, hx]

theorem shellCut_le_one (j : ℤ) (r : RatCenter Q) (x : UC) : P.shellCut j r x ≤ 1 := by
  by_cases hx : x ∈ P.Dj j r <;> simp [Params.shellCut, hx]

/--
Tube projector (TeX `\eqref{eq:P_U_def}`) with an explicit shell cut-off:

`P_{U_{j,k}}(ξ) := 1_{𝒟_j}(ξ) * ϑ_{I(k)}(ξ) * χ_j(ν_{I(k)}(ξ) - t_{j,k})`.

This keeps the SSU story 1D in `j` while ensuring the “dyadic shell” interpretation matches the
`ψ_j` primitives.
-/
def Pproj (j : ℤ) (k : κ (Q := Q)) : UC → ℝ :=
  fun ξ =>
    (P.shellCut j k.1 ξ) *
      ((P.ϑ k.1 ξ) * P.χ j ((Params.ν (Q := Q) k.1 ξ) - P.t j k))

/-!
### Fejér window `Φ̂_H` (Option A)

Compactly supported tent at scale `1/H` in the canonical “absolute value” on `AddCircle 1`,
implemented as the norm `‖ξ‖ = dist(ξ,0)`.
-/

def Φ (ξ : UC) : ℂ :=
  ((χBase (‖ξ‖ * P.H)) : ℝ)

theorem measurable_Φ : Measurable P.Φ := by
  have hnormH : Measurable fun ξ : UC => ‖ξ‖ * P.H :=
    (continuous_norm.mul continuous_const).measurable
  have hχ : Measurable fun ξ : UC => χBase (‖ξ‖ * P.H) :=
    measurable_χBase.comp hnormH
  simpa [Params.Φ, Params.Φ] using (Complex.measurable_ofReal.comp hχ)

theorem Φ_bound_one (ξ : UC) : ‖P.Φ ξ‖ ≤ (1 : ℝ) := by
  have hle : χBase (‖ξ‖ * P.H) ≤ 1 := χBase_le_one _
  have hnonneg : 0 ≤ χBase (‖ξ‖ * P.H) := χBase_nonneg _
  -- `‖Φ‖ = χBase(...) ≤ 1`.
  have hn : ‖P.Φ ξ‖ = χBase (‖ξ‖ * P.H) := by
    simpa [Params.Φ, Params.Φ] using (Complex.norm_of_nonneg hnonneg)
  -- rewrite the goal using `hn`
  simpa [hn] using hle

theorem memLp_Φ : MemLp P.Φ (∞ : ℝ≥0∞) μ := by
  refine MeasureTheory.memLp_top_of_bound (P.measurable_Φ.aestronglyMeasurable) 1 ?_
  exact Filter.Eventually.of_forall (fun ξ => P.Φ_bound_one ξ)

end Params

end

end FejerBankedPlatinum
end Instances
end SSU
