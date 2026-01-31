import SSU.Instances.FejerBankedConstruction
import SSU.Torus.BankSpacing
import SSU.Torus.NormalCoord

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Concrete Fejér-banked tube construction (first Lean-realistic version).

This file takes the “Setup and construction” block from `05b_SSU.tex` and makes it *concrete* on
`𝕋 = AddCircle 1`, with the frozen numerical conventions:

* arc radius constant `cA = 1/1000` (already defined in `SSU.Torus.Bank`),
* arc indices are reduced rationals `RatCenter Q`,
* normal coordinate `ν_I(ξ)` is the signed wrap-around difference (`SSU.Torus.normalCoord`),
* tube projectors are exactly

`P_{U_{j,k}}(ξ) := ϑ_{I(k)}(ξ) * χ_j(ν_{I(k)}(ξ) - t_{j,k})`.

We then *prove* the bounded-overlap statements used in (T1):

* fixed-`j` overlap is bounded by `1`,
* global overlap over a finite shell set `J` is bounded by `#J`.

This is enough to feed the SSU primitive `ψ_j := (∑_k P_{U_{j,k}}) * Φ_H` via
`SSU.Instances.FejerBankedPartition.Data`.

Notes:
* We focus on the **upper** overlap bounds (what SSU needs downstream). The TeX’s lower bound
  `∑_{j,k} P_{U_{j,k}} ≍ 1_𝓐` is deferred until we also formalize the covering-by-translates
  property (equation `\eqref{eq:chi_j}`) in a compatible way.
-/

namespace SSU
namespace Instances
namespace FejerBankedConcrete

open scoped BigOperators ENNReal

open MeasureTheory
open SSU.Torus
open SSU.Torus.Bank
open Metric

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-!
## Construction parameters
-/

structure Params (Q : ℕ) where
  /-- Short-shift scale parameter `H` (TeX). -/
  H : ℝ
  hH : 0 < H
  /-- Finite shell index set used by the SSU engine. -/
  J : Finset ℤ
  /-- Tube-shift truncation: at shell `j`, use `n ∈ [-N j, N j]`. -/
  N : ℤ → ℕ
  /-- An `L^∞` window multiplier `Φ_H` (TeX’s Fejér window, treated abstractly here). -/
  Φ : UC → ℂ
  hΦ : MemLp Φ (∞ : ℝ≥0∞) μ
  Φmax : ℝ
  Φmax_nonneg : 0 ≤ Φmax
  Φ_bound : ∀ x : UC, ‖Φ x‖ ≤ Φmax
  /--
  A disjointness hypothesis relating `Q` and `H`.

  This is the “`Q^2 ≪ H`” condition, used to show the major arcs of radius `cA/H` do not overlap.
  -/
  hQH : ((Q : ℝ) ^ 2) ≤ H

namespace Params

variable {Q : ℕ} (P : Params Q)

abbrev ι : Type := RatCenter Q

abbrev κ : Type := (RatCenter Q) × ℤ

instance : DecidableEq (κ (Q := Q)) := by classical infer_instance

-- We use all reduced rationals with denominator `≤ Q` as arc indices.
-- This type is finite (bounded by `Q`).
instance : Finite (ι (Q := Q)) := by
  classical
  -- Inject into `Fin (Q+1) × Fin (Q+1)` via `(q,a)`.
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

theorem step_pos (j : ℤ) : 0 < (2 : ℝ) ^ (-j) / P.H := by
  have hpow : 0 < (2 : ℝ) ^ (-j) := by
    -- `2^z` is always positive.
    simpa using (zpow_pos (by norm_num : (0 : ℝ) < (2 : ℝ)) (-j))
  exact div_pos hpow P.hH

/-- Tube step size in the normal coordinate: `2^{-j} / H`. -/
abbrev step (j : ℤ) : ℝ :=
  (2 : ℝ) ^ (-j) / P.H

/-- Shift index set at shell `j`: integers `n ∈ [-N j, N j]`. -/
def shiftSet (j : ℤ) : Finset ℤ :=
  Finset.Icc (-Int.ofNat (P.N j)) (Int.ofNat (P.N j))

/-- Full tube index set at shell `j`: all arcs × all shift indices. -/
def K (j : ℤ) : Finset (κ (Q := Q)) :=
  (Finset.univ : Finset (RatCenter Q)).product (P.shiftSet j)

/-- Parent arc of a tube index. -/
def parent : (κ (Q := Q)) → RatCenter Q := Prod.fst

/-- Tangential taper `ϑ_I`: here the hard cutoff `1_{majorArc}` (measurable, `0 ≤ ϑ ≤ 1`). -/
def ϑ (r : RatCenter Q) : UC → ℝ :=
  Set.indicator (majorArc (Q := Q) (H := P.H) (cA := cA) r) (fun _ => (1 : ℝ))

theorem measurable_ϑ (r : RatCenter Q) : Measurable (P.ϑ r) := by
  have hS : MeasurableSet (majorArc (Q := Q) (H := P.H) (cA := cA) r) :=
    (isClosed_closedBall).measurableSet
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

/-- Short-axis bump `χ_j`: a half-open interval cutoff of width `step j`. -/
def χ (j : ℤ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (0 : ℝ) (P.step j)) (fun _ => (1 : ℝ))

theorem measurable_χ (j : ℤ) : Measurable (P.χ j) := by
  have hS : MeasurableSet (Set.Ioc (0 : ℝ) (P.step j)) := measurableSet_Ioc
  simpa [Params.χ] using (measurable_const.indicator hS)

theorem χ_nonneg (j : ℤ) (t : ℝ) : 0 ≤ P.χ j t := by
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) (P.step j) <;> simp [Params.χ, ht]

theorem χ_le_one (j : ℤ) (t : ℝ) : P.χ j t ≤ 1 := by
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) (P.step j) <;> simp [Params.χ, ht]

/-- Tube shift `t_{j,(r,n)} := n * step j`. -/
def t (j : ℤ) (k : κ (Q := Q)) : ℝ :=
  (k.2 : ℝ) * P.step j

/-- Tube projector `P_{U_{j,k}}(ξ) := ϑ_{I(k)}(ξ) * χ_j(ν_{I(k)}(ξ) - t_{j,k})`. -/
def PU (j : ℤ) (k : κ (Q := Q)) : UC → ℝ :=
  fun ξ => (P.ϑ k.1 ξ) * P.χ j ((Params.ν (Q := Q) k.1 ξ) - P.t j k)

theorem PU_eq (j : ℤ) (k : κ (Q := Q)) (ξ : UC) :
    P.PU j k ξ = (P.ϑ k.1 ξ) * P.χ j ((Params.ν (Q := Q) k.1 ξ) - P.t j k) :=
  rfl

/-!
## Compatibility with a (hard) bank weight (TeX Lemma `lem:bank-dom`)

The TeX uses a smooth Fejér taper `ŵ_bank`. For this first concrete construction we record the
analogous pointwise domination by the hard cutoff `1_{𝓐}`; this is already enough for any downstream
estimate that only needs an absolute weight dominating the tube projectors.
-/

/-- Hard bank weight `1_{𝓐}` for the major-arc bank `𝓐 = bankSet Q H cA`. -/
def bankWeight : UC → ℝ :=
  Set.indicator (bankSet (Q := Q) (H := P.H) (cA := cA)) (fun _ => (1 : ℝ))

theorem PU_le_ϑ (j : ℤ) (k : κ (Q := Q)) (ξ : UC) : P.PU j k ξ ≤ P.ϑ k.1 ξ := by
  have hχ : P.χ j ((Params.ν (Q := Q) k.1 ξ) - P.t j k) ≤ 1 :=
    P.χ_le_one j ((Params.ν (Q := Q) k.1 ξ) - P.t j k)
  have hϑ0 : 0 ≤ P.ϑ k.1 ξ := P.ϑ_nonneg k.1 ξ
  calc
    P.PU j k ξ = P.ϑ k.1 ξ * P.χ j ((Params.ν (Q := Q) k.1 ξ) - P.t j k) := by
        simp [Params.PU]
    _ ≤ P.ϑ k.1 ξ * 1 := mul_le_mul_of_nonneg_left hχ hϑ0
    _ = P.ϑ k.1 ξ := by simp

theorem ϑ_le_bankWeight (r : RatCenter Q) (ξ : UC) : P.ϑ r ξ ≤ P.bankWeight ξ := by
  by_cases h : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r
  · have hbank : ξ ∈ bankSet (Q := Q) (H := P.H) (cA := cA) := by
      -- `majorArc r ⊆ bankSet`.
      change ξ ∈ ⋃ r : RatCenter Q, majorArc (Q := Q) (H := P.H) (cA := cA) r
      exact (Set.mem_iUnion).2 ⟨r, h⟩
    simp [Params.ϑ, Params.bankWeight, h, hbank]
  · have hbw : 0 ≤ P.bankWeight ξ := by
      by_cases hbank : ξ ∈ bankSet (Q := Q) (H := P.H) (cA := cA)
      · simp [Params.bankWeight, hbank]
      · simp [Params.bankWeight, hbank]
    simpa [Params.ϑ, h] using hbw

theorem PU_le_bankWeight (j : ℤ) (k : κ (Q := Q)) (ξ : UC) :
    P.PU j k ξ ≤ P.bankWeight ξ := by
  exact le_trans (P.PU_le_ϑ (j := j) (k := k) (ξ := ξ)) (P.ϑ_le_bankWeight (r := k.1) (ξ := ξ))

/-!
## (T1) upper bounds: bounded overlap
-/

theorem majorArc_disjoint (r s : RatCenter Q) (hrs : r ≠ s) :
    Disjoint (majorArc (Q := Q) (H := P.H) (cA := cA) r)
      (majorArc (Q := Q) (H := P.H) (cA := cA) s) := by
  have hdist :
      (1 : ℝ) / ((r.q * s.q : ℕ) : ℝ) ≤ dist r.center s.center :=
    SSU.Torus.Bank.dist_center_lower_bound (r := r) (s := s) hrs
  have hnpos : 0 < ((r.q * s.q : ℕ) : ℝ) := by
    have hrpos : 0 < r.q := Nat.succ_le_iff.mp r.hq1
    have hspos : 0 < s.q := Nat.succ_le_iff.mp s.hq1
    exact_mod_cast (Nat.mul_pos hrpos hspos)
  -- Show `cA/H + cA/H < 1/(r.q*s.q)` by comparing denominators.
  have hrad :
      (cA / P.H) + (cA / P.H) < (1 : ℝ) / ((r.q * s.q : ℕ) : ℝ) := by
    have hqq_le_Q2 : ((r.q * s.q : ℕ) : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have : r.q * s.q ≤ Q * Q := Nat.mul_le_mul r.hqQ s.hqQ
      simpa [pow_two, Nat.cast_mul] using (show ((r.q * s.q : ℕ) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) by
        exact_mod_cast this)
    have hqq_le_H : ((r.q * s.q : ℕ) : ℝ) ≤ P.H := le_trans hqq_le_Q2 P.hQH
    have hHlt : P.H < (500 : ℝ) * P.H := by
      have : (1 : ℝ) < (500 : ℝ) := by norm_num
      simpa [one_mul] using (mul_lt_mul_of_pos_right this P.hH)
    have hqq_lt_500H : ((r.q * s.q : ℕ) : ℝ) < (500 : ℝ) * P.H :=
      lt_of_le_of_lt hqq_le_H hHlt
    have hdiv : (1 : ℝ) / ((500 : ℝ) * P.H) < (1 : ℝ) / ((r.q * s.q : ℕ) : ℝ) :=
      one_div_lt_one_div_of_lt hnpos hqq_lt_500H
    have hsum : (cA / P.H) + (cA / P.H) = (1 : ℝ) / ((500 : ℝ) * P.H) := by
      -- `2*cA = 1/500`.
      have : (2 * cA : ℝ) = (1 : ℝ) / 500 := by norm_num [cA]
      calc
        (cA / P.H) + (cA / P.H) = (2 * cA) / P.H := by ring
        _ = ((1 : ℝ) / 500) / P.H := by simp [this]
        _ = (1 : ℝ) / ((500 : ℝ) * P.H) := by field_simp [P.hH.ne']
    simpa [hsum] using hdiv
  have hrad' : (cA / P.H) + (cA / P.H) < dist r.center s.center :=
    lt_of_lt_of_le hrad hdist
  -- Closed balls are disjoint when the sum of radii is strictly smaller than the distance.
  simpa [majorArc, RatCenter.center] using
    (closedBall_disjoint_closedBall (x := r.center) (y := s.center) (δ := cA / P.H) (ε := cA / P.H) hrad')

/-- At a point `ξ`, at most one arc projector `ϑ_r(ξ)` is nonzero. -/
theorem unique_arc (ξ : UC) {r s : RatCenter Q}
    (hr : P.ϑ r ξ ≠ 0) (hs : P.ϑ s ξ ≠ 0) : r = s := by
  classical
  -- `ϑ` is an indicator: nonzero means membership in the major arc.
  have hr' : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r := by
    by_contra h
    have : P.ϑ r ξ = 0 := by simp [Params.ϑ, h]
    exact hr this
  have hs' : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) s := by
    by_contra h
    have : P.ϑ s ξ = 0 := by simp [Params.ϑ, h]
    exact hs this
  by_cases hrs : r = s
  · exact hrs
  · have hd : Disjoint (majorArc (Q := Q) (H := P.H) (cA := cA) r)
        (majorArc (Q := Q) (H := P.H) (cA := cA) s) := P.majorArc_disjoint (r := r) (s := s) hrs
    exact (hd.le_bot ⟨hr', hs'⟩).elim

/-- Bounded overlap of the translate cutoffs `χ_j(· - n*step)` over a finite `Finset` of shifts. -/
theorem χ_sum_le_one (j : ℤ) (x : ℝ) :
    (∑ n ∈ P.shiftSet j, P.χ j (x - (n : ℝ) * P.step j)) ≤ (1 : ℝ) := by
  classical
  let active : ℤ → Prop := fun n => (x - (n : ℝ) * P.step j) ∈ Set.Ioc (0 : ℝ) (P.step j)
  let S : Finset ℤ := P.shiftSet j
  -- Uniqueness: at most one shift index can be active (the translates tile `ℝ` without overlap).
  have huniq : ∀ a ∈ S.filter active, ∀ b ∈ S.filter active, a = b := by
    intro a ha b hb
    have ha' : a ∈ S ∧ active a := by simpa [S, Finset.mem_filter] using ha
    have hb' : b ∈ S ∧ active b := by simpa [S, Finset.mem_filter] using hb
    have ha0 : (a : ℝ) * P.step j < x := by
      have : 0 < x - (a : ℝ) * P.step j := (Set.mem_Ioc.1 ha'.2).1
      linarith
    have ha1 : x ≤ ((a : ℝ) + 1) * P.step j := by
      have : x - (a : ℝ) * P.step j ≤ P.step j := (Set.mem_Ioc.1 ha'.2).2
      linarith
    have hb0 : (b : ℝ) * P.step j < x := by
      have : 0 < x - (b : ℝ) * P.step j := (Set.mem_Ioc.1 hb'.2).1
      linarith
    have hb1 : x ≤ ((b : ℝ) + 1) * P.step j := by
      have : x - (b : ℝ) * P.step j ≤ P.step j := (Set.mem_Ioc.1 hb'.2).2
      linarith
    by_contra hab
    have hab' : a < b ∨ b < a := lt_or_gt_of_ne hab
    cases hab' with
    | inl hablt =>
        have hab1 : a + 1 ≤ b := Int.add_one_le_of_lt hablt
        have hab1R : ((a : ℝ) + 1) * P.step j ≤ (b : ℝ) * P.step j := by
          have : (a + 1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab1
          exact mul_le_mul_of_nonneg_right this (P.step_pos j).le
        have : x ≤ (b : ℝ) * P.step j := le_trans ha1 hab1R
        exact (this.not_gt hb0).elim
    | inr hablt =>
        have hab1 : b + 1 ≤ a := Int.add_one_le_of_lt hablt
        have hab1R : ((b : ℝ) + 1) * P.step j ≤ (a : ℝ) * P.step j := by
          have : (b + 1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab1
          exact mul_le_mul_of_nonneg_right this (P.step_pos j).le
        have : x ≤ (a : ℝ) * P.step j := le_trans hb1 hab1R
        exact (this.not_gt ha0).elim
  have hcard : (S.filter active).card ≤ 1 := (Finset.card_le_one.2 huniq)
  have hsumNat :
      (∑ n ∈ S, ite (active n) (1 : ℕ) 0) ≤ 1 := by
    have hEq :
        (S.filter active).card = (∑ n ∈ S, ite (active n) (1 : ℕ) 0) := by
      simpa using (Finset.card_filter (p := active) S)
    simpa [hEq] using hcard
  -- Convert the desired sum into an `ite` sum, then use `hsumNat`.
  have hsumReal :
      (∑ n ∈ S, P.χ j (x - (n : ℝ) * P.step j)) =
        ∑ n ∈ S, ite (active n) (1 : ℝ) 0 := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hact : active n
    · have hmem :
        (x - (n : ℝ) * P.step j) ∈ Set.Ioc (0 : ℝ) (P.step j) := by
          simpa [active] using hact
      have : P.χ j (x - (n : ℝ) * P.step j) = (1 : ℝ) := by
        simpa [Params.χ] using
          (Set.indicator_of_mem hmem (fun _ : ℝ => (1 : ℝ)))
      simp [this, hact]
    · have hmem :
        (x - (n : ℝ) * P.step j) ∉ Set.Ioc (0 : ℝ) (P.step j) := by
          simpa [active] using hact
      have : P.χ j (x - (n : ℝ) * P.step j) = (0 : ℝ) := by
        simpa [Params.χ] using
          (Set.indicator_of_notMem hmem (fun _ : ℝ => (1 : ℝ)))
      simp [this, hact]
  have hsumReal' :
      (∑ n ∈ S, ite (active n) (1 : ℝ) 0) ≤ (1 : ℝ) := by
    exact_mod_cast hsumNat
  simpa [S, hsumReal] using hsumReal'

/-- Fixed-`j` bounded overlap: `∑_k P_{U_{j,k}}(ξ) ≤ 1`. -/
theorem fixed_j_overlap (j : ℤ) (ξ : UC) :
    (∑ k ∈ P.K j, P.PU j k ξ) ≤ (1 : ℝ) := by
  classical
  let arcs : Finset (RatCenter Q) := Finset.univ
  let inner : RatCenter Q → ℝ :=
    fun r =>
      ∑ n ∈ P.shiftSet j, P.χ j ((Params.ν (Q := Q) r ξ) - (n : ℝ) * P.step j)
  have hK :
      (∑ k ∈ P.K j, P.PU j k ξ) =
        ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := by
    classical
    -- Expand `K j = univ × shiftSet j` and factor out the `ϑ` term (independent of shifts).
    simp [Params.K, Params.PU, Params.t, arcs, inner, Finset.sum_product, Finset.mul_sum]
  have hinner : ∀ r : RatCenter Q, inner r ≤ (1 : ℝ) := by
    intro r
    simpa [inner, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (P.χ_sum_le_one (j := j) (x := (Params.ν (Q := Q) r ξ)))
  by_cases hex : ∃ r : RatCenter Q, ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r
  · rcases hex with ⟨r0, hr0⟩
    have hz : ∀ r : RatCenter Q, r ≠ r0 → P.ϑ r ξ = 0 := by
      intro r hr
      have hd :
          Disjoint (majorArc (Q := Q) (H := P.H) (cA := cA) r)
            (majorArc (Q := Q) (H := P.H) (cA := cA) r0) :=
        P.majorArc_disjoint (r := r) (s := r0) hr
      have : ξ ∉ majorArc (Q := Q) (H := P.H) (cA := cA) r := by
        intro hξ
        exact (hd.le_bot ⟨hξ, hr0⟩).elim
      simp [Params.ϑ, this]
    have hθ : P.ϑ r0 ξ = 1 := by simp [Params.ϑ, hr0]
    have hsum :
        (∑ r ∈ arcs, (P.ϑ r ξ) * inner r) =
          (P.ϑ r0 ξ) * inner r0 := by
      classical
      refine Finset.sum_eq_single r0 ?_ ?_
      · intro r hrmem hne
        have : P.ϑ r ξ = 0 := hz r hne
        simp [this]
      · intro hr0'
        exact (hr0' (by simp [arcs])).elim
    calc
      (∑ k ∈ P.K j, P.PU j k ξ) = ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := hK
      _ = (P.ϑ r0 ξ) * inner r0 := hsum
      _ = inner r0 := by simp [hθ]
      _ ≤ 1 := hinner r0
  · have hθ0 : ∀ r : RatCenter Q, P.ϑ r ξ = 0 := by
      intro r
      have : ξ ∉ majorArc (Q := Q) (H := P.H) (cA := cA) r := by
        intro hξ
        exact hex ⟨r, hξ⟩
      simp [Params.ϑ, this]
    calc
      (∑ k ∈ P.K j, P.PU j k ξ) = ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := hK
      _ = 0 := by
            classical
            simp [arcs, hθ0]
      _ ≤ 1 := by norm_num

/-- Global overlap bound (T1 upper bound): `∑_{j∈J} ∑_k P_{U_{j,k}}(ξ) ≤ #J`. -/
theorem global_overlap (ξ : UC) :
    (∑ j ∈ P.J, ∑ k ∈ P.K j, P.PU j k ξ) ≤ (P.J.card : ℝ) := by
  classical
  -- Apply the fixed-`j` bound and sum.
  have hterm : ∀ j ∈ P.J, (∑ k ∈ P.K j, P.PU j k ξ) ≤ (1 : ℝ) := by
    intro j hj
    exact le_trans (by simpa using P.fixed_j_overlap (j := j) (ξ := ξ)) (le_rfl)
  calc
    (∑ j ∈ P.J, ∑ k ∈ P.K j, P.PU j k ξ)
        ≤ ∑ j ∈ P.J, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun j hj => hterm j hj)
    _ = (P.J.card : ℝ) := by simp

/-!
## Export to `FejerBankedConstruction.Setup`
-/

noncomputable def setup : SSU.Instances.FejerBankedConstruction.Setup (κ (Q := Q)) (ι (Q := Q)) where
  X := 0
  H := P.H
  J := P.J
  K := P.K
  parent := Prod.fst
  ϑ := P.ϑ
  hϑ := fun r => P.measurable_ϑ r
  ϑ_nonneg := fun r x => P.ϑ_nonneg r x
  ϑ_le_one := fun r x => P.ϑ_le_one r x
  ν := fun r : RatCenter Q => SSU.Torus.normalCoord r.center
  hν := fun r => by
    simpa using SSU.Torus.measurable_normalCoord (c := r.center)
  χ := P.χ
  hχ := fun j => P.measurable_χ j
  χ_nonneg := fun j t => P.χ_nonneg j t
  χ_le_one := fun j t => P.χ_le_one j t
  t := P.t
  P := P.PU
  P_eq := by intro j k x; rfl
  Φ := P.Φ
  hΦ := P.hΦ
  Φmax := P.Φmax
  Φmax_nonneg := P.Φmax_nonneg
  Φ_bound := P.Φ_bound
  M := 1
  M_nonneg := by norm_num
  fixed_j_overlap := by
    intro j x
    -- `∑_{k∈K j} P_{U_{j,k}}(x) ≤ 1`.
    simpa [Params.K] using (P.fixed_j_overlap (j := j) (ξ := x))
  ΛP := (P.J.card : ℝ)
  ΛP_nonneg := by
    exact_mod_cast (Nat.zero_le _)
  global_overlap := by
    intro x
    simpa [Params.K] using (P.global_overlap (ξ := x))

end Params

end

end FejerBankedConcrete
end Instances
end SSU
