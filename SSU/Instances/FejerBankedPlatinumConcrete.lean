import SSU.Instances.FejerBankedPlatinum
import SSU.Instances.FejerBankedConstruction
import SSU.Torus.BankSpacing

import Mathlib.Data.Finset.Card

/-!
Concrete (T1) overlap bounds for the frozen “platinum” Fejér-banked conventions.

This file proves the TeX overlap *upper bounds* for the specific choices fixed in
`SSU/Instances/FejerBankedPlatinum.lean`, and exports them as a
`SSU.Instances.FejerBankedConstruction.Setup`.

We prove:
* disjointness of major arcs (hence at most one parent arc contributes at a point),
* a fixed-`j` overlap bound `M` (absolute),
* a global overlap bound `ΛP ≤ M * (#J)`.

We do **not** yet prove the TeX lower bound / “partition” statement.
-/

namespace SSU
namespace Instances
namespace FejerBankedPlatinumConcrete

open scoped BigOperators ENNReal

open MeasureTheory
open SSU.Torus
open SSU.Torus.Bank
open SSU.Instances.FejerBankedPlatinum
open Metric

noncomputable section

namespace Platinum

variable {Q : ℕ} (P : SSU.Instances.FejerBankedPlatinum.Params Q)

abbrev ι : Type := RatCenter Q
abbrev κ : Type := (RatCenter Q) × ℤ

instance : DecidableEq (κ (Q := Q)) := by classical infer_instance

theorem χBase_ne_zero_iff_abs_lt_one (u : ℝ) :
    FejerBankedPlatinum.χBase u ≠ 0 ↔ |u| < 1 := by
  constructor
  · intro h
    by_contra hu
    have hu' : 1 ≤ |u| := le_of_not_gt hu
    have hx : (1 - |u|) ≤ 0 := sub_nonpos.mpr hu'
    have : FejerBankedPlatinum.χBase u = 0 := by
      simp [FejerBankedPlatinum.χBase, max_eq_left hx]
    exact h this
  · intro hu
    have hpos : 0 < (1 - |u|) := sub_pos.mpr hu
    have h0 : 0 ≤ (1 - |u|) := le_of_lt hpos
    have : FejerBankedPlatinum.χBase u = 1 - |u| := by
      simp [FejerBankedPlatinum.χBase, max_eq_right h0]
    simpa [this] using (ne_of_gt hpos)

theorem active_abs_lt_step (j : ℤ) (x : ℝ) (n : ℤ)
    (h : P.χ j (x - (n : ℝ) * P.step j) ≠ 0) :
    |x - (n : ℝ) * P.step j| < P.step j := by
  have hstep : 0 < P.step j := P.step_pos j
  have hu : |(x - (n : ℝ) * P.step j) / P.step j| < 1 := by
    have : FejerBankedPlatinum.χBase ((x - (n : ℝ) * P.step j) / P.step j) ≠ 0 := by
      simpa [SSU.Instances.FejerBankedPlatinum.Params.χ] using h
    exact (χBase_ne_zero_iff_abs_lt_one (u := ((x - (n : ℝ) * P.step j) / P.step j))).1 this
  have : |x - (n : ℝ) * P.step j| / P.step j < 1 := by
    simpa [abs_div, abs_of_pos hstep] using hu
  exact (div_lt_one hstep).1 this

theorem active_bounds (j : ℤ) (x : ℝ) (n : ℤ)
    (h : P.χ j (x - (n : ℝ) * P.step j) ≠ 0) :
    (n : ℝ) * P.step j - P.step j < x ∧ x < (n : ℝ) * P.step j + P.step j := by
  have habs : |x - (n : ℝ) * P.step j| < P.step j :=
    active_abs_lt_step (P := P) (j := j) (x := x) (n := n) h
  have h' := (abs_lt.1 habs)
  constructor <;> linarith

theorem active_le_succ (j : ℤ) (x : ℝ) {a b : ℤ}
    (ha : P.χ j (x - (a : ℝ) * P.step j) ≠ 0)
    (hb : P.χ j (x - (b : ℝ) * P.step j) ≠ 0) :
    b ≤ a + 1 := by
  by_contra hba
  have hab : a + 2 ≤ b := by
    have : a + 1 < b := lt_of_not_ge hba
    -- `(a+1)+1 ≤ b` i.e. `a+2 ≤ b`
    simpa [add_assoc] using (Int.add_one_le_of_lt this)
  have hstep : 0 < P.step j := P.step_pos j
  have haB := active_bounds (P := P) (j := j) (x := x) (n := a) ha
  have hbB := active_bounds (P := P) (j := j) (x := x) (n := b) hb
  -- From `a+2 ≤ b` get `a*step + step ≤ b*step - step`.
  have habR : ((a + 2 : ℤ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have habStep : (a : ℝ) * P.step j + P.step j ≤ (b : ℝ) * P.step j - P.step j := by
    have : ((a + 2 : ℤ) : ℝ) * P.step j ≤ (b : ℝ) * P.step j :=
      mul_le_mul_of_nonneg_right habR hstep.le
    -- Subtract `step` from both sides.
    have : ((a + 2 : ℤ) : ℝ) * P.step j - P.step j ≤ (b : ℝ) * P.step j - P.step j :=
      sub_le_sub_right this (P.step j)
    -- Expand the left-hand side.
    -- `(a+2)*step - step = a*step + step`.
    simpa [two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg, mul_add, add_mul] using this
  have hlt : (b : ℝ) * P.step j - P.step j < (a : ℝ) * P.step j + P.step j :=
    lt_trans hbB.1 haB.2
  have : (b : ℝ) * P.step j - P.step j < (b : ℝ) * P.step j - P.step j :=
    lt_of_lt_of_le hlt habStep
  exact lt_irrefl _ this

/-- Bounded overlap for the short-axis bumps: `∑_{n∈shiftSet} χ_j(x - n*step) ≤ 2`. -/
theorem χ_sum_le_two (j : ℤ) (x : ℝ) :
    (∑ n ∈ P.shiftSet j, P.χ j (x - (n : ℝ) * P.step j)) ≤ (2 : ℝ) := by
  classical
  let active : ℤ → Prop := fun n => P.χ j (x - (n : ℝ) * P.step j) ≠ 0
  let T : Finset ℤ := (P.shiftSet j).filter active
  have hsum :
      (∑ n ∈ P.shiftSet j, P.χ j (x - (n : ℝ) * P.step j))
        =
      (∑ n ∈ T, P.χ j (x - (n : ℝ) * P.step j)) := by
    classical
    let f : ℤ → ℝ := fun n => P.χ j (x - (n : ℝ) * P.step j)
    have hpoint :
        (∑ n ∈ P.shiftSet j, if active n then f n else 0)
          =
        (∑ n ∈ P.shiftSet j, f n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      by_cases hact : active n
      · simp [hact]
      · have : f n = 0 := by
          -- `¬(f n ≠ 0)` gives `f n = 0`.
          exact not_ne_iff.mp hact
        simp [hact, this]
    have hfilter :
        (∑ n ∈ P.shiftSet j, if active n then f n else 0)
          =
        (∑ n ∈ T, f n) := by
      -- `sum_filter` is `∑_{n∈filter} f = ∑_{n∈s} if p n then f n else 0`.
      simpa [T] using
        (Finset.sum_filter (s := P.shiftSet j) (p := active) (f := fun n => f n)).symm
    -- Combine, and unfold `f`.
    have :
        (∑ n ∈ P.shiftSet j, f n) =
          (∑ n ∈ T, f n) := by
      calc
        (∑ n ∈ P.shiftSet j, f n)
            = (∑ n ∈ P.shiftSet j, if active n then f n else 0) := by simpa [hpoint]
        _ = (∑ n ∈ T, f n) := hfilter
    simpa [f] using this
  -- bound the active-index set size by `2` using `min'`.
  have hcard : T.card ≤ 2 := by
    by_cases hne : T.Nonempty
    · let m : ℤ := T.min' hne
      have hm_mem : m ∈ T := Finset.min'_mem T hne
      have hm_act : active m := (Finset.mem_filter.1 hm_mem).2
      have hsub : T ⊆ ({m, m + 1} : Finset ℤ) := by
        intro n hn
        have hn_act : active n := (Finset.mem_filter.1 hn).2
        have hmn : m ≤ n := Finset.min'_le T n hn
        have hnm : n ≤ m + 1 :=
          active_le_succ (P := P) (j := j) (x := x) (a := m) (b := n) hm_act hn_act
        have : n = m ∨ n = m + 1 := by
          omega
        rcases this with rfl | rfl <;> simp
      have : T.card ≤ ({m, m + 1} : Finset ℤ).card := Finset.card_le_card hsub
      have hpair : ({m, m + 1} : Finset ℤ).card ≤ 2 := Finset.card_le_two
      exact le_trans this hpair
    · -- empty
      simpa [T, Finset.not_nonempty_iff_eq_empty.mp hne]
  -- Now: sum ≤ card(T) * 1 ≤ 2.
  have hterm : ∀ n ∈ T, P.χ j (x - (n : ℝ) * P.step j) ≤ (1 : ℝ) := by
    intro n hn
    exact P.χ_le_one j _
  calc
    (∑ n ∈ P.shiftSet j, P.χ j (x - (n : ℝ) * P.step j))
        = (∑ n ∈ T, P.χ j (x - (n : ℝ) * P.step j)) := by simpa [hsum]
    _ ≤ (∑ _n ∈ T, (1 : ℝ)) := by
          exact Finset.sum_le_sum (fun n hn => hterm n hn)
    _ = (T.card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hcard

/-!
## Major arc disjointness (at most one parent arc contributes)
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
  have hqq_le_Q2 : ((r.q * s.q : ℕ) : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have : r.q * s.q ≤ Q * Q := Nat.mul_le_mul r.hqQ s.hqQ
    simpa [pow_two, Nat.cast_mul] using
      (show ((r.q * s.q : ℕ) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) by exact_mod_cast this)
  have hqq_le_H : ((r.q * s.q : ℕ) : ℝ) ≤ P.H := le_trans hqq_le_Q2 P.hQH
  have hHlt : P.H < (500 : ℝ) * P.H := by
    have : (1 : ℝ) < (500 : ℝ) := by norm_num
    simpa [one_mul] using (mul_lt_mul_of_pos_right this P.hH)
  have hqq_lt_500H : ((r.q * s.q : ℕ) : ℝ) < (500 : ℝ) * P.H :=
    lt_of_le_of_lt hqq_le_H hHlt
  have hdiv : (1 : ℝ) / ((500 : ℝ) * P.H) < (1 : ℝ) / ((r.q * s.q : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt hnpos hqq_lt_500H
  have hsum : (cA / P.H) + (cA / P.H) = (1 : ℝ) / ((500 : ℝ) * P.H) := by
    have : (2 * cA : ℝ) = (1 : ℝ) / 500 := by norm_num [cA]
    calc
      (cA / P.H) + (cA / P.H) = (2 * cA) / P.H := by ring
      _ = ((1 : ℝ) / 500) / P.H := by simp [this]
      _ = (1 : ℝ) / ((500 : ℝ) * P.H) := by field_simp [P.hH.ne']
  have hrad :
      (cA / P.H) + (cA / P.H) < (1 : ℝ) / ((r.q * s.q : ℕ) : ℝ) := by
    simpa [hsum] using hdiv
  have hrad' : (cA / P.H) + (cA / P.H) < dist r.center s.center :=
    lt_of_lt_of_le hrad hdist
  simpa [majorArc, RatCenter.center] using
    (closedBall_disjoint_closedBall (x := r.center) (y := s.center)
      (δ := cA / P.H) (ε := cA / P.H) hrad')

/-- Fixed-`j` overlap bound for the tube projectors: `≤ 2`. -/
theorem fixed_j_overlap (j : ℤ) (ξ : UC) :
    (∑ k ∈ P.K j, P.Pproj j k ξ) ≤ (2 : ℝ) := by
  classical
  -- Expand `K j = univ × shiftSet j`.
  let arcs : Finset (RatCenter Q) := Finset.univ
  let inner : RatCenter Q → ℝ :=
    fun r =>
      ∑ n ∈ P.shiftSet j, P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ) -
        (n : ℝ) * P.step j)
  have hK :
      (∑ k ∈ P.K j, P.Pproj j k ξ) =
        ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := by
    classical
    simp [SSU.Instances.FejerBankedPlatinum.Params.K, SSU.Instances.FejerBankedPlatinum.Params.Pproj,
      SSU.Instances.FejerBankedPlatinum.Params.t, arcs, inner, Finset.sum_product, Finset.mul_sum, mul_assoc]
  have hinner : ∀ r : RatCenter Q, inner r ≤ (2 : ℝ) := by
    intro r
    -- `inner r` is of the form `∑ χ_j(x - n*step)` with `x := ν(r,ξ)`.
    simpa [inner, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm,
      mul_comm] using
      (χ_sum_le_two (P := P) (j := j) (x := (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ)))
  -- At most one arc contributes, and for that arc the inner sum is `≤ 2`.
  by_cases hex : ∃ r : RatCenter Q, ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r
  · rcases hex with ⟨r0, hr0⟩
    have hz : ∀ r : RatCenter Q, r ≠ r0 → P.ϑ r ξ = 0 := by
      intro r hr
      have hd :
          Disjoint (majorArc (Q := Q) (H := P.H) (cA := cA) r)
            (majorArc (Q := Q) (H := P.H) (cA := cA) r0) :=
        majorArc_disjoint (P := P) (r := r) (s := r0) hr
      have : ξ ∉ majorArc (Q := Q) (H := P.H) (cA := cA) r := by
        intro hξ
        exact (hd.le_bot ⟨hξ, hr0⟩).elim
      simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, this]
    have hθ : P.ϑ r0 ξ = 1 := by
      simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, hr0]
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
      (∑ k ∈ P.K j, P.Pproj j k ξ) = ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := hK
      _ = (P.ϑ r0 ξ) * inner r0 := hsum
      _ = inner r0 := by simp [hθ]
      _ ≤ 2 := hinner r0
  · have hθ0 : ∀ r : RatCenter Q, P.ϑ r ξ = 0 := by
      intro r
      have : ξ ∉ majorArc (Q := Q) (H := P.H) (cA := cA) r := by
        intro hξ
        exact hex ⟨r, hξ⟩
      simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, this]
    calc
      (∑ k ∈ P.K j, P.Pproj j k ξ) = ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := hK
      _ = 0 := by
            classical
            simp [arcs, hθ0]
      _ ≤ 2 := by norm_num

/-- Global overlap bound: `∑_{j∈J}∑_{k∈K j} P_{U_{j,k}}(ξ) ≤ 2 * (#J)`. -/
theorem global_overlap (ξ : UC) :
    (∑ j ∈ P.J, ∑ k ∈ P.K j, P.Pproj j k ξ) ≤ (2 : ℝ) * (P.J.card : ℝ) := by
  classical
  have hterm : ∀ j ∈ P.J, (∑ k ∈ P.K j, P.Pproj j k ξ) ≤ (2 : ℝ) := by
    intro j hj
    simpa using fixed_j_overlap (P := P) (j := j) (ξ := ξ)
  calc
    (∑ j ∈ P.J, ∑ k ∈ P.K j, P.Pproj j k ξ)
        ≤ ∑ _j ∈ P.J, (2 : ℝ) := by
              exact Finset.sum_le_sum (fun j hj => hterm j hj)
    _ = (2 : ℝ) * (P.J.card : ℝ) := by
          -- `∑ 2 = card • 2 = card * 2 = 2 * card`.
          simpa [two_mul, mul_assoc, mul_comm, mul_left_comm] using
            (Finset.sum_const (s := P.J) (b := (2 : ℝ)))

/-- Export the platinum construction as a `FejerBankedConstruction.Setup`. -/
noncomputable def setup :
    SSU.Instances.FejerBankedConstruction.Setup (κ (Q := Q)) (ι (Q := Q)) where
  X := 0
  H := P.H
  J := P.J
  K := P.K
  parent := Prod.fst
  ϑ := P.ϑ
  hϑ := fun r => P.measurable_ϑ r
  ϑ_nonneg := fun r x => P.ϑ_nonneg r x
  ϑ_le_one := fun r x => P.ϑ_le_one r x
  ν := fun r : RatCenter Q => SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r
  hν := fun r => by
    simpa using (SSU.Instances.FejerBankedPlatinum.Params.measurable_ν (Q := Q) (r := r))
  χ := P.χ
  hχ := fun j => P.measurable_χ j
  χ_nonneg := fun j t => P.χ_nonneg j t
  χ_le_one := fun j t => P.χ_le_one j t
  t := P.t
  P := P.Pproj
  P_eq := by
    intro j k x
    rfl
  Φ := P.Φ
  hΦ := P.memLp_Φ
  Φmax := 1
  Φmax_nonneg := by norm_num
  Φ_bound := fun x => by
    simpa using (P.Φ_bound_one x)
  M := 2
  M_nonneg := by norm_num
  fixed_j_overlap := by
    intro j x
    simpa using fixed_j_overlap (P := P) (j := j) (ξ := x)
  ΛP := (2 : ℝ) * (P.J.card : ℝ)
  ΛP_nonneg := by positivity
  global_overlap := by
    intro x
    simpa using global_overlap (P := P) (ξ := x)

end Platinum

end

end FejerBankedPlatinumConcrete
end Instances
end SSU
