import SSU.Instances.FejerBankedPlatinum
import SSU.Instances.FejerBankedConstruction
import SSU.Instances.FejerBankedTeX
import SSU.Torus.BankSpacing

import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-!
Concrete (T1) tube-overlap bounds for the frozen “platinum” Fejér-banked conventions.

This file proves the TeX overlap *upper bounds* for the specific choices fixed in
`SSU/Instances/FejerBankedPlatinum.lean`, and exports them as a
`SSU.Instances.FejerBankedConstruction.Setup`.

We prove:
* disjointness of major arcs (hence at most one parent arc contributes at a point),
* a fixed-`j` overlap bound `M` (absolute),
* a global overlap bound `ΛP ≤ M * (#J)`.

We prove both sides of the TeX (T1) statement in a Lean-usable form:

* an upper bound `globalSum ≤ ΛP`,
* a lower bound `1 ≤ globalSum` on the active tube region,
* and `globalSum = 0` off that region.
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
## “Other side” of the translate bound for the tent bump

The TeX condition `\eqref{eq:chi_j}` asserts a two-sided partition-of-unity property for the
translates of `χ_j`. For our concrete choice `χ_j(t) = χBase(t / step)`, the *infinite* translate
sum is exactly `1` (two active translates at each point). Here we record a Lean-usable finite-set
version: on a band where the two active translates lie inside the truncation `shiftSet`, the
finite sum is `≥ 1`.
-/

theorem χBase_add_shift_eq_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    FejerBankedPlatinum.χBase t + FejerBankedPlatinum.χBase (t - 1) = 1 := by
  have ht0' : 0 ≤ (1 - |t|) := by
    -- On `[0,1]`, `|t| = t` and `1 - t ≥ 0`.
    simpa [abs_of_nonneg ht0] using (sub_nonneg.mpr ht1)
  have ht1' : 0 ≤ (1 - |t - 1|) := by
    -- On `[0,1]`, `t-1 ≤ 0` so `|t-1| = 1 - t` and `1 - |t-1| = t ≥ 0`.
    have ht_le1 : t - 1 ≤ 0 := by linarith
    have habs : |t - 1| = 1 - t := by simpa [abs_of_nonpos ht_le1] using (abs_of_nonpos ht_le1)
    -- Use the identity `1 - (1 - t) = t`.
    simpa [habs] using ht0
  -- Unfold the tent definition via `max`.
  have hχt : FejerBankedPlatinum.χBase t = 1 - |t| := by
    simp [FejerBankedPlatinum.χBase, max_eq_right ht0']
  have hχt1 : FejerBankedPlatinum.χBase (t - 1) = 1 - |t - 1| := by
    simp [FejerBankedPlatinum.χBase, max_eq_right ht1']
  -- Now compute on `[0,1]`.
  have ht_le1 : t - 1 ≤ 0 := by linarith
  have habs0 : |t| = t := abs_of_nonneg ht0
  have habs1 : |t - 1| = 1 - t := by
    -- `t-1 ≤ 0` so `|t-1| = -(t-1) = 1-t`.
    simpa [abs_of_nonpos ht_le1] using (abs_of_nonpos ht_le1)
  calc
    FejerBankedPlatinum.χBase t + FejerBankedPlatinum.χBase (t - 1)
        = (1 - |t|) + (1 - |t - 1|) := by simp [hχt, hχt1]
    _ = (1 - t) + (1 - (1 - t)) := by simp [habs0, habs1]
    _ = 1 := by ring

theorem χBase_floor_pair_sum_eq_one (u : ℝ) :
    FejerBankedPlatinum.χBase (u - Int.floor u)
      + FejerBankedPlatinum.χBase (u - (Int.floor u + 1)) = 1 := by
  -- Reduce to the unit-interval identity at `t := u - floor u ∈ [0,1]`.
  set t : ℝ := u - Int.floor u with ht
  have ht0 : 0 ≤ t := by
    have : ((Int.floor u : ℤ) : ℝ) ≤ u := by exact Int.floor_le u
    simpa [t, sub_nonneg] using this
  have htlt1 : t < 1 := by
    have : u < (Int.floor u : ℤ) + 1 := Int.lt_floor_add_one u
    -- Rearrange `u < floor u + 1` to `u - floor u < 1`.
    have : u - (Int.floor u : ℤ) < 1 := by linarith
    simpa [t] using this
  have ht1 : t ≤ 1 := htlt1.le
  -- `u - (floor u + 1) = (u - floor u) - 1`.
  have hshift : u - (Int.floor u + 1) = t - 1 := by
    -- `u - (floor u + 1) = (u - floor u) - 1`.
    simp [t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Apply the identity on `[0,1]`.
  simpa [t, hshift] using (χBase_add_shift_eq_one (t := t) ht0 ht1)

/-- Finite translate sum lower bound on a band where the two active translates are in `shiftSet`. -/
theorem χ_sum_ge_one_of_abs_le (j : ℤ) (x : ℝ)
    (hx : |x| ≤ ((P.N j : ℝ) - 1) * P.step j) :
    (1 : ℝ) ≤ (∑ n ∈ P.shiftSet j, P.χ j (x - (n : ℝ) * P.step j)) := by
  classical
  have hstep : 0 < P.step j := P.step_pos j
  -- Scale to `u = x / step`.
  set u : ℝ := x / P.step j with hu
  have huAbs : |u| ≤ (P.N j : ℝ) - 1 := by
    -- Divide the band bound by `step > 0`.
    have : |x| / P.step j ≤ ((P.N j : ℝ) - 1) * P.step j / P.step j := by
      exact (div_le_div_of_nonneg_right hx hstep.le)
    simpa [hu, abs_div, abs_of_pos hstep, mul_div_cancel_right₀ _ hstep.ne'] using this
  -- The two active indices for the tent are `floor u` and `floor u + 1`.
  let n0 : ℤ := Int.floor u
  have hn0_pair :
      P.χ j (x - (n0 : ℝ) * P.step j)
        + P.χ j (x - ((n0 + 1) : ℝ) * P.step j) = 1 := by
    -- Rewrite `P.χ` into `χBase` and use the floor-pair identity.
    have hdiv0 :
        (x - (n0 : ℝ) * P.step j) / P.step j = u - (n0 : ℝ) := by
      -- `(x - n0*step)/step = x/step - n0`.
      simp [u, hu, sub_div, hstep.ne']
    have hdiv1 :
        (x - ((n0 + 1) : ℝ) * P.step j) / P.step j = u - ((n0 + 1 : ℤ) : ℝ) := by
      simp [u, hu, sub_div, hstep.ne']
    have h0 :
        P.χ j (x - (n0 : ℝ) * P.step j)
          = FejerBankedPlatinum.χBase (u - (n0 : ℝ)) := by
      simp [SSU.Instances.FejerBankedPlatinum.Params.χ, FejerBankedPlatinum.Params.χ, hdiv0]
    have h1 :
        P.χ j (x - ((n0 + 1) : ℝ) * P.step j)
          = FejerBankedPlatinum.χBase (u - ((n0 + 1 : ℤ) : ℝ)) := by
      simp [SSU.Instances.FejerBankedPlatinum.Params.χ, FejerBankedPlatinum.Params.χ, hdiv1]
    have hχ :
        FejerBankedPlatinum.χBase (u - (n0 : ℝ))
          + FejerBankedPlatinum.χBase (u - ((n0 + 1 : ℤ) : ℝ)) = 1 := by
      -- This is the floor-pair identity, rewritten with `n0 := floor u`.
      simpa [n0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (χBase_floor_pair_sum_eq_one (u := u))
    simpa [h0, h1] using hχ
  -- Show `n0` and `n0+1` lie in the truncation set.
  have huAbsN : |u| ≤ (P.N j : ℝ) := by
    have : (P.N j : ℝ) - 1 ≤ (P.N j : ℝ) := by linarith
    exact le_trans huAbs this
  have huLower : (-(P.N j : ℝ)) ≤ u :=
    (abs_le.mp huAbsN).1
  have huUpper : u < (P.N j : ℝ) := by
    have hu_le : u ≤ (P.N j : ℝ) - 1 := le_trans (le_abs_self u) huAbs
    have : (P.N j : ℝ) - 1 < (P.N j : ℝ) := by linarith
    exact lt_of_le_of_lt hu_le this
  have hn0_ge : (-Int.ofNat (P.N j)) ≤ n0 := by
    -- Use `Int.le_floor` with the lower bound `-N ≤ u`.
    have : ((-Int.ofNat (P.N j) : ℤ) : ℝ) ≤ u := by
      simpa using huLower
    exact (Int.le_floor).2 this
  have hn0_le : n0 + 1 ≤ Int.ofNat (P.N j) := by
    -- From `u < N`, we get `floor u ≤ N - 1`.
    have hfloor : Int.floor u ≤ (Int.ofNat (P.N j)) - 1 := by
      have : u < (Int.ofNat (P.N j) : ℤ) := by
        simpa using huUpper
      simpa using (Int.floor_le_sub_one_iff (a := u) (z := (Int.ofNat (P.N j) : ℤ))).2 this
    -- Add `1` to both sides.
    have := Int.add_le_add_right hfloor 1
    simpa [add_assoc] using this
  have hn0_mem : n0 ∈ P.shiftSet j := by
    -- `shiftSet j = Icc (-N) N`.
    have hn0_le' : n0 ≤ Int.ofNat (P.N j) := by
      have : n0 ≤ n0 + 1 := by omega
      exact le_trans this hn0_le
    exact (Finset.mem_Icc).2 ⟨hn0_ge, hn0_le'⟩
  have hn1_mem : (n0 + 1) ∈ P.shiftSet j := by
    have hn1_ge : (-Int.ofNat (P.N j)) ≤ n0 + 1 := le_trans hn0_ge (by omega)
    exact (Finset.mem_Icc).2 ⟨hn1_ge, hn0_le⟩
  -- Compare the full sum to the sum over the two active indices.
  let f : ℤ → ℝ := fun n => P.χ j (x - (n : ℝ) * P.step j)
  have hf_nonneg : ∀ n : ℤ, 0 ≤ f n := by
    intro n
    exact P.χ_nonneg j _
  have hsubset : ({n0, n0 + 1} : Finset ℤ) ⊆ P.shiftSet j := by
    intro n hn
    have hn' : n = n0 ∨ n = n0 + 1 := by simpa using (Finset.mem_insert.1 hn)
    rcases hn' with rfl | rfl
    · exact hn0_mem
    · exact hn1_mem
  have hle :
      (∑ n ∈ ({n0, n0 + 1} : Finset ℤ), f n)
        ≤ (∑ n ∈ P.shiftSet j, f n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro n _hn _hnnot
    exact hf_nonneg n
  have hpair :
      (∑ n ∈ ({n0, n0 + 1} : Finset ℤ), f n) = f n0 + f (n0 + 1) := by
    have hne : n0 ≠ n0 + 1 := by omega
    simp [f, Finset.sum_insert, hne]
  -- Conclude `1 ≤ sum`.
  have : (1 : ℝ) ≤ (∑ n ∈ ({n0, n0 + 1} : Finset ℤ), f n) := by
    -- `f n0 + f (n0+1) = 1`.
    have : f n0 + f (n0 + 1) = 1 := by
      simpa [f] using hn0_pair
    simpa [hpair, this]
  exact le_trans this hle

/-!
### A convenient corollary: coverage from the shell bound `|x| ≤ step j`
-/

/--
If the truncation size satisfies `2 ≤ N j`, then the translate-sum lower bound holds on the
smaller band `|x| ≤ step j`.

This is the form used to discharge the TeX “coverage by translates” condition on `𝒟_j`.
-/
theorem χ_sum_ge_one_of_abs_le_step (j : ℤ) (x : ℝ) (hN : 2 ≤ P.N j)
    (hx : |x| ≤ P.step j) :
    (1 : ℝ) ≤ (∑ n ∈ P.shiftSet j, P.χ j (x - (n : ℝ) * P.step j)) := by
  have hstep : 0 < P.step j := P.step_pos j
  have hN' : (1 : ℝ) ≤ (P.N j : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (P.N j : ℝ) := by exact_mod_cast hN
    linarith
  have hmul : P.step j ≤ ((P.N j : ℝ) - 1) * P.step j := by
    have := (mul_le_mul_of_nonneg_right hN' (le_of_lt hstep) : (1 : ℝ) * P.step j ≤ _)
    simpa [one_mul] using this
  have hx' : |x| ≤ ((P.N j : ℝ) - 1) * P.step j := le_trans hx hmul
  exact χ_sum_ge_one_of_abs_le (P := P) (j := j) (x := x) hx'

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
      (P.shellCut j r ξ) *
        (∑ n ∈ P.shiftSet j,
          P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ) - (n : ℝ) * P.step j))
  have hK :
      (∑ k ∈ P.K j, P.Pproj j k ξ) =
        ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := by
    classical
    -- Expand `K j = univ × shiftSet j`, then factor out the `r`-dependent constants.
    calc
      (∑ k ∈ P.K j, P.Pproj j k ξ)
          = ∑ r ∈ arcs, ∑ n ∈ P.shiftSet j, P.Pproj j (r, n) ξ := by
              simp [SSU.Instances.FejerBankedPlatinum.Params.K, arcs, Finset.sum_product]
      _ = ∑ r ∈ arcs, (P.ϑ r ξ) * inner r := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            -- Unfold `Pproj` and `t`, then use `Finset.mul_sum` twice.
            have :
                (∑ n ∈ P.shiftSet j, P.Pproj j (r, n) ξ)
                  =
                (P.ϑ r ξ) * inner r := by
              -- Expand `Pproj`, then factor out the `n`-independent constants.
              -- Write `ν := ν_r(ξ)` to shorten the notation.
              set ν : ℝ := SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ with hν
              calc
                (∑ n ∈ P.shiftSet j, P.Pproj j (r, n) ξ)
                    =
                    (∑ n ∈ P.shiftSet j,
                      (P.shellCut j r ξ) *
                        ((P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j))) := by
                      simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj,
                        SSU.Instances.FejerBankedPlatinum.Params.shellCut,
                        SSU.Instances.FejerBankedPlatinum.Params.t,
                        ν, hν, mul_assoc, mul_left_comm, mul_comm]
                _ = (P.shellCut j r ξ) *
                      (∑ n ∈ P.shiftSet j, (P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j)) := by
                      -- Pull out `shellCut`.
                      simpa [Finset.mul_sum, mul_assoc] using
                        (Finset.mul_sum (s := P.shiftSet j)
                          (f := fun n : ℤ => (P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j))
                          (a := P.shellCut j r ξ)).symm
                _ = (P.shellCut j r ξ) *
                      ((P.ϑ r ξ) *
                        (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j))) := by
                      -- Pull out `ϑ`.
                      have hθpull :
                          (∑ n ∈ P.shiftSet j, (P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j))
                            =
                          (P.ϑ r ξ) * (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j)) := by
                        simpa [mul_assoc] using
                          (Finset.mul_sum (s := P.shiftSet j)
                            (f := fun n : ℤ => P.χ j (ν - (n : ℝ) * P.step j))
                            (a := P.ϑ r ξ)).symm
                      -- Multiply by `shellCut` on the left.
                      have := congrArg (fun z => (P.shellCut j r ξ) * z) hθpull
                      simpa [mul_assoc] using this
                _ = (P.ϑ r ξ) * ((P.shellCut j r ξ) *
                      (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j))) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
                _ = (P.ϑ r ξ) * inner r := by
                      -- Unfold `inner` and `ν`.
                      simp [inner, ν, hν, mul_assoc, mul_left_comm, mul_comm]
            exact this
  have hinner : ∀ r : RatCenter Q, inner r ≤ (2 : ℝ) := by
    intro r
    by_cases hDj : ξ ∈ P.Dj j r
    · have hcut : P.shellCut j r ξ = 1 := by
        simp [SSU.Instances.FejerBankedPlatinum.Params.shellCut, hDj]
      -- On the shell, `inner r` is exactly the translate sum, so it is `≤ 2`.
      simpa [inner, hcut] using
        (χ_sum_le_two (P := P) (j := j)
          (x := (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ)))
    · have hcut : P.shellCut j r ξ = 0 := by
        simp [SSU.Instances.FejerBankedPlatinum.Params.shellCut, hDj]
      -- Off the shell, `inner r = 0`.
      simp [inner, hcut]
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

/--
Fixed-`j` **lower** bound on the shell:
if `ξ` lies in a major arc `r0`, and also in the normal-coordinate shell `Dj j r0`,
then the shell-sum over tube indices is `≥ 1`, provided the finite translate family
`shiftSet j` is large enough to cover the relevant point.

This is the Lean version of the TeX claim
`∑_{k: I(k)=I} P_{U_{j,k}}(ξ) ≍ ϑ_I(ξ)` on `𝒟_j`.
-/
theorem fixed_j_overlap_ge_one_of_mem (j : ℤ) (ξ : UC) (r0 : RatCenter Q)
    (hr0 : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r0)
    (hDj : ξ ∈ P.Dj j r0)
    (hN : 2 ≤ P.N j) :
    (1 : ℝ) ≤ (∑ k ∈ P.K j, P.Pproj j k ξ) := by
  classical
  have hνle : |(SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r0 ξ)| ≤ P.step j := by
    have hDj' :
        P.step (j + 1) < |(SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r0 ξ)| ∧
          |(SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r0 ξ)| ≤ P.step j := by
      simpa [SSU.Instances.FejerBankedPlatinum.Params.Dj] using hDj
    exact hDj'.2
  -- Only the parent arc `r0` contributes (disjoint major arcs).
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
  -- On the shell, the shell cut-off is `1`.
  have hcut : P.shellCut j r0 ξ = 1 := by
    simp [SSU.Instances.FejerBankedPlatinum.Params.shellCut, hDj]
  -- Reduce the sum over `K j = arcs × shiftSet` to the `r0` slice.
  let arcs : Finset (RatCenter Q) := Finset.univ
  let f : RatCenter Q → ℝ :=
    fun r =>
      (P.ϑ r ξ) *
        ((P.shellCut j r ξ) *
          (∑ n ∈ P.shiftSet j,
            P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ) - (n : ℝ) * P.step j)))
  have hK :
      (∑ k ∈ P.K j, P.Pproj j k ξ) = ∑ r ∈ arcs, f r := by
    classical
    calc
      (∑ k ∈ P.K j, P.Pproj j k ξ)
          = ∑ r ∈ arcs, ∑ n ∈ P.shiftSet j, P.Pproj j (r, n) ξ := by
              simp [SSU.Instances.FejerBankedPlatinum.Params.K, arcs, Finset.sum_product]
      _ = ∑ r ∈ arcs, f r := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            -- Unfold and factor out `ϑ` and the shell cut-off.
            -- Same algebra as in `fixed_j_overlap`: compute the inner `n`-sum.
            set ν : ℝ := SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ with hν
            calc
              (∑ n ∈ P.shiftSet j, P.Pproj j (r, n) ξ)
                  =
                  (P.ϑ r ξ) *
                    ((P.shellCut j r ξ) *
                      (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j))) := by
                    -- Repeat the factoring argument.
                    calc
                      (∑ n ∈ P.shiftSet j, P.Pproj j (r, n) ξ)
                          =
                          (∑ n ∈ P.shiftSet j,
                            (P.shellCut j r ξ) *
                              ((P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j))) := by
                                simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj,
                                  SSU.Instances.FejerBankedPlatinum.Params.shellCut,
                                  SSU.Instances.FejerBankedPlatinum.Params.t,
                                  ν, hν, mul_assoc, mul_left_comm, mul_comm]
                      _ = (P.shellCut j r ξ) *
                            (∑ n ∈ P.shiftSet j, (P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j)) := by
                                simpa [Finset.mul_sum, mul_assoc] using
                                  (Finset.mul_sum (s := P.shiftSet j)
                                    (f := fun n : ℤ => (P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j))
                                    (a := P.shellCut j r ξ)).symm
                      _ = (P.shellCut j r ξ) *
                            ((P.ϑ r ξ) * (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j))) := by
                                have hθpull :
                                    (∑ n ∈ P.shiftSet j, (P.ϑ r ξ) * P.χ j (ν - (n : ℝ) * P.step j))
                                      =
                                    (P.ϑ r ξ) * (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j)) := by
                                  -- Factor out the constant `ϑ r ξ` from the sum.
                                  simpa [mul_assoc] using
                                    (Finset.mul_sum (s := P.shiftSet j)
                                      (f := fun n : ℤ => P.χ j (ν - (n : ℝ) * P.step j))
                                      (a := P.ϑ r ξ)).symm
                                simpa [hθpull, mul_assoc] 
                      _ = (P.ϑ r ξ) * ((P.shellCut j r ξ) * (∑ n ∈ P.shiftSet j, P.χ j (ν - (n : ℝ) * P.step j))) := by
                                simp [mul_assoc, mul_left_comm, mul_comm]
              _ = f r := by
                    -- Unfold `f` and `ν`.
                    simp [f, ν, hν, mul_assoc, mul_left_comm, mul_comm]
  have hsum :
      (∑ r ∈ arcs, f r) = f r0 := by
    classical
    refine Finset.sum_eq_single r0 ?_ ?_
    · intro r hrmem hne
      have : P.ϑ r ξ = 0 := hz r hne
      simp [f, this]
    · intro hr0'
      exact (hr0' (by simp [arcs])).elim
  -- The translate sum is `≥ 1` by the tent partition-of-unity (finite version).
  have hχ :
      (1 : ℝ) ≤
        (∑ n ∈ P.shiftSet j,
          P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r0 ξ) - (n : ℝ) * P.step j)) :=
    χ_sum_ge_one_of_abs_le_step (P := P) (j := j)
      (x := (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r0 ξ)) hN hνle
  -- Finish: all the cut-offs are `1` on this slice.
  have : (1 : ℝ) ≤ f r0 := by
    simpa [f, hθ, hcut, one_mul, mul_one, mul_assoc] using hχ
  -- Rewrite the goal.
  simpa [hK, hsum] using this

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
  X := P.X
  H := P.H
  J := P.J
  K := P.K
  parent := Prod.fst
  δ := fun j r => P.shellCut j r
  hδ := fun j r => by
    simpa using (SSU.Instances.FejerBankedPlatinum.Params.measurable_shellCut (Q := Q) (P := P) j r)
  δ_nonneg := fun j r x => by
    simpa using (SSU.Instances.FejerBankedPlatinum.Params.shellCut_nonneg (Q := Q) (P := P) j r x)
  δ_le_one := fun j r x => by
    simpa using (SSU.Instances.FejerBankedPlatinum.Params.shellCut_le_one (Q := Q) (P := P) j r x)
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
  measurable_Φ := P.measurable_Φ
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

/-!
## Coverage hypothesis (TeX `\eqref{eq:chi_j}`) for the tent bump

This is the “other side” of (T1): on the core region `majorArc r ∩ Dj j r` we get a uniform
lower bound on the translate sum.
-/

noncomputable def setup_coverageHypothesis (hN : ∀ j : ℤ, 2 ≤ P.N j) :
    SSU.Instances.FejerBankedConstruction.Coverage.Hypothesis (S := setup (P := P)) := by
  classical
  refine
    { cLower := 1
      cLower_pos := by norm_num
      cover := ?_ }
  intro j r ξ hδ hϑ
  -- Unfold `δ = shellCut` and `ϑ = 1_{majorArc}` to get membership in the core set.
  have hδ' : P.shellCut j r ξ = 1 := by
    simpa [setup] using hδ
  have hϑ' : P.ϑ r ξ = 1 := by
    simpa [setup] using hϑ
  have hr0 : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r := by
    by_contra hmem
    have : P.ϑ r ξ = 0 := by simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, hmem]
    have h01 : (0 : ℝ) = 1 := by simpa [this] using hϑ'
    have hone : (1 : ℝ) ≠ 0 := by norm_num
    exact hone (by simpa using h01.symm)
  have hDj : ξ ∈ P.Dj j r := by
    by_contra hmem
    have : P.shellCut j r ξ = 0 := by simp [SSU.Instances.FejerBankedPlatinum.Params.shellCut, hmem]
    have h01 : (0 : ℝ) = 1 := by simpa [this] using hδ'
    have hone : (1 : ℝ) ≠ 0 := by norm_num
    exact hone (by simpa using h01.symm)
  have hνle : |(SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ)| ≤ P.step j := by
    have hDj' :
        P.step (j + 1) < |(SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ)| ∧
          |(SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ)| ≤ P.step j := by
      simpa [SSU.Instances.FejerBankedPlatinum.Params.Dj] using hDj
    exact hDj'.2
  -- Compute the `χ` translate sum inside `Coverage.χSum` for this concrete setup.
  have hχSum :
      SSU.Instances.FejerBankedConstruction.Coverage.χSum (setup (P := P)) j r ξ =
        (∑ n ∈ P.shiftSet j,
          P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ) - (n : ℝ) * P.step j)) := by
    classical
    let arcs : Finset (RatCenter Q) := Finset.univ
    let g : ℤ → ℝ :=
      fun n =>
        P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ) - (n : ℝ) * P.step j)
    have h1 :
        SSU.Instances.FejerBankedConstruction.Coverage.χSum (setup (P := P)) j r ξ =
          ∑ r' ∈ arcs, ∑ n ∈ P.shiftSet j, if r' = r then g n else 0 := by
      simp [SSU.Instances.FejerBankedConstruction.Coverage.χSum, setup,
        SSU.Instances.FejerBankedPlatinum.Params.K, arcs, g,
        SSU.Instances.FejerBankedPlatinum.Params.t, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, Finset.sum_product]
    have h2 :
        (∑ r' ∈ arcs, ∑ n ∈ P.shiftSet j, if r' = r then g n else 0) =
          (∑ n ∈ P.shiftSet j, g n) := by
      classical
      -- Only `r` contributes in the outer sum.
      let inner : RatCenter Q → ℝ := fun r' => ∑ n ∈ P.shiftSet j, if r' = r then g n else 0
      have hsum : (∑ r' ∈ arcs, inner r') = inner r := by
        refine Finset.sum_eq_single r ?_ ?_
        · intro r' hr'mem hr'ne
          have : inner r' = 0 := by
            simp [inner, hr'ne]
          simp [this]
        · intro hrnot
          exact (hrnot (by simp [arcs])).elim
      -- Simplify `inner r`.
      have : inner r = ∑ n ∈ P.shiftSet j, g n := by
        simp [inner]
      simpa [inner, this] using hsum
    simpa [g] using (h1.trans h2)
  -- Apply the tent translate coverage and rewrite into `χSum`.
  have hcover :
      (1 : ℝ) ≤
        (∑ n ∈ P.shiftSet j,
          P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ) - (n : ℝ) * P.step j)) :=
    χ_sum_ge_one_of_abs_le_step (P := P) (j := j)
      (x := (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ)) (hN j) hνle
  -- `Coverage.Hypothesis` wants a lower bound on `χSum`.
  simpa [hχSum] using hcover

/-!
## TeX-style (T1) “partition on a fixed shell” bounds

This matches the line after `\eqref{eq:P_U_def}` in `05b_SSU.tex`:
on `𝒟_j`, summing over tubes with fixed parent arc recovers `ϑ_I` up to constants.
-/

theorem PSum_bounds_on_shell (hN : ∀ j : ℤ, 2 ≤ P.N j) (j : ℤ) (r0 : RatCenter Q) (ξ : UC)
    (hr0 : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r0)
    (hDj : ξ ∈ P.Dj j r0) :
    (1 : ℝ) ≤ SSU.Instances.FejerBankedConstruction.Coverage.PSum (setup (P := P)) j r0 ξ ∧
      SSU.Instances.FejerBankedConstruction.Coverage.PSum (setup (P := P)) j r0 ξ ≤ (2 : ℝ) := by
  classical
  have hδ : (setup (P := P)).δ j r0 ξ = 1 := by
    -- `δ = shellCut` for the platinum setup.
    simp [setup, SSU.Instances.FejerBankedPlatinum.Params.shellCut, hDj]
  have hϑ : (setup (P := P)).ϑ r0 ξ = 1 := by
    -- `ϑ = 1_{majorArc}`.
    simp [setup, SSU.Instances.FejerBankedPlatinum.Params.ϑ, hr0]
  have hcov :
      (1 : ℝ) ≤ SSU.Instances.FejerBankedConstruction.Coverage.PSum (setup (P := P)) j r0 ξ := by
    -- Coverage gives a lower bound on `PSum` on the core region.
    simpa using
      (SSU.Instances.FejerBankedConstruction.Coverage.PSum_ge_of_hypothesis
        (S := setup (P := P))
        (h := setup_coverageHypothesis (P := P) hN)
        (j := j) (I := r0) (x := ξ) hδ hϑ)
  have hle :
      SSU.Instances.FejerBankedConstruction.Coverage.PSum (setup (P := P)) j r0 ξ ≤ (2 : ℝ) := by
    -- `PSum` is a sub-sum of the full shell sum, and we already proved `≤ 2`.
    have hfull :
        (∑ k ∈ P.K j, P.Pproj j k ξ) ≤ (2 : ℝ) := fixed_j_overlap (P := P) (j := j) (ξ := ξ)
    -- Compare `PSum` to the full sum.
    have hsub :
        SSU.Instances.FejerBankedConstruction.Coverage.PSum (setup (P := P)) j r0 ξ
          ≤ (∑ k ∈ P.K j, P.Pproj j k ξ) := by
      -- `PSum` is the same sum with extra `if parent k = r0` filter; use nonnegativity.
      classical
      -- Rewrite `PSum` into a filtered sum over `P.K j`.
      have :
          SSU.Instances.FejerBankedConstruction.Coverage.PSum (setup (P := P)) j r0 ξ
            =
            (∑ k ∈ P.K j, if k.1 = r0 then P.Pproj j k ξ else 0) := by
        simp [SSU.Instances.FejerBankedConstruction.Coverage.PSum, setup,
          SSU.Instances.FejerBankedPlatinum.Params.K]
      -- Now compare termwise.
      rw [this]
      refine Finset.sum_le_sum ?_
      intro k hk
      by_cases hkpar : k.1 = r0
      · simp [hkpar]
      · have : 0 ≤ P.Pproj j k ξ := by
          -- `Pproj` is nonnegative because it is a product of nonnegative terms.
          have h0 : 0 ≤ P.shellCut j k.1 ξ :=
            P.shellCut_nonneg (Q := Q) (j := j) (r := k.1) (x := ξ)
          have h1 : 0 ≤ P.ϑ k.1 ξ :=
            P.ϑ_nonneg (Q := Q) (r := k.1) (x := ξ)
          have h2 :
              0 ≤ P.χ j
                (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ - P.t j k) :=
            P.χ_nonneg (j := j) _
          have : 0 ≤ (P.shellCut j k.1 ξ) * ((P.ϑ k.1 ξ) * P.χ j
              ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)) :=
            mul_nonneg h0 (mul_nonneg h1 h2)
          simpa [SSU.Instances.FejerBankedPlatinum.Params.Pproj] using this
        simp [hkpar, this]
    exact le_trans hsub hfull
  exact ⟨hcov, hle⟩

/-!
## TeX-style bank domination (Lemma `lem:bank-dom`)

In the “hard cutoff” platinum conventions, the bank weight is simply `1_𝓐`.
Then `P_{U_{j,k}} ≤ 1_𝓐` holds with constant `c = 1`.
-/

/-- Hard bank weight `1_𝓐` for the platinum instance (as an `ℝ`-valued indicator). -/
def bankWeight : UC → ℝ :=
  Set.indicator (bankSet (Q := Q) (H := P.H) (cA := cA)) (fun _ => (1 : ℝ))

theorem Pproj_le_bankWeight (j : ℤ) (k : κ (Q := Q)) (ξ : UC) :
    P.Pproj j k ξ ≤ bankWeight (P := P) ξ := by
  classical
  -- `Pproj ≤ ϑ` since `δ ≤ 1` and `χ ≤ 1`.
  have hδ : P.shellCut j k.1 ξ ≤ 1 := P.shellCut_le_one (Q := Q) (j := j) (r := k.1) (x := ξ)
  have hχ : P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k) ≤ 1 :=
    P.χ_le_one (j := j) _
  have hθ0 : 0 ≤ P.ϑ k.1 ξ := P.ϑ_nonneg (Q := Q) (r := k.1) (x := ξ)
  have hδ0 : 0 ≤ P.shellCut j k.1 ξ := P.shellCut_nonneg (Q := Q) (j := j) (r := k.1) (x := ξ)
  have hχ0 : 0 ≤ P.χ j ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k) :=
    P.χ_nonneg (j := j) _
  have hmul : P.Pproj j k ξ ≤ P.ϑ k.1 ξ := by
    -- unfold and bound `shellCut * (ϑ * χ)` by `ϑ`.
    have hθχ : (P.ϑ k.1 ξ) * P.χ j
        ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k) ≤ P.ϑ k.1 ξ := by
      calc
        (P.ϑ k.1 ξ) * P.χ j
            ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)
            ≤ (P.ϑ k.1 ξ) * 1 := by
                exact mul_le_mul_of_nonneg_left hχ hθ0
        _ = P.ϑ k.1 ξ := by simp
    calc
      P.Pproj j k ξ
          = (P.shellCut j k.1 ξ) *
              ((P.ϑ k.1 ξ) * P.χ j
                ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)) := rfl
      _ ≤ 1 *
          ((P.ϑ k.1 ξ) * P.χ j
            ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)) := by
              exact mul_le_mul_of_nonneg_right hδ (mul_nonneg hθ0 hχ0)
      _ = ((P.ϑ k.1 ξ) * P.χ j
            ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)) := by simp
      _ ≤ P.ϑ k.1 ξ := hθχ
  -- And `ϑ ≤ 1_𝓐`.
  by_cases hmem : ξ ∈ bankSet (Q := Q) (H := P.H) (cA := cA)
  · have : bankWeight (P := P) ξ = 1 := by simp [bankWeight, hmem]
    -- If `ϑ` is `1`, then `ξ` is in the corresponding major arc, hence in the bank set.
    have hθle : P.ϑ k.1 ξ ≤ 1 := P.ϑ_le_one (Q := Q) (r := k.1) (x := ξ)
    exact le_trans hmul (by simpa [this] using hθle)
  · have : bankWeight (P := P) ξ = 0 := by simp [bankWeight, hmem]
    -- If `ξ ∉ bankSet`, then `ξ ∉ majorArc k.1`, hence `ϑ = 0`, hence `Pproj = 0`.
    have hnot : ξ ∉ majorArc (Q := Q) (H := P.H) (cA := cA) k.1 := by
      intro hmaj
      exact hmem (Set.mem_iUnion.2 ⟨k.1, hmaj⟩)
    have hθ0' : P.ϑ k.1 ξ = 0 := by simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, hnot]
    have hP0 : P.Pproj j k ξ = 0 := by simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj, hθ0']
    simpa [this, hP0]

/-!
## TeX-style global partition lower bound (restricted to shells in `J`)

The TeX argument after `\eqref{eq:P_U_def}` is:

1. On each shell `𝒟_j`, the sum over tubes (with a fixed parent arc) is `≍ ϑ_I`.
2. Summing over the finite set of shells yields a partition of unity on the bank.

In the platinum conventions, we implement the usable Lean corollary:
if `ξ` lies in some shell `Dj j r0` with `j ∈ J` inside a major arc `r0`, then the *global*
sum over all shells in `J` dominates `1`.

This is exactly what downstream “(T1) partition” usage needs.
-/

noncomputable def globalSum (ξ : UC) : ℝ :=
  ∑ j ∈ P.J, ∑ k ∈ P.K j, P.Pproj j k ξ

theorem globalSum_nonneg (ξ : UC) : 0 ≤ globalSum (P := P) ξ := by
  classical
  unfold globalSum
  refine Finset.sum_nonneg ?_
  intro j hj
  refine Finset.sum_nonneg ?_
  intro k hk
  -- `Pproj` is a product of nonnegative terms.
  have h0 : 0 ≤ P.shellCut j k.1 ξ :=
    P.shellCut_nonneg (Q := Q) (j := j) (r := k.1) (x := ξ)
  have h1 : 0 ≤ P.ϑ k.1 ξ :=
    P.ϑ_nonneg (Q := Q) (r := k.1) (x := ξ)
  have h2 :
      0 ≤ P.χ j
        (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ - P.t j k) :=
    P.χ_nonneg (j := j) _
  have : 0 ≤ (P.shellCut j k.1 ξ) * ((P.ϑ k.1 ξ) * P.χ j
      ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)) :=
    mul_nonneg h0 (mul_nonneg h1 h2)
  simpa [SSU.Instances.FejerBankedPlatinum.Params.Pproj] using this

theorem globalSum_ge_shellSum (ξ : UC) (j0 : ℤ) (hj0 : j0 ∈ P.J) :
    (∑ k ∈ P.K j0, P.Pproj j0 k ξ) ≤ globalSum (P := P) ξ := by
  classical
  unfold globalSum
  -- Use `Finset.single_le_sum` with nonnegativity.
  have hnonneg :
      ∀ j ∈ P.J, 0 ≤ (∑ k ∈ P.K j, P.Pproj j k ξ) := by
    intro j hj
    refine Finset.sum_nonneg ?_
    intro k hk
    -- same nonneg proof as above
    have h0 : 0 ≤ P.shellCut j k.1 ξ :=
      P.shellCut_nonneg (Q := Q) (j := j) (r := k.1) (x := ξ)
    have h1 : 0 ≤ P.ϑ k.1 ξ :=
      P.ϑ_nonneg (Q := Q) (r := k.1) (x := ξ)
    have h2 :
        0 ≤ P.χ j
          (SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ - P.t j k) :=
      P.χ_nonneg (j := j) _
    have : 0 ≤ (P.shellCut j k.1 ξ) * ((P.ϑ k.1 ξ) * P.χ j
        ((SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) k.1 ξ) - P.t j k)) :=
      mul_nonneg h0 (mul_nonneg h1 h2)
    simpa [SSU.Instances.FejerBankedPlatinum.Params.Pproj] using this
  -- Now apply the lemma.
  have :=
    (Finset.single_le_sum (s := P.J) (a := j0)
        (f := fun j => ∑ k ∈ P.K j, P.Pproj j k ξ)
        (by
          intro j hj
          exact hnonneg j hj)
        hj0)
  simpa using this

theorem global_partition_lower_of_mem_shell
    (hN : ∀ j : ℤ, 2 ≤ P.N j)
    (ξ : UC) (j0 : ℤ) (hj0 : j0 ∈ P.J) (r0 : RatCenter Q)
    (hr0 : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r0)
    (hDj : ξ ∈ P.Dj j0 r0) :
    (1 : ℝ) ≤ globalSum (P := P) ξ := by
  have h1 : (1 : ℝ) ≤ (∑ k ∈ P.K j0, P.Pproj j0 k ξ) :=
    fixed_j_overlap_ge_one_of_mem (P := P) (j := j0) (ξ := ξ) (r0 := r0) hr0 hDj (hN j0)
  have hle : (∑ k ∈ P.K j0, P.Pproj j0 k ξ) ≤ globalSum (P := P) ξ :=
    globalSum_ge_shellSum (P := P) (ξ := ξ) (j0 := j0) hj0
  exact le_trans h1 hle

/-!
## A clean “(T1) partition region” statement for the Lean construction

The actual support of the platinum projectors is the region where *both* the tangential arc cutoff
and the dyadic shell cutoff are active.

This is the precise Lean analogue of the TeX informal line “each `P_{U_{j,k}}` is supported in
`𝓐 ∩ 𝒟_j`”.  It lets downstream code reason about the partition without committing to the exact
choice of what set should be called “the bank” (hard bank vs smooth bank vs interior bank).
-/

/-- The union of all active tube regions: `⋃_{j∈J} ⋃_r (majorArc r ∩ Dj j r)`. -/
def bankShellUnion : Set UC :=
  {ξ : UC | ∃ j ∈ P.J, ∃ r : RatCenter Q, ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r ∧ ξ ∈ P.Dj j r}

theorem mem_bankShellUnion_iff (ξ : UC) :
    ξ ∈ bankShellUnion (P := P) ↔
      ∃ j ∈ P.J, ∃ r : RatCenter Q,
        ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r ∧ ξ ∈ P.Dj j r := Iff.rfl

theorem globalSum_eq_zero_of_not_mem_bankShellUnion (ξ : UC)
    (hξ : ξ ∉ bankShellUnion (P := P)) :
    globalSum (P := P) ξ = 0 := by
  classical
  unfold globalSum
  -- Show each term in the sum is zero.
  refine Finset.sum_eq_zero ?_
  intro j hj
  refine Finset.sum_eq_zero ?_
  intro k hk
  -- If `k = (r,n)`, then `Pproj j k ξ` can only be nonzero if `ξ ∈ majorArc r ∧ ξ ∈ Dj j r`.
  have hnot : ¬(ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) k.1 ∧ ξ ∈ P.Dj j k.1) := by
    intro hmem
    exact hξ ⟨j, hj, k.1, hmem.1, hmem.2⟩
  by_cases hmaj : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) k.1
  · by_cases hDj : ξ ∈ P.Dj j k.1
    · exact (hnot ⟨hmaj, hDj⟩).elim
    · -- shellCut is `0`, so `Pproj = 0`.
      have : P.shellCut j k.1 ξ = 0 := by
        simp [SSU.Instances.FejerBankedPlatinum.Params.shellCut, hDj]
      simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj, this]
  · -- ϑ is `0`, so `Pproj = 0`.
    have : P.ϑ k.1 ξ = 0 := by
      simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, hmaj]
    simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj, this]

theorem global_partition_lower_of_mem_bankShellUnion
    (hN : ∀ j : ℤ, 2 ≤ P.N j)
    (ξ : UC) (hξ : ξ ∈ bankShellUnion (P := P)) :
    (1 : ℝ) ≤ globalSum (P := P) ξ := by
  rcases hξ with ⟨j0, hj0, r0, hr0, hDj⟩
  exact global_partition_lower_of_mem_shell (P := P) (hN := hN) (ξ := ξ) (j0 := j0) hj0
    (r0 := r0) hr0 hDj

/-!
## Wiring: `setup.toData` and `toMultiplierModel`
-/

noncomputable def data : SSU.Instances.FejerBankedPartition.Data (κ (Q := Q)) :=
  (setup (P := P)).toData

noncomputable def multiplierModel : SSU.Instances.TorusDyadicShell.MultiplierModel :=
  (data (P := P)).toMultiplierModel

end Platinum

namespace Platinum

/-!
## Final pre-heart packaging: (T1) and (T3)

This section exposes clean “ready for SSU heart” statements.
-/

variable {Q : ℕ} (P : SSU.Instances.FejerBankedPlatinum.Params Q)

/-- The TeX `Λ` overlap constant for this concrete instance. -/
noncomputable def ΛP : ℝ :=
  (2 : ℝ) * (P.J.card : ℝ)

theorem globalSum_le_ΛP (ξ : UC) :
    globalSum (P := P) ξ ≤ ΛP (P := P) := by
  simpa [ΛP, globalSum] using (global_overlap (P := P) (ξ := ξ))

theorem T1_partition
    (hN : ∀ j : ℤ, 2 ≤ P.N j) (ξ : UC) :
    (ξ ∈ bankShellUnion (P := P) → (1 : ℝ) ≤ globalSum (P := P) ξ) ∧
      (globalSum (P := P) ξ ≤ ΛP (P := P)) ∧
      (ξ ∉ bankShellUnion (P := P) → globalSum (P := P) ξ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hξ
    exact global_partition_lower_of_mem_bankShellUnion (P := P) (hN := hN) (ξ := ξ) hξ
  · exact globalSum_le_ΛP (P := P) (ξ := ξ)
  · intro hξ
    exact globalSum_eq_zero_of_not_mem_bankShellUnion (P := P) (ξ := ξ) hξ

theorem T3_bank_domination (j : ℤ) (k : κ (Q := Q)) (ξ : UC) :
    P.Pproj j k ξ ≤ bankWeight (P := P) ξ :=
  Pproj_le_bankWeight (P := P) (j := j) (k := k) (ξ := ξ)

/-!
## TeX-faithful hypothesis packaging (compromise layer)

This records the TeX “tube overlap + bank domination” consequences as a reusable hypothesis bundle.
The current platinum construction instantiates it with the hard bank indicator as the bank weight.
-/

noncomputable def texHypothesis (hN : ∀ j : ℤ, 2 ≤ P.N j) :
    SSU.Instances.FejerBankedTeX.Hypothesis (κ (Q := Q)) (ι (Q := Q)) where
  S := setup (P := P)
  coverage := setup_coverageHypothesis (P := P) hN
  bankDom :=
    { wBank := bankWeight (P := P)
      wBank_nonneg := fun x => by
        by_cases hx : x ∈ bankSet (Q := Q) (H := P.H) (cA := cA)
        · simp [bankWeight, hx]
        · simp [bankWeight, hx]
      cBank := 1
      cBank_pos := by norm_num
      dominate := by
        intro j k x
        simpa [one_mul] using (T3_bank_domination (P := P) (j := j) (k := k) (ξ := x)) }

/-!
## First SSU-heart milestone for the platinum instance: exact orthogonality across shells

Because `P.Pproj` includes the hard dyadic shell cut-off `1_{Dj j r}`, the already-summed shell
multipliers `ψ_j` have disjoint supports in `j`. Consequently, the corresponding core operators
are exactly orthogonal off-diagonal, yielding a compactly-supported Gram decay function.
-/

namespace Heart

open SSU.Instances.FejerBankedPartition
open SSU.Instances.TorusDyadicShell
open SSU.FourierBridge

variable {Q : ℕ} (P : SSU.Instances.FejerBankedPlatinum.Params Q)

local notation "⟪" x ", " y "⟫" => inner ℂ x y

-- A clean decay function: only the diagonal (`distZ = 0`) contributes.
noncomputable def aDiag : ℕ → NNReal :=
  fun d => if d = 0 then (1 : NNReal) else 0

def shellActive (j : ℤ) : Set UC :=
  {ξ : UC |
    ∃ r : RatCenter Q,
      ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) r ∧ ξ ∈ P.Dj j r}

theorem Dj_disjoint_of_lt (r : RatCenter Q) {i j : ℤ} (hij : i < j) :
    Disjoint (P.Dj i r) (P.Dj j r) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro ξ hi hj
  -- From `Dj i r`: `step (i+1) < |ν|`.
  have hi_lt : P.step (i + 1) < |SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ| := hi.1
  -- From `Dj j r`: `|ν| ≤ step j`.
  have hj_le : |SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ| ≤ P.step j := hj.2
  -- Compare `step j ≤ step (i+1)` since `i+1 ≤ j`.
  have hij' : i + 1 ≤ j := Int.add_one_le_of_lt hij
  have hpow :
      (2 : ℝ) ^ (-j) ≤ (2 : ℝ) ^ (-(i + 1)) := by
    have hbase : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hexp : (-j) ≤ (-(i + 1)) := by
      simpa using (neg_le_neg hij')
    simpa using (zpow_le_zpow_right₀ (a := (2 : ℝ)) hbase hexp)
  have hstep : P.step j ≤ P.step (i + 1) := by
    -- divide by `H > 0`
    have hH : 0 ≤ P.H := le_of_lt P.hH
    simpa [SSU.Instances.FejerBankedPlatinum.Params.step, div_eq_mul_inv, mul_assoc] using
      (mul_le_mul_of_nonneg_right hpow (inv_nonneg.2 hH))
  have : |SSU.Instances.FejerBankedPlatinum.Params.ν (Q := Q) r ξ| ≤ P.step (i + 1) :=
    le_trans hj_le hstep
  exact (not_lt_of_ge this hi_lt).elim

theorem Dj_disjoint (r : RatCenter Q) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (P.Dj i r) (P.Dj j r) := by
  rcases lt_or_gt_of_ne hij with hijlt | hijgt
  · exact Dj_disjoint_of_lt (P := P) (r := r) hijlt
  · exact (Dj_disjoint_of_lt (P := P) (r := r) hijgt).symm

theorem shellActive_disjoint {i j : ℤ} (hij : i ≠ j) :
    Disjoint (shellActive (P := P) i) (shellActive (P := P) j) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro ξ hi hj
  rcases hi with ⟨r1, hr1, hDj1⟩
  rcases hj with ⟨r2, hr2, hDj2⟩
  by_cases hrs : r1 = r2
  · subst hrs
    have hd : Disjoint (P.Dj i r1) (P.Dj j r1) := Dj_disjoint (P := P) (r := r1) hij
    exact (hd.le_bot ⟨hDj1, hDj2⟩).elim
  · have hd :
        Disjoint (majorArc (Q := Q) (H := P.H) (cA := cA) r1)
          (majorArc (Q := Q) (H := P.H) (cA := cA) r2) :=
      majorArc_disjoint (P := P) (r := r1) (s := r2) hrs
    exact (hd.le_bot ⟨hr1, hr2⟩).elim

theorem shellSum_eq_zero_of_not_mem_shellActive (j : ℤ) (ξ : UC)
    (hξ : ξ ∉ shellActive (P := P) j) :
    (data (P := P)).shellSum j ξ = 0 := by
  classical
  -- Expand the concrete `data.shellSum` as a sum over the explicit tube projectors `P.Pproj`.
  -- (`data := setup.toData`, so `data.K = P.K` and `data.P = P.Pproj` by definitional equality.)
  have hrewrite :
      (data (P := P)).shellSum j ξ = (∑ k ∈ P.K j, P.Pproj j k ξ) := by
    simpa [SSU.Instances.FejerBankedPlatinumConcrete.Platinum.data,
      SSU.Instances.FejerBankedPlatinumConcrete.Platinum.setup,
      SSU.Instances.FejerBankedConstruction.Setup.toData,
      FejerBankedPartition.Data.shellSum]
  rw [hrewrite]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hnot :
      ¬(ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) k.1 ∧ ξ ∈ P.Dj j k.1) := by
    intro hmem
    exact hξ ⟨k.1, hmem.1, hmem.2⟩
  by_cases hmaj : ξ ∈ majorArc (Q := Q) (H := P.H) (cA := cA) k.1
  · by_cases hDj : ξ ∈ P.Dj j k.1
    · exact (hnot ⟨hmaj, hDj⟩).elim
    · have : P.shellCut j k.1 ξ = 0 := by
        simp [SSU.Instances.FejerBankedPlatinum.Params.shellCut, hDj]
      simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj, this]
  · have : P.ϑ k.1 ξ = 0 := by
      simp [SSU.Instances.FejerBankedPlatinum.Params.ϑ, hmaj]
    simp [SSU.Instances.FejerBankedPlatinum.Params.Pproj, this]

theorem shellSum_mul_eq_zero_of_ne (i j : ℤ) (hij : i ≠ j) (ξ : UC) :
    (data (P := P)).shellSum i ξ * (data (P := P)).shellSum j ξ = 0 := by
  classical
  by_cases hi : ξ ∈ shellActive (P := P) i
  · have hj' : ξ ∉ shellActive (P := P) j := by
      have hd := shellActive_disjoint (P := P) (i := i) (j := j) hij
      exact fun hj => (hd.le_bot ⟨hi, hj⟩).elim
    have h0 : (data (P := P)).shellSum j ξ = 0 :=
      shellSum_eq_zero_of_not_mem_shellActive (P := P) (j := j) (ξ := ξ) hj'
    simp [h0]
  · have h0 : (data (P := P)).shellSum i ξ = 0 :=
      shellSum_eq_zero_of_not_mem_shellActive (P := P) (j := i) (ξ := ξ) hi
    simp [h0]

theorem ψ_mul_eq_zero_of_ne (i j : ℤ) (hij : i ≠ j) (ξ : UC) :
    (data (P := P)).ψ i ξ * (data (P := P)).ψ j ξ = 0 := by
  classical
  have hmul : (data (P := P)).shellSum i ξ * (data (P := P)).shellSum j ξ = 0 :=
    shellSum_mul_eq_zero_of_ne (P := P) (i := i) (j := j) hij (ξ := ξ)
  have h0 : (data (P := P)).shellSum i ξ = 0 ∨ (data (P := P)).shellSum j ξ = 0 :=
    mul_eq_zero.mp hmul
  rcases h0 with hi0 | hj0
  · simp [FejerBankedPartition.Data.ψ, hi0]
  · simp [FejerBankedPartition.Data.ψ, hj0]

theorem inner_mulL2Op_eq_zero_of_ne (i j : ℤ) (hij : i ≠ j) (f : SSU.Torus.L2) :
    ⟪SSU.Torus.mulL2Op (φ := (data (P := P)).ψ i) ((data (P := P)).memLp_ψ i) f,
      SSU.Torus.mulL2Op (φ := (data (P := P)).ψ j) ((data (P := P)).memLp_ψ j) f⟫ = 0 := by
  classical
  -- Abbreviate the `L^∞` classes of the multipliers.
  let φi : SSU.Torus.Linf := SSU.Torus.toLinf (φ := (data (P := P)).ψ i) ((data (P := P)).memLp_ψ i)
  let φj : SSU.Torus.Linf := SSU.Torus.toLinf (φ := (data (P := P)).ψ j) ((data (P := P)).memLp_ψ j)
  -- `φi = ψi` and `φj = ψj` a.e.
  have hφi : (fun x : UC => φi x) =ᵐ[μ] (data (P := P)).ψ i := by
    simpa [SSU.Torus.toLinf, φi] using
      ((data (P := P)).memLp_ψ i).coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := (data (P := P)).ψ i)
  have hφj : (fun x : UC => φj x) =ᵐ[μ] (data (P := P)).ψ j := by
    simpa [SSU.Torus.toLinf, φj] using
      ((data (P := P)).memLp_ψ j).coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := (data (P := P)).ψ j)
  -- Therefore `φi * φj = 0` a.e. by pointwise disjointness of `ψ_i, ψ_j`.
  have hφmul0 : (fun x : UC => φi x * φj x) =ᵐ[μ] 0 := by
    have hmul : (fun x : UC => φi x * φj x) =ᵐ[μ] fun x => (data (P := P)).ψ i x * (data (P := P)).ψ j x :=
      hφi.mul hφj
    have hmul0' : (fun x : UC => (data (P := P)).ψ i x * (data (P := P)).ψ j x) =ᵐ[μ] 0 :=
      Filter.Eventually.of_forall (fun x => ψ_mul_eq_zero_of_ne (P := P) (i := i) (j := j) hij (ξ := x))
    exact hmul.trans hmul0'
  -- Rewrite the `mulL2Op` outputs as `φi • f` and `φj • f`.
  have hAi :
      (SSU.Torus.mulL2Op (φ := (data (P := P)).ψ i) ((data (P := P)).memLp_ψ i) f : SSU.Torus.L2)
        = (φi • f : SSU.Torus.L2) := by
    rfl
  have hAj :
      (SSU.Torus.mulL2Op (φ := (data (P := P)).ψ j) ((data (P := P)).memLp_ψ j) f : SSU.Torus.L2)
        = (φj • f : SSU.Torus.L2) := by
    rfl
  -- Show the pointwise inner integrand is `0` a.e.
  have hintegrand :
      (fun x : UC =>
          ⟪((φi • f : SSU.Torus.L2) x), ((φj • f : SSU.Torus.L2) x)⟫) =ᵐ[μ] 0 := by
    -- Expand the `Lp` scalar multiplication pointwise and use `φi * φj = 0`.
    have hsmul_i : (φi • f : SSU.Torus.L2) =ᵐ[μ] (fun x : UC => (φi x) • (f x)) := by
      simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := φi) (g := f))
    have hsmul_j : (φj • f : SSU.Torus.L2) =ᵐ[μ] (fun x : UC => (φj x) • (f x)) := by
      simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := φj) (g := f))
    filter_upwards [hsmul_i, hsmul_j, hφmul0] with x hxi hxj hxmul
    have h0 : φi x = 0 ∨ φj x = 0 := mul_eq_zero.mp hxmul
    rcases h0 with h0 | h0
    · simp [hxi, hxj, h0]
    · simp [hxi, hxj, h0]
  -- Conclude by `inner_def` and integrating a.e.-zero.
  have :
      (⟪(φi • f : SSU.Torus.L2), (φj • f : SSU.Torus.L2)⟫ : ℂ)
        = ∫ x : UC, (0 : ℂ) ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    simpa using hintegrand
  have : (⟪(φi • f : SSU.Torus.L2), (φj • f : SSU.Torus.L2)⟫ : ℂ) = 0 := by
    simpa using this
  simpa [hAi, hAj] using this

theorem packetOp_inner_eq_zero_of_ne (i j : ℤ) (hij : i ≠ j) (f : SSU.Torus.L2) :
    ⟪(multiplierModel (P := P)).packetOp i f, (multiplierModel (P := P)).packetOp j f⟫ = 0 := by
  classical
  let M := multiplierModel (P := P)
  have h0 :
      ⟪SSU.Torus.mulL2Op (φ := M.ψ i) (M.hψ i) f,
        SSU.Torus.mulL2Op (φ := M.ψ j) (M.hψ j) f⟫ = 0 := by
    -- `multiplierModel` is built from `data`, so this is just the previous lemma by unfolding.
    simpa [SSU.Instances.FejerBankedPlatinumConcrete.Platinum.multiplierModel,
      SSU.Instances.FejerBankedPartition.Data.toMultiplierModel] using
        (inner_mulL2Op_eq_zero_of_ne (P := P) (i := i) (j := j) hij (f := f))
  -- Expand `packetOp` and peel off the scalar factors.
  calc
    ⟪M.packetOp i f, M.packetOp j f⟫
        = ⟪M.normFactor • SSU.Torus.mulL2Op (φ := M.ψ i) (M.hψ i) f,
            M.normFactor • SSU.Torus.mulL2Op (φ := M.ψ j) (M.hψ j) f⟫ := by
            simp [M, SSU.Instances.TorusDyadicShell.MultiplierModel.packetOp]
    _ = star M.normFactor * ⟪SSU.Torus.mulL2Op (φ := M.ψ i) (M.hψ i) f,
          M.normFactor • SSU.Torus.mulL2Op (φ := M.ψ j) (M.hψ j) f⟫ := by
            simp [inner_smul_left]
    _ = star M.normFactor * (M.normFactor *
          ⟪SSU.Torus.mulL2Op (φ := M.ψ i) (M.hψ i) f,
            SSU.Torus.mulL2Op (φ := M.ψ j) (M.hψ j) f⟫) := by
            simp [inner_smul_right, mul_assoc]
    _ = 0 := by
            rw [h0]
            simp [mul_assoc]

theorem core_inner_eq_zero_of_ne (i j : ℤ) (hij : i ≠ j) (f : SSU.Spaces.L2Z) :
    ⟪(data (P := P)).corePacketFamily.T i f, (data (P := P)).corePacketFamily.T j f⟫ = 0 := by
  classical
  let fT : SSU.FourierBridge.TorusL2 := SSU.FourierBridge.l2ZToTorus f
  have h0 : ⟪(multiplierModel (P := P)).packetOp i fT, (multiplierModel (P := P)).packetOp j fT⟫ = 0 :=
    packetOp_inner_eq_zero_of_ne (P := P) (i := i) (j := j) hij (f := fT)
  -- Unfold `corePacketFamily` as conjugation by the Fourier isometry and transfer orthogonality.
  have hTi :
      (data (P := P)).corePacketFamily.T i f
        = SSU.FourierBridge.torusToL2Z ((multiplierModel (P := P)).packetOp i fT) := by
    simp [FejerBankedPartition.Data.corePacketFamily, SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily,
      SSU.Instances.TorusDyadicShell.TorusPacketFamily.toCorePacketFamily,
      SSU.Instances.TorusDyadicShell.MultiplierModel.toTorusPacketFamily,
      SSU.FourierBridge.Conj.conjOp_apply, fT, SSU.FourierBridge.l2ZToTorus, multiplierModel]
  have hTj :
      (data (P := P)).corePacketFamily.T j f
        = SSU.FourierBridge.torusToL2Z ((multiplierModel (P := P)).packetOp j fT) := by
    simp [FejerBankedPartition.Data.corePacketFamily, SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily,
      SSU.Instances.TorusDyadicShell.TorusPacketFamily.toCorePacketFamily,
      SSU.Instances.TorusDyadicShell.MultiplierModel.toTorusPacketFamily,
      SSU.FourierBridge.Conj.conjOp_apply, fT, SSU.FourierBridge.l2ZToTorus, multiplierModel]
  -- `torusToL2Z` preserves inner products.
  calc
    ⟪(data (P := P)).corePacketFamily.T i f, (data (P := P)).corePacketFamily.T j f⟫
        = ⟪SSU.FourierBridge.torusToL2Z ((multiplierModel (P := P)).packetOp i fT),
            SSU.FourierBridge.torusToL2Z ((multiplierModel (P := P)).packetOp j fT)⟫ := by
            simpa [hTi, hTj]
    _ = ⟪(multiplierModel (P := P)).packetOp i fT, (multiplierModel (P := P)).packetOp j fT⟫ := by
          simpa using
            (SSU.FourierBridge.torusToL2Z.inner_map_map
              ((multiplierModel (P := P)).packetOp i fT) ((multiplierModel (P := P)).packetOp j fT))
    _ = 0 := h0

theorem gram_corePacketFamily :
    SSU.Hilbert.OperatorAOGram (data (P := P)).corePacketFamily.J
      ((data (P := P)).corePacketFamily.T) (aDiag) := by
  classical
  intro f i hi j hj
  by_cases hij : i = j
  · subst hij
    -- diagonal bound by Cauchy–Schwarz
    simpa [aDiag, SSU.Hilbert.distZ_self] using
      (norm_inner_le_norm (𝕜 := ℂ)
        ((data (P := P)).corePacketFamily.T i f) ((data (P := P)).corePacketFamily.T i f))
  · have hdist : SSU.Hilbert.distZ i j ≠ 0 := by
      intro h0
      have hsub : i - j = 0 := by
        exact Int.natAbs_eq_zero.mp (by simpa [SSU.Hilbert.distZ] using h0)
      exact hij (sub_eq_zero.mp hsub)
    have hinner : ⟪(data (P := P)).corePacketFamily.T i f, (data (P := P)).corePacketFamily.T j f⟫ = 0 :=
      core_inner_eq_zero_of_ne (P := P) (i := i) (j := j) hij (f := f)
    simp [aDiag, hdist, hinner]

noncomputable def gramHypothesis_corePacketFamily :
    SSU.Interzone.GramHypothesis (data (P := P)).corePacketFamily.J
      ((data (P := P)).corePacketFamily.T) where
  a := aDiag
  gram := gram_corePacketFamily (P := P)

noncomputable def contract_corePacketFamily :
    SSU.Global.SSUContract (data (P := P)).corePacketFamily :=
  (data (P := P)).contract_of_gramHypothesis (h := gramHypothesis_corePacketFamily (P := P))

end Heart

end Platinum

end

end FejerBankedPlatinumConcrete
end Instances
end SSU
