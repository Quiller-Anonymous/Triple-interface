/-
Absolute-value alignment lemmas for dyadic intervals.  The key trigonometric
input is that on any real interval of length `ℓ` there exists a point where the
cosine has magnitude at least `sin (min (ℓ, π) / 2)`.  We package this in a form
that is convenient for the analytic Goldbach argument.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

noncomputable section

open scoped Real

open Real

namespace AltZeta
namespace Analytic

/-- Zeros of `|cos|` sit at `π/2 + kπ`. -/
def cosZero (k : ℤ) : ℝ := (Real.pi / 2) + (k : ℝ) * Real.pi

/-- `|(-1)^k| = 1` for every integer exponent. -/
lemma abs_neg_one_zpow (k : ℤ) : |(-1 : ℝ) ^ k| = 1 := by
  classical
  cases k using Int.cases_on with
  | ofNat n =>
      simpa [Int.ofNat, zpow_ofNat] using (abs_neg_one_pow n : |(-1 : ℝ) ^ n| = 1)
  | negSucc n =>
      have h := (abs_neg_one_pow (n + 1) : |(-1 : ℝ) ^ (n + 1)| = 1)
      simpa [Int.negSucc, zpow_neg, zpow_ofNat, abs_inv] using h

/-- Relate `|cos|` to `|sin|` after removing a lattice shift. -/
lemma abs_cos_eq_abs_sin_sub_lattice (t : ℝ) (k : ℤ) :
    |Real.cos t| = |Real.sin (t - cosZero k)| := by
  have hshift :
      Real.sin (t - cosZero k)
          = ((-1 : ℝ) ^ k) * Real.sin (t - Real.pi / 2) := by
    have := Real.sin_sub_int_mul_pi (t - Real.pi / 2) k
    simpa [cosZero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using this
  have hcos :
      |Real.cos t| = |Real.sin (t - Real.pi / 2)| := by
    have hsin : Real.sin (t - Real.pi / 2) = -Real.cos t := by
      have := Real.sin_sub t (Real.pi / 2)
      simpa [Real.sin_pi_div_two, Real.cos_pi_div_two, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using this
    simpa [hsin, abs_neg]
  have hshift_abs :
      |Real.sin (t - cosZero k)| = |Real.sin (t - Real.pi / 2)| := by
    calc
      |Real.sin (t - cosZero k)|
          = |(-1 : ℝ) ^ k| * |Real.sin (t - Real.pi / 2)| := by
              simpa [hshift, abs_mul]
      _ = |Real.sin (t - Real.pi / 2)| := by simpa [abs_neg_one_zpow]
  simpa [hshift_abs] using hcos

/-- On `[-π/2, π/2]`, `|sin|` agrees with `sin` of the absolute value. -/
lemma abs_sin_eq_sin_abs_of_abs_le_pi_div_two {u : ℝ}
    (h : |u| ≤ Real.pi / 2) :
    |Real.sin u| = Real.sin |u| := by
  have hx := abs_le.mp h
  by_cases hsign : 0 ≤ u
  · have htop : u ≤ Real.pi / 2 := hx.2
    have hπ : u ≤ Real.pi := by linarith [htop]
    have hsin : 0 ≤ Real.sin u :=
      Real.sin_nonneg_of_nonneg_of_le_pi hsign hπ
    have : |Real.sin u| = Real.sin u := abs_of_nonneg hsin
    simpa [hsign, abs_of_nonneg hsign, this]
  · have hneg : u < 0 := lt_of_not_ge hsign
    let v := -u
    have hv0 : 0 ≤ v := by exact neg_nonneg.mpr hneg.le
    have hvtop : v ≤ Real.pi / 2 := by
      have := hx.1
      linarith
    have hvπ : v ≤ Real.pi := by linarith [hvtop]
    have hsin : 0 ≤ Real.sin v :=
      Real.sin_nonneg_of_nonneg_of_le_pi hv0 hvπ
    have : |Real.sin u| = Real.sin v := by
      have : Real.sin u = -Real.sin v := by
        have : v = -u := rfl
        simp [this]
      simp [this, abs_of_nonneg hsin]
    simpa [abs_of_neg hneg, this]
/-- Midpoint estimate: a point in `[p,q]` is at most half the length away from the midpoint. -/
lemma abs_sub_midpoint_le_half_interval {p q x : ℝ}
    (hpq : p ≤ q) (hx : x ∈ Set.Icc p q) :
    |x - (p + q) / 2| ≤ (q - p) / 2 := by
  rcases hx with ⟨hx₁, hx₂⟩
  have hleft : -( (q - p) / 2) ≤ x - (p + q) / 2 := by
    have := hx₁
    linarith
  have hright : x - (p + q) / 2 ≤ (q - p) / 2 := by
    have := hx₂
    linarith
  exact (abs_le.mpr ⟨hleft, hright⟩)

/-- Pick a lattice point `π/2 + kπ` within distance `≤ π/2` from any real `c`. -/
lemma exists_lattice_within_pi_div_two (c : ℝ) :
    ∃ k : ℤ, |c - cosZero k| ≤ Real.pi / 2 := by
  classical
  have hπpos : 0 < Real.pi := Real.pi_pos
  let n : ℤ := Int.floor (c / Real.pi)
  have hlow : (n : ℝ) ≤ c / Real.pi := Int.floor_le (c / Real.pi)
  have hhigh : c / Real.pi < (n : ℝ) + 1 := Int.lt_floor_add_one (c / Real.pi)
  have hx_low : (n : ℝ) * Real.pi ≤ c := by
    have := mul_le_mul_of_nonneg_right hlow (le_of_lt hπpos)
    simpa [mul_comm] using this
  have hx_high : c ≤ ((n : ℝ) + 1) * Real.pi := by
    have := mul_le_mul_of_nonneg_right (le_of_lt hhigh) (le_of_lt hπpos)
    simpa [mul_add, add_mul, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using this
  have horder : (n : ℝ) * Real.pi ≤ ((n : ℝ) + 1) * Real.pi := by
    have : 0 ≤ Real.pi := le_of_lt hπpos
    have := le_add_of_nonneg_right this (a := (n : ℝ) * Real.pi)
    simpa [mul_add, add_mul, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using this
  have hx_mem :
      c ∈ Set.Icc ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi) :=
    ⟨hx_low, hx_high⟩
  have hmid :=
      abs_sub_midpoint_le_half_interval horder hx_mem
  have hmid_val :
      ((n : ℝ) * Real.pi + ((n : ℝ) + 1) * Real.pi) / 2
        = cosZero n := by
    simp [cosZero, two_mul, add_comm, add_left_comm, add_assoc, mul_add,
      add_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  have hspan :
      (((n : ℝ) + 1) * Real.pi - (n : ℝ) * Real.pi) / 2
        = Real.pi / 2 := by
    simp [two_mul, add_comm, add_left_comm, add_assoc, mul_add,
      add_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  refine ⟨n, ?_⟩
  simpa [hmid_val, hspan] using hmid

/-- Main trig estimate: on `[a,b]` there is `t` with
`|cos t| ≥ sin (min (b - a, π) / 2)`. -/
lemma exists_t_abs_cos_ge_sin_min_half
    {a b : ℝ} (hab : a ≤ b) :
    ∃ t ∈ Set.Icc a b,
      |Real.cos t| ≥ Real.sin (min (b - a) Real.pi / 2) := by
  classical
  set ℓ := b - a with hℓdef
  have hℓ : 0 ≤ ℓ := sub_nonneg.mpr hab
  have hπpos : 0 < Real.pi := Real.pi_pos
  by_cases hbig : Real.pi ≤ ℓ
  · -- the interval contains some `kπ`, so we obtain `|cos| = 1`
    have hx : a / Real.pi ≤ b / Real.pi - 1 := by
      have hlen :
          1 ≤ ℓ / Real.pi := by
        have := (div_le_div_right hπpos).mpr hbig
        simpa [ℓ, hℓdef] using this
      have hdiff :
          ℓ / Real.pi = b / Real.pi - a / Real.pi := by
        simp [ℓ, hℓdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          div_eq_mul_inv, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
      linarith
    let k : ℤ := Int.floor (b / Real.pi)
    have hk_le : (k : ℝ) ≤ b / Real.pi := Int.floor_le (b / Real.pi)
    have hk_gt : b / Real.pi - 1 < (k : ℝ) := by
      have := Int.lt_floor_add_one (b / Real.pi)
      have : b / Real.pi < (k : ℝ) + 1 := by simpa using this
      linarith
    have ha_le : a ≤ (k : ℝ) * Real.pi := by
      have haux : a / Real.pi ≤ (k : ℝ) := le_trans hx (le_of_lt hk_gt)
      have := mul_le_mul_of_nonneg_right haux (le_of_lt hπpos)
      simpa [mul_comm] using this
    have ht_le : (k : ℝ) * Real.pi ≤ b := by
      have := mul_le_mul_of_nonneg_right hk_le (le_of_lt hπpos)
      simpa [mul_comm] using this
    have hmin : min ℓ Real.pi = Real.pi := min_eq_right hbig
    have hleft :
        sin (min ℓ Real.pi / 2) = 1 := by
      simp [hmin, Real.sin_pi_div_two]
    refine ⟨(k : ℝ) * Real.pi, ⟨ha_le, ht_le⟩, ?_⟩
    simpa [hleft, abs_cos_int_mul_pi] using
      (show |Real.cos ((k : ℝ) * Real.pi)| ≥ 1 by
        simpa using (le_of_eq (abs_cos_int_mul_pi k)))
  · -- smaller intervals: push away from a nearby lattice point
    have hsmall : ℓ < Real.pi := lt_of_not_ge hbig
    let c := (a + b) / 2
    obtain ⟨k, hk⟩ := exists_lattice_within_pi_div_two c
    let m := cosZero k
    let d0 := |c - m|
    have hd0 : d0 ≤ Real.pi / 2 := by simpa [d0] using hk
    let s := min (ℓ / 2) (Real.pi / 2 - d0)
    have hs0 : 0 ≤ s := by
      exact le_min (by exact div_nonneg hℓ (show (0 : ℝ) ≤ 2 by norm_num))
        (sub_nonneg.mpr hd0)
    have hs_half : s ≤ ℓ / 2 := min_le_left _ _
    have hs_room : s ≤ Real.pi / 2 - d0 := min_le_right _ _
    have hcenter_sub : c - ℓ / 2 = a := by
      simp [c, ℓ, hℓdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        div_eq_mul_inv, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
    have hcenter_add : c + ℓ / 2 = b := by
      simp [c, ℓ, hℓdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        div_eq_mul_inv, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
    have hbounds {t : ℝ} (ht : |t - c| ≤ ℓ / 2) :
        t ∈ Set.Icc a b := by
      have := abs_le.mp ht
      have : c - ℓ / 2 ≤ t ∧ t ≤ c + ℓ / 2 := by
        simpa [sub_eq_add_neg] using this
      simpa [hcenter_sub, hcenter_add] using this
    have dist_formula :
        ∀ t, (t = c - s ∨ t = c + s) → |t - m| = d0 + s := by
      intro t ht
      cases ht with
      | inl h => -- choose the left endpoint
          have hcm : c ≤ m ∨ m ≤ c := le_total c m
          have hn : c ≤ m := by
            cases hcm with
            | inl h' => exact h'
            | inr h' =>
                have : d0 = 0 := by
                  have : c = m := by
                    have : c - m = 0 := le_antisymm h' (le_of_lt (not_lt.mpr h'))
                    simpa [d0, this]
                  simpa [d0, this] using hd0
                have : c = m := by
                  clear hcm
                  have := abs_nonneg (c - m)
                  have : |c - m| = 0 := by simpa [d0, this] using this
                  exact sub_eq_zero.mp (abs_eq_zero.mp this)
                have : c ≤ m := by simpa [this]
                exact this
          have : |t - m| = (m - c) + s := by
            have hc : c - m ≤ 0 := sub_nonpos.mpr hn
            simp [h, d0, abs_of_nonpos hc, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc] 
          simpa [d0, add_comm, add_left_comm, add_assoc] using this
      | inr h =>
          have hc : m ≤ c ∨ c ≤ m := le_total m c
          have hn : m ≤ c := by
            cases hc with
            | inl h' => exact h'
            | inr h' =>
                have : d0 = 0 := by
                  have : c = m := by
                    have : m - c = 0 := le_antisymm h' (le_of_lt (not_lt.mpr h'))
                    simpa [d0, sub_eq_add_neg, this] using abs_of_nonneg (sub_nonneg.mpr h')
                  simpa [d0, this] using hd0
                have : m ≤ c := by
                  have := abs_nonneg (c - m)
                  have : |c - m| = 0 := by simpa [d0, this] using this
                  have : c = m := sub_eq_zero.mp (abs_eq_zero.mp this)
                  simpa [this]
                exact this
          have : |t - m| = (c - m) + s := by
            have hc' : 0 ≤ c - m := sub_nonneg.mpr hn
            simp [h, d0, abs_of_nonneg hc', add_comm, add_left_comm, add_assoc]
          simpa [d0, add_comm, add_left_comm, add_assoc] using this
    let t :=
      if hcm : c ≤ m then c - s else c + s
    have ht_case : t = c - s ∨ t = c + s := by
      by_cases hcm : c ≤ m
      · simp [t, hcm]
      · simp [t, hcm]
    have ht_mem : t ∈ Set.Icc a b := by
      have : |t - c| = s := by
        cases ht_case with
        | inl h => simpa [h, abs_of_nonpos (by linarith)]
        | inr h => simpa [h, abs_of_nonneg hs0]
      exact hbounds (by simpa [this] using (le_of_eq (Eq.symm this) ▸ hs_half))
    have hdist : |t - m| = d0 + s := dist_formula t ht_case
    have hangle_le : |t - m| ≤ Real.pi / 2 := by
      have := calc
        |t - m| ≤ |c - m| + |t - c| := by
          have := abs_add (c - m) (t - c)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        _ = d0 + s := by
          have : |t - c| = s := by
            cases ht_case with
            | inl h => simpa [h, abs_of_nonpos (by linarith)]
            | inr h => simpa [h, abs_of_nonneg hs0]
          simpa [d0, this]
        _ ≤ d0 + (Real.pi / 2 - d0) := by
          have := hs_room
          linarith
        _ = Real.pi / 2 := by ring
      simpa [hdist]
    have hangle_ge : ℓ / 2 ≤ |t - m| := by
      have hcases := le_total (ℓ / 2) (Real.pi / 2 - d0)
      cases hcases with
      | inl hcase =>
          have hs_eq : s = ℓ / 2 := by
            simpa [s] using min_eq_left hcase
          simpa [hdist, hs_eq]
      | inr hcase =>
          have hs_eq : s = Real.pi / 2 - d0 := by
            simpa [s] using min_eq_right hcase
          have : ℓ / 2 ≤ Real.pi / 2 := by
            have : ℓ < Real.pi := hsmall
            have := (div_le_div_right (show 0 < 2 by norm_num)).mpr (le_of_lt this)
            simpa using this
          simpa [hdist, hs_eq]
    have hsin_ge :
        Real.sin (ℓ / 2) ≤ |Real.sin (t - m)| := by
      have hx : -(Real.pi / 2) ≤ ℓ / 2 := by
        have := div_nonneg hℓ (by norm_num : (0 : ℝ) ≤ 2)
        linarith
      have hy : |t - m| ≤ Real.pi / 2 := by simpa using hangle_le
      have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two hx hy hangle_ge
      have hsin_abs :=
        abs_sin_eq_sin_abs_of_abs_le_pi_div_two hy
      simpa [hsin_abs] using hmono
    have hmin : min ℓ Real.pi = ℓ := min_eq_left (le_of_lt hsmall)
    refine ⟨t, ht_mem, ?_⟩
    have hcos : |Real.cos t| = |Real.sin (t - m)| :=
      abs_cos_eq_abs_sin_sub_lattice t k
    simpa [hcos, hmin] using hsin_ge

/-- The dyadic alignment constant. -/
def kappaAbs (γ : ℝ) : ℝ :=
  Real.sin (min (|γ| * Real.log 2) Real.pi / 2)

/-- On a dyadic interval `[X,2X]` we can align the phase in absolute value. -/
lemma align_abs_re_dyadic
    (X : ℝ) (hX : 0 < X) (γ θ : ℝ) :
    ∃ x, X ≤ x ∧ x ≤ 2 * X ∧
      |Real.cos (γ * Real.log x - θ)| ≥ kappaAbs γ := by
  classical
  have htwo : 0 < (2 : ℝ) := by norm_num
  have htwoX : 0 < 2 * X := by nlinarith [hX]
  let a := Real.log X
  let b := Real.log (2 * X)
  have hab : a ≤ b := by
    have : X ≤ 2 * X := by nlinarith [hX]
    exact (Real.log_le_log hX htwoX).2 this
  have hlen : b - a = Real.log 2 := by
    have hlog := Real.log_mul htwo hX
    have : b = Real.log 2 + a := by
      simpa [a, b, two_mul, mul_comm, mul_left_comm, add_comm,
        add_left_comm, add_assoc] using hlog
    simpa [this, sub_eq_add_neg] using congrArg (fun t => t - a) (Eq.symm this)
  by_cases hγ0 : γ = 0
  · refine ⟨X, le_rfl, ?_, ?_⟩
    · have : X ≤ 2 * X := by nlinarith [hX]
      exact this
    · have hkappa : kappaAbs γ = 0 := by
        simp [kappaAbs, hγ0, Real.sin_zero]
      simpa [hγ0, hkappa] using abs_nonneg (Real.cos θ)
  · have hγnz : γ ≠ 0 := hγ0
    have hγpos_or_neg : γ < 0 ∨ 0 < γ := lt_or_gt_of_ne hγnz
    cases hγpos_or_neg with
    | inl hγneg =>
        let left := γ * b - θ
        let right := γ * a - θ
        have horder : left ≤ right := by
          have := mul_le_mul_of_nonpos_left hab (le_of_lt hγneg)
          simpa [left, right] using this
        obtain ⟨t, htI, hcos⟩ :=
          exists_t_abs_cos_ge_sin_min_half (a := left) (b := right) horder
        let u := (t + θ) / γ
        have hua : a ≤ u := by
          have : t + θ ≤ γ * a := by
            have := htI.2
            simpa [right] using this
          have hmul :
              (-γ) * a ≤ (-γ) * u := by
            have hneg := neg_le_neg this
            simpa [u, hγneg.ne] using hneg
          have hpos : 0 < -γ := by simpa using neg_pos.mpr hγneg
          exact (le_of_mul_le_mul_left hmul hpos)
        have hub : u ≤ b := by
          have : γ * b ≤ t + θ := by
            have := htI.1
            simpa [left] using this
          have hmul :
              (-γ) * u ≤ (-γ) * b := by
            have hneg := neg_le_neg this
            simpa [u, hγneg.ne] using hneg
          have hpos : 0 < -γ := by simpa using neg_pos.mpr hγneg
          exact (le_of_mul_le_mul_left hmul hpos)
        let x := Real.exp u
        have hx_ge : X ≤ x := by
          have := Real.exp_le_exp.mpr hua
          simpa [a, x, Real.exp_log hX] using this
        have hx_le : x ≤ 2 * X := by
          have hpos2X : 0 < 2 * X := htwoX
          have := Real.exp_le_exp.mpr hub
          simpa [b, x, Real.exp_log hpos2X] using this
        have hphase :
            γ * Real.log x - θ = t := by
          have : γ * u = t + θ := by
            simp [u, hγneg.ne]
          have hxlog : Real.log x = u := by simp [x]
          simpa [hxlog, this] 
        have hdiff :
            right - left = |γ| * (b - a) := by
          have htmp : right - left = γ * (a - b) := by
            simp [left, right, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              mul_comm, mul_left_comm, mul_assoc]
          have htmp' : right - left = -γ * (b - a) := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htmp
          have habs : |γ| = -γ := abs_of_neg hγneg
          simpa [habs, mul_comm, mul_left_comm, mul_assoc] using htmp'
        have hkappa :
            Real.sin (min (right - left) Real.pi / 2)
                = kappaAbs γ := by
          simp [kappaAbs, hdiff, hlen, abs_of_neg hγneg, min_comm, min_left_comm]
        refine ⟨x, hx_ge, hx_le, ?_⟩
        simpa [hphase, hkappa] using hcos
    | inr hγpos =>
        let left := γ * a - θ
        let right := γ * b - θ
        have horder : left ≤ right := by
          have := mul_le_mul_of_nonneg_left hab (le_of_lt hγpos)
          simpa [left, right] using this
        obtain ⟨t, htI, hcos⟩ :=
          exists_t_abs_cos_ge_sin_min_half (a := left) (b := right) horder
        let u := (t + θ) / γ
        have hua : a ≤ u := by
          have : γ * a ≤ t + θ := by
            have := htI.1
            simpa [left] using this
          have hpos : 0 < γ := hγpos
          have hmul : γ * a ≤ γ * u := by
            simpa [u, hγpos.ne'] using this
          exact (le_of_mul_le_mul_left hmul hpos)
        have hub : u ≤ b := by
          have : t + θ ≤ γ * b := by
            have := htI.2
            simpa [right] using this
          have hpos : 0 < γ := hγpos
          have hmul : γ * u ≤ γ * b := by
            simpa [u, hγpos.ne'] using this
          exact (le_of_mul_le_mul_left hmul hpos)
        let x := Real.exp u
        have hx_ge : X ≤ x := by
          have := Real.exp_le_exp.mpr hua
          simpa [a, x, Real.exp_log hX] using this
        have hx_le : x ≤ 2 * X := by
          have hpos2X : 0 < 2 * X := htwoX
          have := Real.exp_le_exp.mpr hub
          simpa [b, x, Real.exp_log hpos2X] using this
        have hphase :
            γ * Real.log x - θ = t := by
          have : γ * u = t + θ := by simpa [u, hγpos.ne']
          have hxlog : Real.log x = u := by simp [x]
          simpa [hxlog, this]
        have hdiff :
            right - left = |γ| * (b - a) := by
          have : right - left = γ * (b - a) := by
            simp [left, right, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              mul_comm, mul_left_comm, mul_assoc]
          simpa [abs_of_pos hγpos] using this
        have hkappa :
            Real.sin (min (right - left) Real.pi / 2) = kappaAbs γ := by
          simp [kappaAbs, hdiff, hlen, abs_of_pos hγpos]
        refine ⟨x, hx_ge, hx_le, ?_⟩
        simpa [hphase, hkappa] using hcos
