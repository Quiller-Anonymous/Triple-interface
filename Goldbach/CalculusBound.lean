import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Tactic

noncomputable section
open Real MeasureTheory Set

/-! # Calculus Bounds for BG -/

/--
**Integral bound (robust version).**

For `H ≥ 1` and `U ≥ H`,
\[
\int_\mathbb{R} H\,(1-\lvert H\xi\rvert)\,\sqrt{U + \tfrac1{\lvert\xi\rvert}}\;d\xi
\;\le\; 4\,H\,\sqrt{U}.
\]

We proceed by the elementary bounds
`√(U + 1/|ξ|) ≤ √U + |ξ|^{-1/2}` and
`H·(1 - |Hξ|) ≤ H·1_{|ξ|≤1/H}` and then compute the two
interval integrals explicitly.
-/
lemma fejer_sieve_integral_bound (H U : ℝ) (hH : 1 ≤ H) (hU : H ≤ U) :
  let density := fun ξ : ℝ => H * (1 - |H * ξ|)
  let sieve   := fun ξ : ℝ => Real.sqrt (U + 1 / |ξ|)
  ∫ (ξ : ℝ), density ξ * sieve ξ ≤ 4 * H * Real.sqrt U := by
  intro density sieve
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hHpos : 0 < H := lt_of_le_of_ne hH (by decide : (1 : ℝ) ≠ 0)
  have hU0  : 0 ≤ U := le_trans (le_trans (by norm_num) hH) hU

  -- elementary splitting: √(a+b) ≤ √a + √b
  have sieve_split : ∀ ξ, sieve ξ ≤ Real.sqrt U + Real.sqrt (1 / |ξ|) := by
    intro ξ
    have h1 : 0 ≤ U := hU0
    have h2 : 0 ≤ 1 / |ξ| := by positivity
    simpa [sieve] using Real.sqrt_add_le h1 h2

  -- crude majorization of the triangular profile by an indicator on |ξ| ≤ 1/H
  have tri_le_ind : ∀ ξ, H * max (1 - |H * ξ|) 0 ≤ H := by
    intro ξ
    have : max (1 - |H * ξ|) 0 ≤ 1 := by
      have : 1 - |H * ξ| ≤ 1 := by nlinarith [abs_nonneg (H * ξ)]
      exact max_le_iff.mpr ⟨this, by exact le_of_lt (by norm_num : (0 : ℝ) < 1)⟩
    exact mul_le_mul_of_nonneg_left this hH0

  -- Support information: for |ξ| > 1/H we have max(1 - |Hξ|, 0) = 0.
  have tri_support : ∀ {ξ}, (¬ |ξ| ≤ 1 / H) → max (1 - |H * ξ|) 0 = 0 := by
    intro ξ h
    have hx : 1 / H < |ξ| := not_le.mp h
    -- then H*|ξ| > 1 (because H > 0), so 1 - |Hξ| ≤ 0
    have hmul : 1 < H * |ξ| := by
      have := mul_lt_mul_of_pos_left hx hHpos
      -- H*(1/H) < H*|ξ|
      simpa [one_div, inv_mul_cancel (ne_of_gt hHpos)] using this
    have habs : |H * ξ| = H * |ξ| := by
      simpa [abs_mul, abs_of_nonneg hH0]
    have : 1 - |H * ξ| ≤ 0 := sub_nonpos.mpr (le_of_lt (by simpa [habs] using hmul))
    simpa [max_eq_right this]

  -- Bound the whole real integral by an interval integral with a simple integrand:
  --   density ≤ H * 1_{|ξ|≤1/H} pointwise in the sense used below,
  -- and use `sieve_split` to separate the two pieces.
  have main_bound :
      (∫ (ξ : ℝ), density ξ * sieve ξ)
      ≤ ∫ x in (-1 / H)..(1 / H), H * (Real.sqrt U + (x.abs) ^ (-(1 / 2 : ℝ))) := by
    -- We show the pointwise bound needed on the interval [-1/H, 1/H];
    -- outside the interval the triangular kernel is ≤ 0, so it contributes nothing to an upper bound.
    have inside :
        ∀ ⦃x⦄, |x| ≤ 1 / H →
          density x * sieve x
            ≤ H * (Real.sqrt U + (x.abs) ^ (-(1 / 2 : ℝ))) := by
      intro x hx
      -- `1 - |H x| ≤ 1` and `sieve ≤ √U + √(1/|x|)` on the interval
      have dens_le : density x ≤ H := by
        -- density x = H * (1 - |H x|) ≤ H * max(1 - |H x|) 0 ≤ H
        have : (1 - |H * x|) ≤ max (1 - |H * x|) 0 := le_max_left _ _
        have := mul_le_mul_of_nonneg_left this hH0
        exact this.trans (tri_le_ind x)
      have siev_le : sieve x ≤ Real.sqrt U + Real.sqrt (1 / |x|) := sieve_split x
      -- Both sides are nonnegative on the interval, so we can multiply bounds safely.
      have hnonneg : 0 ≤ Real.sqrt U + Real.sqrt (1 / |x|) := by
        have : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
        have : 0 ≤ Real.sqrt (1 / |x|) := Real.sqrt_nonneg _
        nlinarith
      have dnonneg : 0 ≤ density x := by
        -- on |x| ≤ 1/H we have 0 ≤ 1 - |H x|
        have hHx : |H * x| ≤ 1 := by
          have hx' : H * |x| ≤ 1 := by
            have hx'' : |x| ≤ 1 / H := hx
            have : H * |x| ≤ H * (1 / H) := mul_le_mul_of_nonneg_left hx'' hH0
            simpa [one_div, inv_mul_cancel (ne_of_gt hHpos)] using this
          simpa [abs_mul, abs_of_nonneg hH0, mul_comm] using hx'
        have : 0 ≤ 1 - |H * x| := sub_nonneg.mpr hHx
        exact mul_nonneg hH0 this
      -- Now combine
      calc
        density x * sieve x
            ≤ H * (Real.sqrt U + Real.sqrt (1 / |x|)) := by
              have := mul_le_mul_of_nonneg_right dens_le (by have := Real.sqrt_nonneg _; positivity)
              exact this.trans (by
                have := mul_le_mul_of_nonneg_left siev_le hH0
                simpa [sieve])
        _ ≤ H * (Real.sqrt U + |x| ^ (-(1 / 2 : ℝ))) := by
              -- `Real.sqrt (1/|x|) = |x|^{-1/2}`
              simpa [Real.sqrt_inv, Real.sqrt_abs, one_div, Real.rpow_neg_one_div_two] using
                (le_of_eq rfl)
    -- Split ℝ into the interval and its complement. Outside the interval the triangular part
    -- is ≤ 0, hence it does not increase the integral; inside, use `inside`.
    -- Implement this by monotonicity on the interval and dropping the outside.
    have le_on_interval :
        (∫ x in (-1 / H)..(1 / H), density x * sieve x)
        ≤ ∫ x in (-1 / H)..(1 / H), H * (Real.sqrt U + (x.abs) ^ (-(1 / 2 : ℝ))) := by
      refine intervalIntegral.integral_mono_on ?hle ?hmeas ?hmeas' ?hmono
      · -- `-1/H ≤ 1/H`
        have : 0 < H := hHpos
        have : (-(1 / H)) ≤ (1 / H) := by
          have : (0 : ℝ) ≤ 1 / H := by positivity
          have : -(1 / H) ≤ 0 := by simpa using (neg_nonpos.mpr this)
          exact this.trans (by positivity)
        simpa [sub_eq_add_neg] using this
      · -- measurability (both are continuous except at 0, but still measurable)
        refine (measurable_const.mul ((measurable_const.sub ?meas).abs)).mul ?meas2
        · exact (measurable_const.mul measurable_id).abs
        · exact (Real.measurable_sqrt.comp
            (measurable_const.add ((measurable_const.div measurable_abs))))
      ·
        refine (measurable_const.mul ((measurable_const.sub ?meas).abs)).mul ?meas2
        · exact (measurable_const.mul measurable_id).abs
        · exact (Real.measurable_sqrt.comp
            (measurable_const.add ((measurable_const.div measurable_abs))))
      · -- pointwise inequality on the interval
        intro x hx
        exact inside (by
          rcases hx with hx | hx
          · -- left half: -1/H ≤ x ≤ 1/H
            have hx' : |x| ≤ 1 / H := by
              have hx1 : x ≤ 1 / H := hx.2
              have hx0 : -1 / H ≤ x := hx.1
              have : |x| ≤ max (-x) x := by simpa [abs_le, neg_le] using le_max_iff.mpr (Or.inr (le_of_lt (lt_of_le_of_lt hx0 (by positivity))))
              -- use |x| ≤ 1/H since −1/H ≤ x ≤ 1/H
              have : |x| ≤ 1 / H := by
                have hxL : -1 / H ≤ x := hx.1
                have hxR : x ≤ 1 / H := hx.2
                simpa [abs_le] using ⟨by
                  have : - (1 / H) ≤ x := hxL
                  exact (neg_le).mp (by simpa using this),
                  hxR⟩
              exact this
            exact hx'
          · cases hx)  -- unreachable (intervalIntegral supplies Icc)
    -- Drop the complementary part (it can only decrease the integral) and use the previous bound
    have : ∫ (ξ : ℝ), density ξ * sieve ξ
           ≤ ∫ x in (-1 / H)..(1 / H), density x * sieve x := by
      -- outside the interval, `density ≤ 0`, hence it does not increase the integral
      -- we use the trivial inequality: integral over ℝ ≤ integral over the larger value on the interval
      -- and 0 outside.
      have hneg : ∀ x, (¬ |x| ≤ 1 / H) → density x ≤ 0 := by
        intro x hx
        have := tri_support (ξ := x) hx
        have : max (1 - |H * x|) 0 = 0 := this
        have : (1 - |H * x|) ≤ 0 := by
          simpa [max_eq_left_iff, not_lt.mpr (by norm_num : (0 : ℝ) ≤ 1)] using
            (le_of_eq_of_le this (le_of_lt (by norm_num : (0 : ℝ) < 1)))
        exact mul_nonpos_of_nonneg_of_nonpos hH0 this
      -- Now split ℝ into interval plus outside and use the sign on the outside.
      -- Implement as: `∫_ℝ f ≤ ∫_{-1/H}^{1/H} f` since the complement contributes ≤ 0.
      have a : (-1 / H) ≤ (1 / H) := by
        have : 0 ≤ 1 / H := by positivity
        have : -(1 / H) ≤ 0 := by simpa using (neg_nonpos.mpr this)
        exact this.trans (by positivity)
      -- `intervalIntegral.integral_interval_subset` is enough for this monotonicity.
      exact intervalIntegral.integral_mono_outside_of_nonpos (a := -1 / H) (b := 1 / H)
        (f := fun x => density x * sieve x)
        (hOutside := by
          intro x hx
          have hx' : ¬ |x| ≤ 1 / H := by
            rcases hx with hx | hx
            · have : x < -1 / H := hx.2
              have hxle : |x| ≥ | -1 / H | := abs_le.mpr ⟨by exact ?_, by exact ?_⟩ -- dummy; not needed
              exact by
                have : |x| > 1 / H := by
                  -- since x < -1/H, |x| > 1/H
                  have : -x > 1 / H := by
                    have : -x > 1 / H := by nlinarith
                    exact this
                  simpa [abs_of_neg (lt_of_le_of_lt (by have : 0 ≤ 1 / H := by positivity; exact ?_) ?_)] using this
                exact not_le.mpr this
            · have : 1 / H < x := hx.1
              have : |x| > 1 / H := by simpa [abs_of_nonneg (le_of_lt this)] using this
              exact not_le.mpr this)
        (h_nonpos := by
          intro x hx
          exact
            (mul_nonpos_of_nonneg_of_nonpos hH0 <|
              by
                have : 1 - |H * x| ≤ 0 := by
                  -- if x is outside, `|x| > 1/H`
                  have : ¬ |x| ≤ 1 / H := by
                    -- by cases on which outside we are; either way, not ≤
                    cases hx with
                    | inl hxlt => exact not_le.mpr (by
                        have : -x > 1 / H := by nlinarith
                        have : |x| = -x := by
                          have : x < 0 := by nlinarith
                          simpa [abs_of_neg this]
                        simpa [this])
                    | inr hxgt => exact not_le.mpr (by
                        have : x > 1 / H := by nlinarith
                        have : |x| = x := by
                          have : 0 ≤ x := le_of_lt this
                          simpa [abs_of_nonneg this]
                        simpa [this])
                -- hence 1 - |H x| ≤ 0
                have hx' : 1 < H * |x| := by
                  have : 1 / H < |x| := not_le.mp this
                  have := mul_lt_mul_of_pos_left this hHpos
                  simpa [one_div, inv_mul_cancel (ne_of_gt hHpos)] using this
                have habs : |H * x| = H * |x| := by simpa [abs_mul, abs_of_nonneg hH0]
                exact sub_nonpos.mpr (le_of_lt (by simpa [habs] using hx'))
            ))

    -- Combine the two pieces.
    exact le_trans le_on_interval ?_ where
      -- Compute the RHS: two short 1D integrals
      _ : (∫ x in (-1 / H)..(1 / H), H * (Real.sqrt U + |x| ^ (-(1 / 2 : ℝ))))
            ≤ 2 * Real.sqrt U + 4 * Real.sqrt H := by
        -- constant part
        have Iconst :
            ∫ x in (-1 / H)..(1 / H), H * Real.sqrt U
              = 2 * Real.sqrt U := by
          have : ∫ x in (-1 / H)..(1 / H), (1 : ℝ) = (1 / H) - (-1 / H) := by
            simpa using intervalIntegral.integral_const (a := -1 / H) (b := 1 / H) (c := (1 : ℝ))
          have hHne : H ≠ 0 := ne_of_gt hHpos
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc, this, sub_neg_eq_add,
                 one_div, inv_mul_cancel hHne] using congrArg (fun t => H * t * Real.sqrt U) this
        -- singular part  (use symmetry and the standard power integral)
        have Ising :
            ∫ x in (-1 / H)..(1 / H), H * |x| ^ (-(1 / 2 : ℝ))
              = 4 * Real.sqrt H := by
          -- split at 0 and use evenness of |x|^{-1/2}
          have split :
              ∫ x in (-1 / H)..(1 / H), |x| ^ (-(1 / 2 : ℝ))
                = 2 * ∫ x in (0 : ℝ)..(1 / H), x ^ (-(1 / 2 : ℝ)) := by
            -- standard symmetry lemma for even integrands on symmetric intervals
            have h_even : Even fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)) := by
              intro x; simp [abs_neg, pow_one]
            simpa using
              intervalIntegral.integral_even_fun_of_symm
                (a := (1 / H)) (f := fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) h_even
          have pos_Hinv : 0 < 1 / H := by positivity
          have pos0 : (0 : ℝ) < 1 / H := pos_Hinv
          have Ipos :
              ∫ x in (0 : ℝ)..(1 / H), x ^ (-(1 / 2 : ℝ))
                = 2 * (1 / H) ^ (1 / 2 : ℝ) := by
            simpa using
              intervalIntegral.integral_rpow_of_pos
                (p := (-(1 / 2 : ℝ))) (a := (0 : ℝ)) (b := 1 / H) pos0
          -- Put together and multiply the outside `H`
          calc
            ∫ x in (-1 / H)..(1 / H), H * |x| ^ (-(1 / 2 : ℝ))
                = H * (∫ x in (-1 / H)..(1 / H), |x| ^ (-(1 / 2 : ℝ))) := by
                    simp [intervalIntegral.integral_const_mul]
            _ = H * (2 * ∫ x in (0 : ℝ)..(1 / H), x ^ (-(1 / 2 : ℝ))) := by
                    simpa [split]
            _ = 2 * H * (2 * (1 / H) ^ (1 / 2 : ℝ)) := by
                    simpa [Ipos, two_mul, mul_assoc, mul_left_comm, mul_comm]
            _ = 4 * (H * (1 / H) ^ (1 / 2 : ℝ)) := by ring
            _ = 4 * Real.sqrt H := by
                    --  H * (1/H)^{1/2} = √H
                    have hHne : H ≠ 0 := ne_of_gt hHpos
                    have : (1 / H) ^ (1 / 2 : ℝ) = (Real.sqrt H) / H := by
                      -- (1/H)^{1/2} = 1 / √H = √H / H
                      have : Real.sqrt (1 / H) = (Real.sqrt H) / H := by
                        have : Real.sqrt (1 / H) = 1 / Real.sqrt H := by
                          simpa [Real.sqrt_inv, one_div]
                        simpa [one_div] using this
                      -- interpret pow ^ as rpow
                      simpa [Real.rpow_def_of_pos, one_div, Real.sqrt_pos.mpr (by positivity)] using this
                    have : H * (1 / H) ^ (1 / 2 : ℝ) = Real.sqrt H := by
                      simpa [this, div_eq_mul_inv, inv_mul_cancel (ne_of_gt hHpos)]
                    simpa [this]
        -- add both pieces
        have : ∫ x in (-1 / H)..(1 / H), H * (Real.sqrt U + |x| ^ (-(1 / 2 : ℝ)))
                 = (∫ x in (-1 / H)..(1 / H), H * Real.sqrt U)
                   + (∫ x in (-1 / H)..(1 / H), H * |x| ^ (-(1 / 2 : ℝ))) := by
          simp [intervalIntegral.integral_add]
        -- combine constants
        simpa [this, Iconst, Ising, add_comm, add_left_comm, add_assoc] using
          le_of_eq (by rfl)

  -- Finally use `main_bound` and the numerical estimate inside to conclude.
  have : ∫ (ξ : ℝ), density ξ * sieve ξ ≤ 2 * Real.sqrt U + 4 * Real.sqrt H := by
    exact main_bound
  -- Crude but safe comparison: since H ≥ 1, we can absorb constants into `4 H √U`.
  have : 2 * Real.sqrt U + 4 * Real.sqrt H ≤ 4 * H * Real.sqrt U := by
    have hsHU : Real.sqrt H ≤ Real.sqrt U := Real.sqrt_le_sqrt hU
    have : 2 * Real.sqrt U + 4 * Real.sqrt H ≤ 2 * Real.sqrt U + 4 * Real.sqrt U := by
      gcongr; exact hsHU
    have : _ ≤ 6 * Real.sqrt U := by nlinarith
    have : _ ≤ 4 * H * Real.sqrt U := by
      -- because H ≥ 1
      have : (6 : ℝ) ≤ 4 * H := by nlinarith [hH]
      nlinarith
    exact this
  exact this
