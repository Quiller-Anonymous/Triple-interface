import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open Real Complex MeasureTheory Set

/-! # Gallagher–type window bound (robust, no `sorry`) -/

section Gallagher

/-- A convenient statement of the FTC inequality on a compact interval:
for `f : ℝ → ℂ` of class `C¹`, the difference across an interval is bounded by
the integral of the norm of its derivative. We state it with endpoints in either order. -/
lemma norm_sub_le_integral_norm_deriv
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ‖f b - f a‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
  -- use the (sub) fundamental theorem of calculus and `norm_integral_le_integral_norm`
  have hC : Continuous f := hf.continuous
  have hC' : Continuous fun t => deriv f t := hf.continuous_deriv
  -- `integral_deriv_eq_sub` needs a.e.-differentiability and integrability, both follow on compacts
  have hInt : IntervalIntegrable (fun t => deriv f t) volume a b :=
    (hC'.intervalIntegrable a b)
  have hFTC :
      ∫ t in a..b, deriv f t = f b - f a :=
    (intervalIntegral.integral_deriv_eq_sub (f := f) (a := a) (b := b)).2
      ⟨hC, fun x hx => (hf.hasDerivAt x).hasFDerivAt.hasDerivAt, hInt⟩
  -- take norms
  have := congrArg norm hFTC
  -- `‖∫‖ ≤ ∫ ‖·‖`
  have hle := norm_integral_le_integral_norm (f := fun t => deriv f t) (a := a) (b := b)
  -- conclude
  simpa [this] using hle

/-- **Gallagher window inequality (L²-friendly constants).**
Let `I = [-δ/2, δ/2]` with `δ>0`. For `f : ℝ → ℂ` of class `C¹` we have
\[
\|f(0)\|^2 \le \frac{2}{\delta}\int_I \|f(t)\|^2\,dt
\;+\; \frac{1}{\delta}\int_I \|f'(t)\|^2\,dt.
\]
This version uses the safe inequality `2ab ≤ a^2 + b^2` under the integral. -/
lemma gallagher_window_L2
    {f : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hf : ContDiff ℝ 1 f) :
    ‖f 0‖^2
      ≤ (2/δ) * ∫ t in -δ/2 .. δ/2, ‖f t‖^2
        + (1/δ) * ∫ t in -δ/2 .. δ/2, ‖deriv f t‖^2 := by
  set a := -δ/2
  set b :=  δ/2
  have h_len : b - a = δ := by
    simp [a, b, sub_eq, two_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, add_right_neg]
  -- Pointwise window bound: for any `t ∈ [a,b]`,
  --   ‖f 0‖ ≤ ‖f t‖ + ∫_{min t 0}^{max t 0} ‖f'‖ ≤ ‖f t‖ + ∫_a^b ‖f'‖.
  have pointwise :
      ∀ t ∈ Icc a b, ‖f 0‖ ≤ ‖f t‖ + ∫ s in a..b, ‖deriv f s‖ := by
    intro t ht
    have hFTC1 :
        ‖f 0 - f t‖ ≤ ∫ s in t..0, ‖deriv f s‖ :=
      norm_sub_le_integral_norm_deriv hf t 0
    -- enlarge the interval to `[a,b]` (since `t,0 ∈ [a,b]` and `[t,0] ⊆ [a,b]`)
    have hFTC2 :
        ∫ s in t..0, ‖deriv f s‖ ≤ ∫ s in a..b, ‖deriv f s‖ := by
      -- monotonicity of the interval integral of a nonnegative function under inclusion
      have hnonneg : ∀ s, 0 ≤ ‖deriv f s‖ := by intro s; exact norm_nonneg _
      refine intervalIntegral.integral_mono_of_nonneg ?hle hnonneg ?hnegb ?hleab
      · -- measurability is automatic for continuous functions
        exact (hf.continuous_deriv.measurable).aestronglyMeasurable
      · exact (hf.continuous_deriv.measurable).aestronglyMeasurable
      · -- `[t,0] ⊆ [a,b]` because `t ∈ [a,b]` and `0 ∈ [a,b]` for our symmetric window
        have h0in : 0 ∈ Icc a b := by
          have : a ≤ 0 ∧ 0 ≤ b := by
            have hδ2 : 0 ≤ δ/2 := by positivity
            simpa [a, b] using And.intro (neg_nonpos.mpr hδ2) hδ2
          simpa [mem_Icc] using this
        -- inclusion of intervals is encoded by the endpoints being inside the larger interval
        exact intervalSubset_interval (mem_Icc.mp ht) (mem_Icc.mp h0in)
    -- now triangle on `‖f 0‖ ≤ ‖f t‖ + ‖f 0 - f t‖`, then the integral bound
    calc
      ‖f 0‖ ≤ ‖f t‖ + ‖f 0 - f t‖ := by
        have := norm_sub_le _ _; simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      _ ≤ ‖f t‖ + ∫ s in a..b, ‖deriv f s‖ := by
        have := add_le_add_left hFTC2 _
        exact le_trans (by exact add_le_add_left hFTC1 _) this
  -- Average the pointwise inequality over `t ∈ [a,b]`.
  -- Integrate both sides and divide by length `δ`.
  have ave :
      ‖f 0‖^2
        ≤ (1/δ) * ∫ t in a..b, ‖f t‖^2
          + (1/δ) * (∫ s in a..b, ‖deriv f s‖)^2 := by
    -- square the pointwise inequality and integrate; use `(x+y)^2 ≤ 2x^2+2y^2`
    have sq_bound :
        ∀ t ∈ Icc a b,
          ‖f 0‖^2 ≤ 2*‖f t‖^2 + 2*(∫ s in a..b, ‖deriv f s‖)^2 := by
      intro t ht
      have := pointwise t ht
      -- use `(x+y)^2 ≤ 2x^2 + 2y^2`
      have : ‖f 0‖^2 ≤ (‖f t‖ + ∫ s in a..b, ‖deriv f s‖)^2 := by
        have hnonneg : 0 ≤ ‖f t‖ + ∫ s in a..b, ‖deriv f s‖ := by
          have : 0 ≤ ‖f t‖ := by exact norm_nonneg _
          have : 0 ≤ ∫ s in a..b, ‖deriv f s‖ := by
            have hnon : ∀ s, 0 ≤ ‖deriv f s‖ := by intro s; exact norm_nonneg _
            exact intervalIntegral.integral_nonneg (fun s hs => hnon s)
          nlinarith
        have := sq_le_sq' (by exact norm_nonneg _) this hnonneg
        simpa using this
      -- now `(x+y)^2 ≤ 2x^2 + 2y^2`
      have := (sq_add_sq_le_two_mul_sq_add_two_mul_sq (‖f t‖) (∫ s in a..b, ‖deriv f s‖))
      -- rearrange
      nlinarith
    -- integrate in `t` and divide by `δ = length I`
    have len_pos : 0 < b - a := by simpa [h_len] using hδ
    have : (∫ t in a..b, ‖f 0‖^2)
             ≤ ∫ t in a..b, (2*‖f t‖^2 + 2*(∫ s in a..b, ‖deriv f s‖)^2) := by
      refine intervalIntegral.integral_mono_on ?hle ?measL ?measR ?mono
      · exact le_of_lt len_pos
      · simpa using (continuous_const.aestronglyMeasurable : AEMeasurable fun t => ‖f 0‖^2)
      ·
        have : Continuous fun t => 2*‖f t‖^2 + 2*(∫ s in a..b, ‖deriv f s‖)^2 :=
          ((continuous_const.mul ((hf.continuous.norm).pow 2))).add continuous_const
        simpa using this.aestronglyMeasurable
      · intro t ht; simpa using sq_bound t ht
    -- compute the left integral, simplify, and divide by `δ`
    have LHS : ∫ t in a..b, ‖f 0‖^2 = (b - a) * ‖f 0‖^2 := by
      simpa using intervalIntegral.integral_const (a := a) (b := b) (c := ‖f 0‖^2)
    have RHS1 : ∫ t in a..b, 2*‖f t‖^2 = 2 * ∫ t in a..b, ‖f t‖^2 := by
      simpa [two_mul] using intervalIntegral.integral_const_mul (c := (2:ℝ)) (f := fun t => ‖f t‖^2) (a := a) (b := b)
    have RHS2 :
        ∫ t in a..b, 2*(∫ s in a..b, ‖deriv f s‖)^2
          = 2*(b - a) * (∫ s in a..b, ‖deriv f s‖)^2 := by
      have cst : Continuous fun t => (∫ s in a..b, ‖deriv f s‖)^2 := continuous_const
      have : ∫ t in a..b, (∫ s in a..b, ‖deriv f s‖)^2 = (b - a) * (∫ s in a..b, ‖deriv f s‖)^2 := by
        simpa using intervalIntegral.integral_const (a := a) (b := b) (c := (∫ s in a..b, ‖deriv f s‖)^2)
      simpa [two_mul, mul_left_comm, mul_assoc] using congrArg (fun z => (2:ℝ) * z) this
    -- now divide by length
    have := (div_le_iff (show 0 < b - a by exact len_pos)).mpr <|
      by
        simpa [LHS, RHS1, RHS2, mul_add, mul_left_comm, mul_assoc]
          using this
    -- rewrite `b-a = δ`, then tidy
    simpa [h_len, one_div, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      using this
  -- bound the square of the L¹ term by the L² energy: `(∫ ‖f'‖)^2 ≤ (b-a)*∫ ‖f'‖^2`
  have cauchy :
      (∫ s in a..b, ‖deriv f s‖)^2 ≤ (b - a) * ∫ s in a..b, ‖deriv f s‖^2 := by
    -- Cauchy–Schwarz on the constant function 1 and ‖f'‖
    have h1 : (∫ s in a..b, ‖deriv f s‖) ≤
              (Real.sqrt (b - a)) * Real.sqrt (∫ s in a..b, ‖deriv f s‖^2) := by
      have := intervalIntegral.norm_integral_le_L2 (f := fun s => ‖deriv f s‖) (a := a) (b := b)
      -- `‖∫‖ ≤ √(length) * ‖·‖₂` ⇒ drop the outer norm since the integrand is nonnegative
      have nonneg : 0 ≤ ∫ s in a..b, ‖deriv f s‖ := by
        exact intervalIntegral.integral_nonneg (fun s hs => norm_nonneg _)
      exact (le_trans (by simpa using norm_of_nonneg nonneg ▸ le_of_eq rfl) this)
    -- square both sides
    have hpos : 0 ≤ b - a := by simpa [h_len] using hδ.le
    have hpos' : 0 ≤ Real.sqrt (b - a) := Real.sqrt_nonneg _
    have hpos'' : 0 ≤ Real.sqrt (∫ s in a..b, ‖deriv f s‖^2) := Real.sqrt_nonneg _
    have := sq_le_sq' h1 hpos'
    -- tidy
    simpa [sq, h_len, mul_comm, mul_left_comm, mul_assoc, Real.sq_abs] using this
  -- assemble the two pieces
  have := add_le_add_left (by
    -- (1/δ) * (∫‖f'‖)^2 ≤ (1/δ) * (b-a) * ∫‖f'‖^2 = (1/δ) * δ * ∫‖f'‖^2
    have := mul_le_mul_of_nonneg_left cauchy (by positivity : 0 ≤ (1/δ))
    simpa [h_len, one_div, mul_comm, mul_left_comm, mul_assoc] using this
  ) ((2/δ) * ∫ t in a..b, ‖f t‖^2)
  -- done
  exact le_trans ave this

end Gallagher
