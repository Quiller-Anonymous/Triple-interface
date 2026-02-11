import SSU.Engines.TypeIIBalancedXiTeX
import Mathlib.Analysis.MeanInequalities

/-!
Discharge the TeX ξ-balancing interface (`BalancedXiClaimInv`) for the concrete admissible kernel
`AdmissibleKernel.Khat` defined in `SSU/Engines/TypeII.lean`.

This is intentionally *crude*: it is only meant to remove a hypothesis from the TeX-shaped TT*
wrappers. Tight constants can be improved later without changing downstream APIs.
-/

set_option maxHeartbeats 800000

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

open MeasureTheory

namespace AdmissibleKernel

private lemma invAbs_nonneg (ξ : ℝ) : 0 ≤ invAbs ξ := by
  by_cases hξ : ξ = 0
  · simp [invAbs, hξ]
  · simp [invAbs, hξ, inv_nonneg, abs_nonneg]

private lemma sqrt_mul_sqrt_le_add_div_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  -- Weighted GM ≤ AM with weights `1/2, 1/2`.
  have h :=
    Real.geom_mean_le_arith_mean2_weighted
      (w₁ := (1 / (2 : ℝ))) (w₂ := (1 / (2 : ℝ)))
      (by positivity) (by positivity) hx hy (by norm_num)
  -- Rewrite `x^(1/2)` as `sqrt x`.
  -- (The RHS is `x/2 + y/2 = (x+y)/2`.)
  simpa [Real.sqrt_eq_rpow, add_comm, add_left_comm, add_assoc, div_eq_mul_inv, mul_add,
    add_mul, mul_assoc, mul_left_comm, mul_comm] using h

private lemma Khat_mul_invAbs (H ξ : ℝ) :
    Khat H ξ * invAbs ξ = Khat H ξ / |ξ| := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [invAbs, Khat]
  · simp [invAbs, hξ, div_eq_mul_inv]

/-- A crude TeX `balanced-xi` witness for the concrete admissible kernel `K̂_H`. -/
noncomputable def balancedXiClaimInv_Khat (X H : ℝ) (hX : 0 ≤ X) (hH : 1 < H) :
    BalancedXiClaimInv X H (Khat H) where
  M0 := 2 / (H * H)
  MInv := 2 / (H * Real.log H)
  M1 := 2 * (H⁻¹ * H⁻¹)
  M0_nonneg := by
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have hden : 0 < H * H := mul_pos hH0 hH0
    exact div_nonneg (by norm_num) (le_of_lt hden)
  MInv_nonneg := by
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have hlog : 0 < Real.log H := Real.log_pos hH
    have hden : 0 < H * Real.log H := mul_pos hH0 hlog
    exact div_nonneg (by norm_num) (le_of_lt hden)
  M1_nonneg := by
    have : 0 ≤ (H⁻¹ : ℝ) := by positivity
    positivity
  Khat_nonneg := fun ξ => Khat_nonneg (H := H) (lt_trans (by norm_num) hH) ξ
  Khat_support := fun ξ hξ => Khat_support (H := H) (ξ := ξ) hξ
  mom0 := by
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have hne : H ≠ 0 := ne_of_gt hH0
    have h0 := integral_Khat_le (H := H) hH0
    -- rewrite `band H` and the RHS constant
    have h0' :
        (∫ ξ in band H, Khat H ξ) ≤ 2 * H⁻¹ := by
      simpa [band, one_div] using h0
    -- `2 * H⁻¹ = (2 / (H*H)) * H`.
    have hrw : 2 * H⁻¹ = (2 / (H * H)) * H := by
      field_simp [hne]
    -- This moment hypothesis is only used as an interface; we keep the exact bound `2/H`.
    calc
      (∫ ξ in band H, Khat H ξ) ≤ 2 * H⁻¹ := h0'
      _ = (2 / (H * H)) * H := hrw
  momInv := by
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have hlog : 0 < Real.log H := Real.log_pos hH
    have hne : H * Real.log H ≠ 0 := ne_of_gt (mul_pos hH0 hlog)
    have h0 := integral_Khat_div_abs_le (H := H) hH0
    have h0' :
        (∫ ξ in band H, (Khat H ξ) / |ξ|) ≤ 2 := by
      simpa [band, one_div] using h0
    have hrw : 2 = (2 / (H * Real.log H)) * H * Real.log H := by
      field_simp [hne]
    -- This moment hypothesis is only used as an interface; we keep the exact bound `2`.
    calc
      (∫ ξ in band H, (Khat H ξ) / |ξ|) ≤ 2 := h0'
      _ = (2 / (H * Real.log H)) * H * Real.log H := hrw
  mom1 := by
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have h0 := integral_abs_mul_Khat_le (H := H) hH0
    simpa [band, one_div] using h0
  C := 2
  C_nonneg := by norm_num
  integrable := by
    intro U D hU hD
    classical
    let s : Set ℝ := band H
    have hs : MeasurableSet s := by
      dsimp [s, band]
      measurability
    have hslt : (volume : Measure ℝ) s < ⊤ := by
      -- Finite measure for a finite interval.
      simpa [s, band, one_div] using
        (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-(H⁻¹))) (b := H⁻¹))
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have hmeasKhat : Measurable (Khat H) := by
      classical
      refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
      exact measurableSet_le measurable_abs measurable_const
    have hmeasInvAbs : Measurable invAbs := by
      classical
      refine Measurable.ite ?_ measurable_const ?_
      · simpa using (measurableSet_eq (f := (fun ξ : ℝ => ξ)) (g := fun _ => (0 : ℝ)))
      · exact measurable_const.div measurable_abs
    have hmeasSqrtU :
        Measurable fun ξ : ℝ => Real.sqrt (U + X * invAbs ξ) := by
      have : Measurable fun ξ : ℝ => U + X * invAbs ξ :=
        measurable_const.add (measurable_const.mul hmeasInvAbs)
      simpa using this.sqrt
    have hmeasSqrtD :
        Measurable fun ξ : ℝ => Real.sqrt (D + X * invAbs ξ) := by
      have : Measurable fun ξ : ℝ => D + X * invAbs ξ :=
        measurable_const.add (measurable_const.mul hmeasInvAbs)
      simpa using this.sqrt
    have hf_meas :
        AEStronglyMeasurable
          (fun ξ : ℝ =>
            (Khat H ξ) *
              Real.sqrt (U + X * invAbs ξ) *
                Real.sqrt (D + X * invAbs ξ))
          ((volume : Measure ℝ).restrict s) := by
      have hmeas :
          Measurable
            (fun ξ : ℝ =>
              (Khat H ξ) *
                Real.sqrt (U + X * invAbs ξ) *
                  Real.sqrt (D + X * invAbs ξ)) := by
        simpa [mul_assoc] using (hmeasKhat.mul (hmeasSqrtU.mul hmeasSqrtD))
      exact hmeas.aestronglyMeasurable
    have hf_bound :
        ∀ᵐ ξ ∂((volume : Measure ℝ).restrict s),
          ‖(Khat H ξ) *
              Real.sqrt (U + X * invAbs ξ) *
                Real.sqrt (D + X * invAbs ξ)‖
            ≤
          ((U + D) / 2 + X * H) := by
      refine ae_of_all _ (fun ξ => ?_)
      have hU0 : 0 ≤ U := le_trans (by norm_num) hU
      have hD0 : 0 ≤ D := le_trans (by norm_num) hD
      have hinv0 : 0 ≤ invAbs ξ := invAbs_nonneg ξ
      have hx : 0 ≤ U + X * invAbs ξ := by nlinarith [hU0, hX, hinv0]
      have hy : 0 ≤ D + X * invAbs ξ := by nlinarith [hD0, hX, hinv0]
      have hgm := sqrt_mul_sqrt_le_add_div_two (x := (U + X * invAbs ξ)) (y := (D + X * invAbs ξ)) hx hy
      have hgm' :
          Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ)
            ≤ (U + D) / 2 + X * invAbs ξ := by
        have : ((U + X * invAbs ξ) + (D + X * invAbs ξ)) / 2 = (U + D) / 2 + X * invAbs ξ := by
          ring
        simpa [this] using hgm
      have hK0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH0 ξ
      have hprod0 :
          0 ≤ (Khat H ξ) * Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ) := by
        have hsqrtU0 : 0 ≤ Real.sqrt (U + X * invAbs ξ) := Real.sqrt_nonneg _
        have hsqrtD0 : 0 ≤ Real.sqrt (D + X * invAbs ξ) := Real.sqrt_nonneg _
        exact mul_nonneg (mul_nonneg hK0 hsqrtU0) hsqrtD0
      have hnorm :
          ‖(Khat H ξ) * Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ)‖ =
            (Khat H ξ) * Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ) := by
        simpa using (Real.norm_of_nonneg hprod0)
      have hKle1 : Khat H ξ ≤ 1 := Khat_le_one (H := H) hH0 ξ
      have hKinv_le : Khat H ξ * invAbs ξ ≤ H := by
        -- `Khat*invAbs = Khat/|ξ|` and `Khat/|ξ| ≤ H`.
        simpa [Khat_mul_invAbs] using Khat_div_abs_le (H := H) hH0 ξ
      have hmain :
          (Khat H ξ) * Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ)
            ≤ (U + D) / 2 + X * H := by
        have hstep :
            (Khat H ξ) * Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ)
              ≤ (Khat H ξ) * ((U + D) / 2 + X * invAbs ξ) := by
          have : (Khat H ξ) *
                (Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ))
              ≤ (Khat H ξ) * ((U + D) / 2 + X * invAbs ξ) :=
            mul_le_mul_of_nonneg_left hgm' hK0
          simpa [mul_assoc] using this
        have hstep' :
            (Khat H ξ) * ((U + D) / 2 + X * invAbs ξ)
              ≤ (U + D) / 2 + X * H := by
          calc
            (Khat H ξ) * ((U + D) / 2 + X * invAbs ξ)
                = (Khat H ξ) * ((U + D) / 2) + X * (Khat H ξ * invAbs ξ) := by ring
            _ ≤ (U + D) / 2 + X * H := by
              have h1 : (Khat H ξ) * ((U + D) / 2) ≤ (U + D) / 2 := by
                have hC0 : 0 ≤ (U + D) / 2 := by nlinarith [hU0, hD0]
                nlinarith [hKle1, hC0]
              have h2 : X * (Khat H ξ * invAbs ξ) ≤ X * H :=
                mul_le_mul_of_nonneg_left hKinv_le hX
              nlinarith [h1, h2]
        exact hstep.trans hstep'
      simpa [hnorm] using hmain
    simpa [s] using
      (IntegrableOn.of_bound (μ := (volume : Measure ℝ)) (s := s) (by simpa using hslt)
        hf_meas ((U + D) / 2 + X * H) hf_bound)
  bound := by
    intro U D hU hD
    classical
    have hH0 : 0 < H := lt_trans (by norm_num) hH
    have hneH : H ≠ 0 := ne_of_gt hH0
    let s : Set ℝ := band H
    have hs : MeasurableSet s := by
      dsimp [s, band]
      measurability
    let f : ℝ → ℝ := fun ξ =>
      (Khat H ξ) * Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ)
    let g : ℝ → ℝ := fun ξ =>
      (Khat H ξ) * ((U + D) / 2 + X * invAbs ξ)

    have hU0 : 0 ≤ U := le_trans (by norm_num) hU
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD

    have hfg :
        f ≤ᵐ[(volume : Measure ℝ).restrict s] g := by
      refine ae_of_all _ (fun ξ => ?_)
      have hinv0 : 0 ≤ invAbs ξ := invAbs_nonneg ξ
      have hx : 0 ≤ U + X * invAbs ξ := by nlinarith [hU0, hX, hinv0]
      have hy : 0 ≤ D + X * invAbs ξ := by nlinarith [hD0, hX, hinv0]
      have hgm := sqrt_mul_sqrt_le_add_div_two (x := (U + X * invAbs ξ)) (y := (D + X * invAbs ξ)) hx hy
      have hgm' :
          Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ)
            ≤ (U + D) / 2 + X * invAbs ξ := by
        have : ((U + X * invAbs ξ) + (D + X * invAbs ξ)) / 2 = (U + D) / 2 + X * invAbs ξ := by
          ring
        simpa [this] using hgm
      have hK0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH0 ξ
      have : (Khat H ξ) *
              (Real.sqrt (U + X * invAbs ξ) * Real.sqrt (D + X * invAbs ξ))
            ≤ (Khat H ξ) * ((U + D) / 2 + X * invAbs ξ) :=
        mul_le_mul_of_nonneg_left hgm' hK0
      simpa [f, g, mul_assoc] using this

    have g_integrable : Integrable g ((volume : Measure ℝ).restrict s) := by
      -- Bounded by a constant on `s` using `Khat ≤ 1` and `Khat*invAbs = Khat/|ξ| ≤ H`.
      have hslt : (volume : Measure ℝ) s < ⊤ := by
        simpa [s, band, one_div] using
          (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-(H⁻¹))) (b := H⁻¹))
      have hmeasKhat : Measurable (Khat H) := by
        classical
        refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
        exact measurableSet_le measurable_abs measurable_const
      have hmeasInvAbs : Measurable invAbs := by
        classical
        refine Measurable.ite ?_ measurable_const ?_
        · simpa using (measurableSet_eq (f := (fun ξ : ℝ => ξ)) (g := fun _ => (0 : ℝ)))
        · exact measurable_const.div measurable_abs
      have hmeasInner :
          Measurable fun ξ : ℝ => ((U + D) / 2 : ℝ) + X * invAbs ξ :=
        measurable_const.add (measurable_const.mul hmeasInvAbs)
      have hg_meas : AEStronglyMeasurable g ((volume : Measure ℝ).restrict s) :=
        (hmeasKhat.mul hmeasInner).aestronglyMeasurable
      have hbound :
          ∀ᵐ ξ ∂((volume : Measure ℝ).restrict s), ‖g ξ‖ ≤ ((U + D) / 2 + X * H) := by
        refine ae_of_all _ (fun ξ => ?_)
        have hinv0 : 0 ≤ invAbs ξ := invAbs_nonneg ξ
        have hC0 : 0 ≤ (U + D) / 2 + X * invAbs ξ := by nlinarith [hU0, hD0, hX, hinv0]
        have hK0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH0 ξ
        have hprod0 : 0 ≤ g ξ := mul_nonneg hK0 hC0
        have hnorm : ‖g ξ‖ = g ξ := by simpa [g] using (Real.norm_of_nonneg hprod0)
        have hKle1 : Khat H ξ ≤ 1 := Khat_le_one (H := H) hH0 ξ
        have hKinv_le : Khat H ξ * invAbs ξ ≤ H := by
          simpa [Khat_mul_invAbs] using Khat_div_abs_le (H := H) hH0 ξ
        have hg_le :
            g ξ ≤ (U + D) / 2 + X * H := by
          calc
            g ξ = (Khat H ξ) * ((U + D) / 2) + X * (Khat H ξ * invAbs ξ) := by
              simp [g]
              ring
            _ ≤ (U + D) / 2 + X * H := by
              have h1 : (Khat H ξ) * ((U + D) / 2) ≤ (U + D) / 2 := by
                nlinarith [hKle1, (show 0 ≤ (U + D) / 2 by nlinarith [hU0, hD0])]
              have h2 : X * (Khat H ξ * invAbs ξ) ≤ X * H :=
                mul_le_mul_of_nonneg_left hKinv_le hX
              nlinarith [h1, h2]
        simpa [hnorm] using hg_le
      have : IntegrableOn g s (volume : Measure ℝ) :=
        IntegrableOn.of_bound (μ := (volume : Measure ℝ)) (s := s) (by simpa using hslt)
          hg_meas ((U + D) / 2 + X * H) hbound
      simpa [IntegrableOn, Measure.restrict_restrict, hs] using this

    have f_nonneg :
        0 ≤ᵐ[(volume : Measure ℝ).restrict s] f := by
      refine ae_of_all _ (fun ξ => ?_)
      have hK0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH0 ξ
      have hsqrtU0 : 0 ≤ Real.sqrt (U + X * invAbs ξ) := Real.sqrt_nonneg _
      have hsqrtD0 : 0 ≤ Real.sqrt (D + X * invAbs ξ) := Real.sqrt_nonneg _
      exact mul_nonneg (mul_nonneg hK0 hsqrtU0) hsqrtD0

    have hI_le : (∫ ξ in s, f ξ) ≤ ∫ ξ in s, g ξ := by
      simpa [MeasureTheory.integral, hs] using
        (MeasureTheory.integral_mono_of_nonneg (μ := (volume : Measure ℝ).restrict s)
          (by simpa [f] using f_nonneg) g_integrable hfg)

    have hK0_int : (∫ ξ in s, Khat H ξ) ≤ 2 * H⁻¹ := by
      simpa [s, band, one_div] using (integral_Khat_le (H := H) hH0)
    have hKinv_int : (∫ ξ in s, (Khat H ξ) / |ξ|) ≤ 2 := by
      simpa [s, band, one_div] using (integral_Khat_div_abs_le (H := H) hH0)

    have hmaj : (∫ ξ in s, g ξ) ≤ (U + D) / H + 2 * X := by
      -- Expand `g` as a sum and use the two kernel moment bounds.
      let a : ℝ := (U + D) / 2
      have hKhat_int : Integrable (fun ξ : ℝ => Khat H ξ) ((volume : Measure ℝ).restrict s) := by
        have hslt : (volume : Measure ℝ) s < ⊤ := by
          simpa [s, band, one_div] using
            (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-(H⁻¹))) (b := H⁻¹))
        haveI : Fact ((volume : Measure ℝ) s < ⊤) := ⟨hslt⟩
        have hmeasKhat : Measurable (Khat H) := by
          classical
          refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
          exact measurableSet_le measurable_abs measurable_const
        refine (Integrable.of_bound (μ := (volume : Measure ℝ).restrict s)
          hmeasKhat.aestronglyMeasurable 1 ?_)
        refine ae_of_all _ (fun ξ => ?_)
        have hK0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH0 ξ
        simpa [Real.norm_eq_abs, abs_of_nonneg hK0] using (Khat_le_one (H := H) hH0 ξ)
      have hKhatInv_int :
          Integrable (fun ξ : ℝ => (Khat H ξ) * invAbs ξ) ((volume : Measure ℝ).restrict s) := by
        have hslt : (volume : Measure ℝ) s < ⊤ := by
          simpa [s, band, one_div] using
            (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-(H⁻¹))) (b := H⁻¹))
        haveI : Fact ((volume : Measure ℝ) s < ⊤) := ⟨hslt⟩
        have hmeasKhat : Measurable (Khat H) := by
          classical
          refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
          exact measurableSet_le measurable_abs measurable_const
        have hmeasInvAbs : Measurable invAbs := by
          classical
          refine Measurable.ite ?_ measurable_const ?_
          · simpa using (measurableSet_eq (f := (fun ξ : ℝ => ξ)) (g := fun _ => (0 : ℝ)))
          · exact measurable_const.div measurable_abs
        have hmeas : Measurable fun ξ : ℝ => (Khat H ξ) * invAbs ξ := hmeasKhat.mul hmeasInvAbs
        refine (Integrable.of_bound (μ := (volume : Measure ℝ).restrict s)
          hmeas.aestronglyMeasurable H ?_)
        refine ae_of_all _ (fun ξ => ?_)
        have hK0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH0 ξ
        have hinv0 : 0 ≤ invAbs ξ := invAbs_nonneg ξ
        have hprod0 : 0 ≤ (Khat H ξ) * invAbs ξ := mul_nonneg hK0 hinv0
        have hnorm : ‖(Khat H ξ) * invAbs ξ‖ = (Khat H ξ) * invAbs ξ := by
          simpa using (Real.norm_of_nonneg hprod0)
        have hle : (Khat H ξ) * invAbs ξ ≤ H := by
          simpa [Khat_mul_invAbs] using Khat_div_abs_le (H := H) hH0 ξ
        simpa [hnorm] using hle
      have hsplit :
          (∫ ξ in s, g ξ) =
            a * (∫ ξ in s, Khat H ξ) + X * (∫ ξ in s, (Khat H ξ) * invAbs ξ) := by
        have h1 : Integrable (fun ξ : ℝ => a * Khat H ξ) ((volume : Measure ℝ).restrict s) :=
          hKhat_int.const_mul a
        have h2 :
            Integrable (fun ξ : ℝ => X * ((Khat H ξ) * invAbs ξ))
              ((volume : Measure ℝ).restrict s) :=
          hKhatInv_int.const_mul X
        -- Rewrite `g` pointwise as the sum of these two terms.
        have hcongr :
            (fun ξ : ℝ => g ξ) =ᵐ[(volume : Measure ℝ).restrict s]
              fun ξ : ℝ => a * Khat H ξ + X * ((Khat H ξ) * invAbs ξ) := by
          refine ae_of_all _ (fun ξ => ?_)
          dsimp [g, a]
          ring
        -- Now integrate, working directly with the restricted measure to avoid heavy rewriting.
        let μ : Measure ℝ := (volume : Measure ℝ).restrict s
        have hbase :
            (∫ ξ, g ξ ∂μ) =
              ∫ ξ, (a * Khat H ξ + X * ((Khat H ξ) * invAbs ξ)) ∂μ :=
          MeasureTheory.integral_congr_ae hcongr
        have hadd :
            (∫ ξ, (a * Khat H ξ + X * ((Khat H ξ) * invAbs ξ)) ∂μ) =
              (∫ ξ, a * Khat H ξ ∂μ) + (∫ ξ, X * ((Khat H ξ) * invAbs ξ) ∂μ) := by
          simpa [μ] using (MeasureTheory.integral_add h1 h2)
        have hconst1 : (∫ ξ, a * Khat H ξ ∂μ) = a * (∫ ξ, Khat H ξ ∂μ) := by
          simpa [μ] using
            (MeasureTheory.integral_const_mul a (f := fun ξ : ℝ => Khat H ξ) (μ := μ))
        have hconst2 :
            (∫ ξ, X * ((Khat H ξ) * invAbs ξ) ∂μ) =
              X * (∫ ξ, (Khat H ξ) * invAbs ξ ∂μ) := by
          simpa [μ] using
            (MeasureTheory.integral_const_mul X (f := fun ξ : ℝ => (Khat H ξ) * invAbs ξ) (μ := μ))
        -- Put it together (switch back to `∫ _ in s` by definitional unfolding).
        change (∫ ξ, g ξ ∂μ) = a * (∫ ξ, Khat H ξ ∂μ) + X * (∫ ξ, (Khat H ξ) * invAbs ξ ∂μ)
        calc
          (∫ ξ, g ξ ∂μ) = ∫ ξ, (a * Khat H ξ + X * ((Khat H ξ) * invAbs ξ)) ∂μ := hbase
          _ = (∫ ξ, a * Khat H ξ ∂μ) + (∫ ξ, X * ((Khat H ξ) * invAbs ξ) ∂μ) := hadd
          _ = a * (∫ ξ, Khat H ξ ∂μ) + X * (∫ ξ, (Khat H ξ) * invAbs ξ ∂μ) := by
            rw [hconst1, hconst2]
      have hinv :
          (∫ ξ in s, (Khat H ξ) * invAbs ξ) ≤ 2 := by
        have :
            (∫ ξ in s, (Khat H ξ) * invAbs ξ) = ∫ ξ in s, (Khat H ξ) / |ξ| := by
          refine integral_congr_ae ?_
          refine ae_of_all _ (fun ξ => ?_)
          simp [Khat_mul_invAbs]
        simpa [this] using hKinv_int
      -- Apply the bounds.
      have hA : a * (∫ ξ in s, Khat H ξ) ≤ (U + D) / H := by
        have h1 : a * (∫ ξ in s, Khat H ξ) ≤ a * (2 * H⁻¹) :=
          mul_le_mul_of_nonneg_left hK0_int (by
            have : 0 ≤ a := by dsimp [a]; nlinarith [hU0, hD0]
            exact this)
        have : a * (2 * H⁻¹) = (U + D) / H := by
          dsimp [a]
          -- `(U+D)/2 * 2 = U+D`, and `1/H = H⁻¹`.
          simp [div_eq_mul_inv, mul_assoc]
        exact h1.trans_eq this
      have hB : X * (∫ ξ in s, (Khat H ξ) * invAbs ξ) ≤ 2 * X := by
        have h1 : X * (∫ ξ in s, (Khat H ξ) * invAbs ξ) ≤ X * 2 :=
          mul_le_mul_of_nonneg_left hinv hX
        have : X * 2 = 2 * X := by ring
        exact h1.trans_eq this
      -- Combine.
      calc
        (∫ ξ in s, g ξ)
            = a * (∫ ξ in s, Khat H ξ) + X * (∫ ξ in s, (Khat H ξ) * invAbs ξ) := hsplit
        _ ≤ (U + D) / H + 2 * X := by nlinarith [hA, hB]

    have hI' : (∫ ξ in s, f ξ) ≤ (U + D) / H + 2 * X := hI_le.trans hmaj

    have hUD : (U + D) / H ≤ 2 * (U * D) / H := by
      have hle : U + D ≤ 2 * (U * D) := by
        have hUle : U ≤ U * D := by nlinarith
        have hDle : D ≤ U * D := by nlinarith
        nlinarith [hUle, hDle]
      exact div_le_div_of_nonneg_right hle (le_of_lt hH0)

    have hI'' : (∫ ξ in s, f ξ) ≤ 2 * ((U * D) / H + X) := by
      have : (U + D) / H + 2 * X ≤ 2 * ((U * D) / H + X) := by
        have htmp : (U + D) / H + 2 * X ≤ 2 * (U * D) / H + 2 * X := by
          linarith [hUD]
        have hr : 2 * (U * D) / H + 2 * X = 2 * ((U * D) / H + X) := by ring
        simpa [hr] using htmp
      exact hI'.trans this

    have hterm :
        0 ≤ Real.sqrt X * (Real.sqrt U + Real.sqrt D) * Real.sqrt (H * Real.log H) := by
      positivity
    have hmono :
        (U * D) / H + X ≤
          (U * D) / H +
            Real.sqrt X * (Real.sqrt U + Real.sqrt D) * Real.sqrt (H * Real.log H) + X := by
      linarith
    have : 2 * ((U * D) / H + X) ≤
        2 *
          ((U * D) / H +
            Real.sqrt X * (Real.sqrt U + Real.sqrt D) * Real.sqrt (H * Real.log H) + X) := by
      nlinarith [hmono]

    -- `C = 2`, and the integral is exactly `∫ f`.
    simpa [f, s, mul_assoc] using hI''.trans this

end AdmissibleKernel

end

end TypeII
end Engines
end SSU
