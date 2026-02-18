import SSU.Engines.TypeII
import SSU.Engines.TypeIILargeSieveTeX
import SSU.Engines.TypeIIBalancedXiTeX
import SSU.Engines.LargeSieve.TypeIIStep34CombineTeX

/-!
TeX-faithful TT* wrappers: replace the uniform Step 3–4 surrogate.

`SSU/Engines/TypeII.lean` currently exposes a convenient surrogate:
`Step34LargeSieve` bounds `‖S(ξ)‖²` *uniformly* on `|ξ| ≤ 1/H`, which then trivially bounds the
ξ-integral in Step 2.

The TeX proof instead uses:

* Step 3–5: a large-sieve bound for `‖S(ξ)‖²` with an `X/|ξ|` term (for `ξ ≠ 0`), and
* Lemma `balanced-xi`: moment hypotheses for `K̂_H` controlling the ξ-integral.

This file wires these two TeX-shaped interfaces into the same downstream output:
`SSU.SingleTubeSSUStatement` and hence `SSU.Interzone.GramHypothesis`.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

open MeasureTheory

private theorem tubeEnergy_nonneg (T : Finset TubePoint) (F : TubePoint → ℂ) :
    0 ≤ _root_.SSU.tubeEnergy T F := by
  classical
  unfold _root_.SSU.tubeEnergy
  refine Finset.sum_nonneg ?_
  intro p hp
  positivity

theorem singleTubeSSUStatement_of_step2ToTubeForm_teX
    (td : TubeData) (K : ℤ → ℝ)
    (h2 : Step2ToTubeForm td K)
    (h34 : Step34LargeSieveTeX td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D) :
    SSU.SingleTubeSSUStatement td.X td.H K td.T := by
  classical
  let s : Set ℝ := Set.Icc (-(1 / td.H)) (1 / td.H)
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability

  -- Step 2 identity: `tubeForm = ∫ Khat(ξ) * ‖S(ξ)‖² dξ` (as a cast to `ℂ`).
  refine ⟨
      (h34.C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) / Real.sqrt (td.H / td.X),
      ?_, ?_⟩
  · -- Nonnegativity of the constant.
    have hsqrtHX : 0 ≤ Real.sqrt (td.H / td.X) := by positivity
    have hden : 0 ≤ Real.sqrt (td.H / td.X) := hsqrtHX
    have hnum :
        0 ≤
          h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X) := by
      have hU0 : 0 ≤ td.U := le_trans (show (0 : ℝ) ≤ 1 by linarith) hU
      have hD0 : 0 ≤ td.D := le_trans (show (0 : ℝ) ≤ 1 by linarith) hD
      have hX0 : 0 ≤ td.X := le_of_lt hX
      have hH0 : 0 < td.H := hH
      have hq0 : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
      have hsqrtDU : 0 ≤ Real.sqrt ((td.D * td.U) / (td.q : ℝ)) := by positivity
      have hbig :
          0 ≤
            ((td.U * td.D) / td.H
              + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                  Real.sqrt (td.H * Real.log td.H)
              + td.X) := by
        have hterm1 : 0 ≤ (td.U * td.D) / td.H := by
          exact div_nonneg (mul_nonneg hU0 hD0) (le_of_lt hH0)
        have hterm2 :
            0 ≤ Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                Real.sqrt (td.H * Real.log td.H) := by
          positivity
        nlinarith [hterm1, hterm2, hX0]
      exact
        mul_nonneg
          (mul_nonneg (mul_nonneg h34.C_nonneg hsqrtDU) hbal.C_nonneg)
          hbig
    -- Divide by the nonnegative denominator.
    exact div_nonneg hnum hden
  · intro F
    -- Reduce to a real ξ-integral.
    let r : ℝ :=
      ∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)
    have htube : tubeForm K td.T F = (r : ℂ) := by
      -- Start from the complex-valued integral form, then convert it into the cast of the real integral.
      have htex :
          tubeForm K td.T F =
            ∫ ξ in s,
              ((h2.Khat ξ : ℝ) : ℂ) *
                (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := by
        -- `h2.tubeForm_eq` is stated as a cast of a real integral; `simp` rewrites it into this form.
        simpa [s] using (h2.tubeForm_eq (td := td) (K := K) F)
      have hrew0 :
          (∫ ξ in s,
              ((h2.Khat ξ : ℝ) : ℂ) *
                (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
            =
          ∫ ξ in s,
            (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        refine ae_of_all _ (fun ξ => ?_)
        simp [mul_assoc]
      have hrew1 :
          (∫ ξ in s,
              (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ))
            =
          (r : ℂ) := by
        -- `integral_ofReal` on the restricted measure.
        have hbase :
            (∫ ξ in s,
                (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ))
              =
            (↑(∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ) := by
          exact
            (integral_ofReal
              (𝕜 := ℂ)
              (μ := (volume : Measure ℝ).restrict s)
              (f := fun ξ : ℝ =>
                (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)))
        simpa [r] using hbase
      -- Combine.
      exact htex.trans (hrew0.trans hrew1)
    have hnorm : ‖tubeForm K td.T F‖ = |r| := by
      simpa [htube, RCLike.norm_ofReal] using congrArg (fun z : ℂ => ‖z‖) htube
    -- Since the integrand is nonnegative, `r ≥ 0`, hence `|r| = r`.
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      refine integral_nonneg_of_ae ?_
      -- On the restricted measure, the integrand is pointwise nonnegative.
      refine ae_of_all _ (fun ξ => ?_)
      have hK0 : 0 ≤ h2.Khat ξ := hbal.Khat_nonneg ξ
      have hS0 : 0 ≤ (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 : ℝ) := by positivity
      exact mul_nonneg hK0 hS0
    have habs_r : |r| = r := abs_of_nonneg hr_nonneg

    -- Pointwise (a.e.) Step 5 bound on `‖S(ξ)‖²`, multiplied by `Khat(ξ)`.
    have hbound_ae :
        (fun ξ : ℝ =>
            (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
          ≤ᵐ[(volume : Measure ℝ).restrict s]
        fun ξ : ℝ =>
          (h2.Khat ξ) *
            (h34.C *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + td.X * invAbs ξ) *
                  Real.sqrt (td.D + td.X * invAbs ξ) *
                    tubeEnergy td.T F) := by
      -- Work a.e. on `s` and away from `0`.
      have hne0 : ∀ᵐ ξ ∂(volume : Measure ℝ).restrict s, ξ ≠ 0 := by
        -- Use `ae_iff`: it suffices to show `{ξ | ξ = 0}` has measure `0` under the restricted measure.
        refine (ae_iff.2 ?_)
        have hnull : ((volume : Measure ℝ).restrict s) ({0} : Set ℝ) = 0 := by
          -- `μ.restrict s {0} = 0` since `volume {0} = 0`.
          simp [Measure.restrict_apply, hs]
        -- `{ξ | ¬ ξ ≠ 0} = {0}`.
        have hset : {ξ : ℝ | ¬ ξ ≠ 0} = ({0} : Set ℝ) := by
          ext ξ
          by_cases hξ : ξ = 0 <;> simp [hξ]
        simpa [hset] using hnull
      filter_upwards [ae_restrict_mem hs, hne0] with ξ hξs hξ0
      have hinv : invAbs ξ = 1 / |ξ| := invAbs_eq_one_div_abs (ξ := ξ) hξ0
      have hS :
          ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
            ≤
          h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X / |ξ|) *
              Real.sqrt (td.D + td.X / |ξ|) *
                tubeEnergy td.T F :=
        h34.bound_outerGeom ξ hξ0 (by simpa [s] using hξs) F
      -- Rewrite `/|ξ|` in terms of `invAbs`.
      have hS' :
          ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
            ≤
          h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ) *
                  tubeEnergy td.T F := by
        -- Use `hinv` and `hS`.
        simpa [hinv, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hS
      have hK0 : 0 ≤ h2.Khat ξ := hbal.Khat_nonneg ξ
      exact mul_le_mul_of_nonneg_left hS' hK0

    -- Integrate the a.e. bound.
    have hint :
        r
          ≤
        ∫ ξ in s,
          (h2.Khat ξ) *
            (h34.C *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + td.X * invAbs ξ) *
                  Real.sqrt (td.D + td.X * invAbs ξ) *
                    tubeEnergy td.T F) := by
      dsimp [r]
      -- Use `integral_mono_of_nonneg` on the restricted measure.
      refine
        MeasureTheory.integral_mono_of_nonneg
          (μ := (volume : Measure ℝ).restrict s)
          (by
            -- `0 ≤ᵐ f`.
            refine ae_of_all _ (fun ξ => ?_)
            have hK0 : 0 ≤ h2.Khat ξ := hbal.Khat_nonneg ξ
            have hS0 : 0 ≤ (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 : ℝ) := by positivity
            exact mul_nonneg hK0 hS0)
          (by
            -- `Integrable g`.
            have hintBase :
                IntegrableOn
                  (fun ξ : ℝ =>
                    (h2.Khat ξ) *
                      Real.sqrt (td.U + td.X * invAbs ξ) *
                        Real.sqrt (td.D + td.X * invAbs ξ))
                  s := by
              simpa [band, s] using (hbal.integrable (U := td.U) (D := td.D) hU hD)
            have hintBase' :
                Integrable
                  (fun ξ : ℝ =>
                    (h2.Khat ξ) *
                      Real.sqrt (td.U + td.X * invAbs ξ) *
                        Real.sqrt (td.D + td.X * invAbs ξ))
                  ((volume : Measure ℝ).restrict s) := by
              simpa [Measure.restrict_restrict, hs] using hintBase
            -- Multiply by the constant `h34.C * sqrt(DU/q) * tubeEnergy`.
            have hconst :
                Integrable
                  (fun ξ : ℝ =>
                    (h2.Khat ξ) *
                      (h34.C *
                        Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                          Real.sqrt (td.U + td.X * invAbs ξ) *
                            Real.sqrt (td.D + td.X * invAbs ξ) *
                              tubeEnergy td.T F))
                  ((volume : Measure ℝ).restrict s) := by
              -- rewrite as a constant multiple of `hintBase'`.
              have :
                  (fun ξ : ℝ =>
                      (h2.Khat ξ) *
                        (h34.C *
                          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                            Real.sqrt (td.U + td.X * invAbs ξ) *
                              Real.sqrt (td.D + td.X * invAbs ξ) *
                                tubeEnergy td.T F))
                    =
                  fun ξ : ℝ =>
                    (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
                      ((h2.Khat ξ) *
                        Real.sqrt (td.U + td.X * invAbs ξ) *
                          Real.sqrt (td.D + td.X * invAbs ξ)) := by
                funext ξ; ring
              simpa [this] using (hintBase'.const_mul (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F))
            exact hconst)
          hbound_ae

    -- Pull constants out and apply the balanced-ξ bound.
    have hpull :
        (∫ ξ in s,
            (h2.Khat ξ) *
              (h34.C *
                Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                  Real.sqrt (td.U + td.X * invAbs ξ) *
                    Real.sqrt (td.D + td.X * invAbs ξ) *
                      tubeEnergy td.T F))
          =
        (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
          (∫ ξ in s,
            (h2.Khat ξ) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ)) := by
      set c : ℝ := h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F
      have hcongr :
          (fun ξ : ℝ =>
              (h2.Khat ξ) *
                (h34.C *
                  Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                    Real.sqrt (td.U + td.X * invAbs ξ) *
                      Real.sqrt (td.D + td.X * invAbs ξ) *
                        tubeEnergy td.T F))
            =
          fun ξ : ℝ =>
            c *
              ((h2.Khat ξ) *
                Real.sqrt (td.U + td.X * invAbs ξ) *
                  Real.sqrt (td.D + td.X * invAbs ξ)) := by
        funext ξ
        simp [c]
        ring
      -- Now apply linearity of the integral (no integrability needed).
      simp [hcongr, c, MeasureTheory.integral_const_mul]

    have hbalInt :
        (∫ ξ in s,
            (h2.Khat ξ) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ))
          ≤
        hbal.C *
          ((td.U * td.D) / td.H
            + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                Real.sqrt (td.H * Real.log td.H)
            + td.X) := by
      -- This is exactly the `balanced-xi` interface.
      simpa [band, s] using (hbal.bound (U := td.U) (D := td.D) hU hD)

    have hr_le :
        r ≤
          (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
            (hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) := by
      calc
        r
            ≤
          ∫ ξ in s,
            (h2.Khat ξ) *
              (h34.C *
                Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                  Real.sqrt (td.U + td.X * invAbs ξ) *
                    Real.sqrt (td.D + td.X * invAbs ξ) *
                      tubeEnergy td.T F) := hint
        _ =
          (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
            (∫ ξ in s,
              (h2.Khat ξ) *
                Real.sqrt (td.U + td.X * invAbs ξ) *
                  Real.sqrt (td.D + td.X * invAbs ξ)) := hpull
        _ ≤
          (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
            (hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) := by
          have hconst0 :
              0 ≤ h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F := by
            refine
              mul_nonneg
                (mul_nonneg h34.C_nonneg (Real.sqrt_nonneg _))
                (by
                  -- keep as a local lemma to avoid depending on a global name
                  simpa [tubeEnergy] using (tubeEnergy_nonneg (T := td.T) (F := F)))
          exact mul_le_mul_of_nonneg_left hbalInt hconst0

    -- Convert to the `SingleTubeSSUStatement` normalization (multiply/divide by `sqrt(H/X)`).
    have hHXpos : 0 < Real.sqrt (td.H / td.X) := by
      have : 0 < td.H / td.X := div_pos hH hX
      exact Real.sqrt_pos.2 this
    have hfinal :
        ‖tubeForm K td.T F‖
          ≤
        ((h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) / Real.sqrt (td.H / td.X)) *
          Real.sqrt (td.H / td.X) *
            tubeEnergy td.T F := by
      -- Use `‖tubeForm‖ = r` and the bound `r ≤ ...`.
      have hEq : ‖tubeForm K td.T F‖ = r := by
        simpa [hnorm, habs_r]
      -- Multiply `hr_le` by `1` in the form `sqrt(H/X)/sqrt(H/X)`.
      -- Then discharge by `nlinarith`.
      have hE : r ≤
          (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
            tubeEnergy td.T F := by
        -- Rearrange `hr_le` (it already has `* tubeEnergy` factored).
        -- Just commute factors.
        simpa [mul_assoc, mul_left_comm, mul_comm] using hr_le
      -- Now divide/multiply by `sqrt(H/X)`.
      have hR :
          r ≤
            ((h34.C *
                Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                  hbal.C *
                    ((td.U * td.D) / td.H
                      + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                          Real.sqrt (td.H * Real.log td.H)
                      + td.X)) / Real.sqrt (td.H / td.X)) *
              Real.sqrt (td.H / td.X) *
                tubeEnergy td.T F := by
        -- `A ≤ (A/rt)*rt` for `rt>0`.
        have hrt : Real.sqrt (td.H / td.X) ≠ 0 := ne_of_gt hHXpos
        set A : ℝ :=
          (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X))
        -- rewrite RHS to `A * energy`.
        have hmul :
            (A / Real.sqrt (td.H / td.X)) *
                Real.sqrt (td.H / td.X)
              =
            A := by
          field_simp [hrt]
        have hE' : r ≤ A * tubeEnergy td.T F := by
          simpa [A, mul_assoc, mul_left_comm, mul_comm] using hE
        -- Replace `A` by `(A/rt)*rt` on the RHS.
        have hA : A = (A / Real.sqrt (td.H / td.X)) * Real.sqrt (td.H / td.X) := by
          simpa [mul_assoc] using hmul.symm
        -- Conclude.
        calc
          r ≤ A * tubeEnergy td.T F := hE'
          _ = ((A / Real.sqrt (td.H / td.X)) * Real.sqrt (td.H / td.X)) * tubeEnergy td.T F := by
              nth_rewrite 1 [hA]
              rfl
          _ = (A / Real.sqrt (td.H / td.X)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := by
              ring
          _ = ((h34.C *
                Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                  hbal.C *
                    ((td.U * td.D) / td.H
                      + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                          Real.sqrt (td.H * Real.log td.H)
                      + td.X)) / Real.sqrt (td.H / td.X)) *
                Real.sqrt (td.H / td.X) *
                  tubeEnergy td.T F := by
              simp [A, mul_assoc, mul_left_comm, mul_comm]
      -- Conclude by rewriting `‖tubeForm‖` as `r` and applying `hR`.
      exact (hEq ▸ hR)
    -- Finish.
    simpa [hfinal]

theorem singleTubeSSUStatement_of_step2ToTubeForm_step3_step4_teX
    (td : TubeData) (K : ℤ → ℝ)
    (h2 : Step2ToTubeForm td K)
    (h3 : Step3LargeSieveOuterU td) (h4 : Step4LargeSieveOuterV td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D) :
    SSU.SingleTubeSSUStatement td.X td.H K td.T := by
  have hD' : 0 < td.D := lt_of_lt_of_le (by linarith) hD
  have hU' : 0 < td.U := lt_of_lt_of_le (by linarith) hU
  have hX0 : 0 ≤ td.X := le_of_lt hX
  have h34 : Step34LargeSieveTeX td :=
    SSU.Engines.TypeII.LargeSieve.step34LargeSieveTeX_of_step3_step4 td h3 h4 hD' hU' hX0
  exact
    singleTubeSSUStatement_of_step2ToTubeForm_teX
      (td := td) (K := K) h2 h34 hbal hX hH hU hD

noncomputable def gramHypothesis_of_step2ToTubeForm_teX
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (h2 : Step2ToTubeForm td K)
    (h34 : Step34LargeSieveTeX td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX : 0 < td.X) (hH : 0 < td.H) (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (R : ReductionToTubeForm (J := J) (T := T) td K) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  exact
    gramHypothesis_of_singleTube
      (hSSU :=
        singleTubeSSUStatement_of_step2ToTubeForm_teX
          (td := td) (K := K) h2 h34 hbal hX hH hU hD)
      R

noncomputable def gramHypothesis_of_step2ToTubeForm_step3_step4_teX
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (h2 : Step2ToTubeForm td K)
    (h3 : Step3LargeSieveOuterU td) (h4 : Step4LargeSieveOuterV td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX : 0 < td.X) (hH : 0 < td.H) (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (R : ReductionToTubeForm (J := J) (T := T) td K) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  have hD' : 0 < td.D := lt_of_lt_of_le (by linarith) hD
  have hU' : 0 < td.U := lt_of_lt_of_le (by linarith) hU
  have hX0 : 0 ≤ td.X := le_of_lt hX
  have h34 : Step34LargeSieveTeX td :=
    SSU.Engines.TypeII.LargeSieve.step34LargeSieveTeX_of_step3_step4 td h3 h4 hD' hU' hX0
  exact
    gramHypothesis_of_step2ToTubeForm_teX
      (h2 := h2) (h34 := h34) (hbal := hbal) (hX := hX) (hH := hH) (hU := hU) (hD := hD) R

end

end TypeII
end Engines
end SSU
