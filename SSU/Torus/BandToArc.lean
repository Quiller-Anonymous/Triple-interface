import SSU.Engines.RealChangeOfVariables
import SSU.Torus.ArcBridge

/-!
Band-to-arc bridge for the TeX substitution `x = ξ / X`.

This file packages the deterministic identity

`(1/X) ∫_{|ξ|≤1/H} g((ξ/X):𝕋) dξ = ∫_{𝕋} 1_{arc} g`,

valid under the “no wrap-around” smallness assumption `|(1/H)/X| < 1/2`.
-/

namespace SSU
namespace Torus
namespace BandToArc

noncomputable section

open MeasureTheory
open SSU.Torus
open SSU.Torus.BandMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem one_div_X_smul_integral_band_eval_eq_integral_indicator_arc
    (X H : ℝ)
    (hX : 0 < X)
    (hH : 0 < H)
    (hsmall : (1 / H) / X < (1 / 2 : ℝ))
    (g : UC → E) :
    ((1 / X : ℝ) • ∫ ξ in Set.Icc (-(1 / H)) (1 / H), g ((ξ / X : ℝ) : UC))
      =
    ∫ z : UC, (arc (-(1 / H) / X) ((1 / H) / X)).indicator g z := by
  have hab : (-(1 / H : ℝ)) ≤ (1 / H : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (1 / H : ℝ) := by
      exact le_of_lt (one_div_pos.2 hH)
    exact (neg_le_self hnonneg)
  have hcv :
      ((1 / X : ℝ) • ∫ ξ in Set.Icc (-(1 / H)) (1 / H), g ((ξ / X : ℝ) : UC))
        =
      ∫ x in Set.Icc ((-(1 / H)) / X) ((1 / H) / X), g (x : UC) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (SSU.Engines.RealChangeOfVariables.one_div_X_smul_integral_Icc_comp_div
        (f := fun x : ℝ => g (x : UC))
        (a := (-(1 / H))) (b := (1 / H)) (X := X) hX hab)
  have hpos : 0 < (1 / H) / X := by
    exact div_pos (one_div_pos.2 hH) hX
  have hb :
      ((1 / H) / X) ∈ Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
    have hleft : (-(1 / 2 : ℝ)) < (1 / H) / X := by
      have : (-(1 / 2 : ℝ)) < 0 := by norm_num
      exact lt_trans this hpos
    have hright : (1 / H) / X < ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
      nlinarith [hsmall]
    exact ⟨hleft, hright⟩
  have ha :
      ((-(1 / H)) / X) ∈ Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
    have hleft : (-(1 / 2 : ℝ)) < (-(1 / H) / X) := by
      have : (-(1 / 2 : ℝ)) < -((1 / H) / X) := by
        linarith [hsmall]
      simpa [neg_div] using this
    have hright : (-(1 / H) / X) < ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
      have hneg : (-(1 / H) / X) < 0 := by
        have : -((1 / H) / X) < 0 := by
          linarith [hpos]
        simpa [neg_div] using this
      have hhalf : (0 : ℝ) < ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by norm_num
      exact lt_trans hneg hhalf
    exact ⟨hleft, hright⟩
  have harc :
      (∫ z : UC, (arc (-(1 / H) / X) ((1 / H) / X)).indicator g z)
        =
      ∫ x in Set.Icc (-(1 / H) / X) ((1 / H) / X), g (x : UC) := by
    simpa using
      (SSU.Torus.ArcBridge.integral_indicator_arc_eq_integral_Icc
        (a := (-(1 / H) / X)) (b := ((1 / H) / X)) ha hb g)
  calc
    ((1 / X : ℝ) • ∫ ξ in Set.Icc (-(1 / H)) (1 / H), g ((ξ / X : ℝ) : UC))
        =
      ∫ x in Set.Icc (-(1 / H) / X) ((1 / H) / X), g (x : UC) := by
        simpa [div_eq_mul_inv, mul_assoc] using hcv
    _ =
      ∫ z : UC, (arc (-(1 / H) / X) ((1 / H) / X)).indicator g z := by
        simpa using harc.symm

end

end BandToArc
end Torus
end SSU

