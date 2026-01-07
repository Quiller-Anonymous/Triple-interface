import AltZeta.B2RealBound
import AltZeta.B2RealEnvelope
import AltZeta.B2Comparator

/-!
AltZeta/B2RealBaseline.lean
===========================

Baseline + gain plumbing for the canonical B2 parameter pack.

This file is intentionally conservative: it provides

* a *toy* baseline envelope `EZetaToy0(x) = 2 * ETrunc0(x)` so the gain machinery
  can be exercised immediately, and
* leaves the “true ζ-only baseline” as a future replacement.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-- A toy baseline envelope, meant to be replaced by a real ζ-based bound package. -/
def baselineToy0 : ZetaBaseline W0 :=
{ EZeta := fun x => 2 * ETrunc0 x
, EZeta_nonneg := by
    intro x _hx
    have : 0 ≤ ETrunc0 x := ETrunc0_nonneg (x := x)
    nlinarith
}

lemma gainToy0_value (x : ℝ) (hx : ValidX W0 x) :
    WindowErrorGain trunc0 tail0 baselineToy0 x = 2 := by
  have hxpos : 0 < ETrunc0 x := ETrunc0_pos x hx
  have hxne : ETrunc0 x ≠ 0 := ne_of_gt hxpos
  -- expand and cancel
  simp [WindowErrorGain, baselineToy0, EFull0_eq_ETrunc0, hxne, div_eq_mul_inv, mul_assoc, mul_comm,
    mul_left_comm]

lemma gainToy0_gt_one (x : ℝ) (hx : ValidX W0 x) :
    1 < WindowErrorGain trunc0 tail0 baselineToy0 x := by
  simpa [gainToy0_value x hx] using (by norm_num : (1 : ℝ) < 2)

end B2
end AltZeta
