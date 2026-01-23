import AltZeta.B2Comparator

/-!
AltZeta/B2ZetaControl.lean
==========================

“ζ-only baseline” control for the B2 target.

`AltZeta.B2.ZetaBaseline` (in `AltZeta/B2Comparator.lean`) is only an *envelope function*.
For honesty, an outpowering claim should eventually compare against a baseline that actually
proves a bound for the **same smoothed statistic** `PsiK K x`.

This file introduces that stronger interface as `ZetaControl`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/--
Baseline control package for `PsiK K x`.

This is the “ζ-only baseline” interface we eventually want to populate from a classical
explicit-formula / zero-density / Vinogradov–Korobov toolchain (or an explicit bound package
such as BMOR), specialized to the **same** smoothed statistic used by AltZeta.
-/
structure ZetaControl (W : Window) (K : LogKernel) where
  /-- Baseline envelope function `Eζ(x)`. -/
  EZeta : ℝ → ℝ
  /-- Nonnegativity of the envelope on the window. -/
  EZeta_nonneg : ∀ x, ValidX W x → 0 ≤ EZeta x
  /-- The actual baseline bound for the smoothed statistic. -/
  bound : ∀ x, ValidX W x → |PsiK K x - x| ≤ EZeta x

namespace ZetaControl

variable {W : Window} {K : LogKernel} (zc : ZetaControl W K)

/-- Forgetful map: a `ZetaControl` induces a `ZetaBaseline` envelope. -/
def toZetaBaseline : ZetaBaseline W :=
{ EZeta := zc.EZeta
, EZeta_nonneg := zc.EZeta_nonneg
}

@[simp] lemma toZetaBaseline_EZeta (x : ℝ) :
    zc.toZetaBaseline.EZeta x = zc.EZeta x := rfl

end ZetaControl

end B2
end AltZeta

