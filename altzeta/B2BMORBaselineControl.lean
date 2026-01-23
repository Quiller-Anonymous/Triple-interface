import AltZeta.B2BMORBaseline
import AltZeta.B2ZetaControl

/-!
AltZeta/B2BMORBaselineControl.lean
==================================

Turn the BMOR envelope `Eζ(x) = Cψ·x/log x` into a *control package* once a proof is provided
that it actually bounds the same smoothed statistic `PsiK K0 x`.

At the moment we only have an envelope comparison (`AltZeta/B2BMORBaseline.lean`) showing
the canonical AltZeta envelope is smaller on the canonical window; the missing ingredient for
an honest “ζ-only baseline” is the `bound` field of `ZetaControl`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/--
BMOR baseline control for the canonical window/kernel, **assuming** a proof of the baseline bound
for `PsiK K0 x`.

This keeps the dependency surface explicit: the bridge from the published BMOR `ψ`-bound to our
smoothed `PsiK` statistic is not yet formalized.
-/
def bmorControl0
    (hBound : ∀ x : ℝ, ValidX W0 x → |PsiK K0 x - x| ≤ (baselineBMOR0).EZeta x) :
    ZetaControl W0 K0 :=
{ EZeta := (baselineBMOR0).EZeta
, EZeta_nonneg := (baselineBMOR0).EZeta_nonneg
, bound := hBound
}

end B2
end AltZeta

