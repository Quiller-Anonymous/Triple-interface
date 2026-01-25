import AltZeta.B2BMORBaseline
import AltZeta.B2BMORBaselineControl
import AltZeta.B2Outpowers
import AltZeta.B2RealToConventional

/-!
AltZeta/B2BMOROutpowers0.lean
=============================

Canonical “AltZeta beats BMOR-style baseline” theorem for the B2 target.

This is the first place where the *honesty condition* is enforced syntactically:
we assume a `ZetaControl`-style bound for the **same** smoothed statistic `PsiK K0 x`,
not merely an envelope function.

What we can already prove today (unconditionally) is the envelope improvement
`ETrunc0(x) < Eζ_BMOR(x)` on the canonical window. The remaining missing bridge is
the baseline bound hypothesis `hBound`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/--
Canonical “outpowers” statement for B2 against the BMOR-style baseline envelope, conditional on a
proof that BMOR (or any ζ-only method) actually bounds the same smoothed statistic `PsiK K0 x`.

This is the precise missing obligation for turning the current envelope comparison into an
end-to-end outpowering theorem.
-/
theorem outpowersBMOR0_on_window
    (hBound : ∀ x : ℝ, ValidX W0 x → |PsiK K0 x - x| ≤ (baselineBMOR0).EZeta x) :
    ∀ x : ℝ, ValidX W0 x →
      |PsiK K0 x - x| ≤ ETrunc0 x ∧
        |PsiK K0 x - x| ≤ (baselineBMOR0).EZeta x ∧
        ETrunc0 x < (baselineBMOR0).EZeta x := by
  intro x hx
  let zc : ZetaControl W0 K0 := bmorControl0 hBound
  have hEq : EFull spec0.truncControl tail0 x = ETrunc0 x :=
    EFull_spec0_tail0_eq_ETrunc0 (x := x)
  have hEnv : EFull spec0.truncControl tail0 x < zc.EZeta x := by
    have : ETrunc0 x < (baselineBMOR0).EZeta x := ETrunc0_lt_baselineBMOR0 (x := x) hx
    simpa [zc, bmorControl0, hEq] using this
  have h :=
    outpowersAt (spec := spec0) (tail := tail0) (zc := zc) (x := x) hx hEnv
  refine ⟨?_, ?_, ?_⟩
  · exact (h.1.trans_eq hEq)
  · simpa [zc, bmorControl0] using h.2.1
  · simpa [zc, bmorControl0, hEq] using h.2.2

end B2
end AltZeta

