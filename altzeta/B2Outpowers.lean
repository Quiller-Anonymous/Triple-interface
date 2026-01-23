import AltZeta.B2Gold
import AltZeta.B2ZetaControl

/-!
AltZeta/B2Outpowers.lean
========================

Generic “outpowers ζ” plumbing for the B2 target.

This file is intentionally interface-level: it does not attempt to build a ζ-only baseline.
Instead it records the exact shape of what we would need:

* an AltZeta B2 bound (via `TruncEFSpec` + `TailControl`), and
* a ζ-only baseline bound for the **same** smoothed statistic (via `ZetaControl`),
* together with a pointwise envelope improvement inequality.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/--
Pointwise “AltZeta outpowers ζ” certificate at the B2 level.

Interpretation: both methods prove a bound for the same quantity `|Ψ_K(x) - x|`, and the
AltZeta envelope is strictly smaller at the point `x`.
-/
theorem outpowersAt
    {W : Window} {K : LogKernel} {N : ℕ}
    (spec : TruncEFSpec W K N) (tail : TailControl W K N)
    (zc : ZetaControl W K)
    {x : ℝ} (hx : ValidX W x)
    (hEnv : EFull spec.truncControl tail x < zc.EZeta x) :
    |PsiK K x - x| ≤ EFull spec.truncControl tail x ∧
      |PsiK K x - x| ≤ zc.EZeta x ∧
      EFull spec.truncControl tail x < zc.EZeta x := by
  refine ⟨?_, ?_, hEnv⟩
  · exact b2_bound_on_window (spec := spec) (tail := tail) x hx
  · exact zc.bound x hx

/--
Windowed form: on every `x ∈ [X,2X]`, AltZeta and the ζ-only baseline both bound the same
quantity, and the AltZeta envelope is strictly smaller (as supplied by `hEnv`).
-/
theorem outpowersOnWindow
    {W : Window} {K : LogKernel} {N : ℕ}
    (spec : TruncEFSpec W K N) (tail : TailControl W K N)
    (zc : ZetaControl W K)
    (hEnv : ∀ x : ℝ, ValidX W x → EFull spec.truncControl tail x < zc.EZeta x) :
    ∀ x : ℝ, ValidX W x →
      |PsiK K x - x| ≤ EFull spec.truncControl tail x ∧
        |PsiK K x - x| ≤ zc.EZeta x ∧
        EFull spec.truncControl tail x < zc.EZeta x := by
  intro x hx
  exact outpowersAt (spec := spec) (tail := tail) (zc := zc) hx (hEnv x hx)

end B2
end AltZeta

