import AltZeta.B2RealTrunc
import AltZeta.B2RealToConventional

/-!
AltZeta/B2RealBound.lean
========================

Windowed B2 bound for the canonical parameter pack, conditional on the single
truncation checklist axioms in `AltZeta/B2RealTruncAxioms.lean`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-- For the canonical pack, the full B2 error envelope agrees with `ETrunc0` (tail is zero). -/
lemma EFull0_eq_ETrunc0 (x : ℝ) : EFull trunc0 tail0 x = ETrunc0 x := by
  simp [EFull, trunc0, tail0, tailControl_KHat, ETrunc0, add_comm, add_left_comm, add_assoc]

/--
**Canonical B2 window bound (conditional).**

Since `tail0` has identically zero tail error, the full `Ψ_K` bound matches the
truncation envelope `ETrunc0`.
-/
theorem b2_bound0_on_window :
    ∀ x, ValidX W0 x → |PsiK K0 x - x| ≤ ETrunc0 x := by
  exact b2_bound0_on_window_via_gold

end B2
end AltZeta
