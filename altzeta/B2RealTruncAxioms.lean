import AltZeta.B2RealEnvelope

/-!
AltZeta/B2RealTruncAxioms.lean
==============================

Canonical truncation-side analytic inputs for B2, stated in a checklist-style form.

These are the remaining assumptions needed to prove the canonical B2 bound for `Ψ_K`
once the tail has been discharged (which it is for the compact-support kernel `K0`).

The intent is that this axiom is progressively replaced by a proved theorem as the
explicit-formula machinery is formalized.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-! ### Truncation-side bound (conventional analytic input) -/

/--
**Canonical truncation bound axiom (B2 input).**

This is the single analytic payload required for the canonical B2 window bound once
the tail has been discharged.

Interpretation (intended, not yet formalized here): it is what one obtains from an
explicit formula by bounding the completion side by `CΓ` and the zero/spectral side by
`√x · S_cert` on the window.
-/
axiom trunc0_bound_axiom :
  ∀ x : ℝ, ValidX W0 x → |PsiKTrunc K0 x N0 - x| ≤ ETrunc0 x

end B2
end AltZeta
