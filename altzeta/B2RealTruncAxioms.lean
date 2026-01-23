import AltZeta.B2RealEnvelope

/-!
AltZeta/B2RealTruncAxioms.lean
==============================

Canonical truncation-side analytic inputs for B2, stated in a checklist-style form.

These are the remaining assumptions needed to prove the canonical B2 bound for `Ψ_K`
once the tail has been discharged (which it is for the compact-support kernel `K0`).

The intent is that these axioms are progressively replaced by proved theorems as the
explicit-formula machinery is formalized.  Concretely, we decompose the previously
monolithic truncation bound into:

* an explicit-formula decomposition `Ψ_K^N(x) - x = completion(x) + spectral(x)`,
* a completion-side bound `|completion(x)| ≤ CΓ`,
* a spectral/zero-side envelope `|spectral(x)| ≤ √x · S_cert`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-! ### Truncation-side bound (conventional analytic input) -/

/-!
### Explicit-formula decomposition (B2 input)

We keep the two terms abstract for now; the point of the decomposition is to make
it clear which parts are “completion” versus “spectral/zero-side”.
-/

/-- Placeholder completion-side term in the explicit formula for the canonical truncation story. -/
opaque trunc0_completionTerm : ℝ → ℝ

/-- Placeholder spectral/zero-side term in the explicit formula for the canonical truncation story. -/
opaque trunc0_spectralTerm : ℝ → ℝ

/-- Explicit-formula decomposition axiom for `Ψ_K^N(x) - x` (canonical B2 truncation story). -/
axiom trunc0_explicit_formula_decomp_axiom :
  ∀ x : ℝ, ValidX W0 x →
    PsiKTrunc K0 x N0 - x = trunc0_completionTerm x + trunc0_spectralTerm x

/-- Completion-side bound axiom (canonical B2 truncation story). -/
axiom trunc0_completion_bound_axiom :
  ∀ x : ℝ, ValidX W0 x → |trunc0_completionTerm x| ≤ CGamma0

/-- Spectral/zero-side envelope bound axiom (canonical B2 truncation story). -/
axiom trunc0_spectral_bound_axiom :
  ∀ x : ℝ, ValidX W0 x → |trunc0_spectralTerm x| ≤ Real.sqrt x * S0

/--
**Canonical truncation bound (derived).**

This is the single analytic payload required for the canonical B2 window bound once
the tail has been discharged.

Interpretation (intended, not yet formalized here): it is what one obtains from an
explicit formula by bounding the completion side by `CΓ` and the zero/spectral side by
`√x · S_cert` on the window.
-/
theorem trunc0_bound_axiom :
  ∀ x : ℝ, ValidX W0 x → |PsiKTrunc K0 x N0 - x| ≤ ETrunc0 x := by
  intro x hx
  have hdecomp := trunc0_explicit_formula_decomp_axiom (x := x) hx
  have hcomp : |trunc0_completionTerm x| ≤ CGamma0 :=
    trunc0_completion_bound_axiom (x := x) hx
  have hspectral : |trunc0_spectralTerm x| ≤ Real.sqrt x * S0 :=
    trunc0_spectral_bound_axiom (x := x) hx
  calc
    |PsiKTrunc K0 x N0 - x|
        = |trunc0_completionTerm x + trunc0_spectralTerm x| := by
            simpa [hdecomp]
    _ ≤ |trunc0_completionTerm x| + |trunc0_spectralTerm x| := by
          simpa using (abs_add_le (trunc0_completionTerm x) (trunc0_spectralTerm x))
    _ ≤ CGamma0 + Real.sqrt x * S0 := add_le_add hcomp hspectral
    _ = ETrunc0 x := by simp [ETrunc0]

end B2
end AltZeta
