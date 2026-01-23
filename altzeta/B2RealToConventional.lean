import AltZeta.B2Gold
import AltZeta.B2RealTruncAxioms
import AltZeta.B2RealParams

/-!
AltZeta/B2RealToConventional.lean
=================================

Bridge from the canonical (pinned) B2 truncation axioms to the conventional `TruncEFSpec`
interface.

This makes it explicit that the canonical conditional theorem is just a particular
instantiation of the gold entrypoint `AltZeta.B2.b2_bound_on_window`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-- The canonical truncation axioms packaged as a `TruncEFSpec`. -/
def spec0 : TruncEFSpec W0 K0 N0 :=
{ CGamma := CGamma0
, hCGamma := Goldbach.Census.CGamma_nonneg
, S := S0
, hS := Goldbach.Census.S_cert_nonneg
, completionTerm := trunc0_completionTerm
, spectralTerm := trunc0_spectralTerm
, decomp := trunc0_explicit_formula_decomp_axiom
, completion_bound := trunc0_completion_bound_axiom
, spectral_bound := trunc0_spectral_bound_axiom
}

lemma EFull_spec0_tail0_eq_ETrunc0 (x : ℝ) :
    EFull (spec0.truncControl) tail0 x = ETrunc0 x := by
  simp [EFull, spec0, TruncEFSpec.truncControl, TruncEFSpec.ETrunc, ETrunc0, tail0, tailControl_KHat]

/-- Canonical B2 window bound, recovered from the gold entrypoint. -/
theorem b2_bound0_on_window_via_gold :
    ∀ x : ℝ, ValidX W0 x → |PsiK K0 x - x| ≤ ETrunc0 x := by
  intro x hx
  have h := b2_bound_on_window (spec := spec0) (tail := tail0) x hx
  simpa [EFull_spec0_tail0_eq_ETrunc0 (x := x)] using h

end B2
end AltZeta

