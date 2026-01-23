import AltZeta.B2Hypotheses
import Mathlib.Data.Real.Sqrt

/-!
AltZeta/B2ConventionalTruncSpec.lean
====================================

Conventional-math interface for the B2 truncation-side bound.

This is the “project-invariant” replacement for pinned/canonical axioms: it isolates the
explicit-formula decomposition for `Ψ_K^N(x) - x` into completion + spectral terms, together
with separate bounds for each term.

Downstream files can treat an inhabitant of `TruncEFSpec` as the analytic input expected of a
textbook/paper theorem package.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/--
Conventional B2 truncation-side explicit-formula spec.

This is intentionally parameterized over `(W, K, N)` and abstract constants `(CGamma, S)` so it
does not bake in any project-pinned windows/caps.
-/
structure TruncEFSpec (W : Window) (K : LogKernel) (N : ℕ) where
  /-- Completion-side constant bound `CΓ`. -/
  CGamma : ℝ
  hCGamma : 0 ≤ CGamma
  /-- Spectral envelope constant `S`. -/
  S : ℝ
  hS : 0 ≤ S
  /-- Completion-side term in the explicit formula. -/
  completionTerm : ℝ → ℝ
  /-- Spectral/zero-side term in the explicit formula. -/
  spectralTerm : ℝ → ℝ
  /-- Explicit-formula decomposition for `Ψ_K^N(x) - x` on the window. -/
  decomp :
    ∀ x : ℝ, ValidX W x →
      PsiKTrunc K x N - x = completionTerm x + spectralTerm x
  /-- Completion-side bound `|completion(x)| ≤ CΓ` on the window. -/
  completion_bound :
    ∀ x : ℝ, ValidX W x → |completionTerm x| ≤ CGamma
  /-- Spectral/zero-side envelope `|spectral(x)| ≤ √x · S` on the window. -/
  spectral_bound :
    ∀ x : ℝ, ValidX W x → |spectralTerm x| ≤ Real.sqrt x * S

namespace TruncEFSpec

variable {W : Window} {K : LogKernel} {N : ℕ} (spec : TruncEFSpec W K N)

/-- The canonical truncation envelope induced by the spec: `E_trunc(x) := CΓ + √x · S`. -/
def ETrunc (x : ℝ) : ℝ :=
  spec.CGamma + Real.sqrt x * spec.S

lemma ETrunc_nonneg (x : ℝ) (_hx : ValidX W x) : 0 ≤ spec.ETrunc x := by
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hprod : 0 ≤ Real.sqrt x * spec.S := mul_nonneg hsqrt spec.hS
  exact add_nonneg spec.hCGamma hprod

/--
Truncation-side bound derived from the decomposition + component bounds:

`|Ψ_K^N(x) - x| ≤ CΓ + √x · S`.
-/
theorem trunc_bound :
    ∀ x : ℝ, ValidX W x → |PsiKTrunc K x N - x| ≤ spec.ETrunc x := by
  intro x hx
  have hdecomp := spec.decomp x hx
  have hcomp : |spec.completionTerm x| ≤ spec.CGamma := spec.completion_bound x hx
  have hspectral : |spec.spectralTerm x| ≤ Real.sqrt x * spec.S := spec.spectral_bound x hx
  calc
    |PsiKTrunc K x N - x|
        = |spec.completionTerm x + spec.spectralTerm x| := by
            simpa [hdecomp]
    _ ≤ |spec.completionTerm x| + |spec.spectralTerm x| := by
          simpa using (abs_add_le (spec.completionTerm x) (spec.spectralTerm x))
    _ ≤ spec.CGamma + Real.sqrt x * spec.S := add_le_add hcomp hspectral
    _ = spec.ETrunc x := by simp [ETrunc]

/-- Package a `TruncEFSpec` into the `TruncControl` bundle expected by the B2 interface. -/
def truncControl : TruncControl W K N :=
{ ETrunc := spec.ETrunc
, ETrunc_nonneg := spec.ETrunc_nonneg
, bound_trunc := spec.trunc_bound }

end TruncEFSpec

end B2
end AltZeta

