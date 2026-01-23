import AltZeta.B2ConventionalTruncSpec

/-!
AltZeta/B2Gold.lean
===================

Gold-style entrypoint for the B2 target:

  `|Ψ_K(x) - x| ≤ (CΓ + √x · S) + E_tail(x)` on a dyadic window `[X,2X]`.

This file is intentionally project-invariant: it takes the explicit-formula/truncation
information as a `TruncEFSpec` and the tail story as a `TailControl` bundle.  No canonical
window/census constants are mentioned here.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/--
**B2 window bound (gold entrypoint).**

Given:
* a conventional explicit-formula spec for the truncation side, and
* any certified tail control,

we get a B2-style bound on the full infinite-sum statistic `Ψ_K(x)` on the window.
-/
theorem b2_bound_on_window
    {W : Window} {K : LogKernel} {N : ℕ}
    (spec : TruncEFSpec W K N) (tail : TailControl W K N) :
    ∀ x : ℝ, ValidX W x → |PsiK K x - x| ≤ EFull spec.truncControl tail x := by
  simpa using
    (bound_full_on_window (W := W) (K := K) (N := N) spec.truncControl tail)

/--
Same bound, written out as `CΓ + √x · S + E_tail(x)` for readability.
-/
theorem b2_bound_on_window'
    {W : Window} {K : LogKernel} {N : ℕ}
    (spec : TruncEFSpec W K N) (tail : TailControl W K N) :
    ∀ x : ℝ, ValidX W x → |PsiK K x - x| ≤ spec.CGamma + Real.sqrt x * spec.S + tail.ETail x := by
  intro x hx
  have h := b2_bound_on_window (spec := spec) (tail := tail) x hx
  simpa [TruncEFSpec.truncControl, TruncEFSpec.ETrunc, EFull, add_assoc] using h

end B2
end AltZeta

