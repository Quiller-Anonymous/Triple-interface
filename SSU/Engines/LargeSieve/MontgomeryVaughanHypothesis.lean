import SSU.Engines.TypeII
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Montgomery–Vaughan large sieve: hypothesis interface.

Mathlib (in this repo snapshot) does not provide a ready-to-use Montgomery–Vaughan large sieve in the
exact “TeX Step 3/4” form. To keep SSU modular, we record the needed analytic estimate as a
standalone hypothesis interface.

Downstream SSU code should depend on this interface (or one of its specializations) until we
complete a full proof in a dedicated analytic module.
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

/-!
## A generic finite large-sieve interface for exponential sums

We keep this intentionally abstract:
* `ι` indexes “frequencies” / evaluation points.
* `κ` indexes coefficients.
* `phase : ι → κ → ℝ` is the real-valued phase used in `e(phase i k)`.

The interface records a bound of the form

`∑_{i∈I} ‖∑_{k∈K} a(k) * e(phase i k)‖^2 ≤ C * ∑_{k∈K} ‖a(k)‖^2`.

This is the exact shape consumed by the Type–II Step 3/4 fiber reductions.
-/

structure FiniteLargeSieve (ι κ : Type) [DecidableEq ι] [DecidableEq κ] where
  I : Finset ι
  K : Finset κ
  phase : ι → κ → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ a : κ → ℂ,
      (∑ i ∈ I, ‖∑ k ∈ K, a k * SSU.Engines.TypeII.e (phase i k)‖ ^ 2)
        ≤
      C * (∑ k ∈ K, ‖a k‖ ^ 2)

end

end LargeSieve
end Engines
end SSU
