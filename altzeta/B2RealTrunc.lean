import AltZeta.B2RealEnvelope
import AltZeta.B2RealTruncAxioms
import AltZeta.B2Hypotheses
import Mathlib.Algebra.Order.Field.Basic

/-!
AltZeta/B2RealTrunc.lean
========================

Canonical (real-parameter) truncation-side hypothesis for the B2 workflow.

At this stage we have:
* a canonical window/schedule (`AltZeta.B2RealParams.W0`, `Sch0`),
* a concrete compact-support kernel `K0 := KHat T0`,
* and certifiable tail control `tail0 : TailControl W0 K0 N0` with `ETail = 0`.

The remaining analytic input needed for a full B2 bound is a *truncation control*
statement bounding `|Ψ_K^N(x) - x|` on the window.

This file packages that remaining input as an explicit hypothesis.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-! ### Canonical truncation envelope -/

/--
**Canonical truncation hypothesis (B2 input).**

This is the “explicit formula / completion / zero-side” analytic payload for the B2
prime-counter story, specialized to the canonical window and the canonical compact-support
kernel/cutoff.

It is deliberately stated as an axiom-like hypothesis so that later work can
replace it with a proved theorem package.
-/
theorem trunc0_bound :
  ∀ x : ℝ, ValidX W0 x → |PsiKTrunc K0 x N0 - x| ≤ ETrunc0 x := by
  exact trunc0_bound_axiom

/-- Package the canonical truncation hypothesis into a `TruncControl` bundle. -/
def trunc0 : TruncControl W0 K0 N0 :=
{ ETrunc := ETrunc0
, ETrunc_nonneg := by
    intro x _hx
    simpa using ETrunc0_nonneg (x := x)
, bound_trunc := trunc0_bound
}

end B2
end AltZeta
