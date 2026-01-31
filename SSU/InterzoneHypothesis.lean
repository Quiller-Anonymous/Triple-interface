import SSU.Hilbert.DistZ
import SSU.Hilbert.OperatorLedgerZ

/-!
Interzone hypothesis interface (the “SSU heart” placeholder).

This file isolates the only genuinely hard analytic input behind an interface:
cross-operator almost-orthogonality with summable decay in the external dyadic index `j : ℤ`.

Downstream packages can initially assume an `InterzoneHypothesis` as an axiom/parameter, while SSU’s
deterministic Hilbert-space + Crow machinery remains fully proved.
-/

namespace SSU
namespace Interzone

open SSU.Hilbert

noncomputable section

/--
Interzone decay hypothesis along the external index `j : ℤ`.

This is the intended “single remaining axiom” for the first platinum instantiation:
prove everything else in SSU, and assume this bound (with explicit `C,p`) until the real SSU tube
inequality is formalized.

We keep the decay function as `a : ℕ → NNReal` (nonnegative), indexed by `distZ`.
-/
structure Hypothesis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (J : Finset ℤ) (T : ℤ → (H →L[ℂ] H)) where
  a : ℕ → NNReal
  /-- Cross-operator bound `‖T i† ∘ T j‖ ≤ a(distZ i j)`. -/
  adj_comp_le : ∀ i ∈ J, ∀ j ∈ J, ‖(T i).adjoint.comp (T j)‖ ≤ (a (distZ i j) : ℝ)
  /-- Cross-operator bound `‖T i ∘ T j†‖ ≤ a(distZ i j)`. -/
  comp_adj_le : ∀ i ∈ J, ∀ j ∈ J, ‖(T i).comp (T j).adjoint‖ ≤ (a (distZ i j) : ℝ)

/--
Ledger-friendly interzone hypothesis: pointwise (in `f`) Gram decay for the packet outputs.

This matches SSU’s primary “energy-ledger” engine (`SSU.Hilbert.OperatorAOGram`), and is often the
form produced directly by tube overlap / kernel-product estimates.
-/
structure GramHypothesis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (J : Finset ℤ) (T : ℤ → (H →L[ℂ] H)) where
  a : ℕ → NNReal
  gram : SSU.Hilbert.OperatorAOGram J T a

end

end Interzone
end SSU
