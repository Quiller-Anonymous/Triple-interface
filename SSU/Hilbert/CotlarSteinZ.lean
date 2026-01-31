import SSU.Hilbert.OperatorLedgerZ

/-!
Cotlar–Stein-style wrappers (finite packet family on `ℤ`).

In SSU applications, the “operator route” is primary: prove an almost-orthogonality hypothesis for
the packet operators, then obtain an `L²` operator norm bound for the packet sum.

This file provides a small convenience lemma bundling:

1. `energy_ledger_of_operatorAOGram`, and
2. `opNorm_sum_le_of_energyLedger`.
-/

namespace SSU
namespace Hilbert

open scoped BigOperators

theorem opNorm_sum_le_of_operatorAOGram
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {J : Finset ℤ} {T : ℤ → H₁ →L[ℂ] H₂} {a : ℕ → NNReal} {Crow B : ℝ}
    (hGram : OperatorAOGram J T a)
    (hRow : ∀ i ∈ J, (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ Crow)
    (hBessel : ∀ f : H₁, ∑ i ∈ J, ‖T i f‖ ^ 2 ≤ B * ‖f‖ ^ 2)
    (hCrow : 0 ≤ Crow) (hB : 0 ≤ B) :
    ‖∑ i ∈ J, T i‖ ≤ Real.sqrt (Crow * B) := by
  have hLedger : ∀ f : H₁, ‖∑ i ∈ J, T i f‖ ^ 2 ≤ Crow * ∑ i ∈ J, ‖T i f‖ ^ 2 :=
    energy_ledger_of_operatorAOGram (J := J) (T := T) (a := a) (Crow := Crow) hGram hRow
  exact opNorm_sum_le_of_energyLedger (J := J) (T := T) (Crow := Crow) (B := B)
    hLedger hBessel hCrow hB

end Hilbert
end SSU

