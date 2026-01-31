import SSU.Hilbert.InterzoneZ

/-!
Operator packet API (energy-ledger-first), indexed by `ℤ`.

Main lemma (payoff):

`‖∑_{i∈J} T_i f‖² ≤ Crow * ∑_{i∈J} ‖T_i f‖²`

assuming a pointwise-in-`f` Gram decay hypothesis and a row-sum bound on the decay weights.

This is designed to plug directly into ledger/certificate pipelines.
-/

namespace SSU
namespace Hilbert

open scoped BigOperators

open Complex

noncomputable section

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- Pointwise (in `f`) Gram-decay hypothesis for an operator family. -/
def OperatorAOGram
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (J : Finset ℤ) (T : ℤ → H₁ →L[ℂ] H₂) (a : ℕ → NNReal) : Prop :=
  ∀ f : H₁, ∀ i ∈ J, ∀ j ∈ J,
    ‖⟪T i f, T j f⟫‖ ≤ (a (distZ i j) : ℝ) * ‖T i f‖ * ‖T j f‖

/-- The energy-ledger inequality for a packetized operator family. -/
theorem energy_ledger_of_operatorAOGram
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {J : Finset ℤ} {T : ℤ → H₁ →L[ℂ] H₂} {a : ℕ → NNReal} {Crow : ℝ}
    (hGram : OperatorAOGram J T a)
    (hRow : ∀ i ∈ J, (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ Crow) :
    ∀ f : H₁,
      ‖∑ i ∈ J, T i f‖ ^ 2 ≤ Crow * ∑ i ∈ J, ‖T i f‖ ^ 2 := by
  intro f
  -- Apply the vector interzone lemma to `v i := T i f` and `D i := ‖T i f‖²`.
  have hD : ∀ i ∈ J, 0 ≤ ‖T i f‖ ^ 2 := by
    intro i hi; positivity
  have hGram' :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪T i f, T j f⟫‖
          ≤ (a (distZ i j) : ℝ) * Real.sqrt (‖T i f‖ ^ 2) * Real.sqrt (‖T j f‖ ^ 2) := by
    intro i hi j hj
    have := hGram f i hi j hj
    -- `sqrt(‖x‖²) = ‖x‖`.
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖T i f‖),
      abs_of_nonneg (by positivity : 0 ≤ ‖T j f‖), pow_two] using this
  -- Now apply the general lemma.
  have := norm_sum_sq_le_of_rowSum_gram_boundZ
      (J := J) (v := fun i => T i f) (D := fun i => ‖T i f‖ ^ 2) (a := a) (Crow := Crow)
      hD hGram' hRow
  simpa using this

/--
Corollary: an operator-norm bound for `∑ T_i` from:

1. the energy-ledger inequality, and
2. a Bessel/diagonal bound `∑ ‖T_i f‖² ≤ B ‖f‖²`.
-/
theorem opNorm_sum_le_of_energyLedger
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {J : Finset ℤ} {T : ℤ → H₁ →L[ℂ] H₂} {Crow B : ℝ}
    (hLedger : ∀ f : H₁, ‖∑ i ∈ J, T i f‖ ^ 2 ≤ Crow * ∑ i ∈ J, ‖T i f‖ ^ 2)
    (hBessel : ∀ f : H₁, ∑ i ∈ J, ‖T i f‖ ^ 2 ≤ B * ‖f‖ ^ 2)
    (hCrow : 0 ≤ Crow) (hB : 0 ≤ B) :
    ‖∑ i ∈ J, T i‖ ≤ Real.sqrt (Crow * B) := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound
    (f := (∑ i ∈ J, T i)) (M := Real.sqrt (Crow * B)) (Real.sqrt_nonneg _) ?_
  intro f
  have hcomb : ‖∑ i ∈ J, T i f‖ ^ 2 ≤ (Crow * B) * ‖f‖ ^ 2 := by
    have h1 := hLedger f
    have h2 := hBessel f
    nlinarith [h1, h2]
  have hnonneg : 0 ≤ (Crow * B) * ‖f‖ ^ 2 := by
    have : 0 ≤ Crow * B := mul_nonneg hCrow hB
    positivity
  have hsqrt : ‖∑ i ∈ J, T i f‖ ≤ Real.sqrt ((Crow * B) * ‖f‖ ^ 2) := by
    exact (Real.le_sqrt (x := ‖∑ i ∈ J, T i f‖) (y := (Crow * B) * ‖f‖ ^ 2)
      (by positivity) hnonneg).2 hcomb
  have hsimp : Real.sqrt ((Crow * B) * ‖f‖ ^ 2) = Real.sqrt (Crow * B) * ‖f‖ := by
    have hcb : 0 ≤ Crow * B := mul_nonneg hCrow hB
    calc
      Real.sqrt ((Crow * B) * ‖f‖ ^ 2)
          = Real.sqrt (Crow * B) * Real.sqrt (‖f‖ ^ 2) := by
              exact Real.sqrt_mul hcb (‖f‖ ^ 2)
      _ = Real.sqrt (Crow * B) * ‖f‖ := by
              simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖f‖)]
  -- `((∑ i ∈ J, T i) f)` simplifies to `∑ i ∈ J, T i f`.
  simpa [hsimp] using hsqrt

end

end Hilbert
end SSU
