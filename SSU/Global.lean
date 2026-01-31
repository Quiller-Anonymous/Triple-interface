import SSU.Spaces.L2Z
import SSU.Hilbert.CotlarSteinZ

/-!
Global SSU: statement-level contract (operator route on `ℓ²(ℤ)`).

This file commits SSU’s “core” setting to global `ℓ²(ℤ)` (counting measure), per the SSU notes.

The analytic work (tubes, projectors, kernels, TT*, etc.) is expected to *produce* instances of the
interfaces below; the final `L²` operator norm bound is then discharged by
`SSU.Hilbert.opNorm_sum_le_of_operatorAOGram`.
-/

namespace SSU

open scoped BigOperators

namespace Global

open SSU.Spaces
open SSU.Hilbert

noncomputable section

/-- SSU’s ambient complex signal space `ℓ²(ℤ)`. -/
abbrev Signal : Type := L2Z

/-- Bounded linear operators on the SSU signal space. -/
abbrev Op : Type := Signal →L[ℂ] Signal

/-- A finite “packet family” of SSU operators, indexed by `ℤ`. -/
structure PacketFamily where
  J : Finset ℤ
  T : ℤ → Op

/-- The deterministic row-sum (Crow) bound on a decay function `a : ℕ → NNReal`. -/
def RowSumBound (F : PacketFamily) (a : ℕ → NNReal) (Crow : ℝ) : Prop :=
  ∀ i ∈ F.J, (∑ j ∈ F.J, (a (distZ i j) : ℝ)) ≤ Crow

/-- A Bessel/diagonal bound for a packet family (the “bank overlap” output). -/
def BesselBound (F : PacketFamily) (B : ℝ) : Prop :=
  ∀ f : Signal, ∑ i ∈ F.J, ‖F.T i f‖ ^ 2 ≤ B * ‖f‖ ^ 2

/--
The “ready to plug into Cotlar–Stein” SSU contract.

An SSU instantiation should provide:
- a decay profile `a`,
- a Crow constant for row-sums of `a(distZ · ·)`,
- a diagonal/Bessel constant `B`,
- a pointwise Gram decay hypothesis `OperatorAOGram`.

Then the global operator norm bound follows automatically.
-/
structure SSUContract (F : PacketFamily) where
  a : ℕ → NNReal
  Crow : ℝ
  B : ℝ
  gram : OperatorAOGram F.J F.T a
  row : RowSumBound F a Crow
  bessel : BesselBound F B
  crow_nonneg : 0 ≤ Crow
  b_nonneg : 0 ≤ B

theorem opNorm_sum_le_of_contract {F : PacketFamily} (C : SSUContract F) :
    ‖∑ i ∈ F.J, F.T i‖ ≤ Real.sqrt (C.Crow * C.B) :=
  opNorm_sum_le_of_operatorAOGram (J := F.J) (T := F.T) (a := C.a)
    (Crow := C.Crow) (B := C.B) C.gram C.row C.bessel C.crow_nonneg C.b_nonneg

end

end Global

end SSU
