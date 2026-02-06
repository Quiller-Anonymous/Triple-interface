import SSU.Hilbert.OperatorLedgerZ
import SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal

/-!
Rank-one Type–II signal: first ledger inequality (TeX-faithful “non-toy”, but analytic-trivial).

This file is intentionally modest: it records that the SSU **energy-ledger** inequality is
available (and machine-checks) for the *real-frequency TT\** model packet operators when evaluated
on the TeX rank-one Type–II signal `S(ξ)`.

The bound here uses only Cauchy–Schwarz (i.e. decay function `a ≡ 1`), so the Crow constant is the
finite cardinality of the external index set `J`. This is not the SSU heart; it is just the first
place where the proven Hilbert-space ledger lemma is exercised on the “right” kind of signal.

The *real* SSU heart remains the extraction step + the Type–II analytic bound that produces a
summable decay in `distZ`.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzRankOneLedger

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Hilbert

variable {κ : Type*} [DecidableEq κ]

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

open SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar
open SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal

private noncomputable def packetOp
    (hX : 0 < D.X) (hH : 0 < D.H) (j : ℤ) :
    Model.L2Band D.X D.H →L[ℂ] Model.L2Band D.X D.H :=
  Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j

/--
Energy-ledger inequality on the TT* band model packet family, evaluated on the rank-one Type–II
signal `S(ξ)`.

This uses only `a ≡ 1`, hence the Crow constant is `card(J)`.
-/
theorem energy_ledger_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) :
    ‖∑ j ∈ D.J, (packetOp (D := D) hX hH j)
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H)‖ ^ 2
      ≤
    (D.J.card : ℝ) *
      ∑ j ∈ D.J, ‖(packetOp (D := D) hX hH j)
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H)‖ ^ 2 := by
  classical
  -- Use the SSU ledger lemma with `a ≡ 1`.
  let a : ℕ → NNReal := fun _ => (1 : NNReal)
  have hGram : OperatorAOGram (J := D.J) (T := packetOp (D := D) hX hH) a := by
    intro f i hi j hj
    -- Cauchy–Schwarz in the Hilbert space `L2Band`.
    have : ‖inner ℂ ((packetOp (D := D) hX hH i) f) ((packetOp (D := D) hX hH j) f)‖
        ≤ ‖(packetOp (D := D) hX hH i) f‖ * ‖(packetOp (D := D) hX hH j) f‖ :=
      norm_inner_le_norm _ _
    -- Rewrite the RHS into the `a(dist) * ‖..‖ * ‖..‖` form.
    simpa [a] using this
  have hRow : ∀ i ∈ D.J, (∑ j ∈ D.J, (a (distZ i j) : ℝ)) ≤ (D.J.card : ℝ) := by
    intro i hi
    -- `∑_{j∈J} 1 = card(J)`.
    have hsum : (∑ j ∈ D.J, (a (distZ i j) : ℝ)) = (D.J.card : ℝ) := by
      simp [a]
    exact le_of_eq hsum
  simpa using
    (energy_ledger_of_operatorAOGram (J := D.J) (T := packetOp (D := D) hX hH) (a := a)
      (Crow := (D.J.card : ℝ)) hGram hRow
      (f := RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))

end

end FejerBankedTypeIIToeplitzRankOneLedger
end Instances
end SSU
