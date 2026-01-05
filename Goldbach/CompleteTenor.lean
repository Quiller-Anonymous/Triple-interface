-- Goldbach/CompleteTenor.lean
import Goldbach.CoreTypes
import Goldbach.FiniteBase.CombineAll
import Goldbach.FinalTenor

open Goldbach

namespace Goldbach

/--
Tenor-aligned complete entry point: if you provide a pointwise Tenor witness at some cutoff `X0`,
then together with the checked finite base up to `X0` you get Goldbach for all even `n ≥ 4`.

This is a staging entry point: it wires the Tenor closure layer into the same
"finite base + analytic window" structure as `Goldbach/Complete.lean`, but does not
attempt to construct the Tenor witness from the current analytic engine.
-/
theorem goldbach_from_tenor_witness
    (w : Goldbach.PointwiseWitnessTenor)
    (hBase : FiniteBaseUpTo w.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  intro n hn h4
  exact Goldbach.goldbach_final_tenor (w := w) (hBase := hBase) (N := n) hn h4

/-- Canonical-cutoff convenience: use the repo’s checked finite base up to `1_000_000`. -/
theorem goldbach_from_tenor_witness_1e6
    (w : Goldbach.PointwiseWitnessTenor)
    (hX0 : w.X0 = 1_000_000) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  have hBase' : FiniteBaseUpTo w.X0 := by simpa [hX0] using hBase
  exact goldbach_from_tenor_witness (w := w) (hBase := hBase')

end Goldbach

