import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle

/-!
`Q0MinorDiagonalLedgerTarget` isolates the diagonal packet-energy ledger target for `ε₁`.

This is the easier half of the remaining analytic seam: it only asks for a bound on the *sum of
packet energies* `∑_j ‖v_{X,j}‖²`, with the certified Goldbach scaling
`H / X + 1 / (H Q0^2)`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle

noncomputable section

/--
Diagonal packet-energy ledger target for the dyadic minor-arc packet family.
-/
structure Q0MinorDiagonalLedger (Δ : ℝ) (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  sumD_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j)
        ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) ^ 2)

end

end Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
