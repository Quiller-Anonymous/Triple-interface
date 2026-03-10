import Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget

/-!
`Q0MinorToeplitzTarget` isolates the next analytic bridge after TT* expansion.

The intended workflow is:

1. rewrite the packet Gram entry as a Toeplitz / tube-weighted quadratic form;
2. prove a polynomial decay bound for that quadratic form;
3. combine with the diagonal packet-energy ledger to obtain the TT* target.

This file does not choose a particular Toeplitz model. It only packages the exact data needed to
bridge from a modeled quadratic form back to the existing TT* analytic target.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorToeplitzTarget

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorDiagonalLedgerTarget
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget

noncomputable section

/--
Off-diagonal Toeplitz/tube target for the dyadic packet Gram sum.

`toeplitzExpr X i j` is the modeled quadratic form produced after TT* expansion and
Toeplitz/tube reformulation. The two essential obligations are:

* it agrees with the explicit TT* Gram sum;
* it satisfies the desired polynomial shell-separation bound.
-/
structure Q0MinorToeplitzPolyDecay (Δ : ℝ) (C : ℝ) (p : ℕ) where
  C_nonneg : 0 ≤ C
  p_gt_one : 1 < p
  toeplitzExpr : ℕ → ℕ → ℕ → ℂ
  gramSum_eq :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ i ∈ (JX X : Finset ℕ), ∀ j ∈ (JX X : Finset ℕ),
        dyadicGramSum (X := X) (Δ := Δ) i j = toeplitzExpr X i j
  toeplitz_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ i ∈ (JX X : Finset ℕ), ∀ j ∈ (JX X : Finset ℕ),
        ‖toeplitzExpr X i j‖
          ≤ aPoly C p (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j)

/--
Toeplitz/tube off-diagonal control plus the diagonal ledger immediately yields the TT* analytic
target for `ε₁`.
-/
theorem to_Q0MinorTTStarPolyDecay
    {Δ : ℝ} {C : ℝ} {p : ℕ} {C2 C3 : ℝ}
    (hOff : Q0MinorToeplitzPolyDecay Δ C p)
    (hDiag : Q0MinorDiagonalLedger Δ C2 C3) :
    Q0MinorTTStarPolyDecay Δ C p C2 C3 := by
  refine ⟨hOff.C_nonneg, hOff.p_gt_one, hDiag.C2_nonneg, hDiag.C3_nonneg, ?_, hDiag.sumD_bound⟩
  intro X hX i hi j hj
  rw [hOff.gramSum_eq (X := X) hX i hi j hj]
  exact hOff.toeplitz_bound (X := X) hX i hi j hj

end

end Goldbach.Cert.MajorArcModules.Q0MinorToeplitzTarget
