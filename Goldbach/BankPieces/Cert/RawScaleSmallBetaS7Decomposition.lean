import Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaS7Decomposition

open scoped BigOperators ArithmeticFunction.Moebius

open Complex
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
open Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- The currently preferred low-modulus major-arc singular block. -/
noncomputable def S7 : Finset ℕ := {2, 3, 4, 5, 6, 10}

/-- The exact `q`-secondary contribution restricted to a chosen finite modulus set. -/
noncomputable def smallBetaSecondaryOnModuliC (S : Finset ℕ) (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * ∑ q ∈ (Finset.Icc (2 : ℕ) Q0).filter (fun q => q ∈ S), AqLocalC X N q * qPhaseFactor q N

/-- The exact low-modulus secondary contribution supported on `S7`. -/
noncomputable def smallBetaSecondaryS7MainTermC (X N : ℕ) : ℂ :=
  smallBetaSecondaryOnModuliC S7 X N

/-- The complementary secondary contribution from moduli outside `S7`. -/
noncomputable def smallBetaSecondaryBeyondS7MainTermC (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * ∑ q ∈ (Finset.Icc (2 : ℕ) Q0).filter (fun q => q ∉ S7), AqLocalC X N q * qPhaseFactor q N

theorem smallBetaSecondaryGe2MainTermC_eq_S7_plus_beyondS7
    (X N : ℕ) :
    smallBetaSecondaryGe2MainTermC X N
      =
    smallBetaSecondaryS7MainTermC X N + smallBetaSecondaryBeyondS7MainTermC X N := by
  unfold smallBetaSecondaryGe2MainTermC smallBetaSecondaryS7MainTermC
    smallBetaSecondaryBeyondS7MainTermC smallBetaSecondaryOnModuliC
  rw [← mul_add]
  congr 1
  let s : Finset ℕ := Finset.Icc (2 : ℕ) Q0
  let f : ℕ → ℂ := fun q => AqLocalC X N q * qPhaseFactor q N
  calc
    ∑ q ∈ s, f q
        = (∑ q ∈ s.filter (fun q => q ∈ S7), f q)
            + (∑ q ∈ s.filter (fun q => q ∉ S7), f q) := by
              symm
              exact Finset.sum_filter_add_sum_filter_not (s := s) (p := fun q => q ∈ S7) (f := f)
    _ = (∑ q ∈ s.filter (fun q => q ∈ S7), f q)
          + (∑ q ∈ s.filter (fun q => q ∉ S7), f q) := by
            simp [s, f]

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaS7Decomposition
