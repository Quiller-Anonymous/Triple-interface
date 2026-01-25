import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound

/-!
Step 5 (ε₂-large TT*/Toeplitz): explicit “U-formula” upper bound (structure only).

This file is a *resource lemma* for the certificate route. It does **not** attempt the hard
number-theory/dispersion step.

What it does:
- replaces the `kernelMassNZEven/NZOdd` terms appearing in `toeplitzExprTopTight` by the already
  proved `AX+LX+RX` split bound (and then the uniform `RX` estimate);
- replaces the special `t=0` Fourier coefficient `‖Ŵ(0)‖` by the deterministic major-arc mass
  bound `‖Ŵ(0)‖ ≤ 2*Δ*Q0/X` (here `Δ=1`).

This yields a single explicit expression that depends only on:
- the band-limited mean squares `sumSqOn (evenBand X) (AX X 1)` and `sumSqOn (evenBand X) (LX X)`
  (and the odd analogues),
- plus deterministic small error envelopes.

The generator is expected to align to this expression when producing the numeric candidate `U`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold

noncomputable section

/-!
## Upper bounds for the nonzero-mode kernel masses (structure only)
-/

noncomputable def kernelMassNZEven_upper (X : ℕ) : ℝ :=
  (1 + δ_weightSplit) * (sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t))
    +
  (1 + 1 / δ_weightSplit) * (((evenBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

noncomputable def kernelMassNZOdd_upper (X : ℕ) : ℝ :=
  (1 + δ_weightSplit) * (sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t))
    +
  (1 + 1 / δ_weightSplit) * (((oddBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

theorem kernelMassNZEven_le_upper {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven X (1 : ℝ) (X + H) ≤ kernelMassNZEven_upper X := by
  -- Pure definitional wrapper (avoid `simp` recursion).
  dsimp [kernelMassNZEven_upper]
  exact kernelMassNZEven_le_AX_LX_plus_RX_bound (X := X) hX

theorem kernelMassNZOdd_le_upper {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZOdd X (1 : ℝ) (X + H) ≤ kernelMassNZOdd_upper X := by
  -- Pure definitional wrapper (avoid `simp` recursion).
  dsimp [kernelMassNZOdd_upper]
  exact kernelMassNZOdd_le_AX_LX_plus_RX_bound (X := X) hX

/-!
## A single “generator-facing” Toeplitz upper bound

This is the explicit expression the generator should compute (at `X0`) and export as a candidate
`U` in `Q0MajorTailTTStarCertData.lean`.
-/

noncomputable def toeplitzExprTopTight_upper (X : ℕ) : ℝ :=
  ((1 + 1 / δ_split) * kernelMassNZEven_upper X) * (coeffMass X (X + H)) ^ 2
    +
  (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * (aTerm2Mass X) * (coeffMass X (X + H))
    +
  ((1 + δ_split)
      * ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
            *
          (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
              (Nat.totient q : ℝ) / (q : ℝ))) ^ 2)
      * diagBoundTight X (X + H)

theorem toeplitzExprTopTight_le_upper {X : ℕ} (hX : X0 ≤ X) :
    toeplitzExprTopTight X (1 : ℝ) ≤ toeplitzExprTopTight_upper X := by
  classical
  have hXpos : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hΔ0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  -- Bound the nonzero kernel masses by the Step5 split upper bounds.
  have hEven : kernelMassNZEven X (1 : ℝ) (X + H) ≤ kernelMassNZEven_upper X :=
    kernelMassNZEven_le_upper (X := X) hX
  have hOdd : kernelMassNZOdd X (1 : ℝ) (X + H) ≤ kernelMassNZOdd_upper X :=
    kernelMassNZOdd_le_upper (X := X) hX
  -- Bound the `t=0` coefficient by the major-arc mass estimate.
  have h0 :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖
        ≤ ((2 * (1 : ℝ)) / (X : ℝ))
            * (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
                (Nat.totient q : ℝ) / (q : ℝ)) :=
    norm_majorArcWeightFourier_zero_le_two_div_X_mul_sum_totient_div (X := X) (Δ := (1 : ℝ)) hΔ0 hXpos
  have h0sq :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2
        ≤ (((2 * (1 : ℝ)) / (X : ℝ))
            * (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
                (Nat.totient q : ℝ) / (q : ℝ))) ^ 2 := by
    -- square the inequality (using nonnegativity + `nlinarith`)
    set RHS : ℝ :=
        ((2 * (1 : ℝ)) / (X : ℝ))
          * (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
              (Nat.totient q : ℝ) / (q : ℝ)) with hRHS
    have hXr : 0 < (X : ℝ) := by exact_mod_cast hXpos
    have hsum :
        0 ≤ (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
              (Nat.totient q : ℝ) / (q : ℝ)) := by
      refine Finset.sum_nonneg ?_
      intro q hq
      have hq0 : 0 ≤ (Nat.totient q : ℝ) := by positivity
      have hqpos : 0 < (q : ℝ) := by
        have : (0 : ℕ) < q := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
        exact_mod_cast this
      exact div_nonneg hq0 (le_of_lt hqpos)
    have hRHS_nonneg : 0 ≤ RHS := by
      have hnum : 0 ≤ (2 : ℝ) * (1 : ℝ) := by norm_num
      have hfrac : 0 ≤ ((2 * (1 : ℝ)) / (X : ℝ)) := div_nonneg hnum (le_of_lt hXr)
      simpa [RHS, hRHS] using mul_nonneg hfrac hsum
    have hLHS_nonneg :
        0 ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖ :=
      norm_nonneg _
    have h0' :
        ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖ ≤ RHS := by
      simpa [RHS, hRHS] using h0
    have : ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2 ≤ RHS ^ 2 := by
      nlinarith
    simpa [RHS, hRHS] using this
  -- Now compare term-by-term.
  unfold toeplitzExprTopTight toeplitzExprTopTight_upper
  -- all coefficients are nonnegative, so `mul_le_mul_of_nonneg_right/left` applies cleanly
  have hδ1 : 0 ≤ (1 + 1 / δ_split) := by
    have : 0 ≤ (1 / δ_split) := le_of_lt (one_div_pos.mpr δ_split_pos)
    nlinarith
  have hδ2 : 0 ≤ (1 + δ_split) := by
    have : 0 ≤ δ_split := le_of_lt δ_split_pos
    nlinarith
  have hcoeffsq : 0 ≤ (coeffMass X (X + H)) ^ 2 := sq_nonneg _
  have hcoeff : 0 ≤ coeffMass X (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha2 : 0 ≤ aTerm2Mass X := aTerm2Mass_nonneg X
  have hdiag : 0 ≤ diagBoundTight X (X + H) := by
    unfold diagBoundTight
    have : 0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := sq_nonneg _
    exact mul_nonneg this hcoeff
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- even term
    have hleft :
        (1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)
          ≤ (1 + 1 / δ_split) * kernelMassNZEven_upper X :=
      mul_le_mul_of_nonneg_left hEven hδ1
    exact mul_le_mul_of_nonneg_right hleft hcoeffsq
  · -- odd term
    have h0' : 0 ≤ (2 : ℝ) := by norm_num
    have hδ1' : 0 ≤ (2 * (1 + 1 / δ_split)) := mul_nonneg h0' hδ1
    have hleft :
        2 * (1 + 1 / δ_split) * kernelMassNZOdd X (1 : ℝ) (X + H)
          ≤ 2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X :=
      mul_le_mul_of_nonneg_left hOdd hδ1'
    have hmid :
        (2 * (1 + 1 / δ_split) * kernelMassNZOdd X (1 : ℝ) (X + H)) * aTerm2Mass X
          ≤ (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * aTerm2Mass X :=
      mul_le_mul_of_nonneg_right hleft ha2
    have :
        (2 * (1 + 1 / δ_split) * kernelMassNZOdd X (1 : ℝ) (X + H)) * aTerm2Mass X *
              coeffMass X (X + H)
          ≤
        (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * aTerm2Mass X *
              coeffMass X (X + H) :=
      mul_le_mul_of_nonneg_right hmid hcoeff
    simpa [mul_assoc] using this
  · -- diagonal / t=0 term
    have :
        ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2) *
              diagBoundTight X (X + H)
          ≤
        ((1 + δ_split)
            * ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
                *
              (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
                  (Nat.totient q : ℝ) / (q : ℝ))) ^ 2) *
              diagBoundTight X (X + H) := by
      have hleft :
          (1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2
            ≤
          (1 + δ_split)
            * ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
                *
              (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
                  (Nat.totient q : ℝ) / (q : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_left h0sq hδ2
      exact mul_le_mul_of_nonneg_right hleft hdiag
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound
