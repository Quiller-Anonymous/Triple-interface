import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5AXBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXCoreCollapse
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound

/-!
Step 5 (ε₂-large TT*/Toeplitz): Route-A “U-formula” upper bound.

This file bridges the existing *structure-only* Toeplitz upper bound
`toeplitzExprTopTight_upper` to a fully explicit expression by inserting:

- the deterministic small-`q` bound for `AX` (q≤12),
- the deterministic Route-A (divisor-expansion) mean-square bound for `LX` (q≥13),
- and a generic `‖a+b‖² ≤ 2‖a‖² + 2‖b‖²` inequality to avoid cross terms between `AX` and `LX`.

The goal is a generator-aligned expression depending only on:
`LXMeanSquareUpperCore` and simple rational prefactors.

This is still “certificate-facing”: it does not *compute* the big finite sums, it only reduces the
Lean proof obligations to them.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5AXBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXCoreCollapse
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound

noncomputable section

/-!
## Basic `sumSqOn` inequality for `AX+LX`
-/

private lemma norm_add_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  -- `(‖a+b‖)² ≤ (‖a‖+‖b‖)² ≤ 2(‖a‖²+‖b‖²)`
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have ha : 0 ≤ ‖a‖ := norm_nonneg a
  have hb : 0 ≤ ‖b‖ := norm_nonneg b
  have h2 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    -- Expand and bound the cross term `2‖a‖‖b‖ ≤ ‖a‖² + ‖b‖²`.
    have hxy : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      -- `two_mul_le_add_sq` is `2ab ≤ a^2 + b^2`.
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (two_mul_le_add_sq (‖a‖) (‖b‖))
    have : (‖a‖ + ‖b‖) ^ 2 = ‖a‖ ^ 2 + 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring
    rw [this]
    nlinarith [hxy]
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    have hnonneg : 0 ≤ ‖a + b‖ := norm_nonneg _
    have hnonnegR : 0 ≤ (‖a‖ + ‖b‖ : ℝ) := by positivity
    have := mul_le_mul h1 h1 hnonneg hnonnegR
    simpa [pow_two] using this
  exact le_trans hsq h2

private lemma sumSqOn_add_le_two_mul_sumSqOn {S : Finset ℤ} (f g : ℤ → ℂ) :
    sumSqOn S (fun t => f t + g t) ≤ 2 * (sumSqOn S f + sumSqOn S g) := by
  classical
  unfold sumSqOn
  have hpt :
      ∀ t ∈ S, ‖f t + g t‖ ^ 2 ≤ 2 * (‖f t‖ ^ 2 + ‖g t‖ ^ 2) := by
    intro t ht
    simpa using norm_add_sq_le_two_mul_sum_sq (f t) (g t)
  have hsum :
      (∑ t ∈ S, ‖f t + g t‖ ^ 2)
        ≤
      ∑ t ∈ S, 2 * (‖f t‖ ^ 2 + ‖g t‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    exact hpt t ht
  calc
    (∑ t ∈ S, ‖f t + g t‖ ^ 2)
        ≤
      ∑ t ∈ S, 2 * (‖f t‖ ^ 2 + ‖g t‖ ^ 2) := hsum
    _ =
      2 * (∑ t ∈ S, (‖f t‖ ^ 2 + ‖g t‖ ^ 2)) := by
        simp [Finset.mul_sum]
    _ =
      2 * ((∑ t ∈ S, ‖f t‖ ^ 2) + (∑ t ∈ S, ‖g t‖ ^ 2)) := by
        simp [Finset.sum_add_distrib]
    _ = 2 * (sumSqOn S f + sumSqOn S g) := by
        simp [sumSqOn]

/-!
## Route-A bounds for `sumSqOn (AX+LX)`
-/

theorem sumSqOn_evenBand_AX_add_LX_le
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
      ≤
    2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
      +
      (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore) := by
  have hAX : sumSqOn (evenBand X) (AX X (1 : ℝ))
      ≤ ((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 :=
    sumSqOn_evenBand_AX_le (X := X) hX
  have hLX : sumSqOn (evenBand X) (LX X)
      ≤ (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore :=
    sumSqOn_evenBand_LX_le (hGcd := hGcd) (X := X) hX
  have hadd :
      sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (sumSqOn (evenBand X) (AX X (1 : ℝ)) + sumSqOn (evenBand X) (LX X)) :=
    sumSqOn_add_le_two_mul_sumSqOn (S := evenBand X) (f := fun t => AX X (1 : ℝ) t) (g := LX X)
  calc
    sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (sumSqOn (evenBand X) (AX X (1 : ℝ)) + sumSqOn (evenBand X) (LX X)) := hadd
    _ ≤
      2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
          + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore) := by
      nlinarith [hAX, hLX]

theorem sumSqOn_oddBand_AX_add_LX_le
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
      ≤
    2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
      +
      (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore) := by
  have hAX : sumSqOn (oddBand X) (AX X (1 : ℝ))
      ≤ ((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 :=
    sumSqOn_oddBand_AX_le (X := X) hX
  have hLX : sumSqOn (oddBand X) (LX X)
      ≤ (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore :=
    sumSqOn_oddBand_LX_le (hGcd := hGcd) (X := X) hX
  have hadd :
      sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (sumSqOn (oddBand X) (AX X (1 : ℝ)) + sumSqOn (oddBand X) (LX X)) :=
    sumSqOn_add_le_two_mul_sumSqOn (S := oddBand X) (f := fun t => AX X (1 : ℝ) t) (g := LX X)
  calc
    sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (sumSqOn (oddBand X) (AX X (1 : ℝ)) + sumSqOn (oddBand X) (LX X)) := hadd
    _ ≤
      2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
          + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore) := by
      nlinarith [hAX, hLX]

/-!
## Route-A upper bounds for `kernelMassNZEven_upper/NZOdd_upper`
-/

noncomputable def kernelMassNZEven_upper_routeA (X : ℕ) : ℝ :=
  (1 + δ_weightSplit)
      * (2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore))
    +
  (1 + 1 / δ_weightSplit) * (((evenBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

noncomputable def kernelMassNZOdd_upper_routeA (X : ℕ) : ℝ :=
  (1 + δ_weightSplit)
      * (2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore))
    +
  (1 + 1 / δ_weightSplit) * (((oddBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

/-!
## Collapsed Route-A variant (generator-friendly)

`LXMeanSquareUpperCore` is a huge `(q,q')` double sum. The lemma
`LXMeanSquareUpperCore_eq_collapsed` rewrites it into a single `r`-sum with a squared inner sum.

We expose the corresponding “collapsed” variants of the Route-A upper bounds so the generator can
compute `U` from the same expression Lean uses.
-/

noncomputable def kernelMassNZEven_upper_routeA_collapsed (X : ℕ) : ℝ :=
  (1 + δ_weightSplit)
      * (2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCoreCollapsed))
    +
  (1 + 1 / δ_weightSplit) * (((evenBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

noncomputable def kernelMassNZOdd_upper_routeA_collapsed (X : ℕ) : ℝ :=
  (1 + δ_weightSplit)
      * (2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCoreCollapsed))
    +
  (1 + 1 / δ_weightSplit) * (((oddBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

theorem kernelMassNZEven_upper_routeA_eq_collapsed (X : ℕ) :
    kernelMassNZEven_upper_routeA X = kernelMassNZEven_upper_routeA_collapsed X := by
  classical
  dsimp [kernelMassNZEven_upper_routeA, kernelMassNZEven_upper_routeA_collapsed]
  -- `LXMeanSquareUpperCore` is the only difference.
  rw [LXMeanSquareUpperCore_eq_collapsed]

theorem kernelMassNZOdd_upper_routeA_eq_collapsed (X : ℕ) :
    kernelMassNZOdd_upper_routeA X = kernelMassNZOdd_upper_routeA_collapsed X := by
  classical
  dsimp [kernelMassNZOdd_upper_routeA, kernelMassNZOdd_upper_routeA_collapsed]
  rw [LXMeanSquareUpperCore_eq_collapsed]

theorem kernelMassNZEven_upper_le_routeA
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven_upper X ≤ kernelMassNZEven_upper_routeA X := by
  -- Only the `sumSqOn (AX+LX)` term changes; the RX card-envelope is identical.
  dsimp [kernelMassNZEven_upper, kernelMassNZEven_upper_routeA]
  have hMain :
      sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore) :=
    sumSqOn_evenBand_AX_add_LX_le (hGcd := hGcd) (X := X) hX
  have hδ : 0 ≤ (1 + δ_weightSplit) := by
    have : 0 ≤ δ_weightSplit := le_of_lt δ_weightSplit_pos
    nlinarith
  have hScaled :
      (1 + δ_weightSplit) * sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      (1 + δ_weightSplit)
          * (2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
                + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore)) :=
    mul_le_mul_of_nonneg_left hMain hδ
  nlinarith [hScaled]

theorem kernelMassNZOdd_upper_le_routeA
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZOdd_upper X ≤ kernelMassNZOdd_upper_routeA X := by
  dsimp [kernelMassNZOdd_upper, kernelMassNZOdd_upper_routeA]
  have hMain :
      sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore) :=
    sumSqOn_oddBand_AX_add_LX_le (hGcd := hGcd) (X := X) hX
  have hδ : 0 ≤ (1 + δ_weightSplit) := by
    have : 0 ≤ δ_weightSplit := le_of_lt δ_weightSplit_pos
    nlinarith
  have hScaled :
      (1 + δ_weightSplit) * sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      (1 + δ_weightSplit)
          * (2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
                + (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore)) :=
    mul_le_mul_of_nonneg_left hMain hδ
  nlinarith [hScaled]

/-!
## Route-A Toeplitz upper bound
-/

noncomputable def toeplitzExprTopTight_upper_routeA (X : ℕ) : ℝ :=
  ((1 + 1 / δ_split) * kernelMassNZEven_upper_routeA X) * (coeffMass X (X + H)) ^ 2
    +
  (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_routeA X) * (aTerm2Mass X) * (coeffMass X (X + H))
    +
  ((1 + δ_split)
      * ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
            *
          (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
              (Nat.totient q : ℝ) / (q : ℝ))) ^ 2)
      * diagBoundTight X (X + H)

noncomputable def toeplitzExprTopTight_upper_routeA_collapsed (X : ℕ) : ℝ :=
  ((1 + 1 / δ_split) * kernelMassNZEven_upper_routeA_collapsed X) * (coeffMass X (X + H)) ^ 2
    +
  (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_routeA_collapsed X) * (aTerm2Mass X) *
    (coeffMass X (X + H))
    +
  ((1 + δ_split)
      * ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
            *
          (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
              (Nat.totient q : ℝ) / (q : ℝ))) ^ 2)
      * diagBoundTight X (X + H)

theorem toeplitzExprTopTight_upper_routeA_eq_collapsed (X : ℕ) :
    toeplitzExprTopTight_upper_routeA X = toeplitzExprTopTight_upper_routeA_collapsed X := by
  classical
  dsimp [toeplitzExprTopTight_upper_routeA, toeplitzExprTopTight_upper_routeA_collapsed]
  rw [kernelMassNZEven_upper_routeA_eq_collapsed, kernelMassNZOdd_upper_routeA_eq_collapsed]

theorem toeplitzExprTopTight_le_upper_routeA
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    toeplitzExprTopTight X (1 : ℝ) ≤ toeplitzExprTopTight_upper_routeA X := by
  have h1 : toeplitzExprTopTight X (1 : ℝ) ≤ toeplitzExprTopTight_upper X :=
    toeplitzExprTopTight_le_upper (X := X) hX
  -- upgrade `toeplitzExprTopTight_upper` by replacing the kernel-mass upper bounds
  have hEven : kernelMassNZEven_upper X ≤ kernelMassNZEven_upper_routeA X :=
    kernelMassNZEven_upper_le_routeA (hGcd := hGcd) (X := X) hX
  have hOdd : kernelMassNZOdd_upper X ≤ kernelMassNZOdd_upper_routeA X :=
    kernelMassNZOdd_upper_le_routeA (hGcd := hGcd) (X := X) hX
  have h2 : toeplitzExprTopTight_upper X ≤ toeplitzExprTopTight_upper_routeA X := by
    -- termwise monotonicity in the kernel-mass slots
    unfold toeplitzExprTopTight_upper toeplitzExprTopTight_upper_routeA
    have hδ1 : 0 ≤ (1 + 1 / δ_split) := by
      have : 0 ≤ (1 / δ_split) := le_of_lt (one_div_pos.mpr δ_split_pos)
      nlinarith
    have hδ1' : 0 ≤ (2 * (1 + 1 / δ_split)) := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this hδ1
    have hcoeffsq : 0 ≤ (coeffMass X (X + H)) ^ 2 := sq_nonneg _
    have hcoeff : 0 ≤ coeffMass X (X + H) := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have ha2 : 0 ≤ aTerm2Mass X := aTerm2Mass_nonneg X
    refine add_le_add (add_le_add ?_ ?_) (le_rfl)
    · -- even term
      have hleft :
          (1 + 1 / δ_split) * kernelMassNZEven_upper X
            ≤
          (1 + 1 / δ_split) * kernelMassNZEven_upper_routeA X :=
        mul_le_mul_of_nonneg_left hEven hδ1
      exact mul_le_mul_of_nonneg_right hleft hcoeffsq
    · -- odd term
      have hleft :
          2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X
            ≤
          2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_routeA X :=
        mul_le_mul_of_nonneg_left hOdd hδ1'
      have hmid :
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * aTerm2Mass X
            ≤
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_routeA X) * aTerm2Mass X :=
        mul_le_mul_of_nonneg_right hleft ha2
      have :
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * aTerm2Mass X * coeffMass X (X + H)
            ≤
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_routeA X) * aTerm2Mass X * coeffMass X (X + H) :=
        mul_le_mul_of_nonneg_right hmid hcoeff
      simpa [mul_assoc] using this
  exact le_trans h1 (le_trans h2 (le_rfl))

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA
