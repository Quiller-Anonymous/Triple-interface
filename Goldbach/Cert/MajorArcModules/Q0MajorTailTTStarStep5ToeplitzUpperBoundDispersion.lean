import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5AXBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBoundDispersion
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound

/-!
Step 5 (ε₂-large TT*/Toeplitz): dispersion-refined “U-formula” upper bound.

This file is the dispersion analogue of
`Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.lean`.

It keeps the *structure-only* Step-5 Toeplitz upper bound from
`Q0MajorTailTTStarStep5ToeplitzUpperBound.lean`, but replaces the symbolic
band sum `sumSqOn (AX+LX)` by a bound obtained from:

- the deterministic small-`q` bound for `AX` (q≤12), and
- the conventional band-limited dispersion interface `RamanujanBandDispersion Cdisp`
  applied to the linearized large-`q` term `LX` (q≥13).

No attempt is made here to pick a numeric value of `Cdisp`. That is left to:
- a later conventional-math lemma (if we can prove it in Lean), or
- a conventional axiom boundary (project-neutral) pinned elsewhere.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBoundDispersion

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5AXBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBoundDispersion
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold

noncomputable section

/-!
## Basic `sumSqOn` inequality for `AX+LX`

We avoid cross terms by a coarse (but safe) estimate:
`‖a+b‖² ≤ 2(‖a‖²+‖b‖²)`, summed over the band.
-/

private lemma norm_add_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    have hxy : 2 * ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
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
    _ = 2 * (∑ t ∈ S, (‖f t‖ ^ 2 + ‖g t‖ ^ 2)) := by
      simp [Finset.mul_sum]
    _ = 2 * ((∑ t ∈ S, ‖f t‖ ^ 2) + (∑ t ∈ S, ‖g t‖ ^ 2)) := by
      simp [Finset.sum_add_distrib]
    _ = 2 * (sumSqOn S f + sumSqOn S g) := by
      simp [sumSqOn]

/-!
## Dispersion bounds for `sumSqOn (AX+LX)`
-/

theorem sumSqOn_evenBand_AX_add_LX_le_of_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
      ≤
    2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
      +
      (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (evenBand X))) := by
  have hAX :
      sumSqOn (evenBand X) (AX X (1 : ℝ))
        ≤ ((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 :=
    sumSqOn_evenBand_AX_le (X := X) hX
  have hLX :
      sumSqOn (evenBand X) (LX X)
        ≤ (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (evenBand X)) :=
    sumSqOn_evenBand_LX_le_of_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd) (X := X)
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
          +
          (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (evenBand X))) := by
      nlinarith [hAX, hLX]

theorem sumSqOn_oddBand_AX_add_LX_le_of_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
      ≤
    2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
      +
      (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (oddBand X))) := by
  have hAX :
      sumSqOn (oddBand X) (AX X (1 : ℝ))
        ≤ ((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 :=
    sumSqOn_oddBand_AX_le (X := X) hX
  have hLX :
      sumSqOn (oddBand X) (LX X)
        ≤ (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (oddBand X)) :=
    sumSqOn_oddBand_LX_le_of_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd) (X := X)
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
          +
          (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (oddBand X))) := by
      nlinarith [hAX, hLX]

/-!
## Dispersion-refined upper bounds for `kernelMassNZEven_upper/NZOdd_upper`
-/

noncomputable def kernelMassNZEven_upper_dispersion (Cdisp : ℝ) (X : ℕ) : ℝ :=
  (1 + δ_weightSplit)
      * (2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            +
            (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (evenBand X))))
    +
  (1 + 1 / δ_weightSplit) * (((evenBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

noncomputable def kernelMassNZOdd_upper_dispersion (Cdisp : ℝ) (X : ℕ) : ℝ :=
  (1 + δ_weightSplit)
      * (2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            +
            (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (oddBand X))))
    +
  (1 + 1 / δ_weightSplit) * (((oddBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2)

theorem kernelMassNZEven_upper_le_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven_upper X ≤ kernelMassNZEven_upper_dispersion Cdisp X := by
  dsimp [kernelMassNZEven_upper, kernelMassNZEven_upper_dispersion]
  have hMain :
      sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            +
            (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (evenBand X))) :=
    sumSqOn_evenBand_AX_add_LX_le_of_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd) (X := X) hX
  -- The RX envelope term matches identically.
  nlinarith

theorem kernelMassNZOdd_upper_le_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZOdd_upper X ≤ kernelMassNZOdd_upper_dispersion Cdisp X := by
  dsimp [kernelMassNZOdd_upper, kernelMassNZOdd_upper_dispersion]
  have hMain :
      sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t)
        ≤
      2 * (((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2
            +
            (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (oddBand X))) :=
    sumSqOn_oddBand_AX_add_LX_le_of_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd) (X := X) hX
  nlinarith

/-!
## Dispersion-refined Toeplitz top expression (generator-facing)

This is the dispersion analogue of
`Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound.toeplitzExprTopTight_upper`.

It is **still** a certificate-facing bound: it reduces the Lean obligations to a finite
band-sum expression `LXBandDispCore` together with a conventional dispersion constant `Cdisp`.
-/

noncomputable def toeplitzExprTopTight_upper_dispersion (Cdisp : ℝ) (X : ℕ) : ℝ :=
  ((1 + 1 / δ_split) * kernelMassNZEven_upper_dispersion Cdisp X) * (coeffMass X (X + H)) ^ 2
    +
  (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_dispersion Cdisp X) *
        (aTerm2Mass X) * (coeffMass X (X + H))
    +
  ((1 + δ_split)
      * ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
            *
          (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
              (Nat.totient q : ℝ) / (q : ℝ))) ^ 2)
      * diagBoundTight X (X + H)

theorem toeplitzExprTopTight_le_upper_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    Q0MajorTailTTStarStep5ABC.toeplitzExprTopTight X (1 : ℝ) ≤
      toeplitzExprTopTight_upper_dispersion Cdisp X := by
  -- First compare to the structure-only upper bound.
  have h0 :
      Q0MajorTailTTStarStep5ABC.toeplitzExprTopTight X (1 : ℝ) ≤ toeplitzExprTopTight_upper X :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound.toeplitzExprTopTight_le_upper
      (X := X) hX
  -- Then upgrade the nonzero kernel-mass uppers using dispersion.
  have hEven :
      kernelMassNZEven_upper X ≤ kernelMassNZEven_upper_dispersion Cdisp X :=
    kernelMassNZEven_upper_le_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd) (X := X) hX
  have hOdd :
      kernelMassNZOdd_upper X ≤ kernelMassNZOdd_upper_dispersion Cdisp X :=
    kernelMassNZOdd_upper_le_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd) (X := X) hX
  -- Compare `toeplitzExprTopTight_upper` term-by-term.
  have hδ1 : 0 ≤ (1 + 1 / δ_split : ℝ) := by
    have : 0 ≤ (1 / δ_split : ℝ) := le_of_lt (one_div_pos.mpr δ_split_pos)
    nlinarith
  have hcoeffsq : 0 ≤ (coeffMass X (X + H)) ^ 2 := sq_nonneg _
  have hcoeff : 0 ≤ coeffMass X (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha2 : 0 ≤ aTerm2Mass X := aTerm2Mass_nonneg X
  have h0' : 0 ≤ (2 : ℝ) := by norm_num
  have hδ1' : 0 ≤ (2 * (1 + 1 / δ_split) : ℝ) := mul_nonneg h0' hδ1
  have hdiag : 0 ≤ diagBoundTight X (X + H) := by
    unfold diagBoundTight
    have : 0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := sq_nonneg _
    exact mul_nonneg this hcoeff
  have hUpper :
      toeplitzExprTopTight_upper X ≤ toeplitzExprTopTight_upper_dispersion Cdisp X := by
    classical
    unfold Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound.toeplitzExprTopTight_upper
      toeplitzExprTopTight_upper_dispersion
    refine add_le_add (add_le_add ?_ ?_) le_rfl
    · have hEven' :
          (1 + 1 / δ_split) * kernelMassNZEven_upper X
            ≤ (1 + 1 / δ_split) * kernelMassNZEven_upper_dispersion Cdisp X :=
        mul_le_mul_of_nonneg_left hEven hδ1
      exact mul_le_mul_of_nonneg_right hEven' hcoeffsq
    · have hOdd' :
          2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X
            ≤ 2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_dispersion Cdisp X :=
        mul_le_mul_of_nonneg_left hOdd hδ1'
      have hOdd'' :
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * aTerm2Mass X
            ≤ (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_dispersion Cdisp X) * aTerm2Mass X :=
        mul_le_mul_of_nonneg_right hOdd' ha2
      have :
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper X) * aTerm2Mass X * coeffMass X (X + H)
            ≤
          (2 * (1 + 1 / δ_split) * kernelMassNZOdd_upper_dispersion Cdisp X) * aTerm2Mass X *
              coeffMass X (X + H) :=
        mul_le_mul_of_nonneg_right hOdd'' hcoeff
      simpa [mul_assoc] using this
  exact le_trans h0 (le_trans hUpper le_rfl)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBoundDispersion
