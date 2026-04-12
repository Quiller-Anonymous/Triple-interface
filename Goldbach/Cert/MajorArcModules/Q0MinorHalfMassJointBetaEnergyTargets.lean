import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeJointEnergyTargets
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers
import Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy

/-!
# Global β-energy fallback for the corrected freeze discrepancy

This file is the bounded fallback after the q=1-only and separated q≥2 routes failed.

The point of the new surface is to keep the full corrected q=1 / weighted q≥2 discrepancy
together and to move the quadratic energy to the β variable:

`∫ β, ∑ ordered pairs ‖Δ X N M β‖^2`.

No separate q=1 or q≥2 estimates are introduced here.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassJointBetaEnergyTargets

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open MeasureTheory

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeJointEnergyTargets
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers
open Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
Resonance scale for the double-q TT* split.

The next analytic proof should choose this scale explicitly; it is deliberately a parameter here
because the correct threshold depends on the eventual β-orthogonality estimate.
-/
abbrev canonicalJointFreezeDiscrepancyResonanceScale := ℝ

/-- Local alias for the exact joint q=1 / weighted q≥2 β-preabsolute discrepancy. -/
abbrev canonicalJointFreezeDiscrepancyBetaPreAbsoluteIntegrand
    (X N M : ℕ) (β : ℝ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β

/--
The ordered-pair β-integrand in the new global-energy variable.

This keeps all ordered pairs under the β-integral instead of estimating each β-integral first.
-/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ‖canonicalJointFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β‖ ^ 2
      else 0

/-- Global ordered-pair β-energy of the exact joint freeze discrepancy. -/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy
    (X : ℕ) : ℝ :=
  ∫ β in aβ..bβ,
    canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand X β

/--
One weighted `q ≥ 2` β-endpoint summand, before the outer q-sum is taken.

This is the exact summand occurring in
`canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint`, with the outer weight
distributed onto the summand so that the endpoint is a plain finite q-sum.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2BetaRawEndpointSummand
    (X q N : ℕ) (β : ℝ) : ℂ :=
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  let qXinv : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
  let rescaled : ℂ :=
    ∫ u : ℝ,
      (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaRescaledArchShell X N q u β) u
  let frozen : ℂ :=
    ∫ u : ℝ,
      (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaFrozenRescaledArchShell N u β) u
  w * (((w⁻¹ * qXinv * rescaled) - (w⁻¹ * qXinv * frozen)) * qPhaseFactor q N)

theorem canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint_eq_sum_summands
    (X N : ℕ) (β : ℝ) :
    canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint X N β
      =
    ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
      canonicalJointFreezeDiscrepancyWeightedGe2BetaRawEndpointSummand X q N β := by
  unfold canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint
    canonicalJointFreezeDiscrepancyWeightedGe2BetaRawEndpointSummand
  rw [Finset.mul_sum]

/--
The unified q-atom for the exact joint endpoint.

`q = 1` is the corrected q=1 endpoint.  All other q-values use the weighted freeze-defect
summand; in this file the atom is only summed over `Icc 1 Q0`, so the non-`q = 1` branch is used
exactly on the `q ≥ 2` tail.
-/
noncomputable def canonicalJointFreezeDiscrepancyBetaQAtom
    (X q N : ℕ) (β : ℝ) : ℂ :=
  if q = 1 then
    canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X N β
  else
    canonicalJointFreezeDiscrepancyWeightedGe2BetaRawEndpointSummand X q N β

theorem canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint_eq_sum_qAtom
    (X N : ℕ) (β : ℝ) :
    canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X N β
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      canonicalJointFreezeDiscrepancyBetaQAtom X q N β := by
  rw [canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint,
    canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint_eq_sum_summands]
  have hsplit :
      Finset.Icc (1 : ℕ) Q0 = insert 1 (Finset.Icc (2 : ℕ) Q0) := by
    ext q
    simp [Nat.succ_le_iff]
    omega
  have hnotmem : 1 ∉ Finset.Icc (2 : ℕ) Q0 := by simp
  rw [hsplit, Finset.sum_insert hnotmem]
  have h1 :
      canonicalJointFreezeDiscrepancyBetaQAtom X 1 N β
        =
      canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X N β := by
    simp [canonicalJointFreezeDiscrepancyBetaQAtom]
  have hrest :
      (∑ q ∈ Finset.Icc (2 : ℕ) Q0,
          canonicalJointFreezeDiscrepancyBetaQAtom X q N β)
        =
      ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
        canonicalJointFreezeDiscrepancyWeightedGe2BetaRawEndpointSummand X q N β := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq_ne : q ≠ 1 := by
      have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
      omega
    simp [canonicalJointFreezeDiscrepancyBetaQAtom, hq_ne]
  rw [h1, hrest]

/-- The exact pair endpoint written as a unified finite q-sum. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint
    (X N M : ℕ) (β : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
    (canonicalJointFreezeDiscrepancyBetaQAtom X q N β
      - canonicalJointFreezeDiscrepancyBetaQAtom X q M β)

theorem canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand_eq_qsum
    (X N M : ℕ) (β : ℝ) :
    canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β
      =
    betaSmallSet.indicator
      (fun β : ℝ => canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint X N M β) β := by
  unfold canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand
    canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint
  have hN := canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint_eq_sum_qAtom X N β
  have hM := canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint_eq_sum_qAtom X M β
  by_cases hβ : β ∈ betaSmallSet
  · simp [Set.indicator_of_mem hβ, hN, hM, Finset.sum_sub_distrib]
  · simp [Set.indicator_of_notMem hβ]

/--
Concrete q-summed expansion of the global β-integrand.

The q-sum remains inside the norm square.  The next analytic step should expand this square and
group by q/frequency before applying any estimates.
-/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ‖betaSmallSet.indicator
          (fun β : ℝ => canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint X N M β) β‖ ^ 2
      else 0

theorem norm_sq_sum_complex_eq_double_sum_re
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2
      =
    ∑ a ∈ s, ∑ b ∈ s, ((f a * star (f b)).re) := by
  calc
    ‖∑ a ∈ s, f a‖ ^ 2
        = (((∑ a ∈ s, f a) * star (∑ a ∈ s, f a)).re) := by
            have hmulconj :
                (((∑ a ∈ s, f a) * star (∑ a ∈ s, f a)).re)
                  =
                Complex.normSq (∑ a ∈ s, f a) := by
              exact congrArg Complex.re (Complex.mul_conj (∑ a ∈ s, f a))
            rw [hmulconj, Complex.normSq_eq_norm_sq]
    _ = ∑ a ∈ s, ((f a * star (∑ b ∈ s, f b)).re) := by
            rw [sum_mul_star_re]
    _ = ∑ a ∈ s, ∑ b ∈ s, ((f a * star (f b)).re) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [sum_star_mul_re]

/-- One q-atom in the ordered-pair endpoint. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQPairAtom
    (X N M q : ℕ) (β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyBetaQAtom X q N β
    - canonicalJointFreezeDiscrepancyBetaQAtom X q M β

/-- The `q`-dependent local phase shift `θ = u/(qX)` in a weighted shell. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQTheta
    (X q : ℕ) (u : ℝ) : ℝ :=
  u / ((q : ℝ) * (X : ℝ))

/-- The `β + u/(qX)` finite geometric factor in a weighted shell. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQPlusSum
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp
      (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) n

/-- The `u/(qX) - β` finite geometric factor in a weighted shell. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQMinusSum
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp
      (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) n

theorem canonicalJointFreezeDiscrepancyBetaQPlusSum_eq_finiteGExpIco
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaQPlusSum X q N u β
      =
    finiteGExpIco N (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) := by
  rfl

theorem canonicalJointFreezeDiscrepancyBetaQMinusSum_eq_finiteGExpIco
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaQMinusSum X q N u β
      =
    finiteGExpIco N (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) := by
  rfl

/--
Closed-form Dirichlet-kernel inspection of the unexpanded plus/minus finite-sum product.

This keeps the q-dependent centers `u/(qX) ± β` in the denominators instead of expanding the
finite sums termwise.
-/
theorem canonicalJointFreezeDiscrepancyBetaQPlusMinusProduct_eq_dirichletProduct
    (X q N : ℕ) (u β : ℝ)
    (hplus :
      Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) 1 ≠ 1)
    (hminus :
      Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) 1 ≠ 1)
    (hIco : 4 ≤ (N - 2) + 1) :
    canonicalJointFreezeDiscrepancyBetaQPlusSum X q N u β
      * canonicalJointFreezeDiscrepancyBetaQMinusSum X q N u β
      =
    ((((Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) 1) ^ 4
        - (Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) 1) ^ ((N - 2) + 1))
        / (1 - Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) 1))
      *
      (((Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) 1) ^ 4
        - (Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) 1) ^ ((N - 2) + 1))
        / (1 - Goldbach.Cert.MajorArcStep2ExpSums.gExp
          (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) 1))) := by
  rw [canonicalJointFreezeDiscrepancyBetaQPlusSum_eq_finiteGExpIco,
    canonicalJointFreezeDiscrepancyBetaQMinusSum_eq_finiteGExpIco]
  rw [finiteGExpIco_eq_geom_div_of_phase_ne_one N
      (canonicalJointFreezeDiscrepancyBetaQTheta X q u + β) hplus hIco]
  rw [finiteGExpIco_eq_geom_div_of_phase_ne_one N
      (canonicalJointFreezeDiscrepancyBetaQTheta X q u - β) hminus hIco]

/--
Unexpanded shifted-kernel factor for the moving part of a `q`-atom.

This is the TT* object to keep intact: kernel, Fourier phase, and the two shifted finite
Dirichlet-kernel factors are all still present before termwise expansion or absolute values.
-/
noncomputable def canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (fourier (T := (1 : ℝ)) (-(N : ℤ))
        ((canonicalJointFreezeDiscrepancyBetaQTheta X q u : ℝ) : UC) : ℂ)
    * (canonicalJointFreezeDiscrepancyBetaQPlusSum X q N u β
        * canonicalJointFreezeDiscrepancyBetaQMinusSum X q N u β)

/-- Ordered-pair difference of the moving shifted-kernel factor at fixed `(q,u,β)`. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQMovingKernelPairFactor
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β
    - canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q M u β

/--
The exact `q ≥ 2` u-level weighted freeze-defect summand before the `u`-integral is taken.

This is the object that can carry the resonance predicate `|u/q - u'/q'|`: the fully integrated
q-atom kernel below has already forgotten `u,u'`.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtom
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  let qXinv : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
  w * ((w⁻¹ * qXinv
    * ((centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaRescaledShellGap X N q u β) u)) * qPhaseFactor q N)

/--
Factored u-level weighted `q ≥ 2` atom.

The moving part is kept as the shifted-kernel factor, whose plus/minus finite sums have the
Dirichlet closed form above; the frozen subtraction remains explicit.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  let qXinv : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
  w * ((w⁻¹ * qXinv
    * ((centeredUnitSet (1 : ℝ)).indicator
        (fun u =>
          canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β
            - smallBetaFrozenRescaledArchShell N u β) u)) * qPhaseFactor q N)

/-- Moving part of the factored u-level weighted `q ≥ 2` atom. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  let qXinv : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
  w * ((w⁻¹ * qXinv
    * ((centeredUnitSet (1 : ℝ)).indicator
        (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β) u))
      * qPhaseFactor q N)

/-- Frozen part of the factored u-level weighted `q ≥ 2` atom. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomFrozen
    (X q N : ℕ) (u β : ℝ) : ℂ :=
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  let qXinv : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
  w * ((w⁻¹ * qXinv
    * ((centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaFrozenRescaledArchShell N u β) u)) * qPhaseFactor q N)

theorem canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored_eq_moving_sub_frozen
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored X q N u β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving X q N u β
      - canonicalJointFreezeDiscrepancyWeightedGe2UAtomFrozen X q N u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomFrozen
  by_cases hu : u ∈ centeredUnitSet (1 : ℝ)
  · simp [Set.indicator_of_mem hu]
    ring
  · simp [Set.indicator_of_notMem hu]

/-- Ordered-pair difference of the exact `q ≥ 2` u-level weighted freeze-defect summand. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtom X q N u β
    - canonicalJointFreezeDiscrepancyWeightedGe2UAtom X q M u β

/-- Ordered-pair difference of the factored u-level weighted atom. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored X q N u β
    - canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored X q M u β

/-- Moving ordered-pair part of the factored weighted u-atom. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving X q N u β
    - canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving X q M u β

/-- Frozen ordered-pair part of the factored weighted u-atom. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomFrozen X q N u β
    - canonicalJointFreezeDiscrepancyWeightedGe2UAtomFrozen X q M u β

theorem canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored_eq_moving_sub_frozen
    (X q N M : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored X q N M u β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β
      - canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen X q N M u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen
  rw [canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored_eq_moving_sub_frozen X q N u β,
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored_eq_moving_sub_frozen X q M u β]
  ring

/-- Weight/amplitude multiplying the moving u-level shell for a fixed `q`. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude
    (X q N : ℕ) : ℂ :=
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  let qXinv : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
  w * ((w⁻¹ * qXinv) * qPhaseFactor q N)

theorem canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving_eq_amplitude_mul_indicator
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving X q N u β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
      * ((centeredUnitSet (1 : ℝ)).indicator
          (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β) u) := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving
    canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude
  ring

theorem canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving_eq_amplitude_pair
    (X q N M : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β
      =
    (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
      * ((centeredUnitSet (1 : ℝ)).indicator
          (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β) u))
      -
    (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q M
      * ((centeredUnitSet (1 : ℝ)).indicator
          (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q M u β) u)) := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving
  rw [canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving_eq_amplitude_mul_indicator,
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving_eq_amplitude_mul_indicator]

/-- Exact `q ≥ 2` u/u′-level off-diagonal kernel integrand before β-integration. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrand
    (X N M q q' : ℕ) (u u' β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor X q N M u β
    * star (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor X q' N M u' β)

/-- Factored form of the exact `q ≥ 2` u/u′-level off-diagonal kernel integrand. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandFactored
    (X N M q q' : ℕ) (u u' β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored X q N M u β
    * star (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored X q' N M u' β)

/-- Moving-moving part of the factored u/u′ off-diagonal kernel integrand. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving
    (X N M q q' : ℕ) (u u' β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β
    * star (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q' N M u' β)

/-- The three cross/frozen remainder terms in the factored u/u′ off-diagonal kernel integrand. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandCrossFrozen
    (X N M q q' : ℕ) (u u' β : ℝ) : ℂ :=
  - canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β
      * star (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen X q' N M u' β)
  - canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen X q N M u β
      * star (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q' N M u' β)
  + canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen X q N M u β
      * star (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFrozen X q' N M u' β)

theorem canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandFactored_eq_movingMoving_add_crossFrozen
    (X N M q q' : ℕ) (u u' β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandFactored
        X N M q q' u u' β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving
        X N M q q' u u' β
      + canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandCrossFrozen
        X N M q q' u u' β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandFactored
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandCrossFrozen
  rw [canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored_eq_moving_sub_frozen
      X q N M u β,
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored_eq_moving_sub_frozen
      X q' N M u' β]
  simp only [star_sub]
  ring_nf

theorem canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving_eq_amplitude_pair_product
    (X N M q q' : ℕ) (u u' β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving
        X N M q q' u u' β
      =
    ((canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
        * ((centeredUnitSet (1 : ℝ)).indicator
            (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β) u))
        -
      (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q M
        * ((centeredUnitSet (1 : ℝ)).indicator
            (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q M u β) u)))
      *
    star
      (((canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q' N
          * ((centeredUnitSet (1 : ℝ)).indicator
              (fun u' => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
                X q' N u' β) u'))
          -
        (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q' M
          * ((centeredUnitSet (1 : ℝ)).indicator
              (fun u' => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
                X q' M u' β) u')))) := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving
  rw [canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving_eq_amplitude_pair,
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving_eq_amplitude_pair]

/-- β-integrated exact `q ≥ 2` u/u′-level off-diagonal kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernel
    (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrand
          X N M q q' u u' β) β

/-- Real part of the exact `q ≥ 2` u/u′-level off-diagonal kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelRe
    (X N M q q' : ℕ) (u u' : ℝ) : ℝ :=
  (canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernel X N M q q' u u').re

/-- β-integrated moving-moving u/u′-level kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernel
    (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving
          X N M q q' u u' β) β

/-- Real part of the β-integrated moving-moving u/u′-level kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernelRe
    (X N M q q' : ℕ) (u u' : ℝ) : ℝ :=
  (canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernel X N M q q' u u').re

/--
Integrated moving-moving kernel written at the last exact factorized surface.

This is the point where any nonresonant proof has to enter: the remaining integrand is a
β-integral of shifted plus/minus Dirichlet-kernel products, multiplied by the explicit
`q,q'` amplitudes and centered-unit indicators.
-/
theorem canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernel_eq_amplitude_pair_integral
    (X N M q q' : ℕ) (u u' : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernel
        X N M q q' u u'
      =
    ∫ β in aβ..bβ,
      (betaSmallSet.indicator
        (fun β : ℝ =>
          ((canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
              * ((centeredUnitSet (1 : ℝ)).indicator
                  (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
                    X q N u β) u))
              -
            (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q M
              * ((centeredUnitSet (1 : ℝ)).indicator
                  (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
                    X q M u β) u)))
            *
          star
            (((canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q' N
                * ((centeredUnitSet (1 : ℝ)).indicator
                    (fun u' => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
                      X q' N u' β) u'))
                -
              (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q' M
                * ((centeredUnitSet (1 : ℝ)).indicator
                    (fun u' => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
                      X q' M u' β) u'))))) β) := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernel
  refine intervalIntegral.integral_congr ?_
  intro β hβ
  by_cases hβsmall : β ∈ betaSmallSet
  · simp [Set.indicator_of_mem hβsmall,
      canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandMovingMoving_eq_amplitude_pair_product]
  · simp [Set.indicator_of_notMem hβsmall]

/-- β-integrated cross/frozen u/u′-level remainder kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUCrossFrozenKernel
    (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandCrossFrozen
          X N M q q' u u' β) β

/-- Real part of the β-integrated cross/frozen u/u′-level remainder kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUCrossFrozenKernelRe
    (X N M q q' : ℕ) (u u' : ℝ) : ℝ :=
  (canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUCrossFrozenKernel X N M q q' u u').re

/--
Complex off-diagonal TT* kernel integrand at fixed `(q,q',u,u')`.

The real off-diagonal contribution is obtained by taking the real part after the β-integral.
-/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalKernelIntegrand
    (X N M q q' : ℕ) (u u' β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyBetaQMovingKernelPairFactor X q N M u β
    * star (canonicalJointFreezeDiscrepancyBetaQMovingKernelPairFactor X q' N M u' β)

/-- β-integrated complex TT* kernel for a fixed off-diagonal `(q,q',u,u')`. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalKernel
    (X N M q q' : ℕ) (u u' : ℝ) : ℂ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalJointFreezeDiscrepancyOffDiagonalKernelIntegrand X N M q q' u u' β) β

/-- Real part of the β-integrated TT* kernel, matching the expanded energy atom. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalKernelRe
    (X N M q q' : ℕ) (u u' : ℝ) : ℝ :=
  (canonicalJointFreezeDiscrepancyOffDiagonalKernel X N M q q' u u').re

/-- Exact q-atom TT* kernel integrand for the already β-level endpoint atoms. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelIntegrand
    (X N M q q' : ℕ) (β : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyBetaQPairAtom X N M q β
    * star (canonicalJointFreezeDiscrepancyBetaQPairAtom X N M q' β)

/-- Exact β-integrated q-atom TT* kernel for the off-diagonal energy atom. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernel
    (X N M q q' : ℕ) : ℂ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelIntegrand X N M q q' β) β

/-- Real form of the exact β-integrated q-atom TT* kernel. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelRe
    (X N M q q' : ℕ) : ℝ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        (canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelIntegrand X N M q q' β).re) β

theorem canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor_eq_rescaledArchShell
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β
      =
    smallBetaRescaledArchShell X N q u β := by
  unfold canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor
    smallBetaRescaledArchShell smallBetaCenteredArchShell
    canonicalJointFreezeDiscrepancyBetaQTheta
    canonicalJointFreezeDiscrepancyBetaQPlusSum
    canonicalJointFreezeDiscrepancyBetaQMinusSum
  rfl

theorem canonicalJointFreezeDiscrepancyWeightedGe2UAtom_eq_factored
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtom X q N u β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored X q N u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2UAtom
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomFactored
  by_cases hu : u ∈ centeredUnitSet (1 : ℝ)
  · simp [Set.indicator_of_mem hu, smallBetaRescaledShellGap,
      canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor_eq_rescaledArchShell]
  · simp [Set.indicator_of_notMem hu]

theorem canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor_eq_factored
    (X q N M : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor X q N M u β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored X q N M u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorFactored
  rw [canonicalJointFreezeDiscrepancyWeightedGe2UAtom_eq_factored X q N u β,
    canonicalJointFreezeDiscrepancyWeightedGe2UAtom_eq_factored X q M u β]

theorem canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrand_eq_factored
    (X N M q q' : ℕ) (u u' β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrand X N M q q' u u' β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandFactored
      X N M q q' u u' β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrand
    canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelIntegrandFactored
  rw [canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor_eq_factored X q N M u β,
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactor_eq_factored X q' N M u' β]

/--
The kernel-level nonresonant target.

The intended proof should exploit shifted Dirichlet-kernel separation in
`|u/q - u'/q'|`, not termwise β-oscillation.
-/
structure CanonicalJointFreezeDiscrepancyOffDiagonalNonresonantKernelBound
    (bound :
      canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ)
    : Prop where
  nonneg :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      0 ≤ bound ρ X N M q q' u u'
  le_bound :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      ρ < |u / (q : ℝ) - u' / (q' : ℝ)| →
        |canonicalJointFreezeDiscrepancyOffDiagonalKernelRe X N M q q' u u'|
          ≤ bound ρ X N M q q' u u'

/--
Nonresonant kernel target for the exact `q ≥ 2` u/u′-level freeze-defect kernel.

This is the valid first nonresonant theorem target: unlike the fully integrated q-atom kernel, it
still has the variables in the resonance predicate.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalNonresonantUKernelBound
    (bound :
      canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ)
    : Prop where
  nonneg :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      0 ≤ bound ρ X N M q q' u u'
  le_bound :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      ρ < |u / (q : ℝ) - u' / (q' : ℝ)| →
        |canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernelRe X N M q q' u u'|
          ≤ bound ρ X N M q q' u u'

/-- Nonresonant decay target for the moving-moving `q ≥ 2` u/u′-kernel. -/
structure CanonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalMovingMovingNonresonantUKernelBound
    (bound :
      canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ)
    : Prop where
  nonneg :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      0 ≤ bound ρ X N M q q' u u'
  le_bound :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      ρ < |u / (q : ℝ) - u' / (q' : ℝ)| →
        |canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUMovingMovingKernelRe
          X N M q q' u u'|
          ≤ bound ρ X N M q q' u u'

/-- Crude target for the cross/frozen u/u′-kernel remainder. -/
structure CanonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalCrossFrozenUKernelBound
    (bound :
      canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ)
    : Prop where
  nonneg :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      0 ≤ bound ρ X N M q q' u u'
  le_bound :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      |canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUCrossFrozenKernelRe
        X N M q q' u u'|
        ≤ bound ρ X N M q q' u u'

/--
The kernel-level resonant target.

This should be proved by a measure/counting estimate for the region
`|u/q - u'/q'| ≤ ρ`, not by β-oscillation.
-/
structure CanonicalJointFreezeDiscrepancyOffDiagonalResonantKernelBound
    (bound :
      canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ)
    : Prop where
  nonneg :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      0 ≤ bound ρ X N M q q' u u'
  le_bound :
    ∀ (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X N M q q' : ℕ) (u u' : ℝ),
      |u / (q : ℝ) - u' / (q' : ℝ)| ≤ ρ →
        |canonicalJointFreezeDiscrepancyOffDiagonalKernelRe X N M q q' u u'|
          ≤ bound ρ X N M q q' u u'

private lemma joint_star_e (x : ℝ) :
    star (Goldbach.Cert.MajorArcExponential.e x)
      = Goldbach.Cert.MajorArcExponential.e (-x) := by
  unfold Goldbach.Cert.MajorArcExponential.e
  let z : ℂ := (Complex.I : ℂ) * (2 * Real.pi * x : ℂ)
  have hconjexp : star (Complex.exp z) = Complex.exp (star z) := by
    simp [Complex.exp_conj]
  have harg : star z = (Complex.I : ℂ) * (2 * Real.pi * (-x) : ℂ) := by
    simp [z, mul_left_comm, mul_comm]
  rw [hconjexp, harg]
  simp

private lemma joint_star_gExp (θ : ℝ) (n : ℕ) :
    star (Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n)
      =
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ) n := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp
  simpa [neg_mul] using joint_star_e (θ * (n : ℝ))

/--
Termwise q/q′ phase factorization for the moving shell factors.

After expanding the finite sums, the β-dependence is the integer-frequency factor
`gExp β n * gExp (-β) m * gExp (-β) n' * gExp β m'`; the q-dependent shifts
`θ, θ'` remain in the coefficient.  This is the exact inspection lemma for the proposed
nonresonant split.
-/
theorem canonicalJointFreezeDiscrepancyBetaQMovingTerm_mul_star_factorized
    (θ θ' β : ℝ) (n m n' m' : ℕ) :
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
      * star
        (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m'))
      =
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') m'))
      *
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp β m')) := by
  rw [Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add θ β n]
  have hθm :
      Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m
        =
      Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) m := by
    simpa [sub_eq_add_neg] using
      Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add θ (-β) m
  rw [hθm]
  rw [star_mul]
  have hstarPlus :
      star (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n')
        =
      Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n' := by
    rw [joint_star_gExp]
    have h :
        Goldbach.Cert.MajorArcStep2ExpSums.gExp (-(θ' + β)) n'
          =
        Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ' + -β) n' := by
      ring_nf
    rw [h]
    exact Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add (-θ') (-β) n'
  have hstarMinus :
      star (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')
        =
      Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') m'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp β m' := by
    rw [joint_star_gExp]
    have h :
        Goldbach.Cert.MajorArcStep2ExpSums.gExp (-(θ' - β)) m'
          =
        Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ' + β) m' := by
      ring_nf
    rw [h]
    exact Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add (-θ') β m'
  rw [hstarPlus, hstarMinus]
  ring

/--
Fourier coefficient of the β-localized outer kernel weight appearing after the moving-moving
termwise β-collapse.

Because the actual branch is localized by `betaSmallSet` and contains `kernelPolyC * star
kernelPolyC`, the β-integral collapses to this coefficient, not to a bare Kronecker delta.
-/
noncomputable def canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff
    (t : ℤ) : ℂ :=
  ∫ β in aβ..bβ,
    betaSmallSet.indicator
      (fun β : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
          * star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)))
          * (fourier (T := (1 : ℝ)) t (β : UC) : ℂ)) β

private theorem norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six_joint
    {g : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ β, β ∈ betaSmallSet → ‖g β‖ ≤ C) :
    ‖∫ β in aβ..bβ, betaSmallSet.indicator g β‖ ≤ C / 6 := by
  let s : Set ℝ := betaSmallSet
  let a : ℝ := aβ
  let b : ℝ := bβ
  have hab : a ≤ b := hle
  have hs : MeasurableSet s := measurableSet_betaSmallSet
  have hI :
      (∫ β in a..b, s.indicator g β ∂volume) =
      ∫ β in Set.Ioc a b, s.indicator g β ∂volume := by
    simpa [a, b] using
      (intervalIntegral.integral_of_le (μ := volume) (f := fun β => s.indicator g β)
        (a := a) (b := b) hab)
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc a b)
  haveI : IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    simpa [μ0] using (measure_Ioc_lt_top (μ := volume) (a := a) (b := b))
  have hAeImp : ∀ᵐ β ∂μ0, β ∈ s → ‖g β‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro β hβ
    exact hg β hβ
  have hAe :
      ∀ᵐ β ∂(μ0.restrict s), ‖g β‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := μ0) (s := s) hs).2 hAeImp
  have hbound :
      ‖∫ β, g β ∂(μ0.restrict s)‖ ≤ C * (μ0.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ0.restrict s) (f := g) (C := C) hAe
  have hind :
      (∫ β in Set.Ioc a b, s.indicator g β ∂volume) = ∫ β, g β ∂(μ0.restrict s) := by
    simpa [μ0, s] using (MeasureTheory.integral_indicator (μ := μ0) (f := g) hs)
  have hμ :
      ((μ0.restrict s).real Set.univ) ≤ (volume s).toReal := by
    have h1 : (μ0.restrict s).real Set.univ = μ0.real s := by
      simpa using (measureReal_restrict_apply_univ (μ := μ0) (s := s))
    have h2 : μ0.real s = volume.real (s ∩ Set.Ioc a b) := by
      simp [μ0, measureReal_restrict_apply hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have h3 : volume.real (s ∩ Set.Ioc a b) ≤ volume.real s := by
      refine measureReal_mono (Set.inter_subset_left) ?_
      have hfinite : volume s < ⊤ := by
        have hvol : volume s = ENNReal.ofReal (2 * betaSmallRadius) := by
          simp [s, betaSmallSet, Real.volume_Icc, betaSmallRadius, sub_eq_add_neg, two_mul,
            add_assoc, add_left_comm, add_comm, mul_assoc]
        rw [hvol]
        exact ENNReal.ofReal_lt_top
      exact hfinite.ne
    simpa [h1, h2] using h3
  have hvol :
      (volume s).toReal ≤ (1 : ℝ) / 6 := by
    have hvol_eq :
        volume s = ENNReal.ofReal (2 * betaSmallRadius) := by
      simp [s, betaSmallSet, Real.volume_Icc, betaSmallRadius, sub_eq_add_neg, two_mul,
        add_assoc, add_left_comm, add_comm, mul_assoc]
    have htoReal :
        (volume s).toReal = (1 : ℝ) / (2 * Real.pi) := by
      have hnonneg : 0 ≤ (2 * betaSmallRadius : ℝ) := by
        nlinarith [le_of_lt betaSmallRadius_pos]
      calc
        (volume s).toReal = (ENNReal.ofReal (2 * betaSmallRadius)).toReal := by
            simp [hvol_eq]
        _ = 2 * betaSmallRadius := by
            simpa using ENNReal.toReal_ofReal hnonneg
        _ = (1 : ℝ) / (2 * Real.pi) := by
            have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
            unfold betaSmallRadius
            field_simp [hpi0]
            ring
    have h2pi : (6 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hden_le :
        (1 : ℝ) / (2 * Real.pi) ≤ (1 : ℝ) / 6 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) h2pi
    simpa [htoReal] using hden_le
  calc
    ‖∫ β in aβ..bβ, betaSmallSet.indicator g β‖
        = ‖∫ β in a..b, s.indicator g β ∂volume‖ := by rfl
    _ = ‖∫ β in Set.Ioc a b, s.indicator g β ∂volume‖ := by rw [hI]
    _ = ‖∫ β, g β ∂(μ0.restrict s)‖ := by rw [hind]
    _ ≤ C * (μ0.restrict s).real Set.univ := hbound
    _ ≤ C * (volume s).toReal := by gcongr
    _ ≤ C * ((1 : ℝ) / 6) := by gcongr
    _ = C / 6 := by ring

theorem norm_canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff_le_kernelCap_sq_div_six
    (t : ℤ) :
    ‖canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff t‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap ^ 2 / 6 := by
  unfold canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff
  refine norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six_joint
    (C := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap ^ 2) ?_ ?_
  · exact sq_nonneg _
  · intro β hβ
    have hk :
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
          ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap
        (x := (β : UC))
    have hcap_nonneg : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    have hfourier :
        ‖(fourier (T := (1 : ℝ)) t (β : UC) : ℂ)‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    calc
      ‖(Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
          * star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)))
          * (fourier (T := (1 : ℝ)) t (β : UC) : ℂ)‖
        =
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        * ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ := by
          rw [norm_mul, norm_mul, norm_star, hfourier, mul_one]
      _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := by
            exact mul_le_mul hk hk (norm_nonneg _) hcap_nonneg
      _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap ^ 2 := by ring

private lemma canonicalJointFreezeDiscrepancy_betaFrequencyFactor_eq_fourier
    (β : ℝ) (n m n' m' : ℕ) :
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp β m'))
      =
    (fourier (T := (1 : ℝ))
      (((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ))) (β : UC) : ℂ) := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp
    Goldbach.Cert.MajorArcExponential.e
  simp [fourier_apply, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  repeat rw [← Complex.exp_add]
  congr 1
  ring_nf

/--
Termwise β-collapse for the moving-moving kernel.

This is the exact identity at the level where the proposed Fejér/Dirichlet collapse must begin.
The localization and outer kernel do not disappear; they become the Fourier coefficient
`canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff` at the integer difference mode
`n - m - n' + m'`.
-/
theorem canonicalJointFreezeDiscrepancy_movingMovingTerm_betaCollapse
    (θ θ' : ℝ) (n m n' m' : ℕ) :
    (∫ β in aβ..bβ,
      betaSmallSet.indicator
        (fun β : ℝ =>
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
            * star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)))
            *
          (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
            * star
              (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')))) β)
      =
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') m'))
      * canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff
          (((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ))) := by
  let c : ℂ :=
    ((Goldbach.Cert.MajorArcStep2ExpSums.gExp θ n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp θ m)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') n'
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (-θ') m'))
  change
    (∫ β in aβ..bβ,
      betaSmallSet.indicator
        (fun β : ℝ =>
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
            * star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)))
            *
          (((Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
            * star
              (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' + β) n'
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ' - β) m')))) β)
      =
    c * canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff
          (((n : ℤ) - (m : ℤ) - (n' : ℤ) + (m' : ℤ)))
  unfold canonicalJointFreezeDiscrepancyBetaLocalizedKernelCoeff
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro β hβ
  by_cases hβsmall : β ∈ betaSmallSet
  · simp only [Set.indicator_of_mem hβsmall]
    rw [canonicalJointFreezeDiscrepancyBetaQMovingTerm_mul_star_factorized]
    rw [canonicalJointFreezeDiscrepancy_betaFrequencyFactor_eq_fourier]
    change
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))) *
          (c * (fourier (T := (1 : ℝ)) (↑n - ↑m - ↑n' + ↑m') (β : UC) : ℂ))
        =
      c *
        ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            star (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))) *
          (fourier (T := (1 : ℝ)) (↑n - ↑m - ↑n' + ↑m') (β : UC) : ℂ))
    ring
  · simp [Set.indicator_of_notMem hβsmall]

/-- The q/q′ resonance gap in the moving shell phases. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQThetaGap
    (X q q' : ℕ) (u u' : ℝ) : ℝ :=
  canonicalJointFreezeDiscrepancyBetaQTheta X q u
    - canonicalJointFreezeDiscrepancyBetaQTheta X q' u'

theorem canonicalJointFreezeDiscrepancyBetaQThetaGap_eq_resonanceGap_div_X
    {X q q' : ℕ} {u u' : ℝ}
    (hX : ((X : ℝ) : ℝ) ≠ 0) (hq : ((q : ℝ) : ℝ) ≠ 0)
    (hq' : ((q' : ℝ) : ℝ) ≠ 0) :
    canonicalJointFreezeDiscrepancyBetaQThetaGap X q q' u u'
      =
    (u / (q : ℝ) - u' / (q' : ℝ)) / (X : ℝ) := by
  unfold canonicalJointFreezeDiscrepancyBetaQThetaGap
    canonicalJointFreezeDiscrepancyBetaQTheta
  field_simp [hX, hq, hq']

/--
Exact factorization of a weighted rescaled shell into its two β-oscillatory one-dimensional
geometric factors.

For off-diagonal q/q′ inspection, the important point is that the β-frequencies are
`β + u/(qX)` and `u/(qX) - β`; the q-dependence is still present in the phase.
-/
theorem smallBetaRescaledArchShell_eq_joint_q_factorized
    (X N q : ℕ) (u β : ℝ) :
    smallBetaRescaledArchShell X N q u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (fourier (T := (1 : ℝ)) (-(N : ℤ))
          ((canonicalJointFreezeDiscrepancyBetaQTheta X q u : ℝ) : UC) : ℂ)
      * (canonicalJointFreezeDiscrepancyBetaQPlusSum X q N u β
          * canonicalJointFreezeDiscrepancyBetaQMinusSum X q N u β) := by
  unfold smallBetaRescaledArchShell smallBetaCenteredArchShell
    canonicalJointFreezeDiscrepancyBetaQTheta
    canonicalJointFreezeDiscrepancyBetaQPlusSum
    canonicalJointFreezeDiscrepancyBetaQMinusSum
  rfl

/--
The weighted shell gap has the same q-dependent β-frequency channels in its moving part, with
the frozen `θ = 0` shell subtracted.
-/
theorem smallBetaRescaledShellGap_eq_joint_q_factorized_sub_frozen
    (X N q : ℕ) (u β : ℝ) :
    smallBetaRescaledShellGap X N q u β
      =
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (fourier (T := (1 : ℝ)) (-(N : ℤ))
          ((canonicalJointFreezeDiscrepancyBetaQTheta X q u : ℝ) : UC) : ℂ)
      * (canonicalJointFreezeDiscrepancyBetaQPlusSum X q N u β
          * canonicalJointFreezeDiscrepancyBetaQMinusSum X q N u β))
      - smallBetaFrozenRescaledArchShell N u β := by
  unfold smallBetaRescaledShellGap
  rw [smallBetaRescaledArchShell_eq_joint_q_factorized]

/-- The real q/q′ atom appearing after expanding the square of the q-summed endpoint. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom
    (X N M q q' : ℕ) (β : ℝ) : ℝ :=
  ((canonicalJointFreezeDiscrepancyBetaQPairAtom X N M q β)
    * star (canonicalJointFreezeDiscrepancyBetaQPairAtom X N M q' β)).re

theorem canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom_eq_qAtomKernelIntegrand_re
    (X N M q q' : ℕ) (β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β
      =
    (canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelIntegrand X N M q q' β).re := by
  rfl

/--
Exact β-level off-diagonal atom kernelization.

This is the precise rewrite available before Fubini: the full q-atom, including weights,
endpoint differences, q-phases, and frozen pieces, is represented as a β-integrated TT* kernel.
The moving-shell kernel above is a later subkernel obtained only after opening the q-atom.
-/
theorem canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernel_eq_integral_doubleQAtom
    (X N M q q' : ℕ) :
    canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelRe X N M q q'
      =
    (∫ β in aβ..bβ,
      betaSmallSet.indicator
        (fun β : ℝ =>
          canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β) β) := by
  unfold canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelRe
    canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelIntegrand
    canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom
  simp

/-- Exact double-q expansion of the square, with the β-small-set indicator kept outside. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion
    (X N M : ℕ) (β : ℝ) : ℝ :=
  betaSmallSet.indicator
    (fun β : ℝ =>
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ q' ∈ Finset.Icc (1 : ℕ) Q0,
          canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β) β

/-- Diagonal `q = q'` part of the double-q square expansion. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaDoubleQDiagonalExpansion
    (X N M : ℕ) (β : ℝ) : ℝ :=
  betaSmallSet.indicator
    (fun β : ℝ =>
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q β) β

/-- Off-diagonal `q ≠ q'` part of the double-q square expansion. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion
    (X N M : ℕ) (β : ℝ) : ℝ :=
  betaSmallSet.indicator
    (fun β : ℝ =>
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ q' ∈ (Finset.Icc (1 : ℕ) Q0).erase q,
          canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β) β

theorem canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion_eq_qAtomKernelIntegrandSum
    (X N M : ℕ) (β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion X N M β
      =
    betaSmallSet.indicator
      (fun β : ℝ =>
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ q' ∈ (Finset.Icc (1 : ℕ) Q0).erase q,
            (canonicalJointFreezeDiscrepancyOffDiagonalQAtomKernelIntegrand X N M q q' β).re) β := by
  unfold canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion
  by_cases hβ : β ∈ betaSmallSet
  · simp [Set.indicator_of_mem hβ,
      canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom_eq_qAtomKernelIntegrand_re]
  · simp [Set.indicator_of_notMem hβ]

theorem canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion_eq_diagonal_add_offDiagonal
    (X N M : ℕ) (β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion X N M β
      =
    canonicalJointFreezeDiscrepancyBetaDoubleQDiagonalExpansion X N M β
      + canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion X N M β := by
  unfold canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion
    canonicalJointFreezeDiscrepancyBetaDoubleQDiagonalExpansion
    canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion
  by_cases hβ : β ∈ betaSmallSet
  · simp [Set.indicator_of_mem hβ]
    calc
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ q' ∈ Finset.Icc (1 : ℕ) Q0,
            canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β
        =
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          (canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q β
            +
           ∑ q' ∈ (Finset.Icc (1 : ℕ) Q0).erase q,
             canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            calc
              (∑ q' ∈ Finset.Icc (1 : ℕ) Q0,
                  canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β)
                  =
              (∑ q' ∈ (Finset.Icc (1 : ℕ) Q0).erase q,
                  canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β)
                + canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q β := by
                    exact (Finset.sum_erase_add
                      (s := Finset.Icc (1 : ℕ) Q0)
                      (a := q)
                      (f := fun q' =>
                        canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β)
                      hq).symm
              _ =
              canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q β
                +
              ∑ q' ∈ (Finset.Icc (1 : ℕ) Q0).erase q,
                canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β := by
                  ring
      _ =
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q β)
        +
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ q' ∈ (Finset.Icc (1 : ℕ) Q0).erase q,
          canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β := by
            simp [Finset.sum_add_distrib]
  · simp [Set.indicator_of_notMem hβ]

theorem norm_sq_canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ
    (X N M : ℕ) (β : ℝ) :
    ‖canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint X N M β‖ ^ 2
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ∑ q' ∈ Finset.Icc (1 : ℕ) Q0,
        canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom X N M q q' β := by
  unfold canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint
    canonicalJointFreezeDiscrepancyBetaDoubleQSquareAtom
    canonicalJointFreezeDiscrepancyBetaQPairAtom
  exact norm_sq_sum_complex_eq_double_sum_re
    (s := Finset.Icc (1 : ℕ) Q0)
    (f := fun q =>
      canonicalJointFreezeDiscrepancyBetaQAtom X q N β
        - canonicalJointFreezeDiscrepancyBetaQAtom X q M β)

theorem norm_sq_indicator_canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ
    (X N M : ℕ) (β : ℝ) :
    ‖betaSmallSet.indicator
        (fun β : ℝ => canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint X N M β) β‖ ^ 2
      =
    canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion X N M β := by
  by_cases hβ : β ∈ betaSmallSet
  · simp [canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion,
      Set.indicator_of_mem hβ,
      norm_sq_canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ]
  · simp [canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion,
      Set.indicator_of_notMem hβ]

/-- The global β-integrand after expanding the q-sum square into q/q′ atoms. -/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion X N M β
      else 0

/-- Ordered-pair global β-integrand restricted to the diagonal q/q′ terms. -/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQDiagonalBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        canonicalJointFreezeDiscrepancyBetaDoubleQDiagonalExpansion X N M β
      else 0

/-- Ordered-pair global β-integrand restricted to the off-diagonal q/q′ terms. -/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQOffDiagonalBetaIntegrand
    (X : ℕ) (β : ℝ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion X N M β
      else 0

/--
Resonant off-diagonal contribution.

This is intentionally theorem-facing: after expanding the u/u′ integrals inside the q/q′ atom,
this piece should correspond to `|u/q - u'/q'| ≤ ρ`.
-/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQResonantBetaIntegrand
    (_ρ : canonicalJointFreezeDiscrepancyResonanceScale)
    (_X : ℕ) (_β : ℝ) : ℝ :=
  0

/--
Nonresonant off-diagonal contribution.

This should correspond to the complementary region `ρ < |u/q - u'/q'|`, where β-oscillation is
expected to give the TT*/orthogonality gain.
-/
noncomputable def canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQNonresonantBetaIntegrand
    (_ρ : canonicalJointFreezeDiscrepancyResonanceScale)
    (_X : ℕ) (_β : ℝ) : ℝ :=
  0

/--
The resonant/nonresonant split surface for the off-diagonal double-q integrand.

This is the new mathematical bottleneck: instantiate the two placeholder integrands above with
the actual u/u′-split and prove this identity before attempting bounds.
-/
structure CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit where
  resonant : canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℝ → ℝ
  nonresonant : canonicalJointFreezeDiscrepancyResonanceScale → ℕ → ℝ → ℝ
  eq_split :
    ∀ ρ X β,
      canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQOffDiagonalBetaIntegrand X β
        =
      resonant ρ X β + nonresonant ρ X β

/-- Global β-energy of a resonant off-diagonal model. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalResonantGlobalBetaEnergy
    (S : CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit)
    (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X : ℕ) : ℝ :=
  ∫ β in aβ..bβ, S.resonant ρ X β

/-- Global β-energy of a nonresonant off-diagonal model. -/
noncomputable def canonicalJointFreezeDiscrepancyOffDiagonalNonresonantGlobalBetaEnergy
    (S : CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit)
    (ρ : canonicalJointFreezeDiscrepancyResonanceScale) (X : ℕ) : ℝ :=
  ∫ β in aβ..bβ, S.nonresonant ρ X β

/-- Global β-energy of the diagonal q/q′ contribution. -/
noncomputable def canonicalJointFreezeDiscrepancyDoubleQDiagonalGlobalBetaEnergy
    (X : ℕ) : ℝ :=
  ∫ β in aβ..bβ,
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQDiagonalBetaIntegrand X β

/-- Route-sized target for the diagonal contribution. -/
structure CanonicalJointFreezeDiscrepancyDiagonalBetaEnergyTarget
    (Cdiag : ℝ) : Prop where
  Cdiag_nonneg : 0 ≤ Cdiag
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalJointFreezeDiscrepancyDoubleQDiagonalGlobalBetaEnergy X
        ≤
      Cdiag * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))

/-- Route-sized target for the resonant off-diagonal contribution. -/
structure CanonicalJointFreezeDiscrepancyOffDiagonalResonantBetaEnergyTarget
    (S : CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit)
    (ρ : canonicalJointFreezeDiscrepancyResonanceScale)
    (Cres : ℝ) : Prop where
  Cres_nonneg : 0 ≤ Cres
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalJointFreezeDiscrepancyOffDiagonalResonantGlobalBetaEnergy S ρ X
        ≤
      Cres * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))

/-- Route-sized target for the nonresonant off-diagonal contribution. -/
structure CanonicalJointFreezeDiscrepancyOffDiagonalNonresonantBetaEnergyTarget
    (S : CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit)
    (ρ : canonicalJointFreezeDiscrepancyResonanceScale)
    (Cnonres : ℝ) : Prop where
  Cnonres_nonneg : 0 ≤ Cnonres
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalJointFreezeDiscrepancyOffDiagonalNonresonantGlobalBetaEnergy S ρ X
        ≤
      Cnonres * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))

/--
Global β-energy split into diagonal, resonant off-diagonal, and nonresonant off-diagonal pieces.

This is intentionally a theorem surface rather than a derived theorem: the pointwise split alone
does not justify `intervalIntegral.integral_add` without integrability hypotheses for the concrete
resonant/nonresonant model.
-/
structure CanonicalJointFreezeDiscrepancyGlobalDiagResNonresSplit
    (S : CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit)
    (ρ : canonicalJointFreezeDiscrepancyResonanceScale) : Prop where
  eq_global :
    ∀ X,
      ∫ β in aβ..bβ,
          canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand X β
        =
      canonicalJointFreezeDiscrepancyDoubleQDiagonalGlobalBetaEnergy X
        + canonicalJointFreezeDiscrepancyOffDiagonalResonantGlobalBetaEnergy S ρ X
        + canonicalJointFreezeDiscrepancyOffDiagonalNonresonantGlobalBetaEnergy S ρ X

theorem canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand_eq_diagonal_add_offDiagonal
    (X : ℕ) (β : ℝ) :
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand X β
      =
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQDiagonalBetaIntegrand X β
      + canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQOffDiagonalBetaIntegrand X β := by
  unfold canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQDiagonalBetaIntegrand
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQOffDiagonalBetaIntegrand
  let a : ℕ → ℕ → ℝ := fun N M =>
    if N ≤ M then canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion X N M β else 0
  let d : ℕ → ℕ → ℝ := fun N M =>
    if N ≤ M then canonicalJointFreezeDiscrepancyBetaDoubleQDiagonalExpansion X N M β else 0
  let o : ℕ → ℕ → ℝ := fun N M =>
    if N ≤ M then canonicalJointFreezeDiscrepancyBetaDoubleQOffDiagonalExpansion X N M β else 0
  change
    (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, a N M)
      =
    (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, d N M)
      + (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, o N M)
  calc
    ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, a N M
      =
    ∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, (d N M + o N M) := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          refine Finset.sum_congr rfl ?_
          intro M hM
          by_cases hNM : N ≤ M
          · simp [a, d, o, hNM,
              canonicalJointFreezeDiscrepancyBetaDoubleQSquareExpansion_eq_diagonal_add_offDiagonal]
          · simp [a, d, o, hNM]
    _ =
    (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, d N M)
      + (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, o N M) := by
        simp [Finset.sum_add_distrib]

theorem canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand_eq_doubleQ
    (X : ℕ) (β : ℝ) :
    canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand X β
      =
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand X β := by
  unfold canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
    canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM,
      norm_sq_indicator_canonicalJointFreezeDiscrepancyBetaQSumPairEndpoint_eq_doubleQ]
  · simp [hNM]

/--
The finite-sum/Fubini rewrite surface connecting the existing pair-summed β-energy to the new
global β-energy variable.

This is intentionally a theorem surface: forcing this rewrite is proof-engineering, not the live
arithmetic bottleneck.
-/
structure CanonicalJointFreezeDiscrepancyBetaEnergyIntegralRewrite : Prop where
  eq_global :
    ∀ X,
      canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy X
        =
      canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy X

/--
The deterministic transport from post-β pairwise energy to the global β-energy variable.

The proof is finite-sum bookkeeping plus the per-pair β-L² transport already exposed in the joint
freeze file, followed by the rewrite from pair-summed β-energy to global β-energy.
-/
structure CanonicalJointFreezeDiscrepancyGlobalBetaL2Transport : Prop where
  bound :
    ∀ X,
      canonicalCorrectedFreezeDiscrepancyOrderedPairwiseWindowEnergy X
        ≤
      ((1 : ℝ) / 6) * canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy X

theorem canonicalJointFreezeDiscrepancyGlobalBetaL2Transport_of_pairwise
    (hpair : CanonicalCorrectedFreezeDiscrepancyBetaL2Transport)
    (hrewrite : CanonicalJointFreezeDiscrepancyBetaEnergyIntegralRewrite) :
    CanonicalJointFreezeDiscrepancyGlobalBetaL2Transport where
  bound := by
    intro X
    have hsum :
        canonicalCorrectedFreezeDiscrepancyOrderedPairwiseWindowEnergy X
          ≤
        ((1 : ℝ) / 6)
          * canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy X := by
      unfold canonicalCorrectedFreezeDiscrepancyOrderedPairwiseWindowEnergy
        canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy
      let a : ℕ → ℕ → ℝ := fun N M =>
        if N ≤ M then
          ‖∫ β in aβ..bβ,
              canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β‖ ^ 2
        else 0
      let b : ℕ → ℕ → ℝ := fun N M =>
        if N ≤ M then canonicalCorrectedFreezeDiscrepancyBetaEnergy X N M else 0
      change
        (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, a N M)
          ≤
        ((1 : ℝ) / 6)
          * (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, b N M)
      have hpoint : ∀ N M, a N M ≤ ((1 : ℝ) / 6) * b N M := by
        intro N M
        by_cases hNM : N ≤ M
        · simp [a, b, hNM]
          simpa [one_div] using hpair.bound X N M
        · simp [a, b, hNM]
      have hsum' :
          (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, a N M)
            ≤
          (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, ((1 : ℝ) / 6) * b N M) := by
        refine Finset.sum_le_sum ?_
        intro N hN
        refine Finset.sum_le_sum ?_
        intro M hM
        exact hpoint N M
      calc
        (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, a N M)
          ≤
        (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, ((1 : ℝ) / 6) * b N M) := hsum'
        _ =
        ((1 : ℝ) / 6)
          * (∑ N ∈ EvenIn X H, ∑ M ∈ EvenIn X H, b N M) := by
            simp [Finset.mul_sum]
    calc
      canonicalCorrectedFreezeDiscrepancyOrderedPairwiseWindowEnergy X
        ≤
      ((1 : ℝ) / 6)
        * canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy X := hsum
      _ =
      ((1 : ℝ) / 6)
        * canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy X := by
          rw [hrewrite.eq_global X]

/--
Route-sized target for the global β-energy of the exact joint discrepancy.

This is the new analytic bottleneck.  Its proof should expand the square before estimating pieces
and use β-orthogonality / TT* structure if available.
-/
structure CanonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergyTarget
    (Cjoint : ℝ) : Prop where
  Cjoint_nonneg : 0 ≤ Cjoint
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy X
        ≤
      Cjoint * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))

theorem canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergyTarget_of_diag_res_nonres
    {S : CanonicalJointFreezeDiscrepancyOffDiagonalResonantSplit}
    {ρ : canonicalJointFreezeDiscrepancyResonanceScale}
    {Cdiag Cres Cnonres : ℝ}
    (hglobalSplit : CanonicalJointFreezeDiscrepancyGlobalDiagResNonresSplit S ρ)
    (hdiag : CanonicalJointFreezeDiscrepancyDiagonalBetaEnergyTarget Cdiag)
    (hres : CanonicalJointFreezeDiscrepancyOffDiagonalResonantBetaEnergyTarget S ρ Cres)
    (hnonres :
      CanonicalJointFreezeDiscrepancyOffDiagonalNonresonantBetaEnergyTarget S ρ Cnonres)
    (hrewrite : ∀ X,
      canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy X
        =
      ∫ β in aβ..bβ,
        canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand X β) :
    CanonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergyTarget
      (Cdiag + Cres + Cnonres) where
  Cjoint_nonneg := by
    nlinarith [hdiag.Cdiag_nonneg, hres.Cres_nonneg, hnonres.Cnonres_nonneg]
  bound := by
    intro X hX
    have hdiagX := hdiag.bound hX
    have hresX := hres.bound hX
    have hnonresX := hnonres.bound hX
    rw [hrewrite X, hglobalSplit.eq_global X]
    calc
      canonicalJointFreezeDiscrepancyDoubleQDiagonalGlobalBetaEnergy X
          + canonicalJointFreezeDiscrepancyOffDiagonalResonantGlobalBetaEnergy S ρ X
          + canonicalJointFreezeDiscrepancyOffDiagonalNonresonantGlobalBetaEnergy S ρ X
        ≤
      Cdiag * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))
          + Cres * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))
          + Cnonres * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2)) := by
            nlinarith
      _ =
      (Cdiag + Cres + Cnonres) * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2)) := by
        ring

theorem canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergyTarget_of_global
    {Cjoint : ℝ}
    (hrewrite : CanonicalJointFreezeDiscrepancyBetaEnergyIntegralRewrite)
    (hglobal : CanonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergyTarget Cjoint) :
    CanonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergyTarget Cjoint where
  Cjoint_nonneg := hglobal.Cjoint_nonneg
  bound := by
    intro X hX
    calc
      canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy X
        =
      canonicalJointFreezeDiscrepancyOrderedPairwiseGlobalBetaEnergy X := hrewrite.eq_global X
      _ ≤ Cjoint * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2)) := hglobal.bound hX

/--
Pointwise β-integrand rewrite surface for the exact residual algebra.

This is where the next serious proof should begin: expand the square of the joint discrepancy
before using absolute values.
-/
structure CanonicalJointFreezeDiscrepancyBetaIntegrandExpansion where
  expanded : ℕ → ℝ → ℝ
  eq_expanded :
    ∀ X β,
      canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand X β
        =
      expanded X β

theorem canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand_eq_qsum
    (X : ℕ) (β : ℝ) :
    canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand X β
      =
    canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand X β := by
  unfold canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand
    canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
    canonicalJointFreezeDiscrepancyBetaPreAbsoluteIntegrand
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  by_cases hNM : N ≤ M
  · simp [hNM, canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand_eq_qsum]
  · simp [hNM]

def canonicalJointFreezeDiscrepancyBetaIntegrandExpansion_qsum :
    CanonicalJointFreezeDiscrepancyBetaIntegrandExpansion where
  expanded := canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand
  eq_expanded := canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand_eq_qsum

def canonicalJointFreezeDiscrepancyBetaIntegrandExpansion_doubleQ :
    CanonicalJointFreezeDiscrepancyBetaIntegrandExpansion where
  expanded := canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand
  eq_expanded := by
    intro X β
    calc
      canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand X β
        =
      canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand X β :=
        canonicalJointFreezeDiscrepancyOrderedPairwiseBetaIntegrand_eq_qsum X β
      _ =
      canonicalJointFreezeDiscrepancyOrderedPairwiseDoubleQBetaIntegrand X β :=
        canonicalJointFreezeDiscrepancyOrderedPairwiseQSumBetaIntegrand_eq_doubleQ X β

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassJointBetaEnergyTargets
