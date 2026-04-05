import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets
import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1CommonWindowTargets

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze

noncomputable section

/--
The exact `β`-integrated common-square contribution in the ordered-pair `q = 1` shell difference.

This is the surviving interior term in the exact decomposition of the paired two-sided-shift
difference. The live `q = 1` bottleneck is to prove that this common contribution cancels or
telescopes on the canonical even window.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonIntegral
    (X N M : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
          X N M β) β

/--
Positive-frequency overlap component of the common-square term.

The first index is the overlap width; the second is the centered-shift parameter carried by the
phase defect. This is the natural exact object for a gap/difference-energy proof.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveOverlap
    (X overlap K : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (overlap - 5),
    ∑ k ∈ Finset.range (overlap - 5),
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * Goldbach.Cert.MajorArcExponential.e
            (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        * Goldbach.Cert.MajorArcExponential.e
            ((u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))

/--
Negative-frequency overlap component of the common-square term.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonNegativeOverlap
    (X overlap K : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (overlap - 5),
    ∑ k ∈ Finset.range (overlap - 5),
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * Goldbach.Cert.MajorArcExponential.e
            (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        * Goldbach.Cert.MajorArcExponential.e
            (-((u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))))

/-- The kernel-weighted `u`-integral of the positive overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    (X overlap K : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
      (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β

/-- The kernel-weighted `u`-integral of the negative overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
    (X overlap K : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
      (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))
      * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β

/-- The `β`-integrated positive overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral
    (X overlap K : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β) β

/-- The `β`-integrated negative overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral
    (X overlap K : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β) β

/--
Ordered-pair window energy of the common-square contribution.

The `if N ≤ M` gate matches the exact common/strip decomposition theorem, which is currently only
proved for ordered pairs.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2 else 0

/--
Abstract cancellation surface for the common-square contribution.

Experiments now show that literal pointwise cancellation is too strong to be the live theorem,
but this exact surface is still useful as a special case: any later symmetry/telescoping theorem
can still feed through it automatically.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonCancellation : Prop where
  vanish :
    ∀ {X N M : ℕ}, N ≤ M →
      canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M = 0

/--
Route-sized target for the ordered-pair common-square contribution.

This is now the live theorem-facing surface for the common piece. The earlier cancellation target
is retained only as a special case feeding into this bound with constant `0`.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Exact phase/cos-defect rewrite of the common-square contribution.

This makes the current obstruction explicit: on the shared overlap square, the geometric support is
the same, but the centered shift still depends on `N + 2` versus `M + 2`, so the common term is
not termwise zero without an additional cancellation theorem.
-/
theorem canonicalQ1TwoSidedShiftCommonSquareDiff_eq_phase_mul_real_cos_defect_sub
    (X N M : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β
      =
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        let phase :=
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        let defectN : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((N + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        let defectM : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((M + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        phase * (defectN - defectM) := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect]
  rw [q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect]
  ring

/--
Exact gap/decomposition surface for the common `β`-integrated contribution.

The proven raw square decomposition above shows the right overlap profiles. The next live theorem is
to transport that structure through the `u`- and `β`-integrals without reintroducing cancellation
claims.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonIntegralGapDecomposition : Prop where
  eq_add :
    ∀ X N M,
      canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M
        =
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N N
        - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N M
        + canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X N N
        - canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X N M

/--
The common-square contribution is not termwise zero in general.

The shared overlap square carries the same geometric support, but the centered shift defect still
depends on `N + 2` versus `M + 2`. So the proof route for the common piece must be a direct
ordered-pair energy bound, not a strip-only argument and not naive pointwise cancellation.
-/
theorem canonicalQ1TwoSidedShiftCommonSquareDiff_obstruction_comment
    (X N M : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β
      =
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        let phase :=
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        let defectN : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((N + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        let defectM : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((M + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        phase * (defectN - defectM) := by
  exact canonicalQ1TwoSidedShiftCommonSquareDiff_eq_phase_mul_real_cos_defect_sub X N M u β

theorem canonicalQ1TwoSidedShiftCommonSquareDiff_self
    (X N : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N N u β = 0 := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_self
    (X N : ℕ) (β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
        X N N β = 0 := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
  have hfun :
      (fun u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
          (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))
          * Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff X N N u β)
        =
      fun _ : ℝ => (0 : ℂ) := by
        funext u
        rw [canonicalQ1TwoSidedShiftCommonSquareDiff_self]
        simp
  rw [hfun]
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegral_self
    (X N : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N N = 0 := by
  have hpoint :
      ∀ β : ℝ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ =>
              (Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
                X N N β : ℂ)) β
          = 0 := by
    intro β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · rw [Set.indicator_of_mem hβ]
      rw [canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_self]
    · simp [hβ]
  unfold canonicalQ1TwoSidedShiftBoundaryCommonIntegral
  have hfun :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            (Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
              X N N β : ℂ)) β)
        =
      fun _ : ℝ => (0 : ℂ) := by
        funext β
        exact hpoint β
  rw [hfun]
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy_eq_zero_of_cancellation
    (hCancel : CanonicalQ1TwoSidedShiftBoundaryCommonCancellation)
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X = 0 := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy
  refine Finset.sum_eq_zero ?_
  intro N hN
  refine Finset.sum_eq_zero ?_
  intro M hM
  by_cases hNM : N ≤ M
  · rw [if_pos hNM, hCancel.vanish hNM]
    simp
  · rw [if_neg hNM]

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_cancellation
    (hCancel : CanonicalQ1TwoSidedShiftBoundaryCommonCancellation) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget 0 where
  C3_nonneg := by positivity
  bound := by
    intro X hX
    rw [canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy_eq_zero_of_cancellation
      hCancel X]
    have hright :
        2 * (((EvenIn X H).card : ℝ)
          * (0 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
          =
        0 := by
      rw [zero_div, mul_zero, mul_zero]
    have hnonneg :
        0 ≤
          2 * (((EvenIn X H).card : ℝ)
            * (0 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
      rw [hright]
    exact hnonneg

end
