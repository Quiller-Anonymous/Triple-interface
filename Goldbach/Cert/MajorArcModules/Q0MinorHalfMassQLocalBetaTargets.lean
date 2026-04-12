import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassJointBetaEnergyTargets

/-!
# q-local major-arc rebuild surfaces

This file starts the second rebuild after the global `β` / mode-sum approach failed on scale.

The guiding principle is to keep each `q` on its own local coordinate centered at
`u / (q X)`, prove fixed-`q` local energy bounds there, and only then sum over `q`.
No global `β` surface or global Fourier-mode regrouping is introduced in this file.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQLocalBetaTargets

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open MeasureTheory

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassJointBetaEnergyTargets

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- The local `β`-coordinate centered at `u / (q X)`. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQLocalCoordinate
    (X q : ℕ) (u β : ℝ) : ℝ :=
  β - canonicalJointFreezeDiscrepancyBetaQTheta X q u

/-- The inverse map from the local `q`-coordinate back to the global `β` variable. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQLocalize
    (X q : ℕ) (u ξ : ℝ) : ℝ :=
  ξ + canonicalJointFreezeDiscrepancyBetaQTheta X q u

theorem canonicalJointFreezeDiscrepancyBetaQLocalize_localCoordinate
    (X q : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyBetaQLocalize X q u
        (canonicalJointFreezeDiscrepancyBetaQLocalCoordinate X q u β)
      =
    β := by
  unfold canonicalJointFreezeDiscrepancyBetaQLocalize
    canonicalJointFreezeDiscrepancyBetaQLocalCoordinate
  ring

theorem canonicalJointFreezeDiscrepancyBetaQLocalCoordinate_localize
    (X q : ℕ) (u ξ : ℝ) :
    canonicalJointFreezeDiscrepancyBetaQLocalCoordinate X q u
        (canonicalJointFreezeDiscrepancyBetaQLocalize X q u ξ)
      =
    ξ := by
  unfold canonicalJointFreezeDiscrepancyBetaQLocalize
    canonicalJointFreezeDiscrepancyBetaQLocalCoordinate
  ring

/-- The translated `β`-window for the local `q`-coordinate at parameter `u`. -/
noncomputable def canonicalJointFreezeDiscrepancyBetaQLocalInterval
    (X q : ℕ) (u : ℝ) : Set ℝ :=
  Set.Icc
    (aβ - canonicalJointFreezeDiscrepancyBetaQTheta X q u)
    (bβ - canonicalJointFreezeDiscrepancyBetaQTheta X q u)

/-- The weighted `q ≥ 2` moving kernel written in the local `q`-coordinate. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingKernel
    (X q N : ℕ) (u ξ : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u
    (canonicalJointFreezeDiscrepancyBetaQLocalize X q u ξ)

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingKernel_eq_translate
    (X q N : ℕ) (u ξ : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingKernel X q N u ξ
      =
    canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u
      (canonicalJointFreezeDiscrepancyBetaQLocalize X q u ξ) := by
  rfl

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingKernel_localCoordinate
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingKernel X q N u
        (canonicalJointFreezeDiscrepancyBetaQLocalCoordinate X q u β)
      =
    canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingKernel
  rw [canonicalJointFreezeDiscrepancyBetaQLocalize_localCoordinate]

/-- The exact weighted `q ≥ 2` moving `u`-atom in the local `q`-coordinate. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingUAtom
    (X q N : ℕ) (u ξ : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving X q N u
    (canonicalJointFreezeDiscrepancyBetaQLocalize X q u ξ)

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingUAtom_localCoordinate
    (X q N : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingUAtom X q N u
        (canonicalJointFreezeDiscrepancyBetaQLocalCoordinate X q u β)
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomMoving X q N u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QLocalMovingUAtom
  rw [canonicalJointFreezeDiscrepancyBetaQLocalize_localCoordinate]

/-- The ordered-pair moving `u`-atom in the local `q`-coordinate. -/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom
    (X q N M : ℕ) (u ξ : ℝ) : ℂ :=
  canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u
    (canonicalJointFreezeDiscrepancyBetaQLocalize X q u ξ)

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom_localCoordinate
    (X q N M : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom X q N M u
        (canonicalJointFreezeDiscrepancyBetaQLocalCoordinate X q u β)
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom
  rw [canonicalJointFreezeDiscrepancyBetaQLocalize_localCoordinate]

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom_localize
    (X q N M : ℕ) (u ξ : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom X q N M u ξ
      =
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u
      (canonicalJointFreezeDiscrepancyBetaQLocalize X q u ξ) := by
  rfl

/--
Fixed-`q` local `β`-energy slice for one ordered pair and one local parameter `u`.

The `β`-integral is now expressed in the translated local coordinate `ξ`.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice
    (X q N M : ℕ) (u : ℝ) : ℝ :=
  ∫ ξ in
      (aβ - canonicalJointFreezeDiscrepancyBetaQTheta X q u)..
      (bβ - canonicalJointFreezeDiscrepancyBetaQTheta X q u),
    ‖canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom X q N M u ξ‖ ^ 2

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice_eq_global
    (X q N M : ℕ) (u : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice X q N M u
      =
    ∫ β in aβ..bβ,
      ‖canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β‖ ^ 2 := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairUAtom
  simpa [canonicalJointFreezeDiscrepancyBetaQLocalize, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using
    (intervalIntegral.integral_comp_add_right
      (f := fun β : ℝ =>
        ‖canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β‖ ^ 2)
      (a := aβ - canonicalJointFreezeDiscrepancyBetaQTheta X q u)
      (b := bβ - canonicalJointFreezeDiscrepancyBetaQTheta X q u)
      (d := canonicalJointFreezeDiscrepancyBetaQTheta X q u))

/--
The global `β`-slice for the weighted `q ≥ 2` moving ordered-pair atom.

This is the exact fixed-`q` analytic slice that the local-coordinate transport reduces to.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice
    (X q N M : ℕ) (u : ℝ) : ℝ :=
  ∫ β in aβ..bβ,
    ‖canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β‖ ^ 2

/--
The explicit moving amplitude/indicator pair that underlies the fixed-`q` global moving slice.

This is the first theorem surface where the `1 / (q X)` scale becomes visible.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q N
      * ((Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.centeredUnitSet (1 : ℝ)).indicator
          (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β) u))
    -
  (canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude X q M
      * ((Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.centeredUnitSet (1 : ℝ)).indicator
          (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q M u β) u))

/--
The kernel-only ordered-pair difference at fixed `(q,u,β)`, before the arithmetic amplitudes are
attached.

This isolates the part of the local slice that the new `q`-local analysis must control.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairKernelForm
    (X q N M : ℕ) (u β : ℝ) : ℂ :=
  ((Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.centeredUnitSet (1 : ℝ)).indicator
      (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q N u β) u)
    -
  ((Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.centeredUnitSet (1 : ℝ)).indicator
      (fun u => canonicalJointFreezeDiscrepancyBetaQMovingKernelFactor X q M u β) u)

/--
Kernel-only global `β`-slice for the fixed-`q` moving ordered-pair difference.

This is the object whose scale decides whether the `q`-local rebuild is alive.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairKernelBetaEnergySlice
    (X q N M : ℕ) (u : ℝ) : ℝ :=
  ∫ β in aβ..bβ,
    ‖canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairKernelForm X q N M u β‖ ^ 2

theorem canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm_eq
    (X q N M : ℕ) (u β : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β
      =
    canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm X q N M u β := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm
  simpa using
    (canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving_eq_amplitude_pair
      X q N M u β)

theorem canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice_eq_amplitudeForm
    (X q N M : ℕ) (u : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice X q N M u
      =
    ∫ β in aβ..bβ,
      ‖canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm X q N M u β‖ ^ 2 := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice
  simp_rw [canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm_eq]

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice_eq_globalSlice
    (X q N M : ℕ) (u : ℝ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice X q N M u
      =
    canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice X q N M u := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice
  exact canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice_eq_global X q N M u

/--
Fixed-`q` ordered-pair local energy before summing over `q`.

This is the first genuine analytic target of the local-major-arc rebuild.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy
    (X q : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∫ u in (-1 : ℝ)..(1 : ℝ),
          canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice X q N M u
      else 0

/--
The fixed-`q` ordered-pair energy written directly on the original global `β` surface, but using
only the moving ordered-pair atom.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseGlobalMovingBetaEnergy
    (X q : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∫ u in (-1 : ℝ)..(1 : ℝ),
          canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice X q N M u
      else 0

theorem canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy_eq_global
    (X q : ℕ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy X q
      =
    ∑ N ∈ EvenIn X H,
      ∑ M ∈ EvenIn X H,
        if N ≤ M then
          ∫ u in (-1 : ℝ)..(1 : ℝ),
            ∫ β in aβ..bβ,
              ‖canonicalJointFreezeDiscrepancyWeightedGe2UAtomPairFactorMoving X q N M u β‖ ^ 2
        else 0 := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  split_ifs with hNM
  · simp_rw [canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice_eq_global]
  · rfl

theorem canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy_eq_globalMoving
    (X q : ℕ) :
    canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy X q
      =
    canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseGlobalMovingBetaEnergy X q := by
  unfold canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy
    canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseGlobalMovingBetaEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro M hM
  split_ifs with hNM
  · simp_rw [canonicalJointFreezeDiscrepancyWeightedGe2QLocalPairBetaEnergySlice_eq_globalSlice]
  · rfl

/--
Local `q,q'` interaction after both shells have been recentered in their own local variables.

This is left as a theorem surface rather than expanded globally; the point is to postpone any
cross-`q` summation until fixed-parameter local control is available.
-/
noncomputable def canonicalJointFreezeDiscrepancyWeightedGe2QQPairwiseLocalInteraction
    (X q q' : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ∫ u in (-1 : ℝ)..(1 : ℝ),
          ∫ u' in (-1 : ℝ)..(1 : ℝ),
            canonicalJointFreezeDiscrepancyWeightedGe2OffDiagonalUKernel
              X N M q q' u u'
      else 0

/--
Abstract local-energy upper bound for a fixed `q`.

The function `B X q` is the local scale delivered by the future local-singular analysis.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QLocalEnergyUpperBound
    (B : ℕ → ℕ → ℝ) : Prop where
  bound :
    ∀ {X q : ℕ}, X0 ≤ X → 2 ≤ q → q ≤ Q0 →
      canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy X q ≤ B X q

/--
Analytic upper-bound surface for the fixed-`q` global moving ordered-pair energy.

This is the first direct theorem target after the exact local-to-global transport.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingEnergyUpperBound
    (B : ℕ → ℕ → ℝ) : Prop where
  bound :
    ∀ {X q : ℕ}, X0 ≤ X → 2 ≤ q → q ≤ Q0 →
      canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseGlobalMovingBetaEnergy X q
        ≤ B X q

/--
Analytic target surface after exposing the moving pair in amplitude form.

This is the first place where fixed-`q` feasibility can be checked directly from the visible
`canonicalJointFreezeDiscrepancyWeightedGe2MovingAmplitude` factor.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingAmplitudeEnergyUpperBound
    (B : ℕ → ℕ → ℝ) : Prop where
  bound :
    ∀ {X q : ℕ}, X0 ≤ X → 2 ≤ q → q ≤ Q0 →
      (∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∫ u in (-1 : ℝ)..(1 : ℝ),
              ∫ β in aβ..bβ,
                ‖canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairAmplitudeForm
                  X q N M u β‖ ^ 2
          else 0)
        ≤ B X q

/--
Kernel-only fixed-`q` energy target, before restoring the explicit arithmetic amplitudes.

This is the first place where the viability of the local-major-arc rebuild can be tested without
mixing in the already-visible `1 / (q X)` prefactor.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingKernelEnergyUpperBound
    (K : ℕ → ℕ → ℝ) : Prop where
  bound :
    ∀ {X q : ℕ}, X0 ≤ X → 2 ≤ q → q ≤ Q0 →
      (∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H,
          if N ≤ M then
            ∫ u in (-1 : ℝ)..(1 : ℝ),
              canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairKernelBetaEnergySlice
                X q N M u
          else 0)
        ≤ K X q

theorem canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingEnergyUpperBound_of_amplitude
    {B : ℕ → ℕ → ℝ}
    (hamp : CanonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingAmplitudeEnergyUpperBound B) :
    CanonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingEnergyUpperBound B where
  bound hX hq hqQ0 := by
    unfold canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseGlobalMovingBetaEnergy
    refine le_of_eq_of_le ?_ (hamp.bound hX hq hqQ0)
    refine Finset.sum_congr rfl ?_
    intro N hN
    refine Finset.sum_congr rfl ?_
    intro M hM
    split_ifs with hNM
    · simp_rw [canonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingPairBetaEnergySlice_eq_amplitudeForm]
    · rfl

theorem canonicalJointFreezeDiscrepancyWeightedGe2QLocalEnergyUpperBound_of_globalMoving
    {B : ℕ → ℕ → ℝ}
    (hglobal : CanonicalJointFreezeDiscrepancyWeightedGe2QGlobalMovingEnergyUpperBound B) :
    CanonicalJointFreezeDiscrepancyWeightedGe2QLocalEnergyUpperBound B where
  bound hX hq hqQ0 := by
    rw [canonicalJointFreezeDiscrepancyWeightedGe2QOrderedPairwiseLocalBetaEnergy_eq_globalMoving]
    exact hglobal.bound hX hq hqQ0

/--
Abstract local off-diagonal interaction bound for a fixed ordered pair `(q,q')`.

This is the local replacement for the failed global off-diagonal mode-weight route.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QQPairwiseLocalInteractionUpperBound
    (Boff : ℕ → ℕ → ℕ → ℝ) : Prop where
  bound :
    ∀ {X q q' : ℕ}, X0 ≤ X → 2 ≤ q → q ≤ Q0 → 2 ≤ q' → q' ≤ Q0 →
      ‖canonicalJointFreezeDiscrepancyWeightedGe2QQPairwiseLocalInteraction X q q'‖
        ≤ Boff X q q'

/--
Summation surface for the fixed-`q` local major-arc route.

Once local bounds `B X q` are established, this is the only remaining arithmetic summation step
before comparing to the route-sized target.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QLocalSummationTarget
    (B : ℕ → ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      Finset.sum (Finset.Icc (2 : ℕ) Q0) (fun q => B X q)
        ≤ H / ((Q0 : ℝ) ^ 2)

/--
Mixed local-major-arc summation surface including diagonal and off-diagonal local interactions.

This is the q-local replacement for the failed global `β`-energy mode-sum target.
-/
structure CanonicalJointFreezeDiscrepancyWeightedGe2QLocalRouteTarget
    (B : ℕ → ℕ → ℝ) (Boff : ℕ → ℕ → ℕ → ℝ) : Prop where
  diagonal :
    CanonicalJointFreezeDiscrepancyWeightedGe2QLocalSummationTarget B
  offDiagonal :
    ∀ {X : ℕ}, X0 ≤ X →
      Finset.sum (Finset.Icc (2 : ℕ) Q0) (fun q =>
        Finset.sum (Finset.Icc (2 : ℕ) Q0) (fun q' =>
          if q = q' then 0 else Boff X q q'))
        ≤ H / ((Q0 : ℝ) ^ 2)

end
