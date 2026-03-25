import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

/-- The exact weighted coefficient-side minor object indexed by the α-frequency `t`. -/
noncomputable def weightedMinorCoeff (X N : ℕ) (t : ℤ) : ℂ :=
  coeff X N t

/--
The coefficient-side core before the hard minor Fourier weight is attached. This is the natural
`T_{X,N}(t)` object in the singularity-first minor decomposition program.
-/
noncomputable def minorCoeffCore (X N : ℕ) (t : ℤ) : ℂ :=
  q0NormFactor N
    * ∑ nm ∈ nmSupportOfT N t,
        aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm)

/-- Finite-support Fourier projector on the `t`-index set. -/
noncomputable def finiteModeProjector (S : Finset ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun t => if t ∈ S then f t else 0

/-- Arithmetic mean of a coefficient object over a chosen finite mode set. -/
noncomputable def coeffMeanOn (S : Finset ℤ) (f : ℤ → ℂ) : ℂ :=
  (((S.card : ℕ) : ℂ))⁻¹ * ∑ t ∈ S, f t

/--
Centered coefficient object on a chosen finite mode set: subtract the average on the set and
vanish outside the set.
-/
noncomputable def centeredCoeffOn (S : Finset ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun t => if t ∈ S then f t - coeffMeanOn S f else 0

/-- The natural finite frequency support for the canonical weighted minor coefficients. -/
noncomputable def weightedMinorCoeffSupport (N : ℕ) : Finset ℤ :=
  tSupport N

/--
Window-stable ambient support for cross-`N` minor-mode comparisons. This keeps all `N ∈ EvenIn X H`
inside a common finite `t`-index box.
-/
noncomputable def windowMinorCoeffSupport (X : ℕ) : Finset ℤ :=
  tSupport (X + H)

/-- The raw weight-only coefficient sequence. -/
noncomputable def weightCoeff (X : ℕ) (t : ℤ) : ℂ :=
  minorArcWeightFourier X Δ_canon t

/-- The `t = 0`-removed weighted minor coefficient object. -/
noncomputable def weightedMinorCoeffNoZero (X N : ℕ) : ℤ → ℂ :=
  finiteModeProjector ((weightedMinorCoeffSupport N).erase 0) (weightedMinorCoeff X N)

/-- The centered weighted minor coefficient object after removing the `t = 0` mode. -/
noncomputable def weightedMinorCoeffCentered (X N : ℕ) : ℤ → ℂ :=
  centeredCoeffOn ((weightedMinorCoeffSupport N).erase 0) (weightedMinorCoeff X N)

/-- The `t = 0`-removed coefficient object on the window-stable ambient support. -/
noncomputable def coeffZeroRemoved (X N : ℕ) : ℤ → ℂ :=
  finiteModeProjector ((windowMinorCoeffSupport X).erase 0) (weightedMinorCoeff X N)

/-- The centered weighted minor coefficient object on the window-stable ambient support. -/
noncomputable def coeffCentered (X N : ℕ) : ℤ → ℂ :=
  centeredCoeffOn ((windowMinorCoeffSupport X).erase 0) (weightedMinorCoeff X N)

/-- The centered weight-only coefficient object on the same ambient support. -/
noncomputable def weightCentered (X : ℕ) : ℤ → ℂ :=
  centeredCoeffOn ((windowMinorCoeffSupport X).erase 0) (weightCoeff X)

/-- Generic finite-rank projector infrastructure: choose a finite mode set and project onto it. -/
noncomputable def rankKProjector (modes : Finset ℤ) : (ℤ → ℂ) → (ℤ → ℂ) :=
  finiteModeProjector modes

/-- Finite-support sesquilinear pairing on the `t`-index set. -/
noncomputable def coeffDotOn (S : Finset ℤ) (f g : ℤ → ℂ) : ℂ :=
  ∑ t ∈ S, f t * star (g t)

/-- Finite-support squared norm on the `t`-index set. -/
noncomputable def coeffNormSqOn (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ∑ t ∈ S, ‖f t‖ ^ 2

/--
Least-squares scalar for projection of `f` onto `g` over a chosen finite `t`-mode set.
This is the neutral regression object used before any specific singularity theorem is chosen.
-/
noncomputable def leastSquaresScalarOn (S : Finset ℤ) (f g : ℤ → ℂ) : ℂ :=
  if _hzero : coeffNormSqOn S g = 0 then
    0
  else
    coeffDotOn S f g * (((coeffNormSqOn S g : ℝ) : ℂ))⁻¹

/-- The least-squares weight-regression scalar on the canonical window-stable support. -/
noncomputable def weightRegressionAlpha (X N : ℕ) : ℂ :=
  leastSquaresScalarOn ((windowMinorCoeffSupport X).erase 0) (coeffCentered X N) (weightCentered X)

/--
The weight-regressed arithmetic residual: centered weighted minor coefficient minus its projection
onto the centered weight-only sequence.
-/
noncomputable def coeffArith (X N : ℕ) : ℤ → ℂ :=
  fun t => coeffCentered X N t - weightRegressionAlpha X N * weightCentered X t

theorem weightedMinorCoeff_eq_minorArcWeightFourier_mul_minorCoeffCore
    (X N : ℕ) (t : ℤ) :
    weightedMinorCoeff X N t
      =
    minorArcWeightFourier X Δ_canon t * minorCoeffCore X N t := by
  unfold weightedMinorCoeff coeff minorCoeffCore
  have hsum :
      (∑ nm ∈ nmSupportOfT N t, atom X N nm)
        =
      minorArcWeightFourier X Δ_canon t
        * ∑ nm ∈ nmSupportOfT N t,
            aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm) := by
    calc
      (∑ nm ∈ nmSupportOfT N t, atom X N nm)
          =
        ∑ nm ∈ nmSupportOfT N t,
          minorArcWeightFourier X Δ_canon t
            * (aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm)) := by
              refine Finset.sum_congr rfl ?_
              intro nm hnm
              have ht : tFn N nm = t := (mem_nmSupportOfT_iff.mp hnm).2.2
              unfold atom
              rw [ht]
              ring
      _ =
        minorArcWeightFourier X Δ_canon t
          * ∑ nm ∈ nmSupportOfT N t,
              aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm) := by
                rw [Finset.mul_sum]
  calc
    q0NormFactor N * (∑ nm ∈ nmSupportOfT N t, atom X N nm)
        =
      q0NormFactor N
        * (minorArcWeightFourier X Δ_canon t
            * ∑ nm ∈ nmSupportOfT N t,
                aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm)) := by
                  rw [hsum]
    _ =
      minorArcWeightFourier X Δ_canon t
        * (q0NormFactor N
            * ∑ nm ∈ nmSupportOfT N t,
                aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm)) := by
                  ring

theorem weightedMinorCoeff_apply_zero
    (X N : ℕ) :
    weightedMinorCoeffNoZero X N 0 = 0 := by
  unfold weightedMinorCoeffNoZero finiteModeProjector weightedMinorCoeffSupport
  simp

theorem weightedMinorCoeffNoZero_apply_mem
    {X N : ℕ} {t : ℤ}
    (ht : t ∈ (weightedMinorCoeffSupport N).erase 0) :
    weightedMinorCoeffNoZero X N t = weightedMinorCoeff X N t := by
  unfold weightedMinorCoeffNoZero finiteModeProjector
  simp [ht]

theorem weightedMinorCoeffNoZero_apply_not_mem
    {X N : ℕ} {t : ℤ}
    (ht : t ∉ (weightedMinorCoeffSupport N).erase 0) :
    weightedMinorCoeffNoZero X N t = 0 := by
  unfold weightedMinorCoeffNoZero finiteModeProjector
  simp [ht]

theorem centeredCoeffOn_apply_mem
    {S : Finset ℤ} {f : ℤ → ℂ} {t : ℤ} (ht : t ∈ S) :
    centeredCoeffOn S f t = f t - coeffMeanOn S f := by
  unfold centeredCoeffOn
  simp [ht]

theorem centeredCoeffOn_apply_not_mem
    {S : Finset ℤ} {f : ℤ → ℂ} {t : ℤ} (ht : t ∉ S) :
    centeredCoeffOn S f t = 0 := by
  unfold centeredCoeffOn
  simp [ht]

theorem coeffZeroRemoved_apply_mem
    {X N : ℕ} {t : ℤ}
    (ht : t ∈ (windowMinorCoeffSupport X).erase 0) :
    coeffZeroRemoved X N t = weightedMinorCoeff X N t := by
  unfold coeffZeroRemoved finiteModeProjector
  simp [ht]

theorem coeffZeroRemoved_apply_not_mem
    {X N : ℕ} {t : ℤ}
    (ht : t ∉ (windowMinorCoeffSupport X).erase 0) :
    coeffZeroRemoved X N t = 0 := by
  unfold coeffZeroRemoved finiteModeProjector
  simp [ht]

theorem coeffCentered_eq_weightedMinorCoeff_sub_mean
    {X N : ℕ} {t : ℤ}
    (ht : t ∈ (windowMinorCoeffSupport X).erase 0) :
    coeffCentered X N t
      =
    weightedMinorCoeff X N t
      - coeffMeanOn ((windowMinorCoeffSupport X).erase 0) (weightedMinorCoeff X N) := by
  exact centeredCoeffOn_apply_mem (S := (windowMinorCoeffSupport X).erase 0)
    (f := weightedMinorCoeff X N) ht

theorem weightCentered_eq_weightCoeff_sub_mean
    {X : ℕ} {t : ℤ}
    (ht : t ∈ (windowMinorCoeffSupport X).erase 0) :
    weightCentered X t
      =
    weightCoeff X t
      - coeffMeanOn ((windowMinorCoeffSupport X).erase 0) (weightCoeff X) := by
  exact centeredCoeffOn_apply_mem (S := (windowMinorCoeffSupport X).erase 0)
    (f := weightCoeff X) ht

theorem coeffArith_eq_coeffCentered_sub_alpha_mul_weightCentered
    (X N : ℕ) (t : ℤ) :
    coeffArith X N t
      =
    coeffCentered X N t - weightRegressionAlpha X N * weightCentered X t := by
  rfl

theorem minorResidual_eq_sum_weightedMinorCoeff
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    minorResidual X N Δ_canon
      =
    ∑ t ∈ weightedMinorCoeffSupport N, weightedMinorCoeff X N t := by
  simpa [weightedMinorCoeffSupport, weightedMinorCoeff] using
    minorResidual_eq_sum_tSupport_coeff (X := X) (N := N) hX hN

theorem canonicalExpansion_eq_weightedMinorCoeff :
    Q0MinorTTStarFrequencyExpansion.canonicalExpansion.coeff = weightedMinorCoeff := by
  rfl

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
