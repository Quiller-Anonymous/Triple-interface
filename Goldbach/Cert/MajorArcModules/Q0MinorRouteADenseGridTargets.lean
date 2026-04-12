import Goldbach.Cert.MajorArcModules.Q0MinorRouteABContract

/-!
# Route A dense-grid targets

This file starts the missing upstream Route-A layer.

The current repo already exposes the route-visible minor scalar and the downstream Route A / Route
B contracts, but it does not yet formalize the paper's actual Route-A mechanism:

1. define a band-limited local statistic on centers,
2. prove a positive mean and a small variance,
3. deduce a dense good grid,
4. upgrade from the grid to every center by Sampling / Bernstein.

This file records those objects and theorem surfaces explicitly on the current route-visible scalar.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteADenseGridTargets

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorRouteABContract
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition

noncomputable section

/-- Route-A grid spacing, matching the paper's `Δ = ⌈H / C0⌉` with a safe `C0 ≥ 1` convention. -/
def routeADenseGridStep (C0 : ℕ) : ℕ :=
  let d := max 1 C0
  (H + d - 1) / d

lemma routeADenseGridStep_pos (C0 : ℕ) : 0 < routeADenseGridStep C0 := by
  unfold routeADenseGridStep
  set d : ℕ := max 1 C0
  have hd : 0 < d := by
    unfold d
    exact lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)
  have hH : 0 < H := by
    unfold H
    positivity
  have hnum : 0 < H + d - 1 := by
    omega
  have hle : d ≤ H + d - 1 := by
    omega
  exact Nat.div_pos hle hd

/--
The Route-A grid of centers on `[X, 2X]`, with integer spacing `routeADenseGridStep C0`.

This is the machine-facing discrete proxy for the paper's `Δ`-spaced dense grid.
-/
def routeADenseGrid (X C0 : ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter (fun y => (y - X) % routeADenseGridStep C0 = 0)

lemma mem_routeADenseGrid_iff {X C0 y : ℕ} :
    y ∈ routeADenseGrid X C0 ↔
      y ∈ Finset.Icc X (2 * X) ∧ (y - X) % routeADenseGridStep C0 = 0 := by
  unfold routeADenseGrid
  simp

lemma mem_routeADenseGrid_window {X C0 y : ℕ} (hy : y ∈ routeADenseGrid X C0) :
    y ∈ Finset.Icc X (2 * X) := by
  exact (mem_routeADenseGrid_iff.mp hy).1

lemma routeADenseGrid_step_dvd_offset {X C0 y : ℕ} (hy : y ∈ routeADenseGrid X C0) :
    routeADenseGridStep C0 ∣ y - X := by
  exact Nat.dvd_of_mod_eq_zero (mem_routeADenseGrid_iff.mp hy).2

lemma routeADenseGrid_exists_eq_left_add_step_mul {X C0 y : ℕ} (hy : y ∈ routeADenseGrid X C0) :
    ∃ k : ℕ, y = X + routeADenseGridStep C0 * k := by
  rcases routeADenseGrid_step_dvd_offset hy with ⟨k, hk⟩
  have hXle : X ≤ y := by
    exact (Finset.mem_Icc.mp (mem_routeADenseGrid_window hy)).1
  refine ⟨k, ?_⟩
  omega

lemma left_mem_routeADenseGrid (X C0 : ℕ) : X ∈ routeADenseGrid X C0 := by
  rw [mem_routeADenseGrid_iff]
  constructor
  · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  · simp

lemma routeADenseGrid_nonempty (X C0 : ℕ) : (routeADenseGrid X C0).Nonempty := by
  exact ⟨X, left_mem_routeADenseGrid X C0⟩

lemma routeADenseGrid_card_pos (X C0 : ℕ) : 0 < (routeADenseGrid X C0).card := by
  exact Finset.card_pos.mpr (routeADenseGrid_nonempty X C0)

lemma routeADenseGrid_card_le_windowCard (X C0 : ℕ) :
    (routeADenseGrid X C0).card ≤ (Finset.Icc X (2 * X)).card := by
  unfold routeADenseGrid
  exact Finset.card_filter_le _ _

lemma routeADenseGrid_card_le (X C0 : ℕ) :
    (routeADenseGrid X C0).card ≤ X + 1 := by
  calc
    (routeADenseGrid X C0).card ≤ (Finset.Icc X (2 * X)).card :=
      routeADenseGrid_card_le_windowCard X C0
    _ = X + 1 := by
      rw [Nat.card_Icc]
      omega

/--
Band-limited Route-A statistic built from the exact route-visible minor scalar.

The parameter `K` is the center kernel on integer differences. The eventual Route-A proof should
instantiate `K` with the chosen band-limited kernel/extractor profile.
-/
noncomputable def routeABandLimitedStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, (((K ((N : ℤ) - (y : ℤ)) : ℝ) : ℂ) * routeVisibleScalar X N)

/-- Real part of the Route-A band-limited statistic. -/
noncomputable def routeABandLimitedStatisticRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  (routeABandLimitedStatistic K X y).re

/-- Route-A statistic formed from the frozen geometric witness `G_formula`. -/
noncomputable def routeAGeometricStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, (((K ((N : ℤ) - (y : ℤ)) : ℝ) : ℂ) * G_formula X N)

/-- Route-A statistic formed from the zero-mode correction `SS_formula`. -/
noncomputable def routeAZeroModeStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, (((K ((N : ℤ) - (y : ℤ)) : ℝ) : ℂ) * SS_formula X N)

/-- Route-A statistic formed from the exact residual `R_formula`. -/
noncomputable def routeAResidualStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, (((K ((N : ℤ) - (y : ℤ)) : ℝ) : ℂ) * R_formula X N)

/-- Route-A statistic formed from the frozen `G + SS` witness. -/
noncomputable def routeAFrozenModelStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  routeAGeometricStatistic K X y + routeAZeroModeStatistic K X y

/-- Route-A statistic formed from the mean channel alone. -/
noncomputable def routeAMeanChannelStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, (((K ((N : ℤ) - (y : ℤ)) : ℝ) : ℂ) * meanChannelScalar X N)

/-- Route-A statistic formed from the exact mean-channel approximation error. -/
noncomputable def routeAMeanChannelApproxErrorStatistic
    (K : ℤ → ℝ) (X y : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, (((K ((N : ℤ) - (y : ℤ)) : ℝ) : ℂ) * meanChannelApproxError X N)

/--
Normalization used by the paper's Route-A statistic `T(y) = (log^2 X / H) S(y)`.

This is separated so the mean/variance theorem surfaces can speak either about the raw statistic or
the normalized one.
-/
def routeAStatisticNormalization (X : ℕ) : ℝ :=
  (Real.log (X : ℝ) ^ 2) / (H : ℝ)

/-- Normalized real Route-A statistic on integer centers. -/
noncomputable def routeABandLimitedStatisticNormalizedRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  routeAStatisticNormalization X * routeABandLimitedStatisticRe K X y

noncomputable def routeAFrozenModelStatisticNormalizedRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  routeAStatisticNormalization X * (routeAFrozenModelStatistic K X y).re

noncomputable def routeAResidualStatisticNormalizedRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  routeAStatisticNormalization X * (routeAResidualStatistic K X y).re

noncomputable def routeAGeometricStatisticNormalizedRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  routeAStatisticNormalization X * (routeAGeometricStatistic K X y).re

noncomputable def routeAMeanChannelStatisticNormalizedRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  routeAStatisticNormalization X * (routeAMeanChannelStatistic K X y).re

noncomputable def routeAMeanChannelApproxErrorStatisticNormalizedRe
    (K : ℤ → ℝ) (X y : ℕ) : ℝ :=
  routeAStatisticNormalization X * (routeAMeanChannelApproxErrorStatistic K X y).re

lemma routeABandLimitedStatisticNormalizedRe_eq_normalization_mul
    (K : ℤ → ℝ) (X y : ℕ) :
    routeABandLimitedStatisticNormalizedRe K X y
      =
    routeAStatisticNormalization X * routeABandLimitedStatisticRe K X y := by
  rfl

lemma normalization_mul_re_add (c : ℝ) (a b : ℂ) :
    c * (a + b).re = c * a.re + c * b.re := by
  simp [Complex.add_re, mul_add]

theorem routeABandLimitedStatistic_eq_geometric_plus_zeroMode_plus_residual
    (K : ℤ → ℝ) (X y : ℕ) :
    routeABandLimitedStatistic K X y
      =
    routeAGeometricStatistic K X y
      + routeAZeroModeStatistic K X y
      + routeAResidualStatistic K X y := by
  unfold routeABandLimitedStatistic routeAGeometricStatistic routeAZeroModeStatistic
    routeAResidualStatistic
  simp_rw [routeVisibleScalar_eq_G_formula_add_SS_formula_add_R_formula, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem routeABandLimitedStatistic_eq_frozenModel_plus_residual
    (K : ℤ → ℝ) (X y : ℕ) :
    routeABandLimitedStatistic K X y
      =
    routeAFrozenModelStatistic K X y + routeAResidualStatistic K X y := by
  rw [routeABandLimitedStatistic_eq_geometric_plus_zeroMode_plus_residual]
  simp [routeAFrozenModelStatistic, add_assoc]

theorem routeAMeanChannelStatistic_eq_geometric_plus_meanChannelApproxError
    (K : ℤ → ℝ) (X y : ℕ) :
    routeAMeanChannelStatistic K X y
      =
    routeAGeometricStatistic K X y + routeAMeanChannelApproxErrorStatistic K X y := by
  unfold routeAMeanChannelStatistic routeAGeometricStatistic
    routeAMeanChannelApproxErrorStatistic
  simp_rw [meanChannelScalar_eq_G_formula_add_meanChannelApproxError, mul_add]
  rw [Finset.sum_add_distrib]

structure RouteAPointwiseFrozenResidualSplit (K : ℤ → ℝ) : Prop where
  split :
    ∀ X y,
      routeABandLimitedStatisticNormalizedRe K X y
        =
      routeAFrozenModelStatisticNormalizedRe K X y
        + routeAResidualStatisticNormalizedRe K X y

structure RouteAPointwiseMeanChannelGeometricSplit (K : ℤ → ℝ) : Prop where
  split :
    ∀ X y,
      routeAMeanChannelStatisticNormalizedRe K X y
        =
      routeAGeometricStatisticNormalizedRe K X y
        + routeAMeanChannelApproxErrorStatisticNormalizedRe K X y

axiom routeAPointwiseFrozenResidualSplit_from_visible
    (K : ℤ → ℝ) : RouteAPointwiseFrozenResidualSplit K

axiom routeAPointwiseMeanChannelGeometricSplit_from_visible
    (K : ℤ → ℝ) : RouteAPointwiseMeanChannelGeometricSplit K

noncomputable def routeAGridAverage (C0 : ℕ) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  (((routeADenseGrid X C0).card : ℝ)⁻¹
    * Finset.sum (routeADenseGrid X C0) (fun y => f y))

noncomputable def routeAGridCenteredQuadratic (C0 : ℕ) (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  Finset.sum (routeADenseGrid X C0) (fun y => (f y - routeAGridAverage C0 f X) ^ 2)

theorem routeAGridAverage_add (C0 : ℕ) (f g : ℕ → ℝ) (X : ℕ) :
    routeAGridAverage C0 (fun y => f y + g y) X
      =
    routeAGridAverage C0 f X + routeAGridAverage C0 g X := by
  unfold routeAGridAverage
  rw [Finset.sum_add_distrib]
  ring

theorem routeAGridAverage_congr
    (C0 X : ℕ) {f g : ℕ → ℝ}
    (hfg : ∀ y ∈ routeADenseGrid X C0, f y = g y) :
    routeAGridAverage C0 f X = routeAGridAverage C0 g X := by
  unfold routeAGridAverage
  congr 1
  exact Finset.sum_congr rfl hfg

lemma sq_add_le_two_mul_add_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem routeAGridCenteredQuadratic_add_le
    (C0 : ℕ) (f g : ℕ → ℝ) (X : ℕ) :
    routeAGridCenteredQuadratic C0 (fun y => f y + g y) X
      ≤
    2 * routeAGridCenteredQuadratic C0 f X
      + 2 * routeAGridCenteredQuadratic C0 g X := by
  let μf := routeAGridAverage C0 f X
  let μg := routeAGridAverage C0 g X
  have hμ : routeAGridAverage C0 (fun y => f y + g y) X = μf + μg := by
    simp [μf, μg, routeAGridAverage_add]
  calc
    routeAGridCenteredQuadratic C0 (fun y => f y + g y) X
      = Finset.sum (routeADenseGrid X C0) (fun y => (((f y - μf) + (g y - μg)) ^ 2)) := by
          unfold routeAGridCenteredQuadratic
          rw [hμ]
          refine Finset.sum_congr rfl ?_
          intro y hy
          ring
    _ ≤ Finset.sum (routeADenseGrid X C0) (fun y => 2 * ((f y - μf) ^ 2 + (g y - μg) ^ 2)) := by
          refine Finset.sum_le_sum ?_
          intro y hy
          exact sq_add_le_two_mul_add_sq (f y - μf) (g y - μg)
    _ = 2 * routeAGridCenteredQuadratic C0 f X
          + 2 * routeAGridCenteredQuadratic C0 g X := by
          unfold routeAGridCenteredQuadratic
          simp [μf, μg, Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul,
            add_assoc, add_left_comm, add_comm]

noncomputable def routeAGridAverageNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridAverage C0 (fun y => routeABandLimitedStatisticNormalizedRe K X y) X

noncomputable def routeAGridAverageFrozenModelNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridAverage C0 (fun y => routeAFrozenModelStatisticNormalizedRe K X y) X

noncomputable def routeAGridAverageResidualNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridAverage C0 (fun y => routeAResidualStatisticNormalizedRe K X y) X

noncomputable def routeAGridCenteredQuadraticNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridCenteredQuadratic C0 (fun y => routeABandLimitedStatisticNormalizedRe K X y) X

noncomputable def routeAGridCenteredQuadraticFrozenModelNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridCenteredQuadratic C0 (fun y => routeAFrozenModelStatisticNormalizedRe K X y) X

noncomputable def routeAGridCenteredQuadraticResidualNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridCenteredQuadratic C0 (fun y => routeAResidualStatisticNormalizedRe K X y) X

noncomputable def routeAGridAverageMeanChannelNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridAverage C0 (fun y => routeAMeanChannelStatisticNormalizedRe K X y) X

noncomputable def routeAGridAverageGeometricNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridAverage C0 (fun y => routeAGeometricStatisticNormalizedRe K X y) X

noncomputable def routeAGridAverageMeanChannelApproxErrorNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridAverage C0 (fun y => routeAMeanChannelApproxErrorStatisticNormalizedRe K X y) X

noncomputable def routeAGridCenteredQuadraticMeanChannelNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridCenteredQuadratic C0 (fun y => routeAMeanChannelStatisticNormalizedRe K X y) X

noncomputable def routeAGridCenteredQuadraticGeometricNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridCenteredQuadratic C0 (fun y => routeAGeometricStatisticNormalizedRe K X y) X

noncomputable def routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic
    (K : ℤ → ℝ) (C0 X : ℕ) : ℝ :=
  routeAGridCenteredQuadratic C0 (fun y => routeAMeanChannelApproxErrorStatisticNormalizedRe K X y) X

attribute [irreducible]
  routeAFrozenModelStatisticNormalizedRe
  routeAResidualStatisticNormalizedRe
  routeAGeometricStatisticNormalizedRe
  routeAMeanChannelStatisticNormalizedRe
  routeAMeanChannelApproxErrorStatisticNormalizedRe

theorem routeAGridAverage_eq_split_of_pointwise
    (C0 X : ℕ) {f g h : ℕ → ℝ}
    (hsplit : ∀ y, f y = g y + h y) :
    routeAGridAverage C0 f X
      =
    routeAGridAverage C0 g X + routeAGridAverage C0 h X := by
  calc
    routeAGridAverage C0 f X
      = routeAGridAverage C0 (fun y => g y + h y) X := by
          apply routeAGridAverage_congr
          intro y hy
          exact hsplit y
    _ = routeAGridAverage C0 g X + routeAGridAverage C0 h X := by
          exact routeAGridAverage_add C0 g h X

theorem routeAGridAverage_lowerBound_of_pointwise
    (C0 X : ℕ) {f g h : ℕ → ℝ} {L M : ℝ}
    (hsplit : ∀ y, f y = g y + h y)
    (hg : L ≤ routeAGridAverage C0 g X)
    (hh : M ≤ routeAGridAverage C0 h X) :
    L + M ≤ routeAGridAverage C0 f X := by
  rw [routeAGridAverage_eq_split_of_pointwise C0 X hsplit]
  linarith

theorem routeAGridCenteredQuadratic_le_split_of_pointwise
    (C0 X : ℕ) {f g h : ℕ → ℝ}
    (hsplit : ∀ y, f y = g y + h y) :
    routeAGridCenteredQuadratic C0 f X
      ≤
    2 * routeAGridCenteredQuadratic C0 g X
      + 2 * routeAGridCenteredQuadratic C0 h X := by
  calc
    routeAGridCenteredQuadratic C0 f X
      = routeAGridCenteredQuadratic C0 (fun y => g y + h y) X := by
          unfold routeAGridCenteredQuadratic
          have havg :
              routeAGridAverage C0 f X = routeAGridAverage C0 (fun y => g y + h y) X := by
            exact routeAGridAverage_congr C0 X (fun y hy => hsplit y)
          apply Finset.sum_congr rfl
          intro y hy
          rw [hsplit y]
          congr 1
          simpa using congrArg (fun t => g y + h y - t) havg
    _ ≤ 2 * routeAGridCenteredQuadratic C0 g X
          + 2 * routeAGridCenteredQuadratic C0 h X := by
          exact routeAGridCenteredQuadratic_add_le C0 g h X

theorem routeAGridAverageNormalizedStatistic_lowerBound_of_pointwise_frozen_plus_residual
    (K : ℤ → ℝ) (C0 X : ℕ) {L M : ℝ}
    (hsplit :
      ∀ y,
        routeABandLimitedStatisticNormalizedRe K X y
          =
        routeAFrozenModelStatisticNormalizedRe K X y
          + routeAResidualStatisticNormalizedRe K X y)
    (hfrozen : L ≤ routeAGridAverageFrozenModelNormalizedStatistic K C0 X)
    (hresidual : M ≤ routeAGridAverageResidualNormalizedStatistic K C0 X) :
    L + M ≤ routeAGridAverageNormalizedStatistic K C0 X := by
  simpa [routeAGridAverageNormalizedStatistic,
    routeAGridAverageFrozenModelNormalizedStatistic,
    routeAGridAverageResidualNormalizedStatistic] using
    (routeAGridAverage_lowerBound_of_pointwise C0 X hsplit hfrozen hresidual)

theorem routeAGridCenteredQuadraticNormalizedStatistic_le_of_pointwise_frozen_plus_residual
    (K : ℤ → ℝ) (C0 X : ℕ)
    (hsplit :
      ∀ y,
        routeABandLimitedStatisticNormalizedRe K X y
          =
        routeAFrozenModelStatisticNormalizedRe K X y
          + routeAResidualStatisticNormalizedRe K X y) :
    routeAGridCenteredQuadraticNormalizedStatistic K C0 X
      ≤
    2 * routeAGridCenteredQuadraticFrozenModelNormalizedStatistic K C0 X
      + 2 * routeAGridCenteredQuadraticResidualNormalizedStatistic K C0 X := by
  unfold routeAGridCenteredQuadraticNormalizedStatistic
    routeAGridCenteredQuadraticFrozenModelNormalizedStatistic
    routeAGridCenteredQuadraticResidualNormalizedStatistic
  exact routeAGridCenteredQuadratic_le_split_of_pointwise C0 X hsplit

theorem routeAGridAverageMeanChannelNormalizedStatistic_lowerBound_of_pointwise_geometric_plus_error
    (K : ℤ → ℝ) (C0 X : ℕ) {L M : ℝ}
    (hsplit :
      ∀ y,
        routeAMeanChannelStatisticNormalizedRe K X y
          =
        routeAGeometricStatisticNormalizedRe K X y
          + routeAMeanChannelApproxErrorStatisticNormalizedRe K X y)
    (hgeom : L ≤ routeAGridAverageGeometricNormalizedStatistic K C0 X)
    (herror : M ≤ routeAGridAverageMeanChannelApproxErrorNormalizedStatistic K C0 X) :
    L + M ≤ routeAGridAverageMeanChannelNormalizedStatistic K C0 X := by
  simpa [routeAGridAverageMeanChannelNormalizedStatistic,
    routeAGridAverageGeometricNormalizedStatistic,
    routeAGridAverageMeanChannelApproxErrorNormalizedStatistic] using
    (routeAGridAverage_lowerBound_of_pointwise C0 X hsplit hgeom herror)

theorem routeAGridCenteredQuadraticMeanChannelNormalizedStatistic_le_of_pointwise_geometric_plus_error
    (K : ℤ → ℝ) (C0 X : ℕ)
    (hsplit :
      ∀ y,
        routeAMeanChannelStatisticNormalizedRe K X y
          =
        routeAGeometricStatisticNormalizedRe K X y
          + routeAMeanChannelApproxErrorStatisticNormalizedRe K X y) :
    routeAGridCenteredQuadraticMeanChannelNormalizedStatistic K C0 X
      ≤
    2 * routeAGridCenteredQuadraticGeometricNormalizedStatistic K C0 X
      + 2 * routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic K C0 X := by
  unfold routeAGridCenteredQuadraticMeanChannelNormalizedStatistic
    routeAGridCenteredQuadraticGeometricNormalizedStatistic
    routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic
  exact routeAGridCenteredQuadratic_le_split_of_pointwise C0 X hsplit

/--
Grid-level mean lower bound for the normalized Route-A statistic.

This is the first arithmetic positivity theorem Route A actually needs.
-/
structure RouteAGridMeanLowerBound
    (K : ℤ → ℝ) (C0 : ℕ) (μ : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      μ X
        ≤
      (((routeADenseGrid X C0).card : ℝ)⁻¹
        * Finset.sum (routeADenseGrid X C0) (fun y =>
            routeABandLimitedStatisticNormalizedRe K X y))

/--
Grid-level variance upper bound for the normalized Route-A statistic.

Combined with the mean lower bound, this is intended to force a dense good grid by Chebyshev /
Paley-Zygmund style arguments.
-/
structure RouteAGridVarianceUpperBound
    (K : ℤ → ℝ) (C0 : ℕ) (V : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (Finset.sum (routeADenseGrid X C0) (fun y =>
        (routeABandLimitedStatisticNormalizedRe K X y
          - (((routeADenseGrid X C0).card : ℝ)⁻¹
              * Finset.sum (routeADenseGrid X C0) (fun z =>
                  routeABandLimitedStatisticNormalizedRe K X z))) ^ 2))
        ≤ V X

/--
Grid-level mean lower bound for the normalized mean-channel Route-A statistic.

This is the natural main-term positivity target for the smoother Route-A option.
-/
structure RouteAMeanChannelGridMeanLowerBound
    (K : ℤ → ℝ) (C0 : ℕ) (μ : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      μ X ≤ routeAGridAverageMeanChannelNormalizedStatistic K C0 X

/--
Grid-level centered-quadratic upper bound for the normalized mean-channel Route-A statistic.

This is the variance-facing Route-A target before reconnecting the mean channel to the full
route-visible statistic.
-/
structure RouteAMeanChannelGridVarianceUpperBound
    (K : ℤ → ℝ) (C0 : ℕ) (V : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      routeAGridCenteredQuadraticMeanChannelNormalizedStatistic K C0 X ≤ V X

/--
Grid-average lower bound for the normalized frozen geometric Route-A statistic alone.

This is the first genuinely informative arithmetic input for the smoother Route-A option.
-/
structure RouteAGeometricGridAverageLowerBound
    (K : ℤ → ℝ) (C0 : ℕ) (μ : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      μ X ≤ routeAGridAverageGeometricNormalizedStatistic K C0 X

/--
Grid-centered quadratic upper bound for the normalized mean-channel approximation error.

This is the natural error-term input paired with the geometric main statistic in Route A.
-/
structure RouteAMeanChannelApproxErrorGridVarianceUpperBound
    (K : ℤ → ℝ) (C0 : ℕ) (V : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic K C0 X ≤ V X

/--
Dense-good-grid target for Route A.

At least a `(1 - δ X)` proportion of grid points carry a positive lower bound `τ X`.
-/
structure RouteADenseGoodGridTarget
    (K : ℤ → ℝ) (C0 : ℕ) (τ δ : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (1 - δ X) * (((routeADenseGrid X C0).card : ℝ))
        ≤
      (((routeADenseGrid X C0).filter
          (fun y => τ X ≤ routeABandLimitedStatisticNormalizedRe K X y)).card : ℝ)

/--
Sampling/Bernstein upgrade target for Route A.

This is the theorem surface that turns dense positivity on the grid into positivity at every
center in the dyadic interval.
-/
structure RouteASamplingBernsteinTarget
    (K : ℤ → ℝ) (C0 : ℕ) (τ : ℕ → ℝ) : Prop where
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      RouteADenseGoodGridTarget K C0 τ (fun _ => 0) →
        ∀ y ∈ Finset.Icc X (2 * X), τ X / 2 ≤ routeABandLimitedStatisticNormalizedRe K X y

/--
Combined upstream Route-A packet: mean, variance, dense-grid, and the final Sampling/Bernstein
upgrade all live on the exact route-visible scalar.
-/
structure RouteADenseGridClosureTarget
    (K : ℤ → ℝ) (C0 : ℕ)
    (μ V τ δ : ℕ → ℝ) : Prop where
  mean_target : RouteAGridMeanLowerBound K C0 μ
  variance_target : RouteAGridVarianceUpperBound K C0 V
  dense_grid_target : RouteADenseGoodGridTarget K C0 τ δ
  sampling_target : RouteASamplingBernsteinTarget K C0 τ

theorem routeAMeanChannelGridMeanLowerBound_of_pointwise_geometric_plus_error
    (K : ℤ → ℝ) (C0 : ℕ) (μg μe : ℕ → ℝ)
    (hsplit :
      ∀ X y,
        routeAMeanChannelStatisticNormalizedRe K X y
          =
        routeAGeometricStatisticNormalizedRe K X y
          + routeAMeanChannelApproxErrorStatisticNormalizedRe K X y)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        μg X ≤ routeAGridAverageGeometricNormalizedStatistic K C0 X)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        μe X ≤ routeAGridAverageMeanChannelApproxErrorNormalizedStatistic K C0 X) :
    RouteAMeanChannelGridMeanLowerBound K C0 (fun X => μg X + μe X) := by
  refine ⟨?_⟩
  intro X hX
  exact routeAGridAverageMeanChannelNormalizedStatistic_lowerBound_of_pointwise_geometric_plus_error
    K C0 X (fun y => hsplit X y) (hgeom hX) (herror hX)

theorem routeAMeanChannelGridMeanLowerBound_of_split
    (K : ℤ → ℝ) (C0 : ℕ) (μg μe : ℕ → ℝ)
    (hsplit : RouteAPointwiseMeanChannelGeometricSplit K)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        μg X ≤ routeAGridAverageGeometricNormalizedStatistic K C0 X)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        μe X ≤ routeAGridAverageMeanChannelApproxErrorNormalizedStatistic K C0 X) :
    RouteAMeanChannelGridMeanLowerBound K C0 (fun X => μg X + μe X) := by
  exact routeAMeanChannelGridMeanLowerBound_of_pointwise_geometric_plus_error
    K C0 μg μe hsplit.split hgeom herror

theorem routeAMeanChannelGridVarianceUpperBound_of_pointwise_geometric_plus_error
    (K : ℤ → ℝ) (C0 : ℕ) (Vg Ve : ℕ → ℝ)
    (hsplit :
      ∀ X y,
        routeAMeanChannelStatisticNormalizedRe K X y
          =
        routeAGeometricStatisticNormalizedRe K X y
          + routeAMeanChannelApproxErrorStatisticNormalizedRe K X y)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticGeometricNormalizedStatistic K C0 X ≤ Vg X)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic K C0 X ≤ Ve X) :
    RouteAMeanChannelGridVarianceUpperBound K C0 (fun X => 2 * Vg X + 2 * Ve X) := by
  refine ⟨?_⟩
  intro X hX
  have hsplitX :=
    routeAGridCenteredQuadraticMeanChannelNormalizedStatistic_le_of_pointwise_geometric_plus_error
      K C0 X (fun y => hsplit X y)
  have hg := hgeom hX
  have he := herror hX
  linarith

theorem routeAMeanChannelGridVarianceUpperBound_of_split
    (K : ℤ → ℝ) (C0 : ℕ) (Vg Ve : ℕ → ℝ)
    (hsplit : RouteAPointwiseMeanChannelGeometricSplit K)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticGeometricNormalizedStatistic K C0 X ≤ Vg X)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic K C0 X ≤ Ve X) :
    RouteAMeanChannelGridVarianceUpperBound K C0 (fun X => 2 * Vg X + 2 * Ve X) := by
  exact routeAMeanChannelGridVarianceUpperBound_of_pointwise_geometric_plus_error
    K C0 Vg Ve hsplit.split hgeom herror

theorem routeAMeanChannelGridMeanLowerBound_of_visible
    (K : ℤ → ℝ) (C0 : ℕ) (μg μe : ℕ → ℝ)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        μg X ≤ routeAGridAverageGeometricNormalizedStatistic K C0 X)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        μe X ≤ routeAGridAverageMeanChannelApproxErrorNormalizedStatistic K C0 X) :
    RouteAMeanChannelGridMeanLowerBound K C0 (fun X => μg X + μe X) := by
  exact routeAMeanChannelGridMeanLowerBound_of_split
    K C0 μg μe (routeAPointwiseMeanChannelGeometricSplit_from_visible K) hgeom herror

theorem routeAMeanChannelGridVarianceUpperBound_of_visible
    (K : ℤ → ℝ) (C0 : ℕ) (Vg Ve : ℕ → ℝ)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticGeometricNormalizedStatistic K C0 X ≤ Vg X)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticMeanChannelApproxErrorNormalizedStatistic K C0 X ≤ Ve X) :
    RouteAMeanChannelGridVarianceUpperBound K C0 (fun X => 2 * Vg X + 2 * Ve X) := by
  exact routeAMeanChannelGridVarianceUpperBound_of_split
    K C0 Vg Ve (routeAPointwiseMeanChannelGeometricSplit_from_visible K) hgeom herror

theorem routeAMeanChannelGridMeanLowerBound_of_geometric_average_and_error_average
    (K : ℤ → ℝ) (C0 : ℕ) (μg μe : ℕ → ℝ)
    (hgeom : RouteAGeometricGridAverageLowerBound K C0 μg)
    (herror :
      ∀ {X : ℕ}, X0 ≤ X →
        μe X ≤ routeAGridAverageMeanChannelApproxErrorNormalizedStatistic K C0 X) :
    RouteAMeanChannelGridMeanLowerBound K C0 (fun X => μg X + μe X) := by
  exact routeAMeanChannelGridMeanLowerBound_of_visible K C0 μg μe
    (fun {_} hX => hgeom.bound hX) herror

theorem routeAMeanChannelGridVarianceUpperBound_of_geometric_variance_and_error_variance
    (K : ℤ → ℝ) (C0 : ℕ) (Vg Ve : ℕ → ℝ)
    (hgeom :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticGeometricNormalizedStatistic K C0 X ≤ Vg X)
    (herror : RouteAMeanChannelApproxErrorGridVarianceUpperBound K C0 Ve) :
    RouteAMeanChannelGridVarianceUpperBound K C0 (fun X => 2 * Vg X + 2 * Ve X) := by
  exact routeAMeanChannelGridVarianceUpperBound_of_visible K C0 Vg Ve
    hgeom (fun {_} hX => herror.bound hX)

theorem routeAGridMeanLowerBound_of_pointwise_frozen_plus_residual
    (K : ℤ → ℝ) (C0 : ℕ) (μf μr : ℕ → ℝ)
    (hsplit :
      ∀ X y,
        routeABandLimitedStatisticNormalizedRe K X y
          =
        routeAFrozenModelStatisticNormalizedRe K X y
          + routeAResidualStatisticNormalizedRe K X y)
    (hfrozen :
      ∀ {X : ℕ}, X0 ≤ X →
        μf X ≤ routeAGridAverageFrozenModelNormalizedStatistic K C0 X)
    (hresidual :
      ∀ {X : ℕ}, X0 ≤ X →
        μr X ≤ routeAGridAverageResidualNormalizedStatistic K C0 X) :
    RouteAGridMeanLowerBound K C0 (fun X => μf X + μr X) := by
  refine ⟨?_⟩
  intro X hX
  exact routeAGridAverageNormalizedStatistic_lowerBound_of_pointwise_frozen_plus_residual
    K C0 X (fun y => hsplit X y) (hfrozen hX) (hresidual hX)

theorem routeAGridMeanLowerBound_of_frozen_residual_split
    (K : ℤ → ℝ) (C0 : ℕ) (μf μr : ℕ → ℝ)
    (hsplit : RouteAPointwiseFrozenResidualSplit K)
    (hfrozen :
      ∀ {X : ℕ}, X0 ≤ X →
        μf X ≤ routeAGridAverageFrozenModelNormalizedStatistic K C0 X)
    (hresidual :
      ∀ {X : ℕ}, X0 ≤ X →
        μr X ≤ routeAGridAverageResidualNormalizedStatistic K C0 X) :
    RouteAGridMeanLowerBound K C0 (fun X => μf X + μr X) := by
  exact routeAGridMeanLowerBound_of_pointwise_frozen_plus_residual
    K C0 μf μr hsplit.split hfrozen hresidual

theorem routeAGridVarianceUpperBound_of_pointwise_frozen_plus_residual
    (K : ℤ → ℝ) (C0 : ℕ) (Vf Vr : ℕ → ℝ)
    (hsplit :
      ∀ X y,
        routeABandLimitedStatisticNormalizedRe K X y
          =
        routeAFrozenModelStatisticNormalizedRe K X y
          + routeAResidualStatisticNormalizedRe K X y)
    (hfrozen :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticFrozenModelNormalizedStatistic K C0 X ≤ Vf X)
    (hresidual :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticResidualNormalizedStatistic K C0 X ≤ Vr X) :
    RouteAGridVarianceUpperBound K C0 (fun X => 2 * Vf X + 2 * Vr X) := by
  refine ⟨?_⟩
  intro X hX
  change routeAGridCenteredQuadraticNormalizedStatistic K C0 X ≤ 2 * Vf X + 2 * Vr X
  have hsplitX :=
    routeAGridCenteredQuadraticNormalizedStatistic_le_of_pointwise_frozen_plus_residual
      K C0 X (fun y => hsplit X y)
  have hf := hfrozen hX
  have hr := hresidual hX
  linarith

theorem routeAGridVarianceUpperBound_of_frozen_residual_split
    (K : ℤ → ℝ) (C0 : ℕ) (Vf Vr : ℕ → ℝ)
    (hsplit : RouteAPointwiseFrozenResidualSplit K)
    (hfrozen :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticFrozenModelNormalizedStatistic K C0 X ≤ Vf X)
    (hresidual :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticResidualNormalizedStatistic K C0 X ≤ Vr X) :
    RouteAGridVarianceUpperBound K C0 (fun X => 2 * Vf X + 2 * Vr X) := by
  exact routeAGridVarianceUpperBound_of_pointwise_frozen_plus_residual
    K C0 Vf Vr hsplit.split hfrozen hresidual

theorem routeAGridMeanLowerBound_of_visible_frozen_residual
    (K : ℤ → ℝ) (C0 : ℕ) (μf μr : ℕ → ℝ)
    (hfrozen :
      ∀ {X : ℕ}, X0 ≤ X →
        μf X ≤ routeAGridAverageFrozenModelNormalizedStatistic K C0 X)
    (hresidual :
      ∀ {X : ℕ}, X0 ≤ X →
        μr X ≤ routeAGridAverageResidualNormalizedStatistic K C0 X) :
    RouteAGridMeanLowerBound K C0 (fun X => μf X + μr X) := by
  exact routeAGridMeanLowerBound_of_frozen_residual_split
    K C0 μf μr (routeAPointwiseFrozenResidualSplit_from_visible K) hfrozen hresidual

theorem routeAGridVarianceUpperBound_of_visible_frozen_residual
    (K : ℤ → ℝ) (C0 : ℕ) (Vf Vr : ℕ → ℝ)
    (hfrozen :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticFrozenModelNormalizedStatistic K C0 X ≤ Vf X)
    (hresidual :
      ∀ {X : ℕ}, X0 ≤ X →
        routeAGridCenteredQuadraticResidualNormalizedStatistic K C0 X ≤ Vr X) :
    RouteAGridVarianceUpperBound K C0 (fun X => 2 * Vf X + 2 * Vr X) := by
  exact routeAGridVarianceUpperBound_of_frozen_residual_split
    K C0 Vf Vr (routeAPointwiseFrozenResidualSplit_from_visible K) hfrozen hresidual

end

end Goldbach.Cert.MajorArcModules.Q0MinorRouteADenseGridTargets
