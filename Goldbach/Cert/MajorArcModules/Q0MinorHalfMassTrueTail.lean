import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailOnly
import Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailOnly
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering

noncomputable section

/-- Raw window sum of the true normalized sigma tail on the canonical even window. -/
noncomputable def trueSigmaTailWindowRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, normalizedSigmaTail S N

/-- Canonical even-window average of the true normalized sigma tail. -/
noncomputable def trueSigmaTailWindowAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * trueSigmaTailWindowRawSum S X

/-- Raw window sum of the full true normalized singular-series object. -/
noncomputable def trueSigmaWindowRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, trueSigmaNormalizedSeries S N

/-- Canonical even-window average of the full true normalized singular-series object. -/
noncomputable def trueSigmaWindowAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * trueSigmaWindowRawSum S X

/-- Raw window sum of the normalized fixed-`Q0` truncation on the canonical even window. -/
noncomputable def normalizedSigmaTruncWindowRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 S N

/-- Canonical even-window average of the normalized fixed-`Q0` truncation. -/
noncomputable def normalizedSigmaTruncWindowAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * normalizedSigmaTruncWindowRawSum S X

/-- Centered full true normalized singular-series object on the canonical even window. -/
noncomputable def centeredTrueSigmaSeries
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  trueSigmaNormalizedSeries S N - trueSigmaWindowAverage S X

/-- Raw canonical-window arithmetic object after exact geometric recentering. -/
noncomputable def rawHalfMassTailOnlyObservable (X N : ℕ) : ℂ :=
  exactGeometricArithmeticModel X N

/-- Raw gap between the exact-geometric arithmetic object and the full true normalized sigma series. -/
noncomputable def rawHalfMassTrueSeriesCorrection
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  rawHalfMassTailOnlyObservable X N - trueSigmaNormalizedSeries S N

/--
Exact `q ≤ Q0` expansion data for the raw half-mass true-series correction.

An `X`-only scalar term is allowed explicitly. This keeps later span diagnostics honest: if the
correction differs from a pure finite Ramanujan sum by a window-constant scalar, that scalar can be
factored out before centering instead of being silently lost.
-/
structure RawHalfMassTrueSeriesCorrectionSummandData
    (S : TrueSingularSeriesOnWindow) where
  scalarPart : ℕ → ℂ
  summand : ℕ → ℕ → ℕ → ℂ
  sum_eq :
    ∀ X N,
      rawHalfMassTrueSeriesCorrection S X N
        =
      scalarPart X
        + ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, summand X q N

/-- Raw window sum of the uncentered series correction. -/
noncomputable def rawHalfMassTrueSeriesCorrectionWindowRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, rawHalfMassTrueSeriesCorrection S X N

/-- Canonical even-window average of the uncentered series correction. -/
noncomputable def rawHalfMassTrueSeriesCorrectionWindowAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * rawHalfMassTrueSeriesCorrectionWindowRawSum S X

/-- Centered version of the raw series correction on the canonical even window. -/
noncomputable def centeredRawHalfMassTrueSeriesCorrection
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  rawHalfMassTrueSeriesCorrection S X N - rawHalfMassTrueSeriesCorrectionWindowAverage S X

/-- Raw residual between the exact-geometric arithmetic object and the true normalized `q > Q0` tail. -/
noncomputable def rawHalfMassTrueTailResidual
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  rawHalfMassTailOnlyObservable X N - normalizedSigmaTail S N

/--
Finite-truncation combination governing the raw residual on the canonical even window.

This is the algebraic combination
`rawHalfMassTrueSeriesCorrection + normalizedSigmaTruncQ0`
that remains after replacing the full true singular series by truncation plus tail.
-/
noncomputable def rawHalfMassSeriesTruncCombination
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  rawHalfMassTrueSeriesCorrection S X N + normalizedSigmaTruncQ0 S N

/--
The finite-`Q0` combination written explicitly as the raw series correction plus the normalized
`q ≤ Q0` truncation sum.
-/
noncomputable def rawHalfMassSeriesTruncSummedCombination
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  rawHalfMassTrueSeriesCorrection S X N
    + Finset.sum (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0)
        (fun q => normalizedSigmaTruncSummand S q N)

/-- Raw window sum of the uncentered true-tail residual. -/
noncomputable def rawHalfMassTrueTailResidualWindowRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, rawHalfMassTrueTailResidual S X N

/-- Canonical even-window average of the uncentered true-tail residual. -/
noncomputable def rawHalfMassTrueTailResidualWindowAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * rawHalfMassTrueTailResidualWindowRawSum S X

/-- Centered raw residual between the exact-geometric arithmetic object and the true normalized tail. -/
noncomputable def centeredRawHalfMassTrueTailResidual
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  rawHalfMassTrueTailResidual S X N - rawHalfMassTrueTailResidualWindowAverage S X

/-- Centered normalized fixed-`Q0` truncation on the canonical even window. -/
noncomputable def centeredNormalizedSigmaTrunc
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  normalizedSigmaTruncQ0 S N - normalizedSigmaTruncWindowAverage S X

/--
Centered true `q > Q0` singular-series tail on the canonical even window.

This is the corrected arithmetic tail object built from the genuine singular-series seam.
-/
noncomputable def centeredTrueSigmaTail
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  normalizedSigmaTail S N - trueSigmaTailWindowAverage S X

/-- Squared `ℓ²(EvenIn X H)` energy of the centered true sigma tail. -/
noncomputable def centeredTrueSigmaTailWindowEnergy
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredTrueSigmaTail S X N‖ ^ 2

/--
Exact correction between the current half-mass tail-only object and the centered true sigma tail.

If later arithmetic work proves this vanishes on the canonical window, the tail-only frontier is
transported onto the true singular-series seam exactly.
-/
noncomputable def halfMassTrueTailCorrection
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  halfMassTailOnlyObservable X N - centeredTrueSigmaTail S X N

/-- Exact correction between the current half-mass tail-only object and the centered full true sigma series. -/
noncomputable def halfMassTrueSeriesCorrection
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  halfMassTailOnlyObservable X N - centeredTrueSigmaSeries S X N

theorem rawHalfMassTailOnlyObservable_eq_exactGeometricArithmeticModel
    (X N : ℕ) :
    rawHalfMassTailOnlyObservable X N = exactGeometricArithmeticModel X N := by
  rfl

theorem rawHalfMassTrueSeriesCorrection_add_trueSigma_eq_rawTailOnly
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    rawHalfMassTrueSeriesCorrection S X N + trueSigmaNormalizedSeries S N
      = rawHalfMassTailOnlyObservable X N := by
  unfold rawHalfMassTrueSeriesCorrection rawHalfMassTailOnlyObservable
  ring

theorem rawHalfMassTrueSeriesCorrection_eq_rawTailOnly_sub_trueSigma
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    rawHalfMassTrueSeriesCorrection S X N
      = rawHalfMassTailOnlyObservable X N - trueSigmaNormalizedSeries S N := by
  rfl

theorem rawHalfMassTailOnlyObservable_eq_normalizedSigmaTail_add_residual
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    rawHalfMassTailOnlyObservable X N
      =
    normalizedSigmaTail S N + rawHalfMassTrueTailResidual S X N := by
  unfold rawHalfMassTrueTailResidual
  ring

theorem rawHalfMassTailOnlyObservable_sub_eq_normalizedSigmaTail_sub_add_residual_sub
    (S : TrueSingularSeriesOnWindow) (X N M : ℕ) :
    rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M
      =
    (normalizedSigmaTail S N - normalizedSigmaTail S M)
      + (rawHalfMassTrueTailResidual S X N - rawHalfMassTrueTailResidual S X M) := by
  unfold rawHalfMassTrueTailResidual
  ring

theorem rawHalfMassTailOnlyObservable_sub_eq_normalizedSigmaTail_sub_of_residual_eq
    (S : TrueSingularSeriesOnWindow) (X N M : ℕ)
    (hres : rawHalfMassTrueTailResidual S X N = rawHalfMassTrueTailResidual S X M) :
    rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M
      =
    normalizedSigmaTail S N - normalizedSigmaTail S M := by
  rw [rawHalfMassTailOnlyObservable_sub_eq_normalizedSigmaTail_sub_add_residual_sub]
  rw [hres]
  ring

theorem rawHalfMassTrueTailResidual_eq_of_sub_eq_normalizedSigmaTail_sub
    (S : TrueSingularSeriesOnWindow) (X N M : ℕ)
    (hsub : rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M
      = normalizedSigmaTail S N - normalizedSigmaTail S M) :
    rawHalfMassTrueTailResidual S X N = rawHalfMassTrueTailResidual S X M := by
  rw [rawHalfMassTailOnlyObservable_sub_eq_normalizedSigmaTail_sub_add_residual_sub (S := S)] at hsub
  have hsub' :
      (normalizedSigmaTail S N - normalizedSigmaTail S M)
        + (rawHalfMassTrueTailResidual S X N - rawHalfMassTrueTailResidual S X M)
        =
      (normalizedSigmaTail S N - normalizedSigmaTail S M) + 0 := by
    simpa using hsub
  have hzero' : rawHalfMassTrueTailResidual S X N - rawHalfMassTrueTailResidual S X M = 0 := by
    exact add_left_cancel hsub'
  exact sub_eq_zero.mp hzero'

theorem rawHalfMassTrueSeriesCorrection_eq_neg_trunc_add_residual_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    rawHalfMassTrueSeriesCorrection S X N
      =
    -normalizedSigmaTruncQ0 S N + rawHalfMassTrueTailResidual S X N := by
  unfold rawHalfMassTrueSeriesCorrection rawHalfMassTrueTailResidual
  rw [(trueSigmaNormalizedSeries_sub_trunc_eq_tail_of_mem_even_window S hX hN).symm]
  ring

theorem rawHalfMassTrueTailResidual_eq_seriesCorrection_add_trunc_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    rawHalfMassTrueTailResidual S X N
      =
    rawHalfMassTrueSeriesCorrection S X N + normalizedSigmaTruncQ0 S N := by
  rw [rawHalfMassTrueSeriesCorrection_eq_neg_trunc_add_residual_of_mem_even_window S hX hN]
  ring

theorem rawHalfMassSeriesTruncCombination_eq_residual_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    rawHalfMassSeriesTruncCombination S X N
      =
    rawHalfMassTrueTailResidual S X N := by
  unfold rawHalfMassSeriesTruncCombination
  rw [rawHalfMassTrueTailResidual_eq_seriesCorrection_add_trunc_of_mem_even_window S hX hN]

theorem rawHalfMassSeriesTruncCombination_eq_summedCombination
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    rawHalfMassSeriesTruncCombination S X N
      =
    rawHalfMassSeriesTruncSummedCombination S X N := by
  unfold rawHalfMassSeriesTruncCombination rawHalfMassSeriesTruncSummedCombination
  rw [normalizedSigmaTruncQ0_eq_sum_truncSummand]

theorem rawHalfMassTrueSeriesCorrectionWindowRawSum_eq_tailOnlyRawSum_sub_trueSigmaRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) :
    rawHalfMassTrueSeriesCorrectionWindowRawSum S X
      =
    (∑ N ∈ EvenIn X H, rawHalfMassTailOnlyObservable X N) - trueSigmaWindowRawSum S X := by
  unfold rawHalfMassTrueSeriesCorrectionWindowRawSum rawHalfMassTrueSeriesCorrection
    rawHalfMassTailOnlyObservable trueSigmaWindowRawSum
  rw [Finset.sum_sub_distrib]

theorem rawHalfMassTrueSeriesCorrectionWindowAverage_eq_tailOnlyAverage_sub_trueSigmaAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) :
    rawHalfMassTrueSeriesCorrectionWindowAverage S X
      =
    ((EvenIn X H).card : ℂ)⁻¹ * (∑ N ∈ EvenIn X H, rawHalfMassTailOnlyObservable X N)
      - trueSigmaWindowAverage S X := by
  unfold rawHalfMassTrueSeriesCorrectionWindowAverage trueSigmaWindowAverage
  rw [rawHalfMassTrueSeriesCorrectionWindowRawSum_eq_tailOnlyRawSum_sub_trueSigmaRawSum]
  rw [mul_sub]

theorem rawHalfMassTrueTailResidualWindowRawSum_eq_tailOnlyRawSum_sub_trueTailRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) :
    rawHalfMassTrueTailResidualWindowRawSum S X
      =
    (∑ N ∈ EvenIn X H, rawHalfMassTailOnlyObservable X N) - trueSigmaTailWindowRawSum S X := by
  unfold rawHalfMassTrueTailResidualWindowRawSum rawHalfMassTrueTailResidual
    rawHalfMassTailOnlyObservable trueSigmaTailWindowRawSum
  rw [Finset.sum_sub_distrib]

theorem rawHalfMassTrueTailResidualWindowAverage_eq_tailOnlyAverage_sub_trueTailAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) :
    rawHalfMassTrueTailResidualWindowAverage S X
      =
    ((EvenIn X H).card : ℂ)⁻¹ * (∑ N ∈ EvenIn X H, rawHalfMassTailOnlyObservable X N)
      - trueSigmaTailWindowAverage S X := by
  unfold rawHalfMassTrueTailResidualWindowAverage trueSigmaTailWindowAverage
  rw [rawHalfMassTrueTailResidualWindowRawSum_eq_tailOnlyRawSum_sub_trueTailRawSum]
  rw [mul_sub]

theorem halfMassTrueSeriesCorrection_eq_centeredRawSeriesCorrection
    (S : TrueSingularSeriesOnWindow) {X N : ℕ} (hX : X0 ≤ X) :
    halfMassTrueSeriesCorrection S X N
      = centeredRawHalfMassTrueSeriesCorrection S X N := by
  have hsum :
      ∑ M ∈ EvenIn X H, rawHalfMassTailOnlyObservable X M
        =
      ∑ M ∈ EvenIn X H, Q0MinorZeroModeEnvelope.halfMassRecenteredZeroModeObservable X M := by
    unfold rawHalfMassTailOnlyObservable
    refine Finset.sum_congr rfl ?_
    intro M hM
    exact (halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window hX hM).symm
  unfold halfMassTrueSeriesCorrection centeredRawHalfMassTrueSeriesCorrection
    halfMassTailOnlyObservable centeredTrueSigmaSeries rawHalfMassTrueSeriesCorrection
    rawHalfMassTrueSeriesCorrectionWindowAverage trueSigmaWindowAverage
    rawHalfMassTailOnlyObservable
  unfold Q0MinorHalfMassArithmeticBoundary.halfMassCanonicalAverageWitness
    Q0MinorHalfMassArithmeticBoundary.halfMassRecenteredWindowAverage
    Q0MinorHalfMassArithmeticBoundary.halfMassWindowRawSum
  rw [rawHalfMassTrueSeriesCorrectionWindowRawSum_eq_tailOnlyRawSum_sub_trueSigmaRawSum]
  rw [hsum]
  ring

theorem halfMassTrueSeriesCorrection_eq_neg_centeredTrunc_add_centeredResidual_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    halfMassTrueSeriesCorrection S X N
      =
    -centeredNormalizedSigmaTrunc S X N + centeredRawHalfMassTrueTailResidual S X N := by
  have hTailRaw :
      trueSigmaTailWindowRawSum S X
        =
      trueSigmaWindowRawSum S X - normalizedSigmaTruncWindowRawSum S X := by
    unfold trueSigmaTailWindowRawSum trueSigmaWindowRawSum normalizedSigmaTruncWindowRawSum
    calc
      ∑ N ∈ EvenIn X H, normalizedSigmaTail S N
          = ∑ N ∈ EvenIn X H,
              (trueSigmaNormalizedSeries S N - normalizedSigmaTruncQ0 S N) := by
                refine Finset.sum_congr rfl ?_
                intro M hM
                rw [trueSigmaNormalizedSeries_sub_trunc_eq_tail_of_mem_even_window S hX hM]
      _ =
        (∑ N ∈ EvenIn X H, trueSigmaNormalizedSeries S N)
          - ∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 S N := by
            rw [Finset.sum_sub_distrib]
  rw [halfMassTrueSeriesCorrection_eq_centeredRawSeriesCorrection S hX]
  unfold centeredRawHalfMassTrueSeriesCorrection centeredNormalizedSigmaTrunc
    centeredRawHalfMassTrueTailResidual rawHalfMassTrueSeriesCorrection
    rawHalfMassTrueTailResidual rawHalfMassTrueSeriesCorrectionWindowAverage
    rawHalfMassTrueTailResidualWindowAverage normalizedSigmaTruncWindowAverage
  rw [(trueSigmaNormalizedSeries_sub_trunc_eq_tail_of_mem_even_window S hX hN).symm]
  rw [rawHalfMassTrueSeriesCorrectionWindowRawSum_eq_tailOnlyRawSum_sub_trueSigmaRawSum]
  rw [rawHalfMassTrueTailResidualWindowRawSum_eq_tailOnlyRawSum_sub_trueTailRawSum]
  rw [hTailRaw]
  ring_nf

theorem halfMassTailOnlyObservable_eq_centeredTrueSigmaSeries_add_seriesCorrection
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    halfMassTailOnlyObservable X N
      =
    centeredTrueSigmaSeries S X N + halfMassTrueSeriesCorrection S X N := by
  unfold halfMassTrueSeriesCorrection
  ring

theorem trueSigmaTailWindowRawSum_eq_trueSigmaWindowRawSum_sub_truncRawSum
    (S : TrueSingularSeriesOnWindow) {X : ℕ} (hX : X0 ≤ X) :
    trueSigmaTailWindowRawSum S X
      =
    trueSigmaWindowRawSum S X - normalizedSigmaTruncWindowRawSum S X := by
  unfold trueSigmaTailWindowRawSum trueSigmaWindowRawSum normalizedSigmaTruncWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, normalizedSigmaTail S N
        = ∑ N ∈ EvenIn X H,
            (trueSigmaNormalizedSeries S N - normalizedSigmaTruncQ0 S N) := by
              refine Finset.sum_congr rfl ?_
              intro N hN
              rw [trueSigmaNormalizedSeries_sub_trunc_eq_tail_of_mem_even_window S hX hN]
    _ =
      (∑ N ∈ EvenIn X H, trueSigmaNormalizedSeries S N)
        - ∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 S N := by
          rw [Finset.sum_sub_distrib]

theorem trueSigmaTailWindowAverage_eq_trueSigmaWindowAverage_sub_truncAverage
    (S : TrueSingularSeriesOnWindow) {X : ℕ} (hX : X0 ≤ X) :
    trueSigmaTailWindowAverage S X
      =
    trueSigmaWindowAverage S X - normalizedSigmaTruncWindowAverage S X := by
  unfold trueSigmaTailWindowAverage trueSigmaWindowAverage normalizedSigmaTruncWindowAverage
  rw [trueSigmaTailWindowRawSum_eq_trueSigmaWindowRawSum_sub_truncRawSum S hX]
  rw [mul_sub]

theorem centeredTrueSigmaTail_eq_centeredTrueSigmaSeries_sub_centeredTrunc_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    centeredTrueSigmaTail S X N
      = centeredTrueSigmaSeries S X N - centeredNormalizedSigmaTrunc S X N := by
  unfold centeredTrueSigmaTail centeredTrueSigmaSeries centeredNormalizedSigmaTrunc
  rw [(trueSigmaNormalizedSeries_sub_trunc_eq_tail_of_mem_even_window S hX hN).symm]
  rw [trueSigmaTailWindowAverage_eq_trueSigmaWindowAverage_sub_truncAverage S hX]
  ring

theorem halfMassTrueTailCorrection_eq_seriesCorrection_add_centeredTrunc_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    halfMassTrueTailCorrection S X N
      = halfMassTrueSeriesCorrection S X N + centeredNormalizedSigmaTrunc S X N := by
  unfold halfMassTrueTailCorrection halfMassTrueSeriesCorrection
  rw [centeredTrueSigmaTail_eq_centeredTrueSigmaSeries_sub_centeredTrunc_of_mem_even_window S hX hN]
  ring

theorem halfMassTrueTailCorrection_eq_centeredTrunc_of_mem_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hSeries : halfMassTailOnlyObservable X N = centeredTrueSigmaSeries S X N) :
    halfMassTrueTailCorrection S X N = centeredNormalizedSigmaTrunc S X N := by
  rw [halfMassTrueTailCorrection_eq_seriesCorrection_add_centeredTrunc_of_mem_even_window S hX hN]
  unfold halfMassTrueSeriesCorrection
  rw [hSeries]
  ring

theorem halfMassTailOnlyObservable_eq_centeredTrueSigmaTail_add_correction
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) :
    halfMassTailOnlyObservable X N
      =
    centeredTrueSigmaTail S X N + halfMassTrueTailCorrection S X N := by
  unfold halfMassTrueTailCorrection
  ring

theorem centeredRawHalfMassTrueTailResidual_eq_zero_of_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) {ρ : ℂ}
    (hconst : ∀ {M : ℕ}, M ∈ EvenIn X H → rawHalfMassTrueTailResidual S X M = ρ) :
    centeredRawHalfMassTrueTailResidual S X N = 0 := by
  have hsum :
      rawHalfMassTrueTailResidualWindowRawSum S X = ((EvenIn X H).card : ℂ) * ρ := by
    unfold rawHalfMassTrueTailResidualWindowRawSum
    calc
      ∑ M ∈ EvenIn X H, rawHalfMassTrueTailResidual S X M
          = ∑ M ∈ EvenIn X H, ρ := by
              refine Finset.sum_congr rfl ?_
              intro M hM
              exact hconst hM
      _ = ((EvenIn X H).card : ℂ) * ρ := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : (EvenIn X H).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr ⟨canonicalEvenWindowPoint X, canonicalEvenWindowPoint_mem_even_window⟩
  have hcard : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  unfold centeredRawHalfMassTrueTailResidual rawHalfMassTrueTailResidualWindowAverage
  rw [hconst hN, hsum]
  have havg : ((↑(EvenIn X H).card : ℂ)⁻¹ * (((EvenIn X H).card : ℂ) * ρ)) = ρ := by
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  rw [havg]
  ring

theorem halfMassTailOnlyObservable_eq_centeredTrueSigmaTail_of_residual_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) {ρ : ℂ}
    (hconst : ∀ {M : ℕ}, M ∈ EvenIn X H → rawHalfMassTrueTailResidual S X M = ρ) :
    halfMassTailOnlyObservable X N = centeredTrueSigmaTail S X N := by
  have hcenter :
      centeredRawHalfMassTrueTailResidual S X N = 0 :=
    centeredRawHalfMassTrueTailResidual_eq_zero_of_constant_on_even_window S hX hN hconst
  rw [halfMassTailOnlyObservable_eq_centeredTrueSigmaSeries_add_seriesCorrection]
  rw [halfMassTrueSeriesCorrection_eq_neg_centeredTrunc_add_centeredResidual_of_mem_even_window S hX hN]
  rw [hcenter]
  rw [centeredTrueSigmaTail_eq_centeredTrueSigmaSeries_sub_centeredTrunc_of_mem_even_window S hX hN]
  ring

theorem halfMassTailOnlyObservable_eq_centeredTrueSigmaTail_of_residual_zero_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hzero : ∀ {M : ℕ}, M ∈ EvenIn X H → rawHalfMassTrueTailResidual S X M = 0) :
    halfMassTailOnlyObservable X N = centeredTrueSigmaTail S X N := by
  exact halfMassTailOnlyObservable_eq_centeredTrueSigmaTail_of_residual_constant_on_even_window
    S hX hN hzero

theorem rawHalfMassTrueTailResidual_eq_canonical_of_pairwise_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2) :
    rawHalfMassTrueTailResidual S X N
      =
    rawHalfMassTrueTailResidual S X (canonicalEvenWindowPoint X) := by
  exact hpair hN canonicalEvenWindowPoint_mem_even_window

theorem rawHalfMassSeriesTruncCombination_eq_canonical_of_pairwise_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassSeriesTruncCombination S X M1 = rawHalfMassSeriesTruncCombination S X M2) :
    rawHalfMassSeriesTruncCombination S X N
      =
    rawHalfMassSeriesTruncCombination S X (canonicalEvenWindowPoint X) := by
  exact hpair hN canonicalEvenWindowPoint_mem_even_window

theorem rawHalfMassTailOnlyObservable_eq_normalizedSigmaTail_add_canonicalResidual_of_residual_pairwise_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2) :
    rawHalfMassTailOnlyObservable X N
      =
    normalizedSigmaTail S N
      + rawHalfMassTrueTailResidual S X (canonicalEvenWindowPoint X) := by
  rw [rawHalfMassTailOnlyObservable_eq_normalizedSigmaTail_add_residual]
  rw [rawHalfMassTrueTailResidual_eq_canonical_of_pairwise_constant_on_even_window S hX hN hpair]

theorem rawHalfMassTailOnlyObservable_sub_eq_normalizedSigmaTail_sub_of_residual_pairwise_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N M : ℕ}
    (hN : N ∈ EvenIn X H) (hM : M ∈ EvenIn X H)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2) :
    rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M
      =
    normalizedSigmaTail S N - normalizedSigmaTail S M := by
  refine rawHalfMassTailOnlyObservable_sub_eq_normalizedSigmaTail_sub_of_residual_eq S X N M ?_
  exact hpair hN hM

theorem rawHalfMassTrueTailResidual_pairwise_constant_on_even_window_of_canonicalResidual_formula
    (S : TrueSingularSeriesOnWindow) {X : ℕ}
    (hX : X0 ≤ X)
    (haff : ∀ {N : ℕ}, N ∈ EvenIn X H →
      rawHalfMassTailOnlyObservable X N
        =
      normalizedSigmaTail S N
        + rawHalfMassTrueTailResidual S X (canonicalEvenWindowPoint X)) :
    ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2 := by
  intro M1 M2 hM1 hM2
  have h1 : rawHalfMassTrueTailResidual S X M1
      = rawHalfMassTrueTailResidual S X (canonicalEvenWindowPoint X) := by
    refine rawHalfMassTrueTailResidual_eq_of_sub_eq_normalizedSigmaTail_sub S X M1 (canonicalEvenWindowPoint X) ?_
    rw [haff hM1, haff canonicalEvenWindowPoint_mem_even_window]
    ring
  have h2 : rawHalfMassTrueTailResidual S X M2
      = rawHalfMassTrueTailResidual S X (canonicalEvenWindowPoint X) := by
    refine rawHalfMassTrueTailResidual_eq_of_sub_eq_normalizedSigmaTail_sub S X M2 (canonicalEvenWindowPoint X) ?_
    rw [haff hM2, haff canonicalEvenWindowPoint_mem_even_window]
    ring
  rw [h1, h2]

theorem rawHalfMassSeriesTruncCombination_pairwise_constant_on_even_window_of_residual_pairwise_constant
    (S : TrueSingularSeriesOnWindow) {X : ℕ}
    (hX : X0 ≤ X)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2) :
    ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassSeriesTruncCombination S X M1 = rawHalfMassSeriesTruncCombination S X M2 := by
  intro M1 M2 hM1 hM2
  rw [rawHalfMassSeriesTruncCombination_eq_residual_of_mem_even_window S hX hM1]
  rw [rawHalfMassSeriesTruncCombination_eq_residual_of_mem_even_window S hX hM2]
  exact hpair hM1 hM2

theorem rawHalfMassTrueTailResidual_pairwise_constant_on_even_window_of_seriesTruncCombination_pairwise_constant
    (S : TrueSingularSeriesOnWindow) {X : ℕ}
    (hX : X0 ≤ X)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassSeriesTruncCombination S X M1 = rawHalfMassSeriesTruncCombination S X M2) :
    ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2 := by
  intro M1 M2 hM1 hM2
  rw [← rawHalfMassSeriesTruncCombination_eq_residual_of_mem_even_window S hX hM1]
  rw [← rawHalfMassSeriesTruncCombination_eq_residual_of_mem_even_window S hX hM2]
  exact hpair hM1 hM2

theorem halfMassTailOnlyObservable_eq_centeredTrueSigmaTail_of_residual_pairwise_constant_on_even_window
    (S : TrueSingularSeriesOnWindow) {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hpair : ∀ {M1 M2 : ℕ}, M1 ∈ EvenIn X H → M2 ∈ EvenIn X H →
      rawHalfMassTrueTailResidual S X M1 = rawHalfMassTrueTailResidual S X M2) :
    halfMassTailOnlyObservable X N = centeredTrueSigmaTail S X N := by
  refine halfMassTailOnlyObservable_eq_centeredTrueSigmaTail_of_residual_constant_on_even_window
    (S := S) (hX := hX) (hN := hN)
    (ρ := rawHalfMassTrueTailResidual S X (canonicalEvenWindowPoint X)) ?_
  intro M hM
  exact hpair hM canonicalEvenWindowPoint_mem_even_window

theorem centeredTrueSigmaTailWindowEnergy_eq_tailOnlyWindowEnergy_of_eq
    (S : TrueSingularSeriesOnWindow)
    {X : ℕ}
    (hEq : ∀ N ∈ EvenIn X H, halfMassTailOnlyObservable X N = centeredTrueSigmaTail S X N) :
    centeredTrueSigmaTailWindowEnergy S X = halfMassTailOnlyWindowEnergy X := by
  unfold centeredTrueSigmaTailWindowEnergy halfMassTailOnlyWindowEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [← hEq N hN]

/--
Transport from an exact identification with the centered true sigma tail to the direct
tail-only arithmetic frontier.
-/
theorem halfMassTailOnlyWindowUpper_of_trueTail
    (S : TrueSingularSeriesOnWindow)
    {C3 : ℝ} {X : ℕ}
    (hEq : ∀ N ∈ EvenIn X H, halfMassTailOnlyObservable X N = centeredTrueSigmaTail S X N)
    (hBound : centeredTrueSigmaTailWindowEnergy S X
      ≤ C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) :
    halfMassTailOnlyWindowUpper C3 X := by
  unfold halfMassTailOnlyWindowUpper
  rw [← centeredTrueSigmaTailWindowEnergy_eq_tailOnlyWindowEnergy_of_eq S hEq]
  exact hBound

/--
The true-tail theorem surface mirroring the direct half-mass tail-only frontier.
-/
structure CenteredTrueSigmaTailWindowTarget
    (S : TrueSingularSeriesOnWindow) (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredTrueSigmaTailWindowEnergy S X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem CenteredTrueSigmaTailWindowTarget.to_tailOnlyWindowUpper
    (S : TrueSingularSeriesOnWindow) {C3 : ℝ}
    (hT : CenteredTrueSigmaTailWindowTarget S C3)
    (hEq : ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      halfMassTailOnlyObservable X N = centeredTrueSigmaTail S X N) :
    ∀ {X : ℕ}, X0 ≤ X → halfMassTailOnlyWindowUpper C3 X := by
  intro X hX
  exact halfMassTailOnlyWindowUpper_of_trueTail S
    (hEq := fun N hN => hEq hX hN)
    (hBound := hT.bound hX)

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
