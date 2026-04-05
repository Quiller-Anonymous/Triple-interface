import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
import Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassCorrectionSummands

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleWeightedKernel
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge

noncomputable section

local notation "canonicalTrueSeam" =>
  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesOnWindow

/--
The explicit `q`-summand on the weighted-kernel side of the raw half-mass correction problem.

This is the exact finite family suggested by `RawScaleWeightedKernel.lean`: the frozen raw scalar
times the `X⁻¹`-normalized weighted Ramanujan summand `kappaTermR`.
-/
noncomputable def rawHalfMassTrueSeriesCorrectionKappaSummand
    (X q N : ℕ) : ℂ :=
  frozenRawScalarC N (1 : ℝ)
    * ((((X : ℝ) : ℂ)⁻¹) * ((kappaTermR q N : ℝ) : ℂ))

/--
The finite `q ≤ Q0` weighted-kernel sum attached to the explicit correction summands.

This is definitionally aligned with the canonical true-seam arithmetic family, but does not yet
assert that it equals `rawHalfMassTrueSeriesCorrection`.
-/
noncomputable def rawHalfMassTrueSeriesCorrectionKappaSum
    (X N : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
    rawHalfMassTrueSeriesCorrectionKappaSummand X q N

theorem rawHalfMassTrueSeriesCorrectionKappaSum_eq_frozenWeightedMainTermKappaC
    (X N : ℕ) :
    rawHalfMassTrueSeriesCorrectionKappaSum X N = frozenWeightedMainTermKappaC X N := by
  unfold rawHalfMassTrueSeriesCorrectionKappaSum
    rawHalfMassTrueSeriesCorrectionKappaSummand frozenWeightedMainTermKappaC
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        frozenRawScalarC N (1 : ℝ) * ((((X : ℝ) : ℂ)⁻¹) * ((kappaTermR q N : ℝ) : ℂ))
      =
    frozenRawScalarC N (1 : ℝ)
      * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          ((((X : ℝ) : ℂ)⁻¹) * ((kappaTermR q N : ℝ) : ℂ)) := by
            rw [Finset.mul_sum]
    _ =
    frozenRawScalarC N (1 : ℝ)
      * ((((X : ℝ) : ℂ)⁻¹)
          * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
              ((kappaTermR q N : ℝ) : ℂ)) := by
                rw [← Finset.mul_sum]
    _ =
    frozenRawScalarC N (1 : ℝ)
      * ((((X : ℝ) : ℂ)⁻¹)
          * (((∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                kappaTermR q N : ℝ)) : ℂ)) := by
                rw [← Complex.ofReal_sum]
    _ =
    frozenRawScalarC N (1 : ℝ)
      * ((((X : ℝ) : ℂ)⁻¹) * ((kappaLeQ0R N : ℝ) : ℂ)) := by
            rw [kappaLeQ0R_eq_sum_kappaTermR]

/--
Target asserting that the explicit `kappaTermR` summand family really reconstructs the frozen
weighted arithmetic model.

This is a lightweight intermediate seam: the next proof step can establish this first, and then
bridge from the frozen model to `rawHalfMassTrueSeriesCorrection`.
-/
def RawHalfMassTrueSeriesCorrectionKappaSumMatchesFrozenWeightedKernel : Prop :=
  ∀ X N, rawHalfMassTrueSeriesCorrectionKappaSum X N = frozenWeightedMainTermKappaC X N

theorem rawHalfMassTrueSeriesCorrectionKappaSumMatchesFrozenWeightedKernel_true :
    RawHalfMassTrueSeriesCorrectionKappaSumMatchesFrozenWeightedKernel := by
  intro X N
  exact rawHalfMassTrueSeriesCorrectionKappaSum_eq_frozenWeightedMainTermKappaC X N

/--
Raw gap between the true-series correction and the explicit `kappaTermR` finite sum.

This is the scalar-bearing object whose `N`-variation must be eliminated before any meaningful
combined-span diagnostic can be trusted.
-/
noncomputable def rawHalfMassTrueSeriesCorrectionKappaGap
    (X N : ℕ) : ℂ :=
  rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
    - rawHalfMassTrueSeriesCorrectionKappaSum X N

/--
Primary bridge target at the raw level: the `N`-dependence of the correction is exactly the
`kappaTermR` finite sum on the canonical even window.

This is the difference-first formulation. It avoids guessing the `X`-only scalar until the very
end.
-/
structure RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget where
  sub_eq :
    ∀ {X N M : ℕ}, X0 ≤ X → N ∈ EvenIn X H → M ∈ EvenIn X H →
      rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
        - rawHalfMassTrueSeriesCorrection canonicalTrueSeam X M
      =
      rawHalfMassTrueSeriesCorrectionKappaSum X N
        - rawHalfMassTrueSeriesCorrectionKappaSum X M

/--
Difference-first raw bridge target against the frozen weighted kernel.

This remains useful as a reduction artifact and as a record of the exact seam that was tested.
However, the trusted exact-surface numerics show that this is not the live arithmetic endpoint:
the project should not route the main theorem through this target.
-/
structure RawHalfMassTrueSeriesCorrectionFrozenDifferenceTarget where
  sub_eq :
    ∀ {X N M : ℕ}, X0 ≤ X → N ∈ EvenIn X H → M ∈ EvenIn X H →
      rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
        - rawHalfMassTrueSeriesCorrection canonicalTrueSeam X M
      =
      frozenWeightedMainTermKappaC X N - frozenWeightedMainTermKappaC X M

/--
Difference-first raw bridge target for the tail-only observable itself.

This is kept as negative evidence for the discarded frozen-augmented route. It is algebraically
equivalent to the frozen correction-difference target, but the exact-surface diagnostics indicate
that this is not the correct live theorem surface for the arithmetic main term.
-/
structure RawHalfMassTailOnlyFrozenAugmentedDifferenceTarget where
  sub_eq :
    ∀ {X N M : ℕ}, X0 ≤ X → N ∈ EvenIn X H → M ∈ EvenIn X H →
      rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M
        =
      (trueSigmaNormalizedSeries canonicalTrueSeam N + frozenWeightedMainTermKappaC X N)
        - (trueSigmaNormalizedSeries canonicalTrueSeam M + frozenWeightedMainTermKappaC X M)

def RawHalfMassTailOnlyFrozenAugmentedDifferenceTarget.to_frozenDifferenceTarget
    (hT : RawHalfMassTailOnlyFrozenAugmentedDifferenceTarget) :
    RawHalfMassTrueSeriesCorrectionFrozenDifferenceTarget where
  sub_eq := by
    intro X N M hX hN hM
    have hsub := hT.sub_eq (X := X) (N := N) (M := M) hX hN hM
    calc
      rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
          - rawHalfMassTrueSeriesCorrection canonicalTrueSeam X M
        =
      (rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M)
        - (trueSigmaNormalizedSeries canonicalTrueSeam N
            - trueSigmaNormalizedSeries canonicalTrueSeam M) := by
              unfold rawHalfMassTrueSeriesCorrection
              ring
      _ =
      ((trueSigmaNormalizedSeries canonicalTrueSeam N + frozenWeightedMainTermKappaC X N)
          - (trueSigmaNormalizedSeries canonicalTrueSeam M + frozenWeightedMainTermKappaC X M))
        - (trueSigmaNormalizedSeries canonicalTrueSeam N
            - trueSigmaNormalizedSeries canonicalTrueSeam M) := by
              rw [hsub]
      _ = frozenWeightedMainTermKappaC X N - frozenWeightedMainTermKappaC X M := by
            ring

def RawHalfMassTrueSeriesCorrectionFrozenDifferenceTarget.to_tailOnlyAugmentedDifferenceTarget
    (hT : RawHalfMassTrueSeriesCorrectionFrozenDifferenceTarget) :
    RawHalfMassTailOnlyFrozenAugmentedDifferenceTarget where
  sub_eq := by
    intro X N M hX hN hM
    have hsub := hT.sub_eq (X := X) (N := N) (M := M) hX hN hM
    calc
      rawHalfMassTailOnlyObservable X N - rawHalfMassTailOnlyObservable X M
        =
      (rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
          - rawHalfMassTrueSeriesCorrection canonicalTrueSeam X M)
        + (trueSigmaNormalizedSeries canonicalTrueSeam N
            - trueSigmaNormalizedSeries canonicalTrueSeam M) := by
              unfold rawHalfMassTrueSeriesCorrection
              ring
      _ =
      (frozenWeightedMainTermKappaC X N - frozenWeightedMainTermKappaC X M)
        + (trueSigmaNormalizedSeries canonicalTrueSeam N
            - trueSigmaNormalizedSeries canonicalTrueSeam M) := by
              rw [hsub]
      _ =
      (trueSigmaNormalizedSeries canonicalTrueSeam N + frozenWeightedMainTermKappaC X N)
        - (trueSigmaNormalizedSeries canonicalTrueSeam M + frozenWeightedMainTermKappaC X M) := by
            ring

def RawHalfMassTrueSeriesCorrectionFrozenDifferenceTarget.to_kappaDifferenceTarget
    (hT : RawHalfMassTrueSeriesCorrectionFrozenDifferenceTarget) :
    RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget where
  sub_eq := by
    intro X N M hX hN hM
    rw [rawHalfMassTrueSeriesCorrectionKappaSum_eq_frozenWeightedMainTermKappaC,
      rawHalfMassTrueSeriesCorrectionKappaSum_eq_frozenWeightedMainTermKappaC]
    exact hT.sub_eq hX hN hM

theorem RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget.gap_eq
    (hT : RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget)
    {X N M : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) (hM : M ∈ EvenIn X H) :
    rawHalfMassTrueSeriesCorrectionKappaGap X N
      =
    rawHalfMassTrueSeriesCorrectionKappaGap X M := by
  unfold rawHalfMassTrueSeriesCorrectionKappaGap
  have hsub := hT.sub_eq hX hN hM
  ring_nf at hsub ⊢
  exact sub_eq_sub_iff_sub_eq_sub.mp hsub

/-- The canonical-point scalar extracted from the raw gap on the canonical even window. -/
noncomputable def rawHalfMassTrueSeriesCorrectionKappaScalar (X : ℕ) : ℂ :=
  rawHalfMassTrueSeriesCorrectionKappaGap X (canonicalEvenWindowPoint X)

theorem RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget.eq_gap_scalar
    (hT : RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    rawHalfMassTrueSeriesCorrectionKappaGap X N
      =
    rawHalfMassTrueSeriesCorrectionKappaScalar X := by
  unfold rawHalfMassTrueSeriesCorrectionKappaScalar
  exact hT.gap_eq hX hN (canonicalEvenWindowPoint_mem_even_window hX)

/--
Target asserting that the raw half-mass true-series correction is exactly an `X`-only scalar plus
the explicit finite weighted-kernel summand family.

This is now the live bridge theorem on the arithmetic side. It matters because it exposes the
correct exact theorem-level family for the explicit finite-dimensional arithmetic main term used by
the low-rank surface, not because it is expected to force the discarded frozen-augmented target.
-/
structure RawHalfMassTrueSeriesCorrectionKappaExpansionTarget where
  scalarPart : ℕ → ℂ
  eq_scalar_add_sum :
    ∀ X N,
      rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
        =
      scalarPart X + rawHalfMassTrueSeriesCorrectionKappaSum X N

/--
Window-scoped affine expansion target obtained from the raw difference theorem by fixing the
scalar at the canonical even-window point.
-/
structure RawHalfMassTrueSeriesCorrectionKappaWindowExpansionTarget where
  scalarPart : ℕ → ℂ
  eq_scalar_add_sum :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
        =
      scalarPart X + rawHalfMassTrueSeriesCorrectionKappaSum X N

def RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget.to_windowExpansionTarget
    (hT : RawHalfMassTrueSeriesCorrectionKappaDifferenceTarget) :
    RawHalfMassTrueSeriesCorrectionKappaWindowExpansionTarget where
  scalarPart := rawHalfMassTrueSeriesCorrectionKappaScalar
  eq_scalar_add_sum := by
    intro X N hX hN
    have hgap := hT.eq_gap_scalar hX hN
    unfold rawHalfMassTrueSeriesCorrectionKappaGap rawHalfMassTrueSeriesCorrectionKappaScalar at hgap
    exact sub_eq_iff_eq_add.mp hgap

noncomputable def RawHalfMassTrueSeriesCorrectionKappaExpansionTarget.to_summandData
    (hT : RawHalfMassTrueSeriesCorrectionKappaExpansionTarget) :
    RawHalfMassTrueSeriesCorrectionSummandData canonicalTrueSeam where
  scalarPart := hT.scalarPart
  summand := fun X q N => rawHalfMassTrueSeriesCorrectionKappaSummand X q N
  sum_eq := by
    intro X N
    simpa [rawHalfMassTrueSeriesCorrectionKappaSum] using hT.eq_scalar_add_sum X N

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassCorrectionSummands
