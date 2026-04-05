import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailOnly

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering

noncomputable section

/--
Tail-only arithmetic object after exact geometric recentering.

On the canonical even window this is exactly the centered fluctuation, because the recentered shell
vanishes there.
-/
noncomputable def halfMassTailOnlyObservable (X N : ℕ) : ℂ :=
  exactGeometricArithmeticModel X N - halfMassCanonicalAverageWitness X

theorem halfMassCenteredFluctuation_eq_tailOnly_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    halfMassCenteredFluctuation X N = halfMassTailOnlyObservable X N := by
  unfold halfMassTailOnlyObservable
  exact
    halfMassCenteredFluctuation_eq_exactGeometricArithmeticModel_sub_average_of_mem_even_window
      hX hN

/-- Tail-only window energy on the canonical even window. -/
noncomputable def halfMassTailOnlyWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖halfMassTailOnlyObservable X N‖ ^ 2

/--
Direct tail-only window upper bound at scale `X`.

This is the primary arithmetic frontier after exact geometric recentering.
-/
def halfMassTailOnlyWindowUpper (C3 : ℝ) (X : ℕ) : Prop :=
  halfMassTailOnlyWindowEnergy X
    ≤
  C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem halfMassRecenteredVarianceWindowEnergy_eq_tailOnlyWindowEnergy
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassRecenteredVarianceWindowEnergy X = halfMassTailOnlyWindowEnergy X := by
  unfold halfMassRecenteredVarianceWindowEnergy halfMassTailOnlyWindowEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  change ‖halfMassCenteredFluctuation X N‖ ^ 2 = ‖halfMassTailOnlyObservable X N‖ ^ 2
  rw [halfMassCenteredFluctuation_eq_tailOnly_of_mem_even_window hX hN]

theorem halfMassTailOnlyWindowUpper.to_varianceTarget
    {C3 : ℝ} (hC3 : 0 ≤ C3)
    (hTail : ∀ {X : ℕ}, X0 ≤ X → halfMassTailOnlyWindowUpper C3 X) :
    HalfMassArithmeticVarianceTarget 0 C3 := by
  refine ⟨by norm_num, hC3, ?_⟩
  intro X hX
  rw [halfMassRecenteredVarianceWindowEnergy_eq_tailOnlyWindowEnergy hX]
  simpa [halfMassTailOnlyWindowUpper] using hTail hX

/--
Tail-only theorem surface for the arithmetic endpoint after exact geometric recentering.

This is the sharp canonical-window form suggested by the shell vanishing theorem: only the
`1 / (H Q0^2)` term remains live.
-/
structure HalfMassTailOnlyWindowTarget (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      halfMassTailOnlyWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem HalfMassTailOnlyWindowTarget.to_varianceTarget
    {C3 : ℝ} (hTail : HalfMassTailOnlyWindowTarget C3) :
    HalfMassArithmeticVarianceTarget 0 C3 := by
  exact halfMassTailOnlyWindowUpper.to_varianceTarget hTail.C3_nonneg hTail.bound

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailOnly
