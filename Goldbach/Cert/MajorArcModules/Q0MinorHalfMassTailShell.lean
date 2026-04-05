import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

/-!
Centered tail/shell decomposition surface for the arithmetic half-mass endpoint.

This file intentionally avoids reopening the scalar-identification layer.  The live arithmetic
task is to control the centered half-mass fluctuation on `EvenIn X H` by splitting it into:

* a centered arithmetic tail term, expected to contribute the `1 / (H Q0^2)` budget;
* a centered shell/geometric residual, expected to contribute the `H / X` budget.

Once those two centered pieces are controlled, the variance target follows by the elementary
quadratic inequality `‖u + v‖^2 ≤ 2‖u‖^2 + 2‖v‖^2`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

/--
Arithmetic-model part of the half-mass observable: keep the intrinsic unscaled post-`σ` ratio and
only reinstall the fixed `X`-dependent zero-slice normalization.
-/
noncomputable def halfMassArithmeticModel (X N : ℕ) : ℂ :=
  (geometricZeroSliceNormalization X)⁻¹ * unscaledZeroModeMassRatioObservable X N

/--
Shell/geometric residual at the half-mass level: the exact gap between the fully recentered
observable and the arithmetic model with fixed normalization.
-/
noncomputable def halfMassShellResidual (X N : ℕ) : ℂ :=
  halfMassRecenteredZeroModeObservable X N - halfMassArithmeticModel X N

/--
Exact shell formula: the shell residual is the arithmetic model multiplied by the unscaled
half-mass deviation of the geometric zero slice.
-/
theorem halfMassShellResidual_eq_two_mul_arithmeticModel_mul_halfMassError
    (X N : ℕ) (hunscaled : unscaledGeometricZeroSliceMass X N ≠ 0) :
    halfMassShellResidual X N
      =
    (2 : ℂ) * halfMassArithmeticModel X N * unscaledGeometricZeroSliceHalfMassError X N := by
  unfold halfMassShellResidual halfMassArithmeticModel
    halfMassRecenteredZeroModeObservable unscaledZeroModeMassRatioObservable
    unscaledGeometricZeroSliceHalfMassError unscaledGeometricZeroSliceHalfMass
  have hhalf : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by norm_num
  field_simp [hunscaled, hhalf]
  norm_num
  ring_nf

/--
Exact ratio formula for the arithmetic-model term in terms of the half-mass observable and the
unscaled geometric zero slice.
-/
theorem halfMassArithmeticModel_eq_halfMassRecentered_mul_halfMass_div_unscaled
    (X N : ℕ) :
    halfMassArithmeticModel X N
      =
    halfMassRecenteredZeroModeObservable X N
      * (unscaledGeometricZeroSliceHalfMass / unscaledGeometricZeroSliceMass X N) := by
  unfold halfMassArithmeticModel halfMassRecenteredZeroModeObservable
    unscaledZeroModeMassRatioObservable unscaledGeometricZeroSliceHalfMass
  rw [div_eq_mul_inv, div_eq_mul_inv]
  norm_num
  ring_nf

/--
Exact shell formula with the denominator isolated in the unscaled geometric zero slice.

This is the form directly suited to a future pointwise lower/upper comparison for the geometric
zero slice on the canonical window.
-/
theorem halfMassShellResidual_eq_halfMassRecentered_mul_error_div_unscaled
    (X N : ℕ) (hunscaled : unscaledGeometricZeroSliceMass X N ≠ 0) :
    halfMassShellResidual X N
      =
    halfMassRecenteredZeroModeObservable X N
      * (unscaledGeometricZeroSliceHalfMassError X N / unscaledGeometricZeroSliceMass X N) := by
  rw [halfMassShellResidual_eq_two_mul_arithmeticModel_mul_halfMassError X N hunscaled]
  rw [halfMassArithmeticModel_eq_halfMassRecentered_mul_halfMass_div_unscaled X N]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  unfold unscaledGeometricZeroSliceHalfMass
  norm_num
  ring_nf

/-- Exact decomposition of the half-mass observable into arithmetic model plus shell residual. -/
theorem halfMassRecenteredZeroModeObservable_eq_arithmeticModel_add_shellResidual
    (X N : ℕ) :
    halfMassRecenteredZeroModeObservable X N
      = halfMassArithmeticModel X N + halfMassShellResidual X N := by
  unfold halfMassShellResidual
  ring

/-- Raw window sum of the arithmetic-model part on the canonical even window. -/
noncomputable def halfMassArithmeticModelWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, halfMassArithmeticModel X N

/-- Raw window sum of the shell residual on the canonical even window. -/
noncomputable def halfMassShellResidualWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, halfMassShellResidual X N

/-- Canonical even-window average of the arithmetic-model part. -/
noncomputable def halfMassArithmeticModelWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * halfMassArithmeticModelWindowRawSum X

/-- Canonical even-window average of the shell residual. -/
noncomputable def halfMassShellResidualWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * halfMassShellResidualWindowRawSum X

/-- Centered arithmetic-model fluctuation on the canonical even window. -/
noncomputable def centeredHalfMassTailTerm (X N : ℕ) : ℂ :=
  halfMassArithmeticModel X N - halfMassArithmeticModelWindowAverage X

/-- Centered shell residual on the canonical even window. -/
noncomputable def centeredHalfMassShellResidual (X N : ℕ) : ℂ :=
  halfMassShellResidual X N - halfMassShellResidualWindowAverage X

/--
The canonical half-mass window average splits exactly into the arithmetic-model average plus the
shell-residual average.
-/
private theorem halfMassWindowRawSum_eq_arithmeticModelRawSum_add_shellResidualRawSum
    (X : ℕ) :
    halfMassWindowRawSum X
      =
    halfMassArithmeticModelWindowRawSum X + halfMassShellResidualWindowRawSum X := by
  unfold halfMassWindowRawSum
    halfMassArithmeticModelWindowRawSum halfMassShellResidualWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, halfMassRecenteredZeroModeObservable X N
      =
    ∑ N ∈ EvenIn X H, (halfMassArithmeticModel X N + halfMassShellResidual X N) := by
      refine Finset.sum_congr rfl ?_
      intro N hN
      rw [halfMassRecenteredZeroModeObservable_eq_arithmeticModel_add_shellResidual]
    _ =
      (∑ N ∈ EvenIn X H, halfMassArithmeticModel X N)
        + ∑ N ∈ EvenIn X H, halfMassShellResidual X N := by
      rw [Finset.sum_add_distrib]

theorem halfMassWindowAverage_eq_arithmeticModelAverage_add_shellResidualAverage
    (X : ℕ) :
    halfMassRecenteredWindowAverage X
      =
    halfMassArithmeticModelWindowAverage X + halfMassShellResidualWindowAverage X := by
  unfold halfMassRecenteredWindowAverage
    halfMassArithmeticModelWindowAverage halfMassShellResidualWindowAverage
  rw [halfMassWindowRawSum_eq_arithmeticModelRawSum_add_shellResidualRawSum]
  rw [show halfMassArithmeticModelWindowRawSum X
      = ∑ N ∈ EvenIn X H, halfMassArithmeticModel X N by rfl]
  rw [show halfMassShellResidualWindowRawSum X
      = ∑ N ∈ EvenIn X H, halfMassShellResidual X N by rfl]
  rw [mul_add]

/-- The centered arithmetic theorem surface: the fluctuation splits into tail plus shell. -/
structure HalfMassCenteredDecomposition where
  tailTerm : ℕ → ℕ → ℂ
  shellResidual : ℕ → ℕ → ℂ
  centered_eq :
    ∀ X N,
      halfMassCenteredFluctuation X N = tailTerm X N + shellResidual X N

/-- Canonical centered tail/shell decomposition at the half-mass level. -/
noncomputable def canonicalHalfMassCenteredDecomposition : HalfMassCenteredDecomposition where
  tailTerm := centeredHalfMassTailTerm
  shellResidual := centeredHalfMassShellResidual
  centered_eq := by
    intro X N
    unfold halfMassCenteredFluctuation halfMassCanonicalAverageWitness
      centeredHalfMassTailTerm centeredHalfMassShellResidual
    rw [halfMassRecenteredZeroModeObservable_eq_arithmeticModel_add_shellResidual]
    rw [halfMassWindowAverage_eq_arithmeticModelAverage_add_shellResidualAverage]
    ring

/-- Window energy of the centered arithmetic tail term. -/
noncomputable def centeredHalfMassTailWindowEnergy
    (d : HalfMassCenteredDecomposition) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖d.tailTerm X N‖ ^ 2

/-- Window energy of the centered shell/geometric residual term. -/
noncomputable def centeredHalfMassShellWindowEnergy
    (d : HalfMassCenteredDecomposition) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖d.shellResidual X N‖ ^ 2

/-- Raw window energy of the uncentered shell residual. -/
noncomputable def halfMassShellResidualWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2

/--
Exact shell-energy rewrite under nonvanishing of the unscaled geometric zero slice on the
canonical window.

This isolates the shell contribution as a weighted window energy of the existing half-mass error
layer `unscaledGeometricZeroSliceHalfMassError`.
-/
theorem halfMassShellResidualWindowEnergy_eq_weighted_halfMassError
    (X : ℕ)
    (hNZ : ∀ N ∈ EvenIn X H, unscaledGeometricZeroSliceMass X N ≠ 0) :
    halfMassShellResidualWindowEnergy X
      =
    ∑ N ∈ EvenIn X H,
      4 * ‖halfMassArithmeticModel X N‖ ^ 2 * ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2 := by
  unfold halfMassShellResidualWindowEnergy
  apply Finset.sum_congr rfl
  intro N hN
  rw [halfMassShellResidual_eq_two_mul_arithmeticModel_mul_halfMassError X N (hNZ N hN)]
  rw [norm_mul, norm_mul]
  norm_num [pow_two]
  ring

/--
Alternative exact shell-energy rewrite with the denominator isolated in the unscaled geometric zero
slice.
-/
theorem halfMassShellResidualWindowEnergy_eq_weighted_error_div_unscaled
    (X : ℕ)
    (hNZ : ∀ N ∈ EvenIn X H, unscaledGeometricZeroSliceMass X N ≠ 0) :
    halfMassShellResidualWindowEnergy X
      =
    ∑ N ∈ EvenIn X H,
      ‖halfMassRecenteredZeroModeObservable X N‖ ^ 2
        * ‖unscaledGeometricZeroSliceHalfMassError X N / unscaledGeometricZeroSliceMass X N‖ ^ 2 := by
  unfold halfMassShellResidualWindowEnergy
  apply Finset.sum_congr rfl
  intro N hN
  rw [halfMassShellResidual_eq_halfMassRecentered_mul_error_div_unscaled X N (hNZ N hN)]
  rw [norm_mul]
  ring

/--
Pointwise canonical-window comparison target for the unscaled geometric zero slice.

This is stated on norms because the zero-slice mass is currently packaged as a complex quantity.
-/
structure UnscaledGeometricZeroSliceMassWindowNormTarget (c0 c1 : ℝ) : Prop where
  c0_pos : 0 < c0
  c1_nonneg : 0 ≤ c1
  lower :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → c0 ≤ ‖unscaledGeometricZeroSliceMass X N‖
  upper :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → ‖unscaledGeometricZeroSliceMass X N‖ ≤ c1

theorem UnscaledGeometricZeroSliceMassWindowNormTarget.nonzero
    {c0 c1 : ℝ} (hT : UnscaledGeometricZeroSliceMassWindowNormTarget c0 c1)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    unscaledGeometricZeroSliceMass X N ≠ 0 := by
  have hlow : c0 ≤ ‖unscaledGeometricZeroSliceMass X N‖ := hT.lower hX hN
  have hnorm_pos : 0 < ‖unscaledGeometricZeroSliceMass X N‖ := by
    exact lt_of_lt_of_le hT.c0_pos hlow
  intro hz
  have hnorm_zero : ‖unscaledGeometricZeroSliceMass X N‖ = 0 := by simp [hz]
  linarith

/--
Route-sized target for the centered arithmetic tail contribution.

This is where the `1 / (H Q0^2)` term is intended to enter.
-/
structure HalfMassTailWindowTarget (d : HalfMassCenteredDecomposition) (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredHalfMassTailWindowEnergy d X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Route-sized target for the centered shell/geometric residual contribution.

This is where the `H / X` term is intended to enter.
-/
structure HalfMassShellWindowTarget (d : HalfMassCenteredDecomposition) (C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredHalfMassShellWindowEnergy d X
        ≤
      C2 * ((H : ℝ) / (X : ℝ))
        + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

private lemma norm_add_sq_le_two_mul_add_two_mul (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith [hnorm, norm_nonneg (u + v), norm_nonneg u, norm_nonneg v]
  have hquad : (‖u‖ + ‖v‖) ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  exact le_trans hsq hquad

/--
Centered tail and shell control imply the variance target for the half-mass observable.

This is the deterministic combiner for the intended arithmetic proof route.
-/
theorem halfMassArithmeticVarianceTarget_of_tail_and_shell
    {d : HalfMassCenteredDecomposition}
    {C2t C3t C2s C3s : ℝ}
    (hTail : HalfMassTailWindowTarget d C2t C3t)
    (hShell : HalfMassShellWindowTarget d C2s C3s) :
    HalfMassArithmeticVarianceTarget (2 * C2t + 2 * C2s) (2 * C3t + 2 * C3s) := by
  refine ⟨by nlinarith [hTail.C2_nonneg, hShell.C2_nonneg],
    by nlinarith [hTail.C3_nonneg, hShell.C3_nonneg], ?_⟩
  intro X hX
  have hpoint :
      ∀ N ∈ EvenIn X H,
        ‖halfMassCenteredFluctuation X N‖ ^ 2
          ≤
        2 * ‖d.tailTerm X N‖ ^ 2 + 2 * ‖d.shellResidual X N‖ ^ 2 := by
    intro N hN
    rw [d.centered_eq X N]
    exact norm_add_sq_le_two_mul_add_two_mul _ _
  have hsum :
      halfMassRecenteredVarianceWindowEnergy X
        ≤
      ∑ N ∈ EvenIn X H,
        (2 * ‖d.tailTerm X N‖ ^ 2 + 2 * ‖d.shellResidual X N‖ ^ 2) := by
    unfold halfMassRecenteredVarianceWindowEnergy
    exact Finset.sum_le_sum (fun N hN => hpoint N hN)
  have hsplit :
      (∑ N ∈ EvenIn X H,
        (2 * ‖d.tailTerm X N‖ ^ 2 + 2 * ‖d.shellResidual X N‖ ^ 2))
        =
      2 * centeredHalfMassTailWindowEnergy d X
        + 2 * centeredHalfMassShellWindowEnergy d X := by
    unfold centeredHalfMassTailWindowEnergy centeredHalfMassShellWindowEnergy
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hTailBound := hTail.bound (X := X) hX
  have hShellBound := hShell.bound (X := X) hX
  calc
    halfMassRecenteredVarianceWindowEnergy X
      ≤
    ∑ N ∈ EvenIn X H,
      (2 * ‖d.tailTerm X N‖ ^ 2 + 2 * ‖d.shellResidual X N‖ ^ 2) := hsum
    _ =
      2 * centeredHalfMassTailWindowEnergy d X
        + 2 * centeredHalfMassShellWindowEnergy d X := hsplit
    _ ≤
      2 * (C2t * ((H : ℝ) / (X : ℝ))
          + C3t / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        + 2 * (C2s * ((H : ℝ) / (X : ℝ))
          + C3s / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hTailBound (by norm_num))
        (mul_le_mul_of_nonneg_left hShellBound (by norm_num))
    _ =
      (2 * C2t + 2 * C2s) * ((H : ℝ) / (X : ℝ))
        + (2 * C3t + 2 * C3s)
          / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by ring

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
