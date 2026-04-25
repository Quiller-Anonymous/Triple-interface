import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassArithmeticBoundary
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

/-- Canonical even point in the short window `[X, X + H]`. -/
def canonicalEvenWindowPoint (X : ℕ) : ℕ :=
  if IsEven X then X else X + 1

theorem canonicalEvenWindowPoint_mem_even_window
    {X : ℕ} :
    canonicalEvenWindowPoint X ∈ EvenIn X H := by
  unfold canonicalEvenWindowPoint
  by_cases hEven : IsEven X
  · unfold EvenIn IccShift
    have hmem : X ∈ EvenIn X H := by
      unfold EvenIn IccShift
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩, hEven⟩
    simpa [canonicalEvenWindowPoint, hEven] using hmem
  · have h1 : 1 ∈ Finset.range (H + 1) := by
      norm_num [H]
    have hEvenSucc : IsEven (X + 1) := by
      have hNotEven : ¬ Even X := by
        intro hXE
        exact hEven (Goldbach.Windows.isEven_of_even hXE)
      have hOdd : Odd X := Nat.not_even_iff_odd.mp hNotEven
      exact Goldbach.Windows.isEven_of_even (Odd.add_one hOdd)
    have hmem : X + 1 ∈ EvenIn X H := by
      unfold EvenIn IccShift
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨1, h1, by simp⟩, hEvenSucc⟩
    simpa [hEven] using hmem

/-- Exact geometric zero-slice scalar on the canonical even window. -/
noncomputable def exactGeometricScalar (X : ℕ) : ℂ :=
  unscaledGeometricZeroSliceMass X (canonicalEvenWindowPoint X)

theorem unscaledGeometricZeroSliceMass_eq_exactGeometricScalar
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    unscaledGeometricZeroSliceMass X N = exactGeometricScalar X := by
  unfold exactGeometricScalar
  exact unscaledGeometricZeroSliceMass_eq_of_mem_even_window hX hN
    canonicalEvenWindowPoint_mem_even_window

theorem exactGeometricScalar_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    exactGeometricScalar X ≠ 0 := by
  unfold exactGeometricScalar
  exact
    (UnscaledGeometricZeroSliceMassWindowNormTarget.nonzero
      (hT := unscaledGeometricZeroSliceMassWindowNormTarget_explicit)
      hX canonicalEvenWindowPoint_mem_even_window)

/--
Arithmetic-model term after recentering at the exact geometric scalar `γ_X` rather than the
heuristic half-mass baseline `1/2`.
-/
noncomputable def exactGeometricArithmeticModel (X N : ℕ) : ℂ :=
  (2 : ℂ) * exactGeometricScalar X * halfMassArithmeticModel X N

/-- Shell residual after recentering at the exact geometric scalar `γ_X`. -/
noncomputable def exactGeometricShellResidual (X N : ℕ) : ℂ :=
  halfMassRecenteredZeroModeObservable X N - exactGeometricArithmeticModel X N

theorem halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    halfMassRecenteredZeroModeObservable X N = exactGeometricArithmeticModel X N := by
  have hunscaled : unscaledGeometricZeroSliceMass X N ≠ 0 :=
    (UnscaledGeometricZeroSliceMassWindowNormTarget.nonzero
      (hT := unscaledGeometricZeroSliceMassWindowNormTarget_explicit) hX hN)
  have hmass : unscaledGeometricZeroSliceMass X N = exactGeometricScalar X :=
    unscaledGeometricZeroSliceMass_eq_exactGeometricScalar hX hN
  calc
    halfMassRecenteredZeroModeObservable X N
        = halfMassArithmeticModel X N + halfMassShellResidual X N := by
            unfold halfMassShellResidual
            ring
    _ = halfMassArithmeticModel X N
          + (2 : ℂ) * halfMassArithmeticModel X N
              * (exactGeometricScalar X - unscaledGeometricZeroSliceHalfMass) := by
            rw [halfMassShellResidual_eq_two_mul_arithmeticModel_mul_halfMassError X N hunscaled]
            unfold unscaledGeometricZeroSliceHalfMassError
            rw [hmass]
    _ = exactGeometricArithmeticModel X N := by
          unfold exactGeometricArithmeticModel unscaledGeometricZeroSliceHalfMass
          norm_num
          ring

theorem exactGeometricShellResidual_eq_zero_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    exactGeometricShellResidual X N = 0 := by
  unfold exactGeometricShellResidual
  rw [halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window hX hN]
  ring

/--
On the canonical even window, the half-mass raw window sum is exactly the arithmetic-model raw
window sum scaled by the explicit factor `2 * exactGeometricScalar X`.
-/
theorem halfMassWindowRawSum_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowRawSum
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassWindowRawSum X
      =
    ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModelWindowRawSum X := by
  unfold halfMassWindowRawSum halfMassArithmeticModelWindowRawSum
  calc
    ∑ N ∈ EvenIn X H, halfMassRecenteredZeroModeObservable X N
        =
      ∑ N ∈ EvenIn X H, exactGeometricArithmeticModel X N := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          exact halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window hX hN
    _ =
      ∑ N ∈ EvenIn X H, ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModel X N := by
          refine Finset.sum_congr rfl ?_
          intro N hN
          unfold exactGeometricArithmeticModel
          rfl
    _ = ((2 : ℂ) * exactGeometricScalar X) * ∑ N ∈ EvenIn X H, halfMassArithmeticModel X N := by
          rw [← Finset.mul_sum]

/--
On the canonical even window, the half-mass window average is exactly the arithmetic-model window
average scaled by the explicit factor `2 * exactGeometricScalar X`.

This shows that the remaining arithmetic-model average obstruction is not new arithmetic content:
it is the old half-mass window average, modulo a fully explicit deterministic scalar.
-/
theorem halfMassRecenteredWindowAverage_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowAverage
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassRecenteredWindowAverage X
      =
    ((2 : ℂ) * exactGeometricScalar X) * halfMassArithmeticModelWindowAverage X := by
  unfold halfMassRecenteredWindowAverage halfMassArithmeticModelWindowAverage
  rw [halfMassWindowRawSum_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowRawSum hX]
  ring

/--
Inverse form of the arithmetic-model average identity.

This is the clean diagnostic statement: once `exactGeometricScalar X` is fixed, controlling the
arithmetic-model average is equivalent to controlling the old half-mass window average.
-/
theorem halfMassArithmeticModelWindowAverage_eq_inv_two_mul_exactGeometricScalar_mul_average
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassArithmeticModelWindowAverage X
      =
    (((2 : ℂ) * exactGeometricScalar X)⁻¹) * halfMassRecenteredWindowAverage X := by
  set fac : ℂ := ((2 : ℂ) * exactGeometricScalar X)
  have hγ : exactGeometricScalar X ≠ 0 := exactGeometricScalar_ne_zero hX
  have hfac : fac ≠ 0 := by
    dsimp [fac]
    exact mul_ne_zero (by norm_num) hγ
  have hmain : halfMassRecenteredWindowAverage X = fac * halfMassArithmeticModelWindowAverage X := by
    simpa [fac] using
      halfMassRecenteredWindowAverage_eq_two_mul_exactGeometricScalar_mul_arithmeticModelWindowAverage hX
  calc
    halfMassArithmeticModelWindowAverage X
        = fac⁻¹ * (fac * halfMassArithmeticModelWindowAverage X) := by
            field_simp [hfac]
    _ = fac⁻¹ * halfMassRecenteredWindowAverage X := by rw [hmain]
    _ = (((2 : ℂ) * exactGeometricScalar X)⁻¹) * halfMassRecenteredWindowAverage X := by
            simp [fac]

/-- Window energy of the exactly recentered shell residual on the canonical even window. -/
noncomputable def exactGeometricShellResidualWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖exactGeometricShellResidual X N‖ ^ 2

theorem exactGeometricShellResidualWindowEnergy_eq_zero
    {X : ℕ} (hX : X0 ≤ X) :
    exactGeometricShellResidualWindowEnergy X = 0 := by
  unfold exactGeometricShellResidualWindowEnergy
  calc
    ∑ N ∈ EvenIn X H, ‖exactGeometricShellResidual X N‖ ^ 2
        = ∑ N ∈ EvenIn X H, (0 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro N hN
            rw [exactGeometricShellResidual_eq_zero_of_mem_even_window hX hN]
            simp
    _ = 0 := by simp

theorem halfMassCenteredFluctuation_eq_exactGeometricArithmeticModel_sub_average_of_mem_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    halfMassCenteredFluctuation X N =
      exactGeometricArithmeticModel X N - halfMassCanonicalAverageWitness X := by
  unfold halfMassCenteredFluctuation
  rw [halfMassRecenteredZeroModeObservable_eq_exactGeometricArithmeticModel_of_mem_even_window hX hN]

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
