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
    {X : ℕ} (hX : X0 ≤ X) :
    canonicalEvenWindowPoint X ∈ EvenIn X H := by
  unfold canonicalEvenWindowPoint
  by_cases hEven : IsEven X
  · unfold EvenIn IccShift
    have hmem : X ∈ EvenIn X H := by
      unfold EvenIn IccShift
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩, hEven⟩
    simpa [hEven] using hmem
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
    (canonicalEvenWindowPoint_mem_even_window hX)

theorem exactGeometricScalar_ne_zero
    {X : ℕ} (hX : X0 ≤ X) :
    exactGeometricScalar X ≠ 0 := by
  unfold exactGeometricScalar
  exact
    (UnscaledGeometricZeroSliceMassWindowNormTarget.nonzero
      (hT := unscaledGeometricZeroSliceMassWindowNormTarget_explicit)
      hX (canonicalEvenWindowPoint_mem_even_window hX))

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
