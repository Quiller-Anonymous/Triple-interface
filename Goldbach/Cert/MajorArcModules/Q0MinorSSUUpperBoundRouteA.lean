import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound
import Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundSpec

/-!
Route-A generator-facing upper bound for the ε₁ SSU / nonzero-mode piece.

This file keeps the minor-side coefficient masses exact, but replaces the hard major-weight
kernel masses by the existing rigorous Step-5 upper bounds from the major-tail stack. The
resulting expression is substantially easier for an external generator to evaluate.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundRouteA

open scoped BigOperators Interval

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBound
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFourierDecomp
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Route-A zero-frequency major-weight envelope used on the SSU side. -/
noncomputable def weight0SqUpper (X : ℕ) : ℝ :=
  ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
      * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ))) ^ 2

/--
Route-A pointwise SSU upper bound:
exact coefficient masses, but Step-5 upper bounds for the nonzero kernel masses and the
deterministic major-mass bound for the `t = 0` Fourier coefficient.
-/
noncomputable def pointwiseUpper (X N : ℕ) : ℝ :=
  ‖q0NormFactor N‖ ^ 2 *
    (2 *
      ((2 * kernelMassNZEven_upper X) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd_upper X) * (aTerm2Mass X) * (coeffMass X N)
        +
      (3 * weight0SqUpper X) * (diagMass X N)))

/-- Exact Route-A window expression that a generator can evaluate. -/
noncomputable def windowUpper (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, pointwiseUpper X N

private lemma mem_evenIn_le_right {X N : ℕ} (hN : N ∈ EvenIn X H) : N ≤ X + H := by
  rcases Finset.mem_filter.mp hN with ⟨hIcc, _⟩
  rcases Finset.mem_image.mp hIcc with ⟨k, hk, rfl⟩
  exact Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) X

private lemma weight0_sq_le_upper {X : ℕ} (hX : X0 ≤ X) :
    ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2 ≤ weight0SqUpper X := by
  have hΔ0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have hXpos : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have h0 :
      ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖
        ≤
      (((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
        * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) :=
    norm_majorArcWeightFourier_zero_le_two_div_X_mul_sum_totient_div
      (X := X) (Δ := (1 : ℝ)) hΔ0 hXpos
  have hRight_nonneg :
      0 ≤
        (((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
          * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) := by
    refine mul_nonneg ?_ ?_
    · positivity
    · refine Finset.sum_nonneg ?_
      intro q hq
      positivity
  have hLeft_nonneg :
      0 ≤ ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ := norm_nonneg _
  have hsq :
      ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
        ≤
      ((((2 : ℝ) * (1 : ℝ)) / (X : ℝ))
        * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ))) ^ 2 := by
    nlinarith
  simpa [weight0SqUpper] using hsq

lemma ssuPart_sq_le_pointwiseUpper {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖canonicalExpansion.ssuPart X N‖ ^ 2 ≤ pointwiseUpper X N := by
  have hEvenN : Even N := Goldbach.Windows.even_of_isEven (Finset.mem_filter.mp hN).2
  have hNle : N ≤ X + H := mem_evenIn_le_right hN
  have hbase :=
    ssuPart_norm_sq_le_public_parity_bound (X := X) (N := N) hEvenN
  have hEven :
      kernelMassNZEven X Δ_canon N ≤ kernelMassNZEven_upper X := by
    exact le_trans
      (kernelMassNZEven_mono_N (X := X) (Δ := Δ_canon) hNle)
      (kernelMassNZEven_le_upper (X := X) hX)
  have hOdd :
      kernelMassNZOdd X Δ_canon N ≤ kernelMassNZOdd_upper X := by
    exact le_trans
      (kernelMassNZOdd_mono_N (X := X) (Δ := Δ_canon) hNle)
      (kernelMassNZOdd_le_upper (X := X) hX)
  have hWeight0 :
      ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2 ≤ weight0SqUpper X :=
    weight0_sq_le_upper (X := X) hX
  have hCoeffSq : 0 ≤ (coeffMass X N) ^ 2 := sq_nonneg _
  have hCoeff : 0 ≤ coeffMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hA2 : 0 ≤ aTerm2Mass X := aTerm2Mass_nonneg X
  have hDiag : 0 ≤ diagMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hBracket :
      (2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
        +
      (3 * ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N)
        ≤
      (2 * kernelMassNZEven_upper X) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd_upper X) * (aTerm2Mass X) * (coeffMass X N)
        +
      (3 * weight0SqUpper X) * (diagMass X N) := by
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEven (by norm_num)) hCoeffSq
    · have hLeft :
          4 * kernelMassNZOdd X Δ_canon N ≤ 4 * kernelMassNZOdd_upper X :=
        mul_le_mul_of_nonneg_left hOdd (by norm_num)
      have hMid :
          (4 * kernelMassNZOdd X Δ_canon N) * aTerm2Mass X
            ≤
          (4 * kernelMassNZOdd_upper X) * aTerm2Mass X :=
        mul_le_mul_of_nonneg_right hLeft hA2
      exact mul_le_mul_of_nonneg_right hMid hCoeff
    · have hLeft :
          3 * ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
            ≤
          3 * weight0SqUpper X :=
        mul_le_mul_of_nonneg_left hWeight0 (by norm_num)
      exact mul_le_mul_of_nonneg_right hLeft hDiag
  have hScale : 0 ≤ ‖q0NormFactor N‖ ^ 2 := sq_nonneg _
  calc
    ‖canonicalExpansion.ssuPart X N‖ ^ 2
        ≤
      ‖q0NormFactor N‖ ^ 2 *
        (2 *
          ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
            +
          (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
            +
          (3 * ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N))) := by
          simpa [Q0MinorSSUUpperBoundSpec.pointwiseUpper] using
            (Q0MinorSSUUpperBoundSpec.ssuPart_sq_le_pointwiseUpper (X := X) hN)
    _ ≤ pointwiseUpper X N := by
          have hTwoBracket :
              2 *
                  ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
                    +
                  (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
                    +
                  (3 * ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2)
                    * (diagMass X N))
                ≤
              2 *
                  ((2 * kernelMassNZEven_upper X) * (coeffMass X N) ^ 2
                    +
                  (4 * kernelMassNZOdd_upper X) * (aTerm2Mass X) * (coeffMass X N)
                    +
                  (3 * weight0SqUpper X) * (diagMass X N)) := by
            exact mul_le_mul_of_nonneg_left hBracket (by norm_num)
          have hScaled :
              ‖q0NormFactor N‖ ^ 2 *
                  (2 *
                    ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
                      +
                    (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
                      +
                    (3 * ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2)
                      * (diagMass X N)))
                ≤
              ‖q0NormFactor N‖ ^ 2 *
                  (2 *
                    ((2 * kernelMassNZEven_upper X) * (coeffMass X N) ^ 2
                      +
                    (4 * kernelMassNZOdd_upper X) * (aTerm2Mass X) * (coeffMass X N)
                      +
                    (3 * weight0SqUpper X) * (diagMass X N))) := by
            exact mul_le_mul_of_nonneg_left hTwoBracket hScale
          simpa [pointwiseUpper] using hScaled

theorem sum_ssuPart_sq_le_windowUpper (X : ℕ) (hX : X0 ≤ X) :
    (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2) ≤ windowUpper X := by
  refine Finset.sum_le_sum ?_
  intro N hN
  exact ssuPart_sq_le_pointwiseUpper (X := X) hX hN

theorem nonzeroModeEnergyBound_of_windowUpper
    {U : ℝ} (hU_nonneg : 0 ≤ U)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        windowUpper X ≤
          Q0MinorSplitCert.normFactorSq X * (U * ((H : ℝ) / (X : ℝ)))) :
    canonicalExpansion.NonzeroModeEnergyBound U := by
  refine ⟨hU_nonneg, ?_⟩
  intro X hX
  exact le_trans (sum_ssuPart_sq_le_windowUpper X hX) (hUpper hX)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundRouteA
