import Goldbach.BankPieces.Cert.RawScaleSmallBetaQGapC

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaQCollapse

open scoped BigOperators Interval

open Complex
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

theorem AqLocalC_eq_AqCRescaled_of_two_le
    {X N q : ℕ} (hX : 2 ≤ X) (hq : 2 ≤ q) :
    AqLocalC X N q = AqCRescaled X N q (1 : ℝ) := by
  have hqne : q ≠ 1 := by omega
  have hX1 : 1 ≤ X := le_trans (by decide : (1 : ℕ) ≤ 2) hX
  have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
  unfold AqLocalC
  simp [hqne, AqC_eq_AqCRescaled, hX1, hq1]

theorem AqLocalC_uniform_collapse_of_q1_and_rescaled_ge2
    (A : ℕ → ℕ → ℂ)
    {X N : ℕ} {ηA : ℝ}
    (hX : 2 ≤ X)
    (hq1 :
      ‖AqLocalC X N 1 - A X N‖ ≤ ηA)
    (hge2 :
      ∀ q ∈ Finset.Icc (2 : ℕ) Q0, ‖AqCRescaled X N q (1 : ℝ) - A X N‖ ≤ ηA) :
    ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - A X N‖ ≤ ηA := by
  intro q hq
  rcases Nat.eq_or_lt_of_le (Finset.mem_Icc.mp hq).1 with rfl | hqgt
  · exact hq1
  · have hq2 : 2 ≤ q := by omega
    have hq' : q ∈ Finset.Icc (2 : ℕ) Q0 := by
      exact Finset.mem_Icc.mpr ⟨hq2, (Finset.mem_Icc.mp hq).2⟩
    rw [AqLocalC_eq_AqCRescaled_of_two_le hX hq2]
    exact hge2 q hq'

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaQCollapse
