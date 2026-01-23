import Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionDeterministic

/-!
Convenience wrapper: export the deterministic alias-suppression instance.

This keeps `Q0MajorTailAliasSuppressionSpec.lean` as a lightweight interface file while still
providing a one-line theorem that downstream modules can import.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionFromDeterministic

open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionDeterministic

noncomputable section

theorem q0AliasSuppressedHybridLargeSieve_det :
    Q0AliasSuppressedHybridLargeSieve (1 / (X0 : ℝ)) :=
  q0AliasSuppressedHybridLargeSieve

private lemma one_div_X0_le_sixteen : (1 / (X0 : ℝ)) ≤ (16 : ℝ) := by
  have hX0pos : (0 : ℝ) < (X0 : ℝ) := by
    have : 0 < X0 := by decide
    exact_mod_cast this
  have hmul : (1 : ℝ) ≤ (16 : ℝ) * (X0 : ℝ) := by
    have hX0 : (1 : ℝ) ≤ (X0 : ℝ) := by
      exact_mod_cast (by decide : (1 : ℕ) ≤ X0)
    have h16 : (0 : ℝ) ≤ (16 : ℝ) := by
      norm_num
    have h16X0 : (16 : ℝ) ≤ (16 : ℝ) * (X0 : ℝ) := by
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hX0 h16)
    nlinarith
  have h := (div_le_iff₀ hX0pos).2 hmul
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- Convenience: a coarser `C_AS=16` instance for the alias-suppression interface. -/
theorem q0AliasSuppressedHybridLargeSieve_16 :
    Q0AliasSuppressedHybridLargeSieve (16 : ℝ) := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro X hX coeff β
  have hdet : Q0AliasSuppressedHybridLargeSieve (1 / (X0 : ℝ)) :=
    q0AliasSuppressedHybridLargeSieve_det
  have hbound := hdet.bound (X := X) hX coeff β
  have hsum_nonneg : 0 ≤ (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro n hn
    exact sq_nonneg _
  have hX_nonneg : 0 ≤ (X : ℝ) := by
    exact_mod_cast (Nat.zero_le X)
  have hXsum_nonneg : 0 ≤ (X : ℝ) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) :=
    mul_nonneg hX_nonneg hsum_nonneg
  have hmul :
      (1 / (X0 : ℝ)) * (X : ℝ) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2)
        ≤
      (16 : ℝ) * (X : ℝ) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) := by
    have h :=
      mul_le_mul_of_nonneg_right one_div_X0_le_sixteen hXsum_nonneg
    simpa [mul_assoc] using h
  exact le_trans hbound hmul

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionFromDeterministic
