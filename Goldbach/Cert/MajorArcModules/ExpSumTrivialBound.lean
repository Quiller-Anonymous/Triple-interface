import Goldbach.Cert.MajorArcStep12ShiftedExpSums

/-!
Deterministic “triangle inequality” bounds for the shifted exponential sums `expSum`.

These are intentionally crude but stable, and are useful for integrability/plumbing lemmas
(where we only need an explicit finite bound, not cancellation).
-/

namespace Goldbach.Cert.MajorArcModules.ExpSumTrivialBound

open scoped BigOperators

open Complex AddCircle

open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma log_nonneg_of_two_le {N : ℕ} (hN2 : 2 ≤ N) : 0 ≤ Real.log (N : ℝ) := by
  have h1N : (1 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
  exact (Real.log_pos h1N).le

private lemma Lambda_le_log_of_le {n N : ℕ} (hn : n ≤ N) (hN2 : 2 ≤ N) :
    Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) := by
  by_cases hp : Nat.Prime n
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hp.pos
    have hn_le' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    have hlog_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by simpa using hnpos) hn_le'
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := (Real.log_pos (by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
      exact this)).le
    simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlog_nonneg] using hlog_le
  · -- non-prime: `Λ n = 0`
    have hlog0 : 0 ≤ Real.log (N : ℝ) := log_nonneg_of_two_le hN2
    simp [Goldbach.BG_Bank.Λ, hp, hlog0]

theorem norm_expSum_le (X N : ℕ) (hN2 : 2 ≤ N) (γ : UC) :
    ‖expSum X N γ‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
  classical
  -- Triangle inequality for the finite sum.
  have htri :
      ‖expSum X N γ‖ ≤
        ∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
    simpa [Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum] using
      (norm_sum_le (s := s N)
        (f := fun n =>
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)))

  have hlog0 : 0 ≤ Real.log (N : ℝ) := log_nonneg_of_two_le hN2

  have hterm :
      ∀ n ∈ s N,
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ ≤ Real.log (N : ℝ) := by
    intro n hn
    have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    have hΛ : Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) := Lambda_le_log_of_le (n := n) (N := N) hn_le hN2
    have hΛabs : |Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
      -- `Λ n ≥ 0`, so `|Λ n| = Λ n`.
      have hΛnonneg : 0 ≤ Goldbach.BG_Bank.Λ n := by
        by_cases hp : Nat.Prime n
        · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
          simpa [Goldbach.BG_Bank.Λ, hp] using (le_of_lt (Real.log_pos hn1))
        · simp [Goldbach.BG_Bank.Λ, hp]
      simpa [abs_of_nonneg hΛnonneg] using hΛ
    -- `‖aTerm‖` is `|Λ n|` and `‖fourier‖ = 1`.
    have hfour : ‖(fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ = 1 := by
      simp [fourier_apply]
    have haTerm : ‖aTerm X n‖ = |Goldbach.BG_Bank.Λ n| := by
      -- In the current repo, `wX` is definitionally `1`.
      simp [MajorArcStep10RLSmoothIntegral.aTerm, Goldbach.BG_Bank.wX]
    calc
      ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖
          =
        ‖aTerm X n‖ * ‖(fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
            simp [norm_mul]
      _ = |Goldbach.BG_Bank.Λ n| := by
            simp [haTerm, hfour, Goldbach.BG_Bank.wX]
      _ ≤ Real.log (N : ℝ) := hΛabs

  have hsum_le :
      (∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
        ≤ ((s N).card : ℝ) * Real.log (N : ℝ) := by
    have hsum_le_const :
        (∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
          ≤ ∑ _n ∈ s N, Real.log (N : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact hterm n hn
    -- `sum_const` rewrite.
    simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hsum_le_const

  have hcard : ((s N).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    -- Crude bound: `s N ⊆ Icc 0 N`, hence `card ≤ N+1`.
    have hsub : s N ⊆ Finset.Icc 0 N := by
      intro n hn
      have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hn_le⟩
    have hcard' : (s N).card ≤ (Finset.Icc 0 N).card := Finset.card_le_card hsub
    -- `card (Icc 0 N) = N+1`.
    have : (Finset.Icc 0 N).card = N + 1 := by
      simpa using (Finset.card_Icc (a := 0) (b := N))
    exact_mod_cast (le_trans hcard' (by simpa [this]))

  calc
    ‖expSum X N γ‖
        ≤ ∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := htri
    _ ≤ ((s N).card : ℝ) * Real.log (N : ℝ) := hsum_le
    _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcard hlog0

end

end Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
