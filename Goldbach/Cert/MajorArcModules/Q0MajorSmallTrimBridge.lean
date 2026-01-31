import Goldbach.Cert.MajorArcStep12ShiftedExpSums
import Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaBMOR

/-!
Deterministic bridge for ε₂-small assembly: relate the project’s shifted exponential sum
`expSum X N` (range `s N = Icc 2 (N-2)`) to the Step-21 “trimmed” sums on `Ico 4 (N-1)`.

This file contains no analytic number theory: it is pure finite-sum bookkeeping + crude bounds
for the finitely many missing terms `n=2,3`.

It is intended to be used when assembling BMOR Step20–24 into `Q0MajorSmallUpperBound`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallTrimBridge

open scoped BigOperators

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma aTerm_eq_wX_mul_Lambda (X n : ℕ) :
    aTerm X n = ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n : ℝ) : ℂ) := by
  simp [MajorArcStep10RLSmoothIntegral.aTerm, mul_assoc]

noncomputable def expSumTrim (X N : ℕ) (γ : UC) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)

private lemma s_filter_ge4_eq_Ico (N : ℕ) :
    (s N).filter (fun n => 4 ≤ n) = Finset.Ico 4 ((N - 2) + 1) := by
  classical
  ext n
  constructor
  · intro hn
    have hn_s : n ∈ s N := (Finset.mem_filter.mp hn).1
    have hn_ge4 : 4 ≤ n := (Finset.mem_filter.mp hn).2
    have hn_le : n ≤ N - 2 := (Finset.mem_Icc.mp hn_s).2
    have hn_lt : n < (N - 2) + 1 := Nat.lt_succ_iff.mpr hn_le
    exact Finset.mem_Ico.mpr ⟨hn_ge4, hn_lt⟩
  · intro hn
    have hn_ge4 : 4 ≤ n := (Finset.mem_Ico.mp hn).1
    have hn_lt : n < (N - 2) + 1 := (Finset.mem_Ico.mp hn).2
    have hn_le : n ≤ N - 2 := Nat.lt_succ_iff.mp hn_lt
    have hn_ge2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 4) hn_ge4
    have hn_s : n ∈ s N := Finset.mem_Icc.mpr ⟨hn_ge2, hn_le⟩
    exact Finset.mem_filter.mpr ⟨hn_s, hn_ge4⟩

private lemma expSum_eq_sum_Lambda (X N : ℕ) (γ : UC) :
    expSum X N γ =
      ∑ n ∈ s N, aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) := by
  classical
  rfl

private lemma expSumTrim_eq_filter (X N : ℕ) (γ : UC) :
    expSumTrim X N γ = ∑ n ∈ (s N).filter (fun n => 4 ≤ n),
      aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) := by
  classical
  simp [expSumTrim, s_filter_ge4_eq_Ico]

private lemma expSum_sub_expSumTrim_eq_sum_small (X N : ℕ) (γ : UC) :
    expSum X N γ - expSumTrim X N γ =
      ∑ n ∈ (s N).filter (fun n => n < 4),
        aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) := by
  classical
  -- Split `s N` into the `n<4` and `4≤n` parts.
  have hsplit :
      (∑ n ∈ s N, aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ))
        =
      (∑ n ∈ (s N).filter (fun n => n < 4),
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ))
        +
      (∑ n ∈ (s N).filter (fun n => 4 ≤ n),
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)) := by
    -- Split `s N` into the `n < 4` and `4 ≤ n` parts.
    -- (`¬ n < 4` is definitionally `4 ≤ n`.)
    simpa [Nat.not_lt] using
      (Finset.sum_filter_add_sum_filter_not
        (s := s N)
        (f := fun n => aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ))
        (p := fun n => n < 4)).symm
  -- Substitute `expSum` and `expSumTrim`.
  have hexp : expSum X N γ =
      ∑ n ∈ s N, aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) :=
    expSum_eq_sum_Lambda (X := X) (N := N) (γ := γ)
  have htrim : expSumTrim X N γ =
      ∑ n ∈ (s N).filter (fun n => 4 ≤ n),
        aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) :=
    expSumTrim_eq_filter (X := X) (N := N) (γ := γ)
  -- Rearrange.
  -- `a = b + c` implies `a - c = b`.
  calc
    expSum X N γ - expSumTrim X N γ
        = (∑ n ∈ s N, aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ))
            -
          (∑ n ∈ (s N).filter (fun n => 4 ≤ n),
            aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)) := by
          rw [hexp, htrim]
    _ = ∑ n ∈ (s N).filter (fun n => n < 4),
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) := by
          -- Use the split identity: `(a + b) - b = a`, without expanding `fourier`.
          let A : ℂ :=
            ∑ n ∈ (s N).filter (fun n => n < 4),
              aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)
          let B : ℂ :=
            ∑ n ∈ (s N).filter (fun n => 4 ≤ n),
              aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)
          have hsplitAB :
              (∑ n ∈ s N,
                  aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ))
                = A + B := by
            simpa [A, B] using hsplit
          calc
            (∑ n ∈ s N,
                aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)) - B
                = (A + B) - B := by
                    rw [hsplitAB]
            _ = A := add_sub_cancel_right A B
            _ = ∑ n ∈ (s N).filter (fun n => n < 4),
                  aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ) := by
                  simp [A]

private lemma norm_fourier_nat (n : ℕ) (γ : UC) :
    ‖(fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ = 1 := by
  simp [fourier_apply]

private lemma Lambda_le_log_of_le {n N : ℕ} (hn : n ≤ N) (hN : 2 ≤ N) :
    Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) := by
  by_cases hp : Nat.Prime n
  · have hn0 : 0 < (n : ℝ) := by
      have : 0 < n := Nat.pos_of_ne_zero (Nat.Prime.ne_zero hp)
      exact_mod_cast this
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
    have hle : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    -- `log` is monotone on `(0,∞)`.
    have : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hn0 hle
    simpa [Goldbach.BG_Bank.Λ, hp] using this
  · -- Non-primes have `Λ n = 0`.
    have hlog : 0 ≤ Real.log (N : ℝ) := by
      have hN1 : 1 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < (2:ℕ)) hN)
      exact le_of_lt (Real.log_pos hN1)
    simpa [Goldbach.BG_Bank.Λ, hp] using hlog

/-- Crude deterministic trim bound: the difference between `expSum` and the Step-21 trimmed sum is
controlled by the finitely many missing indices `n=2,3`.

This is uniform in `γ` and uses only the inequality `Λ(n) ≤ log N` for `n≤N`. -/
theorem norm_expSum_sub_expSumTrim_le (X N : ℕ) (γ : UC) (hN : 6 ≤ N) :
    ‖expSum X N γ - expSumTrim X N γ‖ ≤ 2 * Real.log (N : ℝ) := by
  classical
  -- Rewrite as a sum over the `n<4` slice of `s N`.
  have hdiff := expSum_sub_expSumTrim_eq_sum_small (X := X) (N := N) (γ := γ)
  -- Triangle inequality on the finite sum.
  have htri :
      ‖∑ n ∈ (s N).filter (fun n => n < 4),
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖
        ≤
      ∑ n ∈ (s N).filter (fun n => n < 4),
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
    simpa using
      (norm_sum_le (s := (s N).filter (fun n => n < 4))
        (f := fun n =>
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)))
  -- Bound each term by `log N` and count at most two terms.
  have hN2 : 2 ≤ N := le_trans (by decide : (2:ℕ) ≤ 6) hN
  have hΛnonneg : ∀ n : ℕ, 0 ≤ Goldbach.BG_Bank.Λ n := by
    intro n
    by_cases hp : Nat.Prime n
    · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
      simpa [Goldbach.BG_Bank.Λ, hp] using (le_of_lt (Real.log_pos hn1))
    · simp [Goldbach.BG_Bank.Λ, hp]
  have hcard : ((s N).filter (fun n => n < 4)).card ≤ 2 := by
    -- The filter can only contain `n=2` or `n=3` since `s N = Icc 2 (N-2)`.
    -- A coarse bound `≤ 2` suffices.
    have : (s N).filter (fun n => n < 4) ⊆ Finset.Icc 2 3 := by
      intro n hn
      have hn_s : n ∈ s N := (Finset.mem_filter.mp hn).1
      have hn_lt : n < 4 := (Finset.mem_filter.mp hn).2
      have hn_ge2 : 2 ≤ n := (Finset.mem_Icc.mp hn_s).1
      have hn_le3 : n ≤ 3 := Nat.lt_succ_iff.mp hn_lt
      exact Finset.mem_Icc.mpr ⟨hn_ge2, hn_le3⟩
    have hcard' := Finset.card_le_card this
    -- `card (Icc 2 3) = 2`.
    simpa using le_trans hcard' (by decide : (Finset.Icc 2 3).card ≤ 2)
  have hterm :
      ∀ n ∈ (s N).filter (fun n => n < 4),
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ ≤ Real.log (N : ℝ) := by
    intro n hn
    have hn_s : n ∈ s N := (Finset.mem_filter.mp hn).1
    have hn_le : n ≤ N := by
      have hn_le' : n ≤ N - 2 := (Finset.mem_Icc.mp hn_s).2
      exact le_trans hn_le' (Nat.sub_le N 2)
    have hΛ : Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) := Lambda_le_log_of_le (n := n) (N := N) hn_le hN2
    have hΛabs : |Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
      -- `Λ n ≥ 0`, so `|Λ n| = Λ n`.
      simpa [abs_of_nonneg (hΛnonneg n)] using hΛ
    -- `‖aTerm X n * fourier‖ = |wX*Λ| ≤ |Λ|`.
    have hwX : |Goldbach.BG_Bank.wX X n| ≤ 1 := Goldbach.BG_Bank.abs_wX_le_one X n
    have hmul :
        |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
          ≤ |Goldbach.BG_Bank.Λ n| := by
      -- `|wX| ≤ 1` and `|Λ| ≥ 0`.
      simpa [abs_mul, mul_assoc] using
        (mul_le_mul_of_nonneg_right hwX (abs_nonneg (Goldbach.BG_Bank.Λ n)))
    have hnorm :
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖
          =
        |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
      -- `aTerm` is a real scalar in `ℂ`, and `‖fourier‖ = 1`.
      simp [MajorArcStep10RLSmoothIntegral.aTerm, aTerm_eq_wX_mul_Lambda, norm_mul,
        norm_fourier_nat (n := n) (γ := γ), abs_mul]
    have hnorm_le_abs :
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ ≤ |Goldbach.BG_Bank.Λ n| := by
      simpa [hnorm] using hmul
    exact le_trans hnorm_le_abs hΛabs
  -- Put it all together.
  have hsum :
      (∑ n ∈ (s N).filter (fun n => n < 4),
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
        ≤
      2 * Real.log (N : ℝ) := by
    have hsum_le_const :
        (∑ n ∈ (s N).filter (fun n => n < 4),
          ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
          ≤
        ∑ _n ∈ (s N).filter (fun n => n < 4), Real.log (N : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact hterm n hn
    have hconst :
        (∑ _n ∈ (s N).filter (fun n => n < 4), Real.log (N : ℝ))
          = ((s N).filter (fun n => n < 4)).card * Real.log (N : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    have hcardR : (((s N).filter (fun n => n < 4)).card : ℝ) * Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have hlog : 0 ≤ Real.log (N : ℝ) := by
        have : (1 : ℝ) < (N : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 6) hN)
        exact le_of_lt (Real.log_pos this)
      have hcard' : (((s N).filter (fun n => n < 4)).card : ℝ) ≤ (2 : ℝ) := by
        exact_mod_cast hcard
      -- Multiply by the nonnegative `log N`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hcard' hlog)
    have hsum' :
        (∑ n ∈ (s N).filter (fun n => n < 4),
          ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
          ≤
        (((s N).filter (fun n => n < 4)).card : ℝ) * Real.log (N : ℝ) := by
      simpa [hconst] using hsum_le_const
    exact le_trans hsum' hcardR
  -- Use the difference identity and the norm bound on the sum.
  calc
    ‖expSum X N γ - expSumTrim X N γ‖
        = ‖∑ n ∈ (s N).filter (fun n => n < 4),
            aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
          simpa [hdiff]
    _ ≤ ∑ n ∈ (s N).filter (fun n => n < 4),
          ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := htri
    _ ≤ 2 * Real.log (N : ℝ) := hsum

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallTrimBridge
