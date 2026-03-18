import Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
import Goldbach.Cert.MajorArcStep5ExpSumApprox
import Goldbach.Cert.MajorArcStep13RealToCircle
import Goldbach.Cert.MajorArcExponentialPrelude

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation

open Complex
open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep5ExpSumApprox
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor

noncomputable section

/--
Pointwise oscillatory identity for the centered small-`β` shell.

This isolates the `θ`-dependence into the single phase
`e (β (n-m) + θ (n+m-N))`.
-/
theorem centered_shell_summand_eq_single_phase
    (N n m : ℕ) (θ β : ℝ) :
    e (((-(N : ℤ) : ℝ) * θ)) * (gExp (θ + β) n * gExp (θ - β) m)
      =
    e (β * ((n : ℝ) - (m : ℝ)) + θ * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
  unfold gExp
  calc
    e (((-(N : ℤ) : ℝ) * θ)) * (e ((θ + β) * (n : ℝ)) * e ((θ - β) * (m : ℝ)))
      = e (((-(N : ℤ) : ℝ) * θ)) * e ((θ + β) * (n : ℝ)) * e ((θ - β) * (m : ℝ)) := by
          ring
    _ = e (((( -(N : ℤ) : ℝ) * θ) + ((θ + β) * (n : ℝ)))) * e ((θ - β) * (m : ℝ)) := by
          rw [← e_add]
    _ = e ((((( -(N : ℤ) : ℝ) * θ) + ((θ + β) * (n : ℝ))) + ((θ - β) * (m : ℝ)))) := by
          rw [← e_add]
    _ = e (β * ((n : ℝ) - (m : ℝ)) + θ * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
          congr 1
          norm_num
          ring

/--
The same oscillatory identity on the unit-arc variable `u = qX θ`.

This is the exact formula that exposes the surviving `q`-dependence as the tiny phase
`e ((u/(qX)) * (n+m-N))`.
-/
theorem rescaled_shell_summand_eq_single_phase
    (X N q n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / ((q : ℝ) * (X : ℝ)))))
        * (gExp ((u / ((q : ℝ) * (X : ℝ))) + β) n
            * gExp ((u / ((q : ℝ) * (X : ℝ))) - β) m)
      =
    e
      (β * ((n : ℝ) - (m : ℝ))
        + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
  simpa using
    centered_shell_summand_eq_single_phase
      (N := N) (n := n) (m := m) (θ := u / ((q : ℝ) * (X : ℝ))) (β := β)

/--
Exact difference identity between the rescaled shell summand and the frozen (`θ = 0`) shell
summand.

This isolates the remaining local discrepancy as a single oscillatory difference of additive
characters.
-/
theorem rescaled_shell_summand_sub_frozen_eq_phase_diff
    (X N q n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / ((q : ℝ) * (X : ℝ)))))
        * (gExp ((u / ((q : ℝ) * (X : ℝ))) + β) n
            * gExp ((u / ((q : ℝ) * (X : ℝ))) - β) m)
      -
      (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))
      =
    e
      (β * ((n : ℝ) - (m : ℝ))
        + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))
      -
    e (β * ((n : ℝ) - (m : ℝ))) := by
  rw [rescaled_shell_summand_eq_single_phase]
  rw [centered_shell_summand_eq_single_phase (N := N) (n := n) (m := m) (θ := 0) (β := β)]
  simp

/--
Norm bound for the local oscillatory difference, conditional on the standard smallness hypothesis
needed by `norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one`.
-/
theorem norm_rescaled_shell_summand_sub_frozen_le
    (X N q n m : ℕ) (u β : ℝ)
    (hsmall :
      |2 * Real.pi * ((u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))| ≤ 1) :
    ‖e (((-(N : ℤ) : ℝ) * (u / ((q : ℝ) * (X : ℝ)))))
        * (gExp ((u / ((q : ℝ) * (X : ℝ))) + β) n
            * gExp ((u / ((q : ℝ) * (X : ℝ))) - β) m)
      -
      (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))‖
      ≤
    4 * Real.pi * |(u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ))| := by
  rw [rescaled_shell_summand_sub_frozen_eq_phase_diff]
  have hxy :
      |2 * Real.pi *
          ((β * ((n : ℝ) - (m : ℝ))
              + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))
            - β * ((n : ℝ) - (m : ℝ)))| ≤ 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      using hsmall
  have hbound :=
    Goldbach.Cert.MajorArcExponential.norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one
      (x :=
        β * ((n : ℝ) - (m : ℝ))
          + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))
      (y := β * ((n : ℝ) - (m : ℝ)))
      hxy
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using hbound

/--
Linear growth bound for the additive character along an arithmetic progression:
`gExp θ n` stays within `O(n |θ|)` of `1` when `|2πθ| ≤ 1`.
-/
theorem norm_gExp_sub_one_le
    (θ : ℝ) (n : ℕ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖gExp θ n - 1‖ ≤ (n : ℝ) * (4 * Real.pi * |θ|) := by
  induction n with
  | zero =>
      simp [Goldbach.Cert.MajorArcStep2ExpSums.gExp, Goldbach.Cert.MajorArcExponential.e]
  | succ n ih =>
      calc
        ‖gExp θ (n + 1) - 1‖
          = ‖(gExp θ (n + 1) - gExp θ n) + (gExp θ n - 1)‖ := by ring_nf
        _ ≤ ‖gExp θ (n + 1) - gExp θ n‖ + ‖gExp θ n - 1‖ := by
              simpa using norm_add_le (gExp θ (n + 1) - gExp θ n) (gExp θ n - 1)
        _ ≤ 4 * Real.pi * |θ| + (n : ℝ) * (4 * Real.pi * |θ|) := by
              gcongr
              exact Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp_succ_sub_gExp_le
                (β := θ) (n := n) hθ
        _ = ((n + 1 : ℕ) : ℝ) * (4 * Real.pi * |θ|) := by
              norm_num
              ring

/--
Shifting the frequency by a small amount changes a single `gExp` term by at most `O(n |θ|)`.
-/
theorem norm_gExp_add_shift_sub_le
    (β θ : ℝ) (n : ℕ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖gExp (β + θ) n - gExp β n‖ ≤ (n : ℝ) * (4 * Real.pi * |θ|) := by
  have hadd := Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add β θ n
  calc
    ‖gExp (β + θ) n - gExp β n‖
      = ‖gExp β n * (gExp θ n - 1)‖ := by
          rw [hadd]
          ring_nf
    _ = ‖gExp β n‖ * ‖gExp θ n - 1‖ := by rw [norm_mul]
    _ ≤ 1 * ((n : ℝ) * (4 * Real.pi * |θ|)) := by
          gcongr
          · exact le_of_eq (Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp β n)
          · exact norm_gExp_sub_one_le θ n hθ
    _ = (n : ℝ) * (4 * Real.pi * |θ|) := by ring

/--
Summed version of `norm_gExp_add_shift_sub_le` on the Step-21 interval `Ico 4 (N-1)`.
-/
theorem norm_gExp_sum_Ico_add_shift_sub_le
    (β θ : ℝ) (N : ℕ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (β + θ) n)
        - (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β n)‖
      ≤ ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
          * ((N - 2 : ℕ) : ℝ)
          * (4 * Real.pi * |θ|) := by
  calc
    ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (β + θ) n)
        - (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β n)‖
      = ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), (gExp (β + θ) n - gExp β n)‖ := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), ‖gExp (β + θ) n - gExp β n‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), (((N - 2 : ℕ) : ℝ) * (4 * Real.pi * |θ|)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn_lt : n < (N - 2) + 1 := (Finset.mem_Ico.mp hn).2
          have hn_le : n ≤ N - 2 := Nat.lt_succ_iff.mp hn_lt
          exact le_trans (norm_gExp_add_shift_sub_le β θ n hθ) <|
            mul_le_mul_of_nonneg_right (by exact_mod_cast hn_le) (by positivity)
    _ = ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
          * (((N - 2 : ℕ) : ℝ) * (4 * Real.pi * |θ|)) := by
            simp
    _ = ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
          * ((N - 2 : ℕ) : ℝ)
          * (4 * Real.pi * |θ|) := by ring

/--
The Fourier phase `fourier (-N) θ` differs from `1` by at most `O(N |θ|)` when `|2πθ| ≤ 1`.
-/
theorem norm_fourier_neg_nat_sub_one_le
    (N : ℕ) (θ : ℝ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ) - 1‖
      ≤ (N : ℝ) * (4 * Real.pi * |θ|) := by
  have hmain := norm_gExp_sub_one_le (-θ) N (by simpa using hθ)
  rw [Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e]
  simpa [Goldbach.Cert.MajorArcStep2ExpSums.gExp, mul_assoc, mul_left_comm, mul_comm] using hmain

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
