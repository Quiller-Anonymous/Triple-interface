import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Elementary signed Mobius partial sums

This module develops the first arithmetic ingredient of the signed-conductor Type-I proposal. The
argument is finite: Mobius inversion gives `sum_{d <= X} mu(d) * floor(X / d) = 1`, and Euclidean
division controls the difference between `floor(X / d)` and `X / d`.
-/

namespace Goldbach.Cert.MajorArcModules.RouteASignedMoebiusPartialSums

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction

noncomputable section

private theorem sum_moebius_divisors_int (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.coe_zeta_mul_moebius
  dsimp only at h
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at h
  exact h

private theorem sum_moebius_mul_natDiv
    {X : ℕ} (hX : 0 < X) :
    (∑ d ∈ Finset.Icc 1 X,
      ArithmeticFunction.moebius d * ((X / d : ℕ) : ℤ)) = 1 := by
  classical
  have hfixed : ∀ d ∈ Finset.Icc 1 X,
      ArithmeticFunction.moebius d * ((X / d : ℕ) : ℤ) =
        ∑ n ∈ Finset.range X,
          if d ∣ n + 1 then ArithmeticFunction.moebius d else 0 := by
    intro d hd
    have hcard := Nat.card_multiples X d
    have hcardInt :
        (((Finset.range X).filter (fun n => d ∣ n + 1)).card : ℤ) =
          ((X / d : ℕ) : ℤ) := by
      exact_mod_cast hcard
    rw [← hcardInt, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.mul_sum]
    simp only [mul_one]
    rw [Finset.sum_filter]
  calc
    (∑ d ∈ Finset.Icc 1 X,
        ArithmeticFunction.moebius d * ((X / d : ℕ) : ℤ)) =
        ∑ d ∈ Finset.Icc 1 X, ∑ n ∈ Finset.range X,
          if d ∣ n + 1 then ArithmeticFunction.moebius d else 0 :=
      Finset.sum_congr rfl hfixed
    _ = ∑ n ∈ Finset.range X, ∑ d ∈ Finset.Icc 1 X,
          if d ∣ n + 1 then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range X, if n + 1 = 1 then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnX : n + 1 ≤ X := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
      have hset :
          (Finset.Icc 1 X).filter (fun d => d ∣ n + 1) = (n + 1).divisors := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdOne, hdX⟩, hdvd⟩
          exact ⟨hdvd, Nat.succ_ne_zero n⟩
        · rintro ⟨hdvd, hnZero⟩
          have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos n)
          exact ⟨⟨hdPos, (Nat.le_of_dvd (Nat.succ_pos n) hdvd).trans hnX⟩, hdvd⟩
      calc
        (∑ d ∈ Finset.Icc 1 X,
            if d ∣ n + 1 then ArithmeticFunction.moebius d else 0) =
            ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d ∣ n + 1),
              ArithmeticFunction.moebius d := by
                rw [Finset.sum_filter]
        _ = ∑ d ∈ (n + 1).divisors, ArithmeticFunction.moebius d := by rw [hset]
        _ = if n + 1 = 1 then 1 else 0 := sum_moebius_divisors_int (n + 1)
    _ = 1 := by
      simp [hX]

/--
The ordinary harmonic Mobius partial sum is bounded by one. This is the elementary cancellation
behind the proposed coprime/totient estimate; importantly, it does not take absolute values before
summing the Mobius coefficients.
-/
noncomputable def signedMoebiusHarmonicPartialSum (X : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 X,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)

theorem abs_signedMoebiusHarmonicPartialSum_le_one (X : ℕ) :
    |signedMoebiusHarmonicPartialSum X| ≤ 1 := by
  classical
  by_cases hXZero : X = 0
  · subst X
    simp [signedMoebiusHarmonicPartialSum]
  have hX : 0 < X := Nat.pos_of_ne_zero hXZero
  have hOneX : 1 ≤ X := hX
  let remainderTerm : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (((X % d : ℕ) : ℝ) / (d : ℝ))
  have hdecomp : ∀ d ∈ Finset.Icc 1 X,
      (X : ℝ) * (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) =
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ) +
          remainderTerm d := by
    intro d hd
    have hdPos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdRealNe : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdPos)
    have hdivision :
        (X : ℝ) / (d : ℝ) =
          ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) / (d : ℝ) := by
      apply (div_eq_iff hdRealNe).2
      rw [add_mul, div_mul_cancel₀ _ hdRealNe]
      have hcast :
          ((X % d : ℕ) : ℝ) + (d : ℝ) * ((X / d : ℕ) : ℝ) = (X : ℝ) := by
        exact_mod_cast Nat.mod_add_div X d
      nlinarith
    calc
      (X : ℝ) * (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) =
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ)) := by
            ring
      _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) / (d : ℝ)) := by
            rw [hdivision]
      _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ) +
            remainderTerm d := by
            simp only [remainderTerm]
            ring
  have hfloorReal :
      (∑ d ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ)) = 1 := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) (sum_moebius_mul_natDiv hX)
    push_cast at hcast
    exact hcast
  have hscaled :
      (X : ℝ) * signedMoebiusHarmonicPartialSum X =
        1 + ∑ d ∈ Finset.Icc 1 X, remainderTerm d := by
    unfold signedMoebiusHarmonicPartialSum
    calc
      (X : ℝ) *
          (∑ d ∈ Finset.Icc 1 X,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) =
          ∑ d ∈ Finset.Icc 1 X,
            (X : ℝ) * (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) := by
              rw [Finset.mul_sum]
      _ = ∑ d ∈ Finset.Icc 1 X,
            (((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ) +
              remainderTerm d) := Finset.sum_congr rfl hdecomp
      _ = (∑ d ∈ Finset.Icc 1 X,
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ)) +
            ∑ d ∈ Finset.Icc 1 X, remainderTerm d := by
              rw [Finset.sum_add_distrib]
      _ = 1 + ∑ d ∈ Finset.Icc 1 X, remainderTerm d := by rw [hfloorReal]
  have hIcc : insert 1 (Finset.Icc 2 X) = Finset.Icc 1 X := by
    simpa using
      (Finset.insert_Icc_add_one_left_eq_Icc (a := 1) (b := X) hOneX)
  have hremainderSum :
      (∑ d ∈ Finset.Icc 1 X, remainderTerm d) =
        ∑ d ∈ Finset.Icc 2 X, remainderTerm d := by
    rw [← hIcc, Finset.sum_insert]
    · simp [remainderTerm, Nat.mod_one]
    · simp
  have hremainderTerm : ∀ d ∈ Finset.Icc 2 X, |remainderTerm d| ≤ 1 := by
    intro d hd
    have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hd).1
    have hdRealPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdPos
    have hmu : |(((ArithmeticFunction.moebius d : ℤ) : ℝ))| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    have hratioNonneg :
        0 ≤ ((X % d : ℕ) : ℝ) / (d : ℝ) :=
      div_nonneg (by positivity) hdRealPos.le
    have hmodLe : ((X % d : ℕ) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (Nat.mod_lt X hdPos).le
    have hratio : |((X % d : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg hratioNonneg]
      exact (div_le_one hdRealPos).2 hmodLe
    calc
      |remainderTerm d| =
          |(((ArithmeticFunction.moebius d : ℤ) : ℝ))| *
            |((X % d : ℕ) : ℝ) / (d : ℝ)| := by
              simp only [remainderTerm, abs_mul]
      _ ≤ 1 * 1 := mul_le_mul hmu hratio (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hremainderAbs :
      |∑ d ∈ Finset.Icc 2 X, remainderTerm d| ≤
        ((Finset.Icc 2 X).card : ℝ) := by
    calc
      |∑ d ∈ Finset.Icc 2 X, remainderTerm d| ≤
          ∑ d ∈ Finset.Icc 2 X, |remainderTerm d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 2 X, (1 : ℝ) := by
        exact Finset.sum_le_sum fun d hd => hremainderTerm d hd
      _ = ((Finset.Icc 2 X).card : ℝ) := by simp
  have hcardNat : (Finset.Icc 2 X).card + 1 ≤ X := by
    simp [Nat.card_Icc]
    omega
  have hcardReal : ((Finset.Icc 2 X).card : ℝ) + 1 ≤ (X : ℝ) := by
    exact_mod_cast hcardNat
  have hscaledAbs :
      |(X : ℝ) * signedMoebiusHarmonicPartialSum X| ≤ (X : ℝ) := by
    rw [hscaled, hremainderSum]
    calc
      |1 + ∑ d ∈ Finset.Icc 2 X, remainderTerm d| ≤
          1 + |∑ d ∈ Finset.Icc 2 X, remainderTerm d| := by
            simpa using abs_add_le (1 : ℝ) (∑ d ∈ Finset.Icc 2 X, remainderTerm d)
      _ ≤ 1 + ((Finset.Icc 2 X).card : ℝ) := add_le_add_left hremainderAbs 1
      _ ≤ (X : ℝ) := by linarith
  have hXRealPos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hmul :
      (X : ℝ) * |signedMoebiusHarmonicPartialSum X| ≤ (X : ℝ) * 1 := by
    simpa [abs_mul, abs_of_pos hXRealPos] using hscaledAbs
  exact (mul_le_mul_iff_right₀ hXRealPos).mp hmul

end

end Goldbach.Cert.MajorArcModules.RouteASignedMoebiusPartialSums
