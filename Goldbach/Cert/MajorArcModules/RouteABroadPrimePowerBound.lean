import Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt

/-!
# Sparse higher-prime-power contamination bound

This module turns the exact contamination expansion into a quantitative bound in terms of the
number of higher prime powers in the candidate support.  It is the key improvement over the old
Step 19 estimate: the cost is proportional to a sparse support cardinality, not to every integer
in `[2, N - 2]`.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerBound

open scoped BigOperators

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt

noncomputable section

/-- Non-prime prime powers that can occur as one component of a representation of `N`. -/
def higherPrimePowerSupport (N : ℕ) : Finset ℕ :=
  (primeCandidateSupport N).filter fun n => IsPrimePow n ∧ ¬Nat.Prime n

private lemma mem_support_sub_of_mem_support
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N) :
    N - n ∈ primeCandidateSupport N := by
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
  have hn_le : n ≤ N := le_trans hnN (Nat.sub_le N 2)
  have h2N : 2 ≤ N := le_trans hn2 hn_le
  have hn_add_two : n + 2 ≤ N := (Nat.le_sub_iff_add_le h2N).mp hnN
  have htwo_add_n : 2 + n ≤ N := by omega
  have hlower : 2 ≤ N - n := (Nat.le_sub_iff_add_le hn_le).mpr htwo_add_n
  have hupper : N - n ≤ N - 2 := Nat.sub_le_sub_left hn2 N
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

lemma higherPrimePowerSupport_subset (N : ℕ) :
    higherPrimePowerSupport N ⊆ primeCandidateSupport N := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

lemma higherPrimePowerWeight_eq_zero_of_mem_support_not_mem_higherSupport
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N)
    (hnot : n ∉ higherPrimePowerSupport N) :
    higherPrimePowerWeight n = 0 := by
  have hnotShape : ¬(IsPrimePow n ∧ ¬Nat.Prime n) := by
    intro hshape
    exact hnot (Finset.mem_filter.mpr ⟨hn, hshape⟩)
  by_cases hp : Nat.Prime n
  · exact higherPrimePowerWeight_eq_zero_of_prime hp
  · have hnotPow : ¬IsPrimePow n := by
      intro hpow
      exact hnotShape ⟨hpow, hp⟩
    exact higherPrimePowerWeight_eq_zero_of_not_isPrimePow hnotPow

lemma broadVonMangoldtWeight_le_log_of_mem_support
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N) :
    broadVonMangoldtWeight n ≤ Real.log (N : ℝ) := by
  have hnN : n ≤ N :=
    le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (Finset.mem_Icc.mp hn).1)
  have hVM : broadVonMangoldtWeight n ≤ Real.log (n : ℝ) := by
    simpa [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM] using
      (ArithmeticFunction.vonMangoldt_le_log (n := n))
  exact hVM.trans (Real.log_le_log hnPos (by exact_mod_cast hnN))

lemma primeWeight_le_log_of_mem_support
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N) :
    Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) :=
  (primeWeight_le_broadVonMangoldtWeight n).trans
    (broadVonMangoldtWeight_le_log_of_mem_support hn)

lemma higherPrimePowerWeight_le_log_of_mem_support
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N) :
    higherPrimePowerWeight n ≤ Real.log (N : ℝ) := by
  have hle : higherPrimePowerWeight n ≤ broadVonMangoldtWeight n := by
    unfold higherPrimePowerWeight
    linarith [lambda_nonneg n]
  exact hle.trans (broadVonMangoldtWeight_le_log_of_mem_support hn)

/-- A non-prime prime power has von Mangoldt weight at most half the ambient logarithm. -/
lemma higherPrimePowerWeight_le_half_log_of_mem_higherSupport
    {N n : ℕ} (hn : n ∈ higherPrimePowerSupport N) :
    higherPrimePowerWeight n ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
  have hnParts := Finset.mem_filter.mp hn
  have hnSupport := hnParts.1
  have hnShape := hnParts.2
  rcases (isPrimePow_nat_iff n).mp hnShape.1 with ⟨p, k, hp, hkPos, hpk⟩
  have hkTwo : 2 ≤ k := by
    have hkNeOne : k ≠ 1 := by
      intro hkOne
      apply hnShape.2
      rw [← hpk, hkOne, pow_one]
      exact hp
    omega
  have hnN : n ≤ N :=
    le_trans (Finset.mem_Icc.mp hnSupport).2 (Nat.sub_le N 2)
  have hpSqLeN : p ^ 2 ≤ N := by
    calc
      p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hkTwo
      _ = n := hpk
      _ ≤ N := hnN
  have hpSqPos : 0 < (((p ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast (pow_pos hp.pos 2)
  have hlogSqLe : Real.log (((p ^ 2 : ℕ) : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hpSqPos (by exact_mod_cast hpSqLeN)
  have hdouble : 2 * Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
    simpa [Nat.cast_pow, Real.log_pow] using hlogSqLe
  have hweight : higherPrimePowerWeight n = Real.log (p : ℝ) := by
    calc
      higherPrimePowerWeight n = broadVonMangoldtWeight n := by
        simp [higherPrimePowerWeight, Goldbach.BG_Bank.Λ, hnShape.2]
      _ = broadVonMangoldtWeight (p ^ k) := by rw [hpk]
      _ = Real.log (p : ℝ) := by
        simp [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM,
          ArithmeticFunction.vonMangoldt_apply_pow hkPos.ne',
          ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hweight]
  nlinarith

/-- The same half-log bound, with the zero cases outside the higher-prime-power support included. -/
lemma higherPrimePowerWeight_le_half_log_of_mem_support
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N) :
    higherPrimePowerWeight n ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
  by_cases hmem : n ∈ higherPrimePowerSupport N
  · exact higherPrimePowerWeight_le_half_log_of_mem_higherSupport hmem
  · rw [higherPrimePowerWeight_eq_zero_of_mem_support_not_mem_higherSupport hn hmem]
    have hnN : n ≤ N :=
      le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2)
        (le_trans (Finset.mem_Icc.mp hn).1 hnN))
    positivity

private noncomputable def primeHigherCross (N : ℕ) : ℝ :=
  ∑ n ∈ primeCandidateSupport N,
    Goldbach.BG_Bank.Λ n * higherPrimePowerWeight (N - n)

private noncomputable def higherPrimeCross (N : ℕ) : ℝ :=
  ∑ n ∈ primeCandidateSupport N,
    higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n)

private noncomputable def higherPrimeSquare (N : ℕ) : ℝ :=
  ∑ n ∈ primeCandidateSupport N,
    higherPrimePowerWeight n * higherPrimePowerWeight (N - n)

private lemma primeHigherCross_eq_higherPrimeCross (N : ℕ) :
    primeHigherCross N = higherPrimeCross N := by
  classical
  unfold primeHigherCross higherPrimeCross
  refine Finset.sum_nbij'
    (s := primeCandidateSupport N) (t := primeCandidateSupport N)
    (fun n => N - n) (fun n => N - n) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    exact mem_support_sub_of_mem_support hn
  · intro n hn
    exact mem_support_sub_of_mem_support hn
  · intro n hn
    have hnN : n ≤ N :=
      le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    exact Nat.sub_sub_self hnN
  · intro n hn
    have hnN : n ≤ N :=
      le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    exact Nat.sub_sub_self hnN
  · intro n hn
    have hnN : n ≤ N :=
      le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    rw [Nat.sub_sub_self hnN]
    ring

private lemma contamination_eq_crosses (N : ℕ) :
    broadPrimePowerContamination N
      = primeHigherCross N + higherPrimeCross N + higherPrimeSquare N := by
  unfold broadPrimePowerContamination primeHigherCross higherPrimeCross higherPrimeSquare
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

private lemma higherPrimeCross_le_card_mul_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    higherPrimeCross N
      ≤ (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := by
  classical
  have hsubset := higherPrimePowerSupport_subset N
  have hzero :
      ∀ n ∈ primeCandidateSupport N,
        n ∉ higherPrimePowerSupport N →
          higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n) = 0 := by
    intro n hn hnot
    rw [higherPrimePowerWeight_eq_zero_of_mem_support_not_mem_higherSupport hn hnot,
      zero_mul]
  unfold higherPrimeCross
  rw [← Finset.sum_subset hsubset hzero]
  calc
    (∑ n ∈ higherPrimePowerSupport N,
        higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n))
        ≤ ∑ _n ∈ higherPrimePowerSupport N, (Real.log (N : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnSupport : n ∈ primeCandidateSupport N := hsubset hn
      have hcompSupport : N - n ∈ primeCandidateSupport N :=
        mem_support_sub_of_mem_support hnSupport
      have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hTwo)
      simpa [pow_two] using
        (mul_le_mul
          (higherPrimePowerWeight_le_log_of_mem_support hnSupport)
          (primeWeight_le_log_of_mem_support hcompSupport)
          (lambda_nonneg (N - n))
          (Real.log_nonneg hNOne))
    _ = (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := by
      simp

private lemma higherPrimeSquare_le_card_mul_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    higherPrimeSquare N
      ≤ (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := by
  classical
  have hsubset := higherPrimePowerSupport_subset N
  have hzero :
      ∀ n ∈ primeCandidateSupport N,
        n ∉ higherPrimePowerSupport N →
          higherPrimePowerWeight n * higherPrimePowerWeight (N - n) = 0 := by
    intro n hn hnot
    rw [higherPrimePowerWeight_eq_zero_of_mem_support_not_mem_higherSupport hn hnot,
      zero_mul]
  unfold higherPrimeSquare
  rw [← Finset.sum_subset hsubset hzero]
  calc
    (∑ n ∈ higherPrimePowerSupport N,
        higherPrimePowerWeight n * higherPrimePowerWeight (N - n))
        ≤ ∑ _n ∈ higherPrimePowerSupport N, (Real.log (N : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnSupport : n ∈ primeCandidateSupport N := hsubset hn
      have hcompSupport : N - n ∈ primeCandidateSupport N :=
        mem_support_sub_of_mem_support hnSupport
      have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hTwo)
      simpa [pow_two] using
        (mul_le_mul
          (higherPrimePowerWeight_le_log_of_mem_support hnSupport)
          (higherPrimePowerWeight_le_log_of_mem_support hcompSupport)
          (higherPrimePowerWeight_nonneg (N - n))
          (Real.log_nonneg hNOne))
    _ = (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := by
      simp

private lemma higherPrimeCross_le_half_card_mul_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    higherPrimeCross N
      ≤ (1 / 2 : ℝ) * (higherPrimePowerSupport N).card
          * (Real.log (N : ℝ)) ^ 2 := by
  classical
  have hsubset := higherPrimePowerSupport_subset N
  have hzero :
      ∀ n ∈ primeCandidateSupport N,
        n ∉ higherPrimePowerSupport N →
          higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n) = 0 := by
    intro n hn hnot
    rw [higherPrimePowerWeight_eq_zero_of_mem_support_not_mem_higherSupport hn hnot,
      zero_mul]
  unfold higherPrimeCross
  rw [← Finset.sum_subset hsubset hzero]
  calc
    (∑ n ∈ higherPrimePowerSupport N,
        higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n))
        ≤ ∑ _n ∈ higherPrimePowerSupport N,
            (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnSupport : n ∈ primeCandidateSupport N := hsubset hn
      have hcompSupport : N - n ∈ primeCandidateSupport N :=
        mem_support_sub_of_mem_support hnSupport
      have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hTwo)
      have hhalfNonneg : 0 ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
        positivity
      have hmul :=
        mul_le_mul
          (higherPrimePowerWeight_le_half_log_of_mem_higherSupport hn)
          (primeWeight_le_log_of_mem_support hcompSupport)
          (lambda_nonneg (N - n)) hhalfNonneg
      calc
        higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n)
            ≤ ((1 / 2 : ℝ) * Real.log (N : ℝ)) * Real.log (N : ℝ) := hmul
        _ = (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by ring
    _ = (1 / 2 : ℝ) * (higherPrimePowerSupport N).card
          * (Real.log (N : ℝ)) ^ 2 := by
      simp
      ring

private lemma higherPrimeSquare_le_quarter_card_mul_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    higherPrimeSquare N
      ≤ (1 / 4 : ℝ) * (higherPrimePowerSupport N).card
          * (Real.log (N : ℝ)) ^ 2 := by
  classical
  have hsubset := higherPrimePowerSupport_subset N
  have hzero :
      ∀ n ∈ primeCandidateSupport N,
        n ∉ higherPrimePowerSupport N →
          higherPrimePowerWeight n * higherPrimePowerWeight (N - n) = 0 := by
    intro n hn hnot
    rw [higherPrimePowerWeight_eq_zero_of_mem_support_not_mem_higherSupport hn hnot,
      zero_mul]
  unfold higherPrimeSquare
  rw [← Finset.sum_subset hsubset hzero]
  calc
    (∑ n ∈ higherPrimePowerSupport N,
        higherPrimePowerWeight n * higherPrimePowerWeight (N - n))
        ≤ ∑ _n ∈ higherPrimePowerSupport N,
            (1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnSupport : n ∈ primeCandidateSupport N := hsubset hn
      have hcompSupport : N - n ∈ primeCandidateSupport N :=
        mem_support_sub_of_mem_support hnSupport
      have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hTwo)
      have hhalfNonneg : 0 ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
        positivity
      have hmul :=
        mul_le_mul
          (higherPrimePowerWeight_le_half_log_of_mem_higherSupport hn)
          (higherPrimePowerWeight_le_half_log_of_mem_support hcompSupport)
          (higherPrimePowerWeight_nonneg (N - n)) hhalfNonneg
      calc
        higherPrimePowerWeight n * higherPrimePowerWeight (N - n)
            ≤ ((1 / 2 : ℝ) * Real.log (N : ℝ))
                * ((1 / 2 : ℝ) * Real.log (N : ℝ)) := hmul
        _ = (1 / 4 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by ring
    _ = (1 / 4 : ℝ) * (higherPrimePowerSupport N).card
          * (Real.log (N : ℝ)) ^ 2 := by
      simp
      ring

/--
The contamination costs at most three log-squared units per non-prime prime power in the candidate
support.  This is the sparse replacement for the old interval-cardinality bound.
-/
theorem broadPrimePowerContamination_le_card_mul_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    broadPrimePowerContamination N
      ≤ 3 * (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := by
  have hCross := higherPrimeCross_le_card_mul_log_sq hTwo
  have hSquare := higherPrimeSquare_le_card_mul_log_sq hTwo
  rw [contamination_eq_crosses, primeHigherCross_eq_higherPrimeCross]
  nlinarith

/--
Refined sparse bound.  Each higher-prime-power occurrence costs at most half a logarithm, so the
two cross terms and the square term cost `1/2 + 1/2 + 1/4 = 5/4` log-squared units.
-/
theorem broadPrimePowerContamination_le_five_fourths_card_mul_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    broadPrimePowerContamination N
      ≤ (5 / 4 : ℝ) * (higherPrimePowerSupport N).card
          * (Real.log (N : ℝ)) ^ 2 := by
  have hCross := higherPrimeCross_le_half_card_mul_log_sq hTwo
  have hSquare := higherPrimeSquare_le_quarter_card_mul_log_sq hTwo
  rw [contamination_eq_crosses, primeHigherCross_eq_higherPrimeCross]
  nlinarith

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerBound
