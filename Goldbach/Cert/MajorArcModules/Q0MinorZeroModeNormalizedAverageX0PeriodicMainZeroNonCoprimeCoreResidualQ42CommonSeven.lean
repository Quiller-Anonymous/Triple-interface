import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private lemma q42_even_window_eq_image_range_halfH_add_one_of_isEven
    {X : ℕ} (hXEven : Goldbach.Windows.IsEven X) :
    EvenIn X H = (Finset.range (H / 2 + 1)).image (fun k : ℕ => X + 2 * k) := by
  classical
  ext N
  constructor
  · intro hN
    rcases Goldbach.ProofTools.Windows.mem_EvenIn_iff (X := X) (H := H) (N := N) |>.mp hN with ⟨hIcc, hNEven⟩
    have hXle : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_IccShift hIcc
    have hdiffEven : Goldbach.Windows.IsEven (N - X) := by
      dsimp [Goldbach.Windows.IsEven] at hXEven hNEven ⊢
      omega
    have hdiffNatEven : Even (N - X) := Goldbach.Windows.even_of_isEven hdiffEven
    refine Finset.mem_image.mpr ?_
    refine ⟨(N - X) / 2, Finset.mem_range.mpr ?_, ?_⟩
    · have hsub : N - X ≤ H := by
        exact Goldbach.ProofTools.Windows.sub_left_le_of_mem_IccShift hIcc
      have hk : (N - X) / 2 ≤ H / 2 := Nat.div_le_div_right hsub
      exact Nat.lt_succ_of_le hk
    · calc
        X + 2 * ((N - X) / 2)
            = X + (N - X) := by
                rw [Nat.two_mul_div_two_of_even hdiffNatEven]
        _ = N := Nat.add_sub_of_le hXle
  · intro hN
    rcases Finset.mem_image.mp hN with ⟨k, hk, rfl⟩
    refine Goldbach.ProofTools.Windows.mem_EvenIn_of_mem_IccShift_of_even ?_ ?_
    · unfold Goldbach.Windows.IccShift
      refine Finset.mem_image.mpr ?_
      refine ⟨2 * k, Finset.mem_range.mpr ?_, rfl⟩
      have hk' : k ≤ H / 2 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have : 2 * k ≤ H := by
        omega
      exact lt_of_le_of_lt this (Nat.lt_succ_self H)
    · dsimp [Goldbach.Windows.IsEven] at hXEven ⊢
      omega

private theorem q42_periodic_shift_mul
    {α : Type*} (f : ℕ → α) {P : ℕ}
    (hper : ∀ k, f (k + P) = f k) :
    ∀ m k : ℕ, f (k + m * P) = f k
  | 0, k => by simp
  | m + 1, k => by
      rw [Nat.succ_mul, ← Nat.add_assoc, hper]
      exact q42_periodic_shift_mul f hper m k

private theorem q42_periodic_sum_range_mul
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {P : ℕ} (hP : 0 < P)
    (hper : ∀ k, f (k + P) = f k) :
    ∀ m : ℕ, ∑ k ∈ Finset.range (m * P), f k = m • ∑ k ∈ Finset.range P, f k
  | 0 => by simp
  | m + 1 => by
      calc
        ∑ k ∈ Finset.range ((m + 1) * P), f k
            =
          ∑ k ∈ Finset.range (m * P), f k
            + ∑ k ∈ Finset.range P, f (m * P + k) := by
                simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  (Finset.sum_range_add f (m * P) P)
        _ = m • ∑ k ∈ Finset.range P, f k + ∑ k ∈ Finset.range P, f (m * P + k) := by
              rw [q42_periodic_sum_range_mul f hP hper m]
        _ = m • ∑ k ∈ Finset.range P, f k + ∑ k ∈ Finset.range P, f k := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hshift : f (k + m * P) = f k :=
                q42_periodic_shift_mul f hper m k
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift
        _ = (m + 1) • ∑ k ∈ Finset.range P, f k := by
              simpa [add_comm] using (succ_nsmul (∑ k ∈ Finset.range P, f k) m).symm

private theorem q42_periodic_sum_range_blocks_add_remainder
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {P : ℕ} (hP : 0 < P)
    (hper : ∀ k, f (k + P) = f k)
    (m r : ℕ) :
    ∑ k ∈ Finset.range (m * P + r), f k
      =
    m • ∑ k ∈ Finset.range P, f k
      + ∑ k ∈ Finset.range r, f (m * P + k) := by
  calc
    ∑ k ∈ Finset.range (m * P + r), f k
        =
      ∑ k ∈ Finset.range (m * P), f k
        + ∑ k ∈ Finset.range r, f (m * P + k) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Finset.sum_range_add f (m * P) r)
    _ =
      m • ∑ k ∈ Finset.range P, f k
        + ∑ k ∈ Finset.range r, f (m * P + k) := by
          rw [q42_periodic_sum_range_mul f hP hper m]

private theorem q42_X0_isEven : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

private theorem q42_evenIn_X0_H_card_eq_5001 :
    (EvenIn X0 H).card = 5001 := by
  rw [q42_even_window_eq_image_range_halfH_add_one_of_isEven q42_X0_isEven]
  rw [Finset.card_image_of_injective]
  · norm_num [H]
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (Nat.add_left_cancel hab)

private theorem q42_ramanujanGcdClassIndicatorRat_twentyOne_period_on_even_progression
    {g X k : ℕ} :
    ramanujanGcdClassIndicatorRat 21 g (X + 2 * (k + 21))
      =
    ramanujanGcdClassIndicatorRat 21 g (X + 2 * k) := by
  unfold ramanujanGcdClassIndicatorRat
  have hgcd :
      Nat.gcd 21 (X + 2 * (k + 21)) = Nat.gcd 21 (X + 2 * k) := by
    calc
      Nat.gcd 21 (X + 2 * (k + 21))
          = Nat.gcd 21 ((X + 2 * k) + 2 * 21) := by ring_nf
      _ = Nat.gcd 21 (X + 2 * k) := by
            rw [Nat.gcd_add_mul_right_right]
  rw [hgcd]

private theorem q42_sum_range_twentyOne_indicatorRat_twentyOne_one_X0 :
    ∑ k ∈ Finset.range 21, ramanujanGcdClassIndicatorRat 21 1 (X0 + 2 * k) = 12 := by
  native_decide

private theorem q42_sum_range_twentyOne_indicatorRat_twentyOne_three_X0 :
    ∑ k ∈ Finset.range 21, ramanujanGcdClassIndicatorRat 21 3 (X0 + 2 * k) = 6 := by
  native_decide

private theorem q42_sum_range_twentyOne_indicatorRat_twentyOne_seven_X0 :
    ∑ k ∈ Finset.range 21, ramanujanGcdClassIndicatorRat 21 7 (X0 + 2 * k) = 2 := by
  native_decide

private theorem q42_sum_range_twentyOne_indicatorRat_twentyOne_twentyOne_X0 :
    ∑ k ∈ Finset.range 21, ramanujanGcdClassIndicatorRat 21 21 (X0 + 2 * k) = 1 := by
  native_decide

private theorem q42_sum_range_three_indicatorRat_twentyOne_one_X0 :
    ∑ x ∈ Finset.range 3, ramanujanGcdClassIndicatorRat 21 1 (X0 + 2 * (4998 + x)) = 2 := by
  native_decide

private theorem q42_sum_range_three_indicatorRat_twentyOne_three_X0 :
    ∑ x ∈ Finset.range 3, ramanujanGcdClassIndicatorRat 21 3 (X0 + 2 * (4998 + x)) = 1 := by
  native_decide

private theorem q42_sum_range_three_indicatorRat_twentyOne_seven_X0 :
    ∑ x ∈ Finset.range 3, ramanujanGcdClassIndicatorRat 21 7 (X0 + 2 * (4998 + x)) = 0 := by
  native_decide

private theorem q42_sum_range_three_indicatorRat_twentyOne_twentyOne_X0 :
    ∑ x ∈ Finset.range 3, ramanujanGcdClassIndicatorRat 21 21 (X0 + 2 * (4998 + x)) = 0 := by
  native_decide

private theorem q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_one_X0 :
    ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 1 N = 2858 := by
  rw [q42_even_window_eq_image_range_halfH_add_one_of_isEven q42_X0_isEven]
  have hsum :
      ∑ N ∈ (Finset.range (H / 2 + 1)).image (fun k : ℕ => X0 + 2 * k),
          ramanujanGcdClassIndicatorRat 21 1 N
        =
      ∑ k ∈ Finset.range (H / 2 + 1),
          ramanujanGcdClassIndicatorRat 21 1 (X0 + 2 * k) := by
    rw [Finset.sum_image]
    simp
  rw [hsum]
  have hlen : H / 2 + 1 = 238 * 21 + 3 := by
    norm_num [H]
  rw [hlen]
  rw [q42_periodic_sum_range_blocks_add_remainder
    (f := fun k => ramanujanGcdClassIndicatorRat 21 1 (X0 + 2 * k))
    (hP := by norm_num)
    (hper := fun k =>
      q42_ramanujanGcdClassIndicatorRat_twentyOne_period_on_even_progression
        (g := 1) (X := X0) (k := k))
    (m := 238) (r := 3)]
  rw [q42_sum_range_twentyOne_indicatorRat_twentyOne_one_X0,
    show 238 * 21 = 4998 by norm_num,
    q42_sum_range_three_indicatorRat_twentyOne_one_X0]
  norm_num

private theorem q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_three_X0 :
    ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 3 N = 1429 := by
  rw [q42_even_window_eq_image_range_halfH_add_one_of_isEven q42_X0_isEven]
  have hsum :
      ∑ N ∈ (Finset.range (H / 2 + 1)).image (fun k : ℕ => X0 + 2 * k),
          ramanujanGcdClassIndicatorRat 21 3 N
        =
      ∑ k ∈ Finset.range (H / 2 + 1),
          ramanujanGcdClassIndicatorRat 21 3 (X0 + 2 * k) := by
    rw [Finset.sum_image]
    simp
  rw [hsum]
  have hlen : H / 2 + 1 = 238 * 21 + 3 := by
    norm_num [H]
  rw [hlen]
  rw [q42_periodic_sum_range_blocks_add_remainder
    (f := fun k => ramanujanGcdClassIndicatorRat 21 3 (X0 + 2 * k))
    (hP := by norm_num)
    (hper := fun k =>
      q42_ramanujanGcdClassIndicatorRat_twentyOne_period_on_even_progression
        (g := 3) (X := X0) (k := k))
    (m := 238) (r := 3)]
  rw [q42_sum_range_twentyOne_indicatorRat_twentyOne_three_X0,
    show 238 * 21 = 4998 by norm_num,
    q42_sum_range_three_indicatorRat_twentyOne_three_X0]
  norm_num

private theorem q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_seven_X0 :
    ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 7 N = 476 := by
  rw [q42_even_window_eq_image_range_halfH_add_one_of_isEven q42_X0_isEven]
  have hsum :
      ∑ N ∈ (Finset.range (H / 2 + 1)).image (fun k : ℕ => X0 + 2 * k),
          ramanujanGcdClassIndicatorRat 21 7 N
        =
      ∑ k ∈ Finset.range (H / 2 + 1),
          ramanujanGcdClassIndicatorRat 21 7 (X0 + 2 * k) := by
    rw [Finset.sum_image]
    simp
  rw [hsum]
  have hlen : H / 2 + 1 = 238 * 21 + 3 := by
    norm_num [H]
  rw [hlen]
  rw [q42_periodic_sum_range_blocks_add_remainder
    (f := fun k => ramanujanGcdClassIndicatorRat 21 7 (X0 + 2 * k))
    (hP := by norm_num)
    (hper := fun k =>
      q42_ramanujanGcdClassIndicatorRat_twentyOne_period_on_even_progression
        (g := 7) (X := X0) (k := k))
    (m := 238) (r := 3)]
  rw [q42_sum_range_twentyOne_indicatorRat_twentyOne_seven_X0,
    show 238 * 21 = 4998 by norm_num,
    q42_sum_range_three_indicatorRat_twentyOne_seven_X0]
  norm_num

private theorem q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_twentyOne_X0 :
    ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 21 N = 238 := by
  rw [q42_even_window_eq_image_range_halfH_add_one_of_isEven q42_X0_isEven]
  have hsum :
      ∑ N ∈ (Finset.range (H / 2 + 1)).image (fun k : ℕ => X0 + 2 * k),
          ramanujanGcdClassIndicatorRat 21 21 N
        =
      ∑ k ∈ Finset.range (H / 2 + 1),
          ramanujanGcdClassIndicatorRat 21 21 (X0 + 2 * k) := by
    rw [Finset.sum_image]
    simp
  rw [hsum]
  have hlen : H / 2 + 1 = 238 * 21 + 3 := by
    norm_num [H]
  rw [hlen]
  rw [q42_periodic_sum_range_blocks_add_remainder
    (f := fun k => ramanujanGcdClassIndicatorRat 21 21 (X0 + 2 * k))
    (hP := by norm_num)
    (hper := fun k =>
      q42_ramanujanGcdClassIndicatorRat_twentyOne_period_on_even_progression
        (g := 21) (X := X0) (k := k))
    (m := 238) (r := 3)]
  rw [q42_sum_range_twentyOne_indicatorRat_twentyOne_twentyOne_X0,
    show 238 * 21 = 4998 by norm_num,
    q42_sum_range_three_indicatorRat_twentyOne_twentyOne_X0]
  norm_num

private theorem q42_ramanujanGcdClassWindowAverageRat_twentyOne_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 1)).card : ℚ) = 2858 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 1)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 1 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 21 N = 1 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 1))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 2858 := q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_one_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [q42_evenIn_X0_H_card_eq_5001, hcount]
  norm_num

private theorem q42_ramanujanGcdClassWindowAverageRat_twentyOne_three_X0 :
    ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 3)).card : ℚ) = 1429 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 3)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 3 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 21 N = 3 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 3))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 1429 := q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_three_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [q42_evenIn_X0_H_card_eq_5001, hcount]
  norm_num

private theorem q42_ramanujanGcdClassWindowAverageRat_twentyOne_seven_X0 :
    ramanujanGcdClassWindowAverageRat X0 21 7 = (476 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 7)).card : ℚ) = 476 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 7)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 7 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 21 N = 7 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 7))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 476 := q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_seven_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [q42_evenIn_X0_H_card_eq_5001, hcount]
  norm_num

private theorem q42_ramanujanGcdClassWindowAverageRat_twentyOne_twentyOne_X0 :
    ramanujanGcdClassWindowAverageRat X0 21 21 = (238 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 21)).card : ℚ) = 238 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 21)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 21 21 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 21 N = 21 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 21 N = 21))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 238 := q42_sum_ramanujanGcdClassIndicatorRat_twentyOne_twentyOne_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [q42_evenIn_X0_H_card_eq_5001, hcount]
  norm_num

private theorem q42_133_avgRat_zero_of_odd_left
    {g : ℕ} (hgOdd : ¬ Goldbach.Windows.IsEven g) :
    ramanujanGcdClassWindowAverageRat X0 42 g = 0 := by
  classical
  unfold ramanujanGcdClassWindowAverageRat
  have hEmpty :
      ((EvenIn X0 H).filter (fun N => Nat.gcd 42 N = g)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro N hN
    rcases Finset.mem_filter.mp hN with ⟨hNEvenIn, hgcd⟩
    have hNEven : Goldbach.Windows.IsEven N :=
      (Goldbach.ProofTools.Windows.mem_EvenIn_iff
        (X := X0) (H := H) (N := N)).1 hNEvenIn |>.2
    have h2N : 2 ∣ N :=
      (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hNEven)
    have h2gcd : 2 ∣ Nat.gcd 42 N :=
      Nat.dvd_gcd (by norm_num) h2N
    have hgEven : Goldbach.Windows.IsEven g := by
      have hEvenGcd : Goldbach.Windows.IsEven (Nat.gcd 42 N) :=
        Goldbach.Windows.isEven_of_even ((even_iff_two_dvd).2 h2gcd)
      rwa [hgcd] at hEvenGcd
    exact hgOdd hgEven
  rw [hEmpty]
  simp only [Finset.card_empty, Nat.cast_zero, zero_div]

private theorem q42_133_avgRat_two_mul_eq_of_odd_divisor
    {n g : ℕ} (hnOdd : Odd n) (hg : g ∈ n.divisors) :
    ramanujanGcdClassWindowAverageRat X0 (2 * n) (2 * g)
      =
    ramanujanGcdClassWindowAverageRat X0 n g := by
  have hreal :
      ramanujanGcdClassWindowAverage X0 (2 * n) (2 * g)
        =
      ramanujanGcdClassWindowAverage X0 n g :=
    ramanujanGcdClassWindowAverage_two_mul_eq_of_odd_divisor
      (X := X0) hnOdd hg
  rw [ramanujanGcdClassWindowAverage_eq_ratCast,
    ramanujanGcdClassWindowAverage_eq_ratCast] at hreal
  exact Rat.cast_injective (α := ℝ) hreal

private theorem q42_133_pairResolved_zero_of_odd_lcm_even_joint
    {g h : ℕ}
    (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h))
    (hJointEven :
      Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus 42 133 g h)) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 g h = 0 := by
  by_cases hcompat : ramanujanGcdClassJointCompatibility 42 133 g h
  · rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible hcompat]
    exact rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus
      X0 42 133 g h hOddL hJointEven
  · exact rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible hcompat

private def q42_133_inner (g h : ℕ) : ℚ :=
  rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 g h
    - ramanujanGcdClassWindowAverageRat X0 133 h
        * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 g
    - ramanujanGcdClassWindowAverageRat X0 42 g
        * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 h
    + ramanujanGcdClassWindowAverageRat X0 42 g
        * ramanujanGcdClassWindowAverageRat X0 133 h
        * evenRamanujanBlockCountRat 42 133

private def q42_133_term (g h : ℕ) : ℚ :=
  ramanujanGcdClassCoeffRat 42 g * ramanujanGcdClassCoeffRat 133 h
    * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
        • q42_133_inner g h)

private theorem q42_133_term_zero_of_left_odd
    {g h : ℕ}
    (hgOdd : ¬ Goldbach.Windows.IsEven g)
    (hQuotEven : Goldbach.Windows.IsEven (42 / g))
    (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h))
    (hJointEven :
      Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus 42 133 g h)) :
    q42_133_term g h = 0 := by
  have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 42 g = 0 :=
    q42_133_avgRat_zero_of_odd_left hgOdd
  have hBlockLeft :
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 g = 0 :=
    rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient
      X0 42 133 42 g hgOdd hQuotEven
  have hPair :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 g h = 0 :=
    q42_133_pairResolved_zero_of_odd_lcm_even_joint hOddL hJointEven
  simp [q42_133_term, q42_133_inner, hAvgLeft, hBlockLeft, hPair]

theorem periodicMainPair_42_133_X1000000_divRight :
    Nat.divisors 133 = ([1, 7, 19, 133] : List ℕ).toFinset := by
  decide

private theorem q42_133_row_zero_of_left_odd
    {g : ℕ}
    (hgOdd : ¬ Goldbach.Windows.IsEven g)
    (hQuotEven : Goldbach.Windows.IsEven (42 / g))
    (hOddL1 : ¬ Goldbach.Windows.IsEven (Nat.lcm g 1))
    (hOddL7 : ¬ Goldbach.Windows.IsEven (Nat.lcm g 7))
    (hOddL19 : ¬ Goldbach.Windows.IsEven (Nat.lcm g 19))
    (hOddL133 : ¬ Goldbach.Windows.IsEven (Nat.lcm g 133))
    (hJoint1 :
      Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus 42 133 g 1))
    (hJoint7 :
      Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus 42 133 g 7))
    (hJoint19 :
      Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus 42 133 g 19))
    (hJoint133 :
      Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus 42 133 g 133)) :
    (∑ h ∈ Nat.divisors 133, q42_133_term g h) = 0 := by
  rw [periodicMainPair_42_133_X1000000_divRight]
  have h1 : q42_133_term g 1 = 0 :=
    q42_133_term_zero_of_left_odd hgOdd hQuotEven hOddL1 hJoint1
  have h7 : q42_133_term g 7 = 0 :=
    q42_133_term_zero_of_left_odd hgOdd hQuotEven hOddL7 hJoint7
  have h19 : q42_133_term g 19 = 0 :=
    q42_133_term_zero_of_left_odd hgOdd hQuotEven hOddL19 hJoint19
  have h133 : q42_133_term g 133 = 0 :=
    q42_133_term_zero_of_left_odd hgOdd hQuotEven hOddL133 hJoint133
  simp [Finset.sum_insert, h1, h7, h19, h133]

theorem periodicMainPair_42_133_X1000000_row_1_struct :
    (∑ h ∈ Nat.divisors 133,
      ramanujanGcdClassCoeffRat 42 1 * ramanujanGcdClassCoeffRat 133 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 1 h
                - ramanujanGcdClassWindowAverageRat X0 133 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 1
                - ramanujanGcdClassWindowAverageRat X0 42 1
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 h
                + ramanujanGcdClassWindowAverageRat X0 42 1
                    * ramanujanGcdClassWindowAverageRat X0 133 h
                    * evenRamanujanBlockCountRat 42 133))) = 0 := by
  change (∑ h ∈ Nat.divisors 133, q42_133_term 1 h) = 0
  exact q42_133_row_zero_of_left_odd
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem periodicMainPair_42_133_X1000000_row_3_struct :
    (∑ h ∈ Nat.divisors 133,
      ramanujanGcdClassCoeffRat 42 3 * ramanujanGcdClassCoeffRat 133 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 3 h
                - ramanujanGcdClassWindowAverageRat X0 133 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 3
                - ramanujanGcdClassWindowAverageRat X0 42 3
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 h
                + ramanujanGcdClassWindowAverageRat X0 42 3
                    * ramanujanGcdClassWindowAverageRat X0 133 h
                    * evenRamanujanBlockCountRat 42 133))) = 0 := by
  change (∑ h ∈ Nat.divisors 133, q42_133_term 3 h) = 0
  exact q42_133_row_zero_of_left_odd
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem periodicMainPair_42_133_X1000000_row_7_struct :
    (∑ h ∈ Nat.divisors 133,
      ramanujanGcdClassCoeffRat 42 7 * ramanujanGcdClassCoeffRat 133 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 7 h
                - ramanujanGcdClassWindowAverageRat X0 133 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 7
                - ramanujanGcdClassWindowAverageRat X0 42 7
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 h
                + ramanujanGcdClassWindowAverageRat X0 42 7
                    * ramanujanGcdClassWindowAverageRat X0 133 h
                    * evenRamanujanBlockCountRat 42 133))) = 0 := by
  change (∑ h ∈ Nat.divisors 133, q42_133_term 7 h) = 0
  exact q42_133_row_zero_of_left_odd
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem periodicMainPair_42_133_X1000000_row_21_struct :
    (∑ h ∈ Nat.divisors 133,
      ramanujanGcdClassCoeffRat 42 21 * ramanujanGcdClassCoeffRat 133 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 21 h
                - ramanujanGcdClassWindowAverageRat X0 133 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 21
                - ramanujanGcdClassWindowAverageRat X0 42 21
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 h
                + ramanujanGcdClassWindowAverageRat X0 42 21
                    * ramanujanGcdClassWindowAverageRat X0 133 h
                    * evenRamanujanBlockCountRat 42 133))) = 0 := by
  change (∑ h ∈ Nat.divisors 133, q42_133_term 21 h) = 0
  exact q42_133_row_zero_of_left_odd
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

private theorem q42_133_inner_2_eq_two_mul_inner_6
    {h : ℕ}
    (hPair :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 h
        =
      2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 h) :
    q42_133_inner 2 h = 2 * q42_133_inner 6 h := by
  have hAvg :
      ramanujanGcdClassWindowAverageRat X0 42 2
        = 2 * ramanujanGcdClassWindowAverageRat X0 42 6 := by
    have h2 :
        ramanujanGcdClassWindowAverageRat X0 42 2
          =
        ramanujanGcdClassWindowAverageRat X0 21 1 := by
      simpa using
        q42_133_avgRat_two_mul_eq_of_odd_divisor
          (n := 21) (g := 1) (by decide) (by decide)
    have h6 :
        ramanujanGcdClassWindowAverageRat X0 42 6
          =
        ramanujanGcdClassWindowAverageRat X0 21 3 := by
      simpa using
        q42_133_avgRat_two_mul_eq_of_odd_divisor
          (n := 21) (g := 3) (by decide) (by decide)
    have hAvg21_1 :
        ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 :=
      q42_ramanujanGcdClassWindowAverageRat_twentyOne_one_X0
    have hAvg21_3 :
        ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 :=
      q42_ramanujanGcdClassWindowAverageRat_twentyOne_three_X0
    rw [h2, h6, hAvg21_1, hAvg21_3]
    norm_num
  have hBlock :
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 2
        =
      2 * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 6 := by
    have h2 :
        rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 2 = (456 : ℚ) := by
      rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    have h6 :
        rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 6 = (228 : ℚ) := by
      rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    rw [h2, h6]
    norm_num
  unfold q42_133_inner
  rw [hPair, hAvg, hBlock]
  ring

private theorem q42_133_termPair_2_6_zero
    {h : ℕ}
    (hPair :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 h
        =
      2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 h) :
    q42_133_term 2 h + q42_133_term 6 h = 0 := by
  have hInner := q42_133_inner_2_eq_two_mul_inner_6 hPair
  have hCoeff2 : ramanujanGcdClassCoeffRat 42 2 = (1 : ℚ) := by
    native_decide
  have hCoeff6 : ramanujanGcdClassCoeffRat 42 6 = (-2 : ℚ) := by
    native_decide
  let C := ramanujanGcdClassCoeffRat 133 h
  let S : ℚ := (((H + 1) / centeredRamanujanPairBlockPeriod 42 133 : ℕ) : ℚ)
  let I := q42_133_inner 6 h
  unfold q42_133_term
  rw [hInner, hCoeff2, hCoeff6]
  simp only [nsmul_eq_mul]
  change (1 * C * (S * (2 * I))) + ((-2) * C * (S * I)) = 0
  ring

private theorem q42_133_inner_14_eq_two_mul_inner_42
    {h : ℕ}
    (hPair :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 h
        =
      2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 h) :
    q42_133_inner 14 h = 2 * q42_133_inner 42 h := by
  have hAvg :
      ramanujanGcdClassWindowAverageRat X0 42 14
        = 2 * ramanujanGcdClassWindowAverageRat X0 42 42 := by
    have h14 :
        ramanujanGcdClassWindowAverageRat X0 42 14
          =
        ramanujanGcdClassWindowAverageRat X0 21 7 := by
      simpa using
        q42_133_avgRat_two_mul_eq_of_odd_divisor
          (n := 21) (g := 7) (by decide) (by decide)
    have h42 :
        ramanujanGcdClassWindowAverageRat X0 42 42
          =
        ramanujanGcdClassWindowAverageRat X0 21 21 := by
      simpa using
        q42_133_avgRat_two_mul_eq_of_odd_divisor
          (n := 21) (g := 21) (by decide) (by decide)
    have hAvg21_7 :
        ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 :=
      q42_ramanujanGcdClassWindowAverageRat_twentyOne_seven_X0
    have hAvg21_21 :
        ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 :=
      q42_ramanujanGcdClassWindowAverageRat_twentyOne_twentyOne_X0
    rw [h14, h42, hAvg21_7, hAvg21_21]
    norm_num
  have hBlock :
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 14
        =
      2 * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 42 := by
    have h14 :
        rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 14 = (76 : ℚ) := by
      rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    have h42 :
        rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 42 = (38 : ℚ) := by
      rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    rw [h14, h42]
    norm_num
  unfold q42_133_inner
  rw [hPair, hAvg, hBlock]
  ring

private theorem q42_133_termPair_14_42_zero
    {h : ℕ}
    (hPair :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 h
        =
      2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 h) :
    q42_133_term 14 h + q42_133_term 42 h = 0 := by
  have hInner := q42_133_inner_14_eq_two_mul_inner_42 hPair
  have hCoeff14 : ramanujanGcdClassCoeffRat 42 14 = (-6 : ℚ) := by
    native_decide
  have hCoeff42 : ramanujanGcdClassCoeffRat 42 42 = (12 : ℚ) := by
    native_decide
  let C := ramanujanGcdClassCoeffRat 133 h
  let S : ℚ := (((H + 1) / centeredRamanujanPairBlockPeriod 42 133 : ℕ) : ℚ)
  let I := q42_133_inner 42 h
  unfold q42_133_term
  rw [hInner, hCoeff14, hCoeff42]
  simp only [nsmul_eq_mul]
  change ((-6) * C * (S * (2 * I))) + (12 * C * (S * I)) = 0
  ring

private theorem q42_133_pair_2_1_eq_two_mul_pair_6_1 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 1
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 1 := by
  have h2 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 1 = (432 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have h6 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 1 = (216 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  rw [h2, h6]
  norm_num

private theorem q42_133_pair_2_7_eq_two_mul_pair_6_7 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 7
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 7 := by
  have h2 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 7 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  have h6 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 7 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  rw [h2, h6]
  norm_num

private theorem q42_133_pair_2_19_eq_two_mul_pair_6_19 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 19
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 19 := by
  have h2 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 19 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have h6 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 19 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  rw [h2, h6]
  norm_num

private theorem q42_133_pair_2_133_eq_two_mul_pair_6_133 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 133
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 133 := by
  have h2 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 2 133 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  have h6 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 6 133 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  rw [h2, h6]
  norm_num

private theorem q42_133_pair_14_1_eq_two_mul_pair_42_1 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 1
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 1 := by
  have h14 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 1 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  have h42 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 1 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  rw [h14, h42]
  norm_num

private theorem q42_133_pair_14_7_eq_two_mul_pair_42_7 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 7
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 7 := by
  have h14 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 7 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have h42 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 7 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  rw [h14, h42]
  norm_num

private theorem q42_133_pair_14_19_eq_two_mul_pair_42_19 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 19
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 19 := by
  have h14 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 19 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  have h42 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 19 = (0 : ℚ) :=
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
      (by native_decide)
  rw [h14, h42]
  norm_num

private theorem q42_133_pair_14_133_eq_two_mul_pair_42_133 :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 133
      =
    2 * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 133 := by
  have h14 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 133 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have h42 :
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 133 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  rw [h14, h42]
  norm_num

theorem periodicMainPair_42_133_X1000000_rows_2_6_struct :
    (∑ h ∈ Nat.divisors 133, q42_133_term 2 h)
      + (∑ h ∈ Nat.divisors 133, q42_133_term 6 h) = 0 := by
  rw [periodicMainPair_42_133_X1000000_divRight]
  rw [← Finset.sum_add_distrib]
  have h1 : q42_133_term 2 1 + q42_133_term 6 1 = 0 :=
    q42_133_termPair_2_6_zero q42_133_pair_2_1_eq_two_mul_pair_6_1
  have h7 : q42_133_term 2 7 + q42_133_term 6 7 = 0 :=
    q42_133_termPair_2_6_zero q42_133_pair_2_7_eq_two_mul_pair_6_7
  have h19 : q42_133_term 2 19 + q42_133_term 6 19 = 0 :=
    q42_133_termPair_2_6_zero q42_133_pair_2_19_eq_two_mul_pair_6_19
  have h133 : q42_133_term 2 133 + q42_133_term 6 133 = 0 :=
    q42_133_termPair_2_6_zero q42_133_pair_2_133_eq_two_mul_pair_6_133
  simp [Finset.sum_insert, h1, h7, h19, h133]

theorem periodicMainPair_42_133_X1000000_rows_14_42_struct :
    (∑ h ∈ Nat.divisors 133, q42_133_term 14 h)
      + (∑ h ∈ Nat.divisors 133, q42_133_term 42 h) = 0 := by
  rw [periodicMainPair_42_133_X1000000_divRight]
  rw [← Finset.sum_add_distrib]
  have h1 : q42_133_term 14 1 + q42_133_term 42 1 = 0 :=
    q42_133_termPair_14_42_zero q42_133_pair_14_1_eq_two_mul_pair_42_1
  have h7 : q42_133_term 14 7 + q42_133_term 42 7 = 0 :=
    q42_133_termPair_14_42_zero q42_133_pair_14_7_eq_two_mul_pair_42_7
  have h19 : q42_133_term 14 19 + q42_133_term 42 19 = 0 :=
    q42_133_termPair_14_42_zero q42_133_pair_14_19_eq_two_mul_pair_42_19
  have h133 : q42_133_term 14 133 + q42_133_term 42 133 = 0 :=
    q42_133_termPair_14_42_zero q42_133_pair_14_133_eq_two_mul_pair_42_133
  simp [Finset.sum_insert, h1, h7, h19, h133]

theorem periodicMainPair_42_133_X1000000_divLeft :
    Nat.divisors 42 = ([1, 2, 3, 6, 7, 14, 21, 42] : List ℕ).toFinset := by
  decide

theorem periodicMainPair_42_133_X1000000_centeredTerm_struct :
    centeredRamanujanPairPeriodicMainTermRat X0 42 133 = (0 : ℚ) := by
  unfold centeredRamanujanPairPeriodicMainTermRat
  change (∑ g ∈ Nat.divisors 42, ∑ h ∈ Nat.divisors 133, q42_133_term g h) = (0 : ℚ)
  rw [periodicMainPair_42_133_X1000000_divLeft]
  let R : ℕ → ℚ := fun g => ∑ h ∈ Nat.divisors 133, q42_133_term g h
  change (∑ g ∈ ([1, 2, 3, 6, 7, 14, 21, 42] : List ℕ).toFinset, R g) = (0 : ℚ)
  have hreorder :
      (∑ g ∈ ([1, 2, 3, 6, 7, 14, 21, 42] : List ℕ).toFinset, R g)
        = R 1 + R 3 + R 7 + R 21 + (R 2 + R 6) + (R 14 + R 42) := by
    norm_num [Finset.sum_insert]
    abel
  rw [hreorder]
  have hrow1 : R 1 = (0 : ℚ) := by
    dsimp [R]
    exact q42_133_row_zero_of_left_odd
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hrow3 : R 3 = (0 : ℚ) := by
    dsimp [R]
    exact q42_133_row_zero_of_left_odd
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hrow7 : R 7 = (0 : ℚ) := by
    dsimp [R]
    exact q42_133_row_zero_of_left_odd
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hrow21 : R 21 = (0 : ℚ) := by
    dsimp [R]
    exact q42_133_row_zero_of_left_odd
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hrows2_6 : R 2 + R 6 = (0 : ℚ) := by
    simpa [R] using periodicMainPair_42_133_X1000000_rows_2_6_struct
  have hrows14_42 : R 14 + R 42 = (0 : ℚ) := by
    simpa [R] using periodicMainPair_42_133_X1000000_rows_14_42_struct
  rw [hrow1, hrow3, hrow7, hrow21, hrows2_6, hrows14_42]
  norm_num

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_42_133_eq_zero_by_commonSeven :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (42, 133) = 0 := by
  have hneq : 42 ≠ 133 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 42 = (5 : ℚ) / 144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 133 = (5 : ℚ) / 11664 := by
    native_decide
  have hvalue : ((5 : ℚ) / 144) * ((5 : ℚ) / 11664) * (0 : ℚ) = (0 : ℚ) := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_42_133_X1000000_centeredTerm_struct
    hvalue

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
