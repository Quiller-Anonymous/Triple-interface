import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem divisor_pos_of_mem_divisors_of_pos_public
    {n d : ℕ} (hd : d ∈ n.divisors) (hn : 1 ≤ n) :
    0 < d := by
  rcases Nat.mem_divisors.mp hd with ⟨hdvd, _hn0⟩
  exact Nat.pos_of_ne_zero (by
    intro hd0
    subst d
    rcases hdvd with ⟨k, hk⟩
    omega)

private theorem ramanujanGcdClassDivisors_coprime_of_coprime_moduli_public
    {q q' g h : ℕ} (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.Coprime g h := by
  have hgdvd : g ∣ q := (Nat.mem_divisors.mp hg).1
  have hhdvd : h ∣ q' := (Nat.mem_divisors.mp hh).1
  exact (hcop.coprime_dvd_left hgdvd).coprime_dvd_right hhdvd

private theorem quotient_pos_of_mem_divisors_public
    {q g : ℕ} (hq : 1 ≤ q) (hg : g ∈ q.divisors) : 0 < q / g := by
  rcases (Nat.mem_divisors.mp hg).1 with ⟨k, hk⟩
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_public hg hq
  have hkpos : 0 < k := by
    have hknz : k ≠ 0 := by
      intro hk0
      have : q = 0 := by simpa [hk0] using hk
      exact (Nat.ne_of_gt hq) this
    exact Nat.pos_of_ne_zero hknz
  have hdiv : q / g = k := by
    rw [hk, Nat.mul_div_right _ hgpos]
  rw [hdiv]
  exact hkpos

private theorem odd_div_of_dvd_odd_public
    {n a : ℕ} (hnOdd : Odd n) (ha : a ∣ n) :
    Odd (n / a) := by
  refine Nat.not_even_iff_odd.mp ?_
  intro hEven
  have h2quot : 2 ∣ n / a := (even_iff_two_dvd).1 hEven
  have hquot_dvd : n / a ∣ n := by
    exact Nat.div_dvd_of_dvd ha
  have h2n : 2 ∣ n := dvd_trans h2quot hquot_dvd
  exact (Nat.not_even_iff_odd.mpr hnOdd) ((even_iff_two_dvd).2 h2n)

private theorem odd_of_mem_divisors_odd_public
    {n a : ℕ} (hnOdd : Odd n) (ha : a ∈ n.divisors) :
    Odd a := by
  refine Nat.not_even_iff_odd.mp ?_
  intro haEven
  have h2a : 2 ∣ a := (even_iff_two_dvd).1 haEven
  have h2n : 2 ∣ n := dvd_trans h2a (Nat.mem_divisors.mp ha).1
  exact (Nat.not_even_iff_odd.mpr hnOdd) ((even_iff_two_dvd).2 h2n)

private theorem not_isEven_divisor_of_not_isEven_public
    {q g : ℕ} (hqOdd : ¬ Goldbach.Windows.IsEven q) (hg : g ∈ q.divisors) :
    ¬ Goldbach.Windows.IsEven g := by
  intro hgEven
  have hg_dvd_q : g ∣ q := (Nat.mem_divisors.mp hg).1
  have h2g : 2 ∣ g := (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hgEven)
  have h2q : 2 ∣ q := dvd_trans h2g hg_dvd_q
  exact hqOdd (Goldbach.Windows.isEven_of_even ((even_iff_two_dvd).2 h2q))

private theorem ramanujanGcdClassJointCompatibility_of_coprime_moduli_divisors_public
    {q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    ramanujanGcdClassJointCompatibility q q' g h := by
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_public hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos_public hh hq'
  have hgh : Nat.Coprime g h :=
    ramanujanGcdClassDivisors_coprime_of_coprime_moduli_public hcop hg hh
  have hqg_dvd : q / g ∣ q := Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hg).1
  have hq'h_dvd : q' / h ∣ q' := Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hh).1
  have hlcm_div_g : Nat.lcm g h / g = h := by
    rw [hgh.lcm_eq_mul]
    simpa [Nat.mul_comm] using (Nat.mul_div_left h hgpos)
  have hlcm_div_h : Nat.lcm g h / h = g := by
    rw [hgh.lcm_eq_mul]
    simpa [Nat.mul_comm] using (Nat.mul_div_right g hhpos)
  unfold ramanujanGcdClassJointCompatibility
  constructor
  · rw [hlcm_div_g]
    exact ((hcop.coprime_dvd_left hqg_dvd).coprime_dvd_right (Nat.mem_divisors.mp hh).1)
  · rw [hlcm_div_h]
    exact (((hcop.coprime_dvd_right hq'h_dvd).coprime_dvd_left (Nat.mem_divisors.mp hg).1).symm)

private theorem card_filter_range_eq_sum_indicator_public
    (L : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (((Finset.range L).filter p).card : ℕ)
      =
    ∑ k ∈ Finset.range L, if p k then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp

private theorem card_filter_range_coprime_shift_eq_totient_public
    (A M : ℕ) (_hM : 0 < M) :
    (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
      = Nat.totient M := by
  calc
    (((Finset.range M).filter (fun t => Nat.Coprime M (A + t))).card : ℕ)
        = (((Finset.Ico A (A + M)).filter (fun x => Nat.Coprime M x)).card : ℕ) := by
          classical
          refine Finset.card_bij
            (fun t _ => A + t)
            (fun t ht => ?_)
            (fun t₁ _ t₂ _ hEq => Nat.add_left_cancel hEq)
            (fun x hx => ?_)
          · rcases Finset.mem_filter.mp ht with ⟨htRange, hcop⟩
            refine Finset.mem_filter.mpr ?_
            refine ⟨?_, ?_⟩
            · exact Finset.mem_Ico.mpr ⟨Nat.le_add_right A t, by
                simpa using Nat.add_lt_add_left (Finset.mem_range.mp htRange) A⟩
            · simpa [Nat.coprime_comm] using hcop
          · rcases Finset.mem_filter.mp hx with ⟨hxIco, hcop⟩
            refine ⟨x - A, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ?_
              refine ⟨Finset.mem_range.mpr ?_, ?_⟩
              · have hxlo := (Finset.mem_Ico.mp hxIco).1
                have hxhi : A + (x - A) < A + M := by
                  simpa [Nat.add_sub_of_le hxlo] using (Finset.mem_Ico.mp hxIco).2
                exact Nat.add_lt_add_iff_left.mp hxhi
              · simpa [Nat.add_sub_of_le (Finset.mem_Ico.mp hxIco).1, Nat.coprime_comm] using hcop
            · exact Nat.add_sub_of_le (Finset.mem_Ico.mp hxIco).1
    _ = Nat.totient M := by
        simpa [Nat.coprime_comm] using (Nat.filter_coprime_Ico_eq_totient M A)

private lemma even_window_eq_image_range_halfH_add_one_of_isEven_public
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

private theorem periodic_shift_mul_public
    {α : Type*} (f : ℕ → α) {P : ℕ}
    (hper : ∀ k, f (k + P) = f k) :
    ∀ m k : ℕ, f (k + m * P) = f k
  | 0, k => by simp
  | m + 1, k => by
      rw [Nat.succ_mul, ← Nat.add_assoc, hper]
      exact periodic_shift_mul_public f hper m k

private theorem periodic_sum_range_mul_public
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
              rw [periodic_sum_range_mul_public f hP hper m]
        _ = m • ∑ k ∈ Finset.range P, f k + ∑ k ∈ Finset.range P, f k := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hshift : f (k + m * P) = f k :=
                periodic_shift_mul_public f hper m k
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift
        _ = (m + 1) • ∑ k ∈ Finset.range P, f k := by
              simpa [add_comm] using (succ_nsmul (∑ k ∈ Finset.range P, f k) m).symm

theorem ramanujanGcdClassIndicator_three_one_add_three_three_eq_one_public
    (N : ℕ) :
    ramanujanGcdClassIndicator 3 1 N + ramanujanGcdClassIndicator 3 3 N = 1 := by
  unfold ramanujanGcdClassIndicator
  by_cases h1 : Nat.gcd 3 N = 1
  · have h3 : Nat.gcd 3 N ≠ 3 := by
      rw [h1]
      norm_num
    simp [h1, h3]
  · have hdiv : Nat.gcd 3 N ∣ 3 := Nat.gcd_dvd_left 3 N
    have h3 : Nat.gcd 3 N = 3 := by
      have hgcdpos : 0 < Nat.gcd 3 N := Nat.gcd_pos_of_pos_left N (by norm_num)
      have hgcdle : Nat.gcd 3 N ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
      have hne2 : Nat.gcd 3 N ≠ 2 := by
        intro h2
        have : 2 ∣ 3 := by simpa [h2] using hdiv
        norm_num at this
      omega
    simp [h1, h3]

theorem ramanujanGcdClassIndicator_three_one_period_three_on_even_progression_public
    {X k : ℕ} :
    ramanujanGcdClassIndicator 3 1 (X + 2 * (k + 3))
      =
    ramanujanGcdClassIndicator 3 1 (X + 2 * k) := by
  unfold ramanujanGcdClassIndicator
  have hgcd :
      Nat.gcd 3 (X + 2 * (k + 3)) = Nat.gcd 3 (X + 2 * k) := by
    calc
      Nat.gcd 3 (X + 2 * (k + 3))
          = Nat.gcd 3 ((X + 2 * k) + 2 * 3) := by ring_nf
      _ = Nat.gcd 3 (X + 2 * k) := by
            rw [Nat.gcd_add_mul_right_right]
  rw [hgcd]

theorem ramanujanGcdClassIndicator_three_one_sum_range_three_eq_two_of_isEven_public
    {X : ℕ} (hXEven : Goldbach.Windows.IsEven X) :
    ∑ k ∈ Finset.range 3, ramanujanGcdClassIndicator 3 1 (X + 2 * k) = 2 := by
  have hXeq : X = 2 * (X / 2) := by
    exact (Nat.two_mul_div_two_of_even (Goldbach.Windows.even_of_isEven hXEven)).symm
  have hterm :
      ∀ k,
        ramanujanGcdClassIndicator 3 1 (X + 2 * k)
          =
        (if Nat.Coprime 3 (X / 2 + k) then 1 else 0) := by
    intro k
    rw [hXeq]
    have hmul : 2 * (X / 2) + 2 * k = 2 * (X / 2 + k) := by ring
    rw [hmul]
    have hcop32 : Nat.Coprime 3 2 := by norm_num
    have hcop :
        Nat.Coprime 3 (2 * (X / 2 + k)) ↔ Nat.Coprime 3 (X / 2 + k) := by
      constructor
      · intro h
        have h' : Nat.Coprime (2 * (X / 2 + k)) 3 := h.symm
        exact (Nat.coprime_mul_iff_left.mp h').2.symm
      · intro h
        have h' : Nat.Coprime (2 * (X / 2 + k)) 3 := by
          exact Nat.coprime_mul_iff_left.mpr ⟨hcop32.symm, h.symm⟩
        exact h'.symm
    have hg : 1 ∈ (3 : ℕ).divisors := by norm_num
    rw [ramanujanGcdClassIndicator_eq_coprimeIndicator_of_mem_divisors (N := 2 * (X / 2 + k)) hg]
    unfold ramanujanGcdClassCoprimeIndicator
    simpa [hcop]
  calc
    ∑ k ∈ Finset.range 3, ramanujanGcdClassIndicator 3 1 (X + 2 * k)
        =
      ∑ k ∈ Finset.range 3, (if Nat.Coprime 3 (X / 2 + k) then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact hterm k
    _ = (((Finset.range 3).filter (fun k => Nat.Coprime 3 (X / 2 + k))).card : ℝ) := by
          exact_mod_cast
            (card_filter_range_eq_sum_indicator_public
              (L := 3) (p := fun k => Nat.Coprime 3 (X / 2 + k))).symm
    _ = 2 := by
          have hcard :
              (((Finset.range 3).filter (fun k => Nat.Coprime 3 (X / 2 + k))).card : ℕ) = 2 := by
            simpa using card_filter_range_coprime_shift_eq_totient_public (X / 2) 3 (by norm_num)
          exact_mod_cast hcard

theorem ramanujanGcdClassWindowAverage_three_one_eq_two_thirds_of_isEven_public
    {X : ℕ} (hXEven : Goldbach.Windows.IsEven X) :
    ramanujanGcdClassWindowAverage X 3 1 = (2 / 3 : ℝ) := by
  unfold ramanujanGcdClassWindowAverage
  rw [even_window_eq_image_range_halfH_add_one_of_isEven_public hXEven]
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_range]
    have hsum :
        ∑ N ∈ (Finset.range (H / 2 + 1)).image (fun k : ℕ => X + 2 * k),
            ramanujanGcdClassIndicator 3 1 N
          =
        ∑ k ∈ Finset.range (H / 2 + 1),
            ramanujanGcdClassIndicator 3 1 (X + 2 * k) := by
      rw [Finset.sum_image]
      simp
    rw [hsum]
    have hlen : H / 2 + 1 = 1667 * 3 := by
      norm_num [H]
    rw [hlen]
    rw [periodic_sum_range_mul_public
      (f := fun k => ramanujanGcdClassIndicator 3 1 (X + 2 * k))
      (P := 3)
      (hP := by norm_num)
      (hper := fun k =>
        ramanujanGcdClassIndicator_three_one_period_three_on_even_progression_public
          (X := X) (k := k))
      (m := 1667)]
    rw [ramanujanGcdClassIndicator_three_one_sum_range_three_eq_two_of_isEven_public hXEven]
    rw [nsmul_eq_mul]
    norm_num
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (Nat.add_left_cancel hab)

theorem ramanujanGcdClassWindowAverage_three_three_eq_one_third_of_isEven_public
    {X : ℕ} (hXEven : Goldbach.Windows.IsEven X) :
    ramanujanGcdClassWindowAverage X 3 3 = (1 / 3 : ℝ) := by
  unfold ramanujanGcdClassWindowAverage
  rw [even_window_eq_image_range_halfH_add_one_of_isEven_public hXEven]
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_range]
    have hsum1 :
        ∑ k ∈ Finset.range (H / 2 + 1),
            ramanujanGcdClassIndicator 3 1 (X + 2 * k)
          = 3334 := by
      have hlen : H / 2 + 1 = 1667 * 3 := by
        norm_num [H]
      rw [hlen]
      rw [periodic_sum_range_mul_public
        (f := fun k => ramanujanGcdClassIndicator 3 1 (X + 2 * k))
        (P := 3)
        (hP := by norm_num)
        (hper := fun k =>
          ramanujanGcdClassIndicator_three_one_period_three_on_even_progression_public
            (X := X) (k := k))
        (m := 1667)]
      rw [ramanujanGcdClassIndicator_three_one_sum_range_three_eq_two_of_isEven_public hXEven]
      norm_num
    have hsumPair :
        (∑ k ∈ Finset.range (H / 2 + 1),
            (ramanujanGcdClassIndicator 3 1 (X + 2 * k)
              + ramanujanGcdClassIndicator 3 3 (X + 2 * k)))
          = (H / 2 + 1 : ℝ) := by
      calc
        (∑ k ∈ Finset.range (H / 2 + 1),
            (ramanujanGcdClassIndicator 3 1 (X + 2 * k)
              + ramanujanGcdClassIndicator 3 3 (X + 2 * k)))
                =
          ∑ k ∈ Finset.range (H / 2 + 1), (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact ramanujanGcdClassIndicator_three_one_add_three_three_eq_one_public (X + 2 * k)
        _ = (H / 2 + 1 : ℝ) := by
            norm_num [H, Finset.sum_const, nsmul_eq_mul]
    have hsum3 :
        ∑ k ∈ Finset.range (H / 2 + 1),
            ramanujanGcdClassIndicator 3 3 (X + 2 * k)
          = 1667 := by
      rw [Finset.sum_add_distrib] at hsumPair
      have hlen : (H / 2 + 1 : ℝ) = 5001 := by norm_num [H]
      linarith
    have hsum :
        ∑ N ∈ (Finset.range (H / 2 + 1)).image (fun k : ℕ => X + 2 * k),
            ramanujanGcdClassIndicator 3 3 N
          =
        ∑ k ∈ Finset.range (H / 2 + 1),
            ramanujanGcdClassIndicator 3 3 (X + 2 * k) := by
      rw [Finset.sum_image]
      simp
    rw [hsum, hsum3]
    change ((5001 : ℝ)⁻¹) * 1667 = (1 / 3 : ℝ)
    norm_num
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (Nat.add_left_cancel hab)

theorem rawEvenRamanujanGcdClassPeriodicPairLen_eq_two_mul_jointModulus_of_coprime_moduli_divisors_public
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
        - (X ⌈/⌉ Nat.lcm g h))
      =
    2 * ramanujanGcdClassJointModulus q q' g h := by
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_public hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos_public hh hq'
  have hgh : Nat.Coprime g h := ramanujanGcdClassDivisors_coprime_of_coprime_moduli_public hcop hg hh
  rw [rawEvenRamanujanGcdClassPeriodicPairLen_eq_blockPeriod_div hq hq' hg hh]
  dsimp [centeredRamanujanPairBlockPeriod, ramanujanGcdClassJointModulus]
  rw [hcop.lcm_eq_mul, hgh.lcm_eq_mul]
  rcases (Nat.mem_divisors.mp hg).1 with ⟨a, ha⟩
  rcases (Nat.mem_divisors.mp hh).1 with ⟨b, hb⟩
  have hgdiv : g * a / g = a := by rw [Nat.mul_div_right _ hgpos]
  have hhdiv : h * b / h = b := by rw [Nat.mul_div_right _ hhpos]
  rw [ha, hb]
  have hmul1 : g * a * (h * b) = (g * h) * (a * b) := by ac_rfl
  have hmul2 : 2 * ((g * h) * (a * b)) = (g * h) * (2 * (a * b)) := by ac_rfl
  calc
    2 * (g * a * (h * b)) / (g * h)
        = 2 * ((g * h) * (a * b)) / (g * h) := by rw [hmul1]
    _ = ((g * h) * (2 * (a * b))) / (g * h) := by rw [hmul2]
    _ = 2 * (a * b) := by
          rw [Nat.mul_div_right _ (Nat.mul_pos hgpos hhpos)]
    _ = 2 * (g * a / g * (h * b / h)) := by
          simp [hgdiv, hhdiv, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem rawEvenRamanujanGcdClassPeriodicLeftLen_eq_two_mul_quotient_mul_of_divisor_public
    {X q q' g : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g))
      =
    2 * ((q / g) * q') := by
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_public hg hq
  rw [rawEvenRamanujanGcdClassPeriodicLeftLen_eq_blockPeriod_div hq hq' hg]
  dsimp [centeredRamanujanPairBlockPeriod]
  rw [hcop.lcm_eq_mul]
  rcases (Nat.mem_divisors.mp hg).1 with ⟨a, ha⟩
  have hgdiv : g * a / g = a := by rw [Nat.mul_div_right _ hgpos]
  rw [ha]
  have hmul : 2 * (g * a * q') = g * (2 * (a * q')) := by ac_rfl
  rw [hmul, Nat.mul_div_right _ hgpos]
  simp [hgdiv, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem rawEvenRamanujanGcdClassPeriodicRightLen_eq_two_mul_quotient_mul_of_divisor_public
    {X q q' h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hh : h ∈ q'.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h))
      =
    2 * ((q' / h) * q) := by
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos_public hh hq'
  rw [rawEvenRamanujanGcdClassPeriodicRightLen_eq_blockPeriod_div hq hq' hh]
  dsimp [centeredRamanujanPairBlockPeriod]
  rw [hcop.lcm_eq_mul]
  rcases (Nat.mem_divisors.mp hh).1 with ⟨b, hb⟩
  have hhdiv : h * b / h = b := by rw [Nat.mul_div_right _ hhpos]
  rw [hb]
  have hmul : 2 * (q * (h * b)) = h * (2 * (b * q)) := by ac_rfl
  rw [hmul, Nat.mul_div_right _ hhpos]
  simp [hhdiv, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem rawEvenRamanujanGcdClassPeriodicPairLen_div_two_mul_jointModulus_eq_one_of_coprime_moduli_divisors_public
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
        - (X ⌈/⌉ Nat.lcm g h))
      / (2 * ramanujanGcdClassJointModulus q q' g h))
      = 1 := by
  have hMpos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    dsimp [ramanujanGcdClassJointModulus]
    exact Nat.mul_pos (quotient_pos_of_mem_divisors_public hq hg) (quotient_pos_of_mem_divisors_public hq' hh)
  have h2Mpos : 0 < 2 * ramanujanGcdClassJointModulus q q' g h := by
    exact Nat.mul_pos (by norm_num) hMpos
  rw [rawEvenRamanujanGcdClassPeriodicPairLen_eq_two_mul_jointModulus_of_coprime_moduli_divisors_public
    hq hq' hcop hg hh]
  exact Nat.div_self h2Mpos

private theorem rawEvenRamanujanGcdClassPeriodicLeftLen_div_two_mul_quotient_eq_rightModulus_of_divisor_public
    {X q q' g : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) :
    ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g))
      / (2 * (q / g)))
      = q' := by
  rw [rawEvenRamanujanGcdClassPeriodicLeftLen_eq_two_mul_quotient_mul_of_divisor_public hq hq' hcop hg]
  have hpos : 0 < 2 * (q / g) := by
    exact Nat.mul_pos (by norm_num) (quotient_pos_of_mem_divisors_public hq hg)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_div_right q' hpos)

private theorem rawEvenRamanujanGcdClassPeriodicRightLen_div_two_mul_quotient_eq_leftModulus_of_divisor_public
    {X q q' h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hh : h ∈ q'.divisors) :
    ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h))
      / (2 * (q' / h)))
      = q := by
  rw [rawEvenRamanujanGcdClassPeriodicRightLen_eq_two_mul_quotient_mul_of_divisor_public hq hq' hcop hh]
  have hpos : 0 < 2 * (q' / h) := by
    exact Nat.mul_pos (by norm_num) (quotient_pos_of_mem_divisors_public hq' hh)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_div_right q hpos)

private theorem rawEvenRamanujanGcdClassPeriodicPairLen_mod_two_mul_jointModulus_eq_zero_of_coprime_moduli_divisors_public
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
        - (X ⌈/⌉ Nat.lcm g h))
      % (2 * ramanujanGcdClassJointModulus q q' g h))
      = 0 := by
  rw [rawEvenRamanujanGcdClassPeriodicPairLen_eq_two_mul_jointModulus_of_coprime_moduli_divisors_public
    hq hq' hcop hg hh]
  simp

private theorem rawEvenRamanujanGcdClassPeriodicLeftLen_mod_two_mul_quotient_eq_zero_of_divisor_public
    {X q q' g : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) :
    ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / g + 1) - (X ⌈/⌉ g))
      % (2 * (q / g)))
      = 0 := by
  rw [rawEvenRamanujanGcdClassPeriodicLeftLen_eq_two_mul_quotient_mul_of_divisor_public hq hq' hcop hg]
  refine Nat.mod_eq_zero_of_dvd ?_
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (dvd_mul_right (2 * (q / g)) q')

private theorem rawEvenRamanujanGcdClassPeriodicRightLen_mod_two_mul_quotient_eq_zero_of_divisor_public
    {X q q' h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hh : h ∈ q'.divisors) :
    ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / h + 1) - (X ⌈/⌉ h))
      % (2 * (q' / h)))
      = 0 := by
  rw [rawEvenRamanujanGcdClassPeriodicRightLen_eq_two_mul_quotient_mul_of_divisor_public hq hq' hcop hh]
  refine Nat.mod_eq_zero_of_dvd ?_
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (dvd_mul_right (2 * (q' / h)) q)

theorem rawEvenRamanujanGcdClassBlockPeriodicCount_eq_evenRamanujanBlockCount_mul_windowAverage_of_eq_three_left_public
    {X b g : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : 1 ≤ b) (hcop : Nat.Coprime 3 b)
    (hg : g ∈ (3 : ℕ).divisors.filter (fun g => ¬ Goldbach.Windows.IsEven g)) :
    rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b 3 g
      =
    evenRamanujanBlockCount X 3 b * ramanujanGcdClassWindowAverage X 3 g := by
  have hq : 1 ≤ 3 := by norm_num
  have hPpos : 0 < centeredRamanujanPairBlockPeriod 3 b := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hb)
  have hgDiv : g ∈ (3 : ℕ).divisors := (Finset.mem_filter.mp hg).1
  have hgOdd : ¬ Goldbach.Windows.IsEven g := (Finset.mem_filter.mp hg).2
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_public hgDiv hq
  have hg_cases : g = 1 ∨ g = 3 := by
    have hgle : g ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.mem_divisors.mp hgDiv).1
    have hne2 : g ≠ 2 := by
      intro hg2
      have : Goldbach.Windows.IsEven 2 := by norm_num [Goldbach.Windows.IsEven]
      exact hgOdd (by simpa [hg2] using this)
    omega
  rcases hg_cases with rfl | rfl
  · rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_odd_g_totient_main_add_remainder_of_odd_quotient
      X 3 b 3 1 (by norm_num) hPpos (by norm_num [Goldbach.Windows.IsEven]) (by norm_num) (by norm_num)]
    dsimp
    have hdiv :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / 1 + 1) - (X ⌈/⌉ 1))
          / (2 * (3 / 1)))
          = b :=
      rawEvenRamanujanGcdClassPeriodicLeftLen_div_two_mul_quotient_eq_rightModulus_of_divisor_public
        hq hb hcop (by norm_num : 1 ∈ (3 : ℕ).divisors)
    have hmod :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / 1 + 1) - (X ⌈/⌉ 1))
          % (2 * (3 / 1)))
          = 0 :=
      rawEvenRamanujanGcdClassPeriodicLeftLen_mod_two_mul_quotient_eq_zero_of_divisor_public
        hq hb hcop (by norm_num : 1 ∈ (3 : ℕ).divisors)
    rw [evenRamanujanBlockCount_eq_lcm, ramanujanGcdClassWindowAverage_three_one_eq_two_thirds_of_isEven_public hXEven]
    rw [hcop.lcm_eq_mul]
    simp [centeredRamanujanPairBlockPeriod, hcop.lcm_eq_mul] at hdiv hmod ⊢
    rw [hdiv, hmod]
    have hphi : Nat.totient 3 = 2 := by
      simpa using Nat.totient_prime (by decide : Nat.Prime 3)
    rw [hphi]
    ring_nf
    simp
  · rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_odd_g_totient_main_add_remainder_of_odd_quotient
      X 3 b 3 3 hgpos hPpos hgOdd (by norm_num) (by norm_num)]
    dsimp
    have hdiv :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / 3 + 1) - (X ⌈/⌉ 3))
          / (2 * (3 / 3)))
          = b :=
      rawEvenRamanujanGcdClassPeriodicLeftLen_div_two_mul_quotient_eq_rightModulus_of_divisor_public
        hq hb hcop (by norm_num : 3 ∈ (3 : ℕ).divisors)
    have hmod :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / 3 + 1) - (X ⌈/⌉ 3))
          % (2 * (3 / 3)))
          = 0 :=
      rawEvenRamanujanGcdClassPeriodicLeftLen_mod_two_mul_quotient_eq_zero_of_divisor_public
        hq hb hcop (by norm_num : 3 ∈ (3 : ℕ).divisors)
    rw [evenRamanujanBlockCount_eq_lcm, ramanujanGcdClassWindowAverage_three_three_eq_one_third_of_isEven_public hXEven]
    rw [hcop.lcm_eq_mul]
    simp [centeredRamanujanPairBlockPeriod, hcop.lcm_eq_mul] at hdiv hmod ⊢
    rw [hdiv, hmod]
    ring_nf
    simp

theorem centeredRamanujanGcdClassPeriodicDensityMismatchTerm_eq_zero_of_isEven_eq_three_left_public
    {X b g h : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : 1 ≤ b) (hcop : Nat.Coprime 3 b)
    (hg : g ∈ (3 : ℕ).divisors.filter (fun g => ¬ Goldbach.Windows.IsEven g)) :
    centeredRamanujanGcdClassPeriodicDensityMismatchTerm X 3 b g h = 0 := by
  have hcount :
      rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b 3 g
        =
      evenRamanujanBlockCount X 3 b * ramanujanGcdClassWindowAverage X 3 g :=
    rawEvenRamanujanGcdClassBlockPeriodicCount_eq_evenRamanujanBlockCount_mul_windowAverage_of_eq_three_left_public
      hXEven hb hcop hg
  have hBne : evenRamanujanBlockCount X 3 b ≠ 0 := by
    exact ne_of_gt (evenRamanujanBlockCount_pos X 3 b (by norm_num) hb)
  unfold centeredRamanujanGcdClassPeriodicDensityMismatchTerm
  rw [hcount]
  field_simp [hBne]
  ring

theorem centeredRamanujanPairPeriodicMainOddOddDensityMismatchContribution_eq_zero_of_isEven_eq_three_left_public
    {X b : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : b ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0)
    (hcop : Nat.Coprime 3 b) :
    centeredRamanujanPairPeriodicMainOddOddDensityMismatchContribution X 3 b = 0 := by
  have hbpos : 1 ≤ b := by
    rcases mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mp hb with ⟨hbCoeff, _hbOdd⟩
    exact (Finset.mem_Icc.mp (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hbCoeff).1).1
  unfold centeredRamanujanPairPeriodicMainOddOddDensityMismatchContribution
  refine Finset.sum_eq_zero ?_
  intro g hg
  refine Finset.sum_eq_zero ?_
  intro h hh
  rw [centeredRamanujanGcdClassPeriodicDensityMismatchTerm_eq_zero_of_isEven_eq_three_left_public
    hXEven hbpos hcop hg]
  ring

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_windowAverage_mul_rightCount_of_eq_three_left_public
    {X b g h : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : 1 ≤ b) (hbOdd : Odd b) (hcop : Nat.Coprime 3 b)
    (hg : g ∈ (3 : ℕ).divisors.filter (fun g => ¬ Goldbach.Windows.IsEven g))
    (hh : h ∈ b.divisors.filter (fun h => ¬ Goldbach.Windows.IsEven h)) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCount X 3 b g h
      =
    ramanujanGcdClassWindowAverage X 3 g
      * rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b b h := by
  have hq : 1 ≤ 3 := by norm_num
  have hPpos : 0 < centeredRamanujanPairBlockPeriod 3 b := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hb)
  have hgDiv : g ∈ (3 : ℕ).divisors := (Finset.mem_filter.mp hg).1
  have hhDiv : h ∈ b.divisors := (Finset.mem_filter.mp hh).1
  have hgOdd : ¬ Goldbach.Windows.IsEven g := (Finset.mem_filter.mp hg).2
  have hhOdd : ¬ Goldbach.Windows.IsEven h := (Finset.mem_filter.mp hh).2
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_public hgDiv hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos_public hhDiv hb
  have hcompat : ramanujanGcdClassJointCompatibility 3 b g h :=
    ramanujanGcdClassJointCompatibility_of_coprime_moduli_divisors_public hq hb hcop hgDiv hhDiv
  have hRightPos : 0 < b / h := quotient_pos_of_mem_divisors_public hb hhDiv
  have hRightOdd : Odd (b / h) := odd_div_of_dvd_odd_public hbOdd (Nat.mem_divisors.mp hhDiv).1
  have hLodd : ¬ Goldbach.Windows.IsEven (Nat.lcm g h) := by
    have hgh : Nat.Coprime g h :=
      ramanujanGcdClassDivisors_coprime_of_coprime_moduli_public hcop hgDiv hhDiv
    intro hEvenL
    have hEvenMul : Goldbach.Windows.IsEven (g * h) := by
      simpa [hgh.lcm_eq_mul] using hEvenL
    have hEvenh : Goldbach.Windows.IsEven h :=
      (isEven_mul_iff_of_not_isEven_left hgOdd).1 hEvenMul
    exact hhOdd hEvenh
  have hPairPos : 0 < ramanujanGcdClassJointModulus 3 b g h := by
    dsimp [ramanujanGcdClassJointModulus]
    exact Nat.mul_pos (quotient_pos_of_mem_divisors_public hq hgDiv) hRightPos
  have hPairOdd : Odd (ramanujanGcdClassJointModulus 3 b g h) := by
    dsimp [ramanujanGcdClassJointModulus]
    exact (odd_div_of_dvd_odd_public (by norm_num : Odd 3) (Nat.mem_divisors.mp hgDiv).1).mul hRightOdd
  have hg_cases : g = 1 ∨ g = 3 := by
    have hgle : g ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.mem_divisors.mp hgDiv).1
    have hne2 : g ≠ 2 := by
      intro hg2
      have : Goldbach.Windows.IsEven 2 := by norm_num [Goldbach.Windows.IsEven]
      exact hgOdd (by simpa [hg2] using this)
    omega
  rcases hg_cases with rfl | rfl
  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_odd_lcm_totient_main_add_remainder_of_odd_jointModulus
      X 3 b 1 h (Nat.lcm_pos (by norm_num) hhpos) hPpos hcompat hLodd hPairPos hPairOdd]
    rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_odd_g_totient_main_add_remainder_of_odd_quotient
      X 3 b b h hhpos hPpos hhOdd hRightPos hRightOdd]
    dsimp
    have hPairDiv :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / Nat.lcm 1 h + 1)
            - (X ⌈/⌉ Nat.lcm 1 h))
          / (2 * ramanujanGcdClassJointModulus 3 b 1 h))
          = 1 :=
      rawEvenRamanujanGcdClassPeriodicPairLen_div_two_mul_jointModulus_eq_one_of_coprime_moduli_divisors_public
        hq hb hcop (by norm_num : 1 ∈ (3 : ℕ).divisors) hhDiv
    have hPairMod :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / Nat.lcm 1 h + 1)
            - (X ⌈/⌉ Nat.lcm 1 h))
          % (2 * ramanujanGcdClassJointModulus 3 b 1 h))
          = 0 :=
      rawEvenRamanujanGcdClassPeriodicPairLen_mod_two_mul_jointModulus_eq_zero_of_coprime_moduli_divisors_public
        hq hb hcop (by norm_num : 1 ∈ (3 : ℕ).divisors) hhDiv
    have hRightDiv :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / h + 1) - (X ⌈/⌉ h))
          / (2 * (b / h)))
          = 3 :=
      rawEvenRamanujanGcdClassPeriodicRightLen_div_two_mul_quotient_eq_leftModulus_of_divisor_public
        hq hb hcop hhDiv
    have hRightMod :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / h + 1) - (X ⌈/⌉ h))
          % (2 * (b / h)))
          = 0 :=
      rawEvenRamanujanGcdClassPeriodicRightLen_mod_two_mul_quotient_eq_zero_of_divisor_public
        hq hb hcop hhDiv
    simp [centeredRamanujanPairBlockPeriod] at hRightDiv hRightMod
    rw [ramanujanGcdClassWindowAverage_three_one_eq_two_thirds_of_isEven_public hXEven]
    simp [ramanujanGcdClassJointModulus] at hPairDiv hPairMod ⊢
    rw [hPairDiv, hPairMod, hRightDiv, hRightMod]
    have hcop3Right : Nat.Coprime 3 (b / h) := by
      exact hcop.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hhDiv).1)
    have htot :
        Nat.totient (3 * (b / h)) = 2 * Nat.totient (b / h) := by
      have hmul := Nat.totient_mul hcop3Right
      have hphi3 : Nat.totient 3 = 2 := by
        simpa using Nat.totient_prime (by decide : Nat.Prime 3)
      simpa [hphi3, Nat.mul_assoc] using hmul
    rw [htot]
    norm_num
    ring
  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_odd_lcm_totient_main_add_remainder_of_odd_jointModulus
      X 3 b 3 h (Nat.lcm_pos (by norm_num) hhpos) hPpos hcompat hLodd hPairPos hPairOdd]
    rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_odd_g_totient_main_add_remainder_of_odd_quotient
      X 3 b b h hhpos hPpos hhOdd hRightPos hRightOdd]
    dsimp
    have hPairDiv :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / Nat.lcm 3 h + 1)
            - (X ⌈/⌉ Nat.lcm 3 h))
          / (2 * ramanujanGcdClassJointModulus 3 b 3 h))
          = 1 :=
      rawEvenRamanujanGcdClassPeriodicPairLen_div_two_mul_jointModulus_eq_one_of_coprime_moduli_divisors_public
        hq hb hcop (by norm_num : 3 ∈ (3 : ℕ).divisors) hhDiv
    have hPairMod :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / Nat.lcm 3 h + 1)
            - (X ⌈/⌉ Nat.lcm 3 h))
          % (2 * ramanujanGcdClassJointModulus 3 b 3 h))
          = 0 :=
      rawEvenRamanujanGcdClassPeriodicPairLen_mod_two_mul_jointModulus_eq_zero_of_coprime_moduli_divisors_public
        hq hb hcop (by norm_num : 3 ∈ (3 : ℕ).divisors) hhDiv
    have hRightDiv :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / h + 1) - (X ⌈/⌉ h))
          / (2 * (b / h)))
          = 3 :=
      rawEvenRamanujanGcdClassPeriodicRightLen_div_two_mul_quotient_eq_leftModulus_of_divisor_public
        hq hb hcop hhDiv
    have hRightMod :
        ((((X + centeredRamanujanPairBlockPeriod 3 b - 1) / h + 1) - (X ⌈/⌉ h))
          % (2 * (b / h)))
          = 0 :=
      rawEvenRamanujanGcdClassPeriodicRightLen_mod_two_mul_quotient_eq_zero_of_divisor_public
        hq hb hcop hhDiv
    simp [centeredRamanujanPairBlockPeriod] at hRightDiv hRightMod
    rw [ramanujanGcdClassWindowAverage_three_three_eq_one_third_of_isEven_public hXEven]
    simp [ramanujanGcdClassJointModulus] at hPairDiv hPairMod ⊢
    rw [hPairDiv, hPairMod, hRightDiv, hRightMod]
    norm_num
    ring

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_eq_zero_of_isEven_eq_three_left_public
    {X b g h : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : 1 ≤ b) (hbOdd : Odd b) (hcop : Nat.Coprime 3 b)
    (hg : g ∈ (3 : ℕ).divisors.filter (fun g => ¬ Goldbach.Windows.IsEven g))
    (hh : h ∈ b.divisors.filter (fun h => ¬ Goldbach.Windows.IsEven h)) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X 3 b g h = 0 := by
  have hq : 1 ≤ 3 := by norm_num
  have hgDiv : g ∈ (3 : ℕ).divisors := (Finset.mem_filter.mp hg).1
  have hhDiv : h ∈ b.divisors := (Finset.mem_filter.mp hh).1
  have hcompat : ramanujanGcdClassJointCompatibility 3 b g h :=
    ramanujanGcdClassJointCompatibility_of_coprime_moduli_divisors_public hq hb hcop hgDiv hhDiv
  have hleft :
      rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b 3 g
        =
      evenRamanujanBlockCount X 3 b * ramanujanGcdClassWindowAverage X 3 g :=
    rawEvenRamanujanGcdClassBlockPeriodicCount_eq_evenRamanujanBlockCount_mul_windowAverage_of_eq_three_left_public
      hXEven hb hcop hg
  have hpair :
      rawEvenRamanujanGcdClassPairBlockPeriodicCount X 3 b g h
        =
      ramanujanGcdClassWindowAverage X 3 g
        * rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b b h :=
    rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_windowAverage_mul_rightCount_of_eq_three_left_public
      hXEven hb hbOdd hcop hg hh
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_periodic_comparison
    hq hb hgDiv hhDiv hcompat]
  rw [hpair, hleft]
  ring

theorem centeredRamanujanPairPeriodicMainOddOddSector_eq_zero_of_isEven_eq_three_left_public
    {X b : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : b ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0)
    (hcop : Nat.Coprime 3 b) :
    centeredRamanujanPairPeriodicMainOddOddSector X 3 b = 0 := by
  rcases mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mp hb with ⟨hbCoeff, hbOdd⟩
  have hbpos : 1 ≤ b :=
    (Finset.mem_Icc.mp (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hbCoeff).1).1
  unfold centeredRamanujanPairPeriodicMainOddOddSector
  refine Finset.sum_eq_zero ?_
  intro g hg
  refine Finset.sum_eq_zero ?_
  intro h hh
  unfold centeredRamanujanPairPeriodicMainParitySummand
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_zero_of_isEven_eq_three_left_public
    hXEven hbpos hbOdd hcop hg hh]
  simp

theorem centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_public
    {X b : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : b ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0)
    (hcop : Nat.Coprime 3 b) :
    centeredRamanujanPairPeriodicMainTerm X 3 b = 0 := by
  rcases mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mp hb with ⟨hbCoeff, hbOdd⟩
  have hbpos : 1 ≤ b :=
    (Finset.mem_Icc.mp (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hbCoeff).1).1
  have h3Odd : ¬ Goldbach.Windows.IsEven 3 := by
    norm_num [Goldbach.Windows.IsEven]
  have hbNotEven : ¬ Goldbach.Windows.IsEven b := by
    intro hbEven
    exact (Nat.not_even_iff_odd.mpr hbOdd) (Goldbach.Windows.even_of_isEven hbEven)
  rw [centeredRamanujanPairPeriodicMainTerm_eq_coprime_modulusParityCases
    (X := X) (q := 3) (q' := b) (by norm_num) hbpos hcop]
  rw [if_neg h3Odd, if_neg hbNotEven]
  exact centeredRamanujanPairPeriodicMainOddOddSector_eq_zero_of_isEven_eq_three_left_public
    hXEven hb hcop

private theorem X0_isEven_public : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_coprime_rowThree_rightOdd_public
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  rcases Finset.mem_filter.mp hp with ⟨hpRowThree, hpRightOdd⟩
  rcases Finset.mem_filter.mp hpRowThree with ⟨hpCoprime, hpLeftThree⟩
  rcases Finset.mem_filter.mp hpCoprime with ⟨hpDyadic, hcopData⟩
  rcases hcopData with ⟨_hnotUnitTwo, hcop⟩
  have hpFullSq :
      p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit :=
    PeriodicMainZeroDyadicExceptionPairs_subset_fullBlockSquarefreeExplicit hpDyadic
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hpFullSq).1
  have hpRightSq : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  have hpRightActive : p.2 ∈ PeriodicMainActiveSupportExplicit := by
    rw [PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit]
    exact hpRightSq
  have hpRightCoeff : p.2 ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 := by
    exact (Finset.mem_filter.mp hpRightActive).1
  have hpRightOddSupp : p.2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
    mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mpr
      ⟨hpRightCoeff, hpRightOdd⟩
  have hcop3 : Nat.Coprime 3 p.2 := by
    simpa [hpLeftThree] using hcop
  have hneq : p.1 ≠ p.2 := by
    intro hdiag
    have hpRightThree : p.2 = 3 := by
      rw [← hdiag, hpLeftThree]
    have hbad : Nat.Coprime 3 3 := by
      simpa [hpLeftThree, hpRightThree] using hcop
    norm_num at hbad
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  rw [if_neg hneq]
  rw [hpLeftThree]
  rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_public
    X0_isEven_public hpRightOddSupp hcop3]
  ring

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOdd_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_coprime_rowThree_rightOdd_public hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
