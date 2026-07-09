import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeCoprimeCoreReduced

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Structural raw-core surface for the coprime-core part of `bothThree`.

This module starts the proof-level replacement for the generated raw fallback:
first expose the raw pair block as the gcd-class pair block sum.  The remaining
orthogonality step can then use the existing odd/odd totient factor machinery.
-/

theorem rawEvenRamanujanPairBlockSum_eq_sum_gcdClassPairBlockSums
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    rawEvenRamanujanPairBlockSum X q q'
      =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * rawEvenRamanujanGcdClassPairBlockSum X q q' g h := by
  unfold rawEvenRamanujanPairBlockSum rawEvenRamanujanGcdClassPairBlockSum
  calc
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        (if Goldbach.Windows.IsEven (X + k) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
        else 0)
      =
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      (if Goldbach.Windows.IsEven (X + k) then
        (∑ g ∈ q.divisors,
          ramanujanGcdClassCoeff q g * ramanujanGcdClassCoprimeIndicator q g (X + k))
          * (∑ h ∈ q'.divisors,
            ramanujanGcdClassCoeff q' h * ramanujanGcdClassCoprimeIndicator q' h (X + k))
      else 0) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        by_cases hEven : Goldbach.Windows.IsEven (X + k)
        · rw [if_pos hEven]
          rw [if_pos hEven]
          rw [ramanujanR_eq_sum_gcdClassIndicators (q := q) (N := X + k) hq]
          rw [ramanujanR_eq_sum_gcdClassIndicators (q := q') (N := X + k) hq']
          refine congrArg₂ (fun a b : ℝ => a * b) ?_ ?_
          · refine Finset.sum_congr rfl ?_
            intro g hg
            rw [ramanujanGcdClassIndicator_eq_coprimeIndicator_of_mem_divisors
              (q := q) (g := g) (N := X + k) hg]
          · refine Finset.sum_congr rfl ?_
            intro h hh
            rw [ramanujanGcdClassIndicator_eq_coprimeIndicator_of_mem_divisors
              (q := q') (g := h) (N := X + k) hh]
        · simp [hEven]
    _ =
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
          * (if Goldbach.Windows.IsEven (X + k) then
              ramanujanGcdClassCoprimeIndicator q g (X + k)
                * ramanujanGcdClassCoprimeIndicator q' h (X + k)
            else 0) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        by_cases hEven : Goldbach.Windows.IsEven (X + k)
        · simp [hEven]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro h _hh
          ring
        · simp [hEven]
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
          * (if Goldbach.Windows.IsEven (X + k) then
              ramanujanGcdClassCoprimeIndicator q g (X + k)
                * ramanujanGcdClassCoprimeIndicator q' h (X + k)
            else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro g _hg
        rw [Finset.sum_comm]
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
          (if Goldbach.Windows.IsEven (X + k) then
            ramanujanGcdClassCoprimeIndicator q g (X + k)
              * ramanujanGcdClassCoprimeIndicator q' h (X + k)
          else 0) := by
        refine Finset.sum_congr rfl ?_
        intro g _hg
        refine Finset.sum_congr rfl ?_
        intro h _hh
        rw [Finset.mul_sum]
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
          (if Goldbach.Windows.IsEven (X + k) then
            ramanujanGcdClassCoprimeIndicator q g (X + k)
              * ramanujanGcdClassCoprimeIndicator q' h (X + k)
          else 0) := by
        rfl

theorem rawCore_divisor_pos_of_mem_divisors_of_pos
    {q g : ℕ} (hq : 1 ≤ q) (hg : g ∈ q.divisors) :
    0 < g :=
  Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hg).1 hq

theorem rawCore_quotient_pos_of_mem_divisors
    {q g : ℕ} (hq : 1 ≤ q) (hg : g ∈ q.divisors) :
    0 < q / g := by
  exact Nat.div_pos
    (Nat.le_of_dvd hq (Nat.mem_divisors.mp hg).1)
    (rawCore_divisor_pos_of_mem_divisors_of_pos hq hg)

theorem rawCore_not_isEven_of_mem_divisors_odd
    {q g : ℕ} (hqOdd : Odd q) (hg : g ∈ q.divisors) :
    ¬ Goldbach.Windows.IsEven g := by
  intro hgEven
  have hgEvenNat : Even g := Goldbach.Windows.even_of_isEven hgEven
  rcases hgEvenNat with ⟨t, ht⟩
  rcases (Nat.mem_divisors.mp hg).1 with ⟨a, ha⟩
  have hqEven : Even q := by
    refine ⟨t * a, ?_⟩
    rw [ha, ht]
    ring
  exact (Nat.not_even_iff_odd.mpr hqOdd) hqEven

theorem rawCore_odd_div_of_mem_divisors_odd
    {q g : ℕ} (hq : 1 ≤ q) (hqOdd : Odd q) (hg : g ∈ q.divisors) :
    Odd (q / g) := by
  refine Nat.not_even_iff_odd.mp ?_
  intro hEvenQuot
  rcases hEvenQuot with ⟨t, ht⟩
  rcases (Nat.mem_divisors.mp hg).1 with ⟨a, ha⟩
  have hgpos : 0 < g := rawCore_divisor_pos_of_mem_divisors_of_pos hq hg
  have hquot : q / g = a := by
    rw [ha, Nat.mul_div_right _ hgpos]
  have haEven : Even a := by
    refine ⟨t, ?_⟩
    rw [← hquot, ht]
  rcases haEven with ⟨u, hu⟩
  have hqEven : Even q := by
    refine ⟨g * u, ?_⟩
    rw [ha, hu]
    ring
  exact (Nat.not_even_iff_odd.mpr hqOdd) hqEven

theorem rawCore_reducedQuotients_coprime_of_coprime_moduli
    {q q' g h : ℕ} (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.Coprime (q / g) (q' / h) := by
  have hqg_dvd : q / g ∣ q :=
    Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hg).1
  have hq'h_dvd : q' / h ∣ q' :=
    Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hh).1
  exact (hcop.coprime_dvd_left hqg_dvd).coprime_dvd_right hq'h_dvd

theorem rawCore_divisors_coprime_of_coprime_moduli
    {q q' g h : ℕ} (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.Coprime g h := by
  exact (hcop.coprime_dvd_left (Nat.mem_divisors.mp hg).1).coprime_dvd_right
    (Nat.mem_divisors.mp hh).1

theorem rawCore_jointCompatibility_of_coprime_moduli_divisors
    {q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    ramanujanGcdClassJointCompatibility q q' g h := by
  have hgpos : 0 < g := rawCore_divisor_pos_of_mem_divisors_of_pos hq hg
  have hhpos : 0 < h := rawCore_divisor_pos_of_mem_divisors_of_pos hq' hh
  have hgh : Nat.Coprime g h := rawCore_divisors_coprime_of_coprime_moduli hcop hg hh
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
    exact ((hcop.coprime_dvd_left hqg_dvd).coprime_dvd_right
      (Nat.mem_divisors.mp hh).1)
  · rw [hlcm_div_h]
    exact (((hcop.coprime_dvd_right hq'h_dvd).coprime_dvd_left
      (Nat.mem_divisors.mp hg).1).symm)

theorem rawEvenRamanujanGcdClassPeriodicPairLen_eq_two_mul_jointModulus_of_coprime_moduli_divisors_for_rawCore
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
        - (X ⌈/⌉ Nat.lcm g h))
      =
    2 * ramanujanGcdClassJointModulus q q' g h := by
  have hgpos : 0 < g := rawCore_divisor_pos_of_mem_divisors_of_pos hq hg
  have hhpos : 0 < h := rawCore_divisor_pos_of_mem_divisors_of_pos hq' hh
  have hgh : Nat.Coprime g h := rawCore_divisors_coprime_of_coprime_moduli hcop hg hh
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

theorem rawEvenRamanujanGcdClassPairBlockSum_eq_totient_mul_of_odd_coprime_moduli_divisors
    {X q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q') (hqOdd : Odd q) (hq'Odd : Odd q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPairBlockSum X q q' g h
      =
    (Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ) := by
  have hcompat : ramanujanGcdClassJointCompatibility q q' g h :=
    rawCore_jointCompatibility_of_coprime_moduli_divisors hq hq' hcop hg hh
  have hgpos : 0 < g := rawCore_divisor_pos_of_mem_divisors_of_pos hq hg
  have hhpos : 0 < h := rawCore_divisor_pos_of_mem_divisors_of_pos hq' hh
  have hLpos : 0 < Nat.lcm g h := Nat.lcm_pos hgpos hhpos
  have hPpos : 0 < centeredRamanujanPairBlockPeriod q q' := by
    dsimp [centeredRamanujanPairBlockPeriod]
    exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hq hq')
  have hgOdd : ¬ Goldbach.Windows.IsEven g := by
    exact rawCore_not_isEven_of_mem_divisors_odd hqOdd hg
  have hhOdd : ¬ Goldbach.Windows.IsEven h := by
    exact rawCore_not_isEven_of_mem_divisors_odd hq'Odd hh
  have hgh : Nat.Coprime g h := rawCore_divisors_coprime_of_coprime_moduli hcop hg hh
  have hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h) := by
    intro hEvenL
    have hEvenMul : Goldbach.Windows.IsEven (g * h) := by
      simpa [hgh.lcm_eq_mul] using hEvenL
    have hEvenh : Goldbach.Windows.IsEven h :=
      (isEven_mul_iff_of_not_isEven_left hgOdd).1 hEvenMul
    exact hhOdd hEvenh
  have hMpos : 0 < ramanujanGcdClassJointModulus q q' g h := by
    unfold ramanujanGcdClassJointModulus
    exact Nat.mul_pos (rawCore_quotient_pos_of_mem_divisors hq hg)
      (rawCore_quotient_pos_of_mem_divisors hq' hh)
  have hMOdd : Odd (ramanujanGcdClassJointModulus q q' g h) := by
    unfold ramanujanGcdClassJointModulus
    exact (rawCore_odd_div_of_mem_divisors_odd hq hqOdd hg).mul
      (rawCore_odd_div_of_mem_divisors_odd hq' hq'Odd hh)
  have hLen :
      (((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        =
      2 * ramanujanGcdClassJointModulus q q' g h :=
    rawEvenRamanujanGcdClassPeriodicPairLen_eq_two_mul_jointModulus_of_coprime_moduli_divisors_for_rawCore
      hq hq' hcop hg hh
  have hdiv :
      ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        / (2 * ramanujanGcdClassJointModulus q q' g h))
        = 1 := by
    have h2Mpos : 0 < 2 * ramanujanGcdClassJointModulus q q' g h :=
      Nat.mul_pos (by norm_num) hMpos
    rw [hLen]
    exact Nat.div_self h2Mpos
  have hmod :
      ((((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        % (2 * ramanujanGcdClassJointModulus q q' g h))
        = 0 := by
    rw [hLen]
    simp
  have hphi :
      (Nat.totient (ramanujanGcdClassJointModulus q q' g h) : ℝ)
        =
      (Nat.totient (q / g) : ℝ) * (Nat.totient (q' / h) : ℝ) := by
    unfold ramanujanGcdClassJointModulus
    exact_mod_cast
      (Nat.totient_mul
        (rawCore_reducedQuotients_coprime_of_coprime_moduli hcop hg hh))
  have hdiv' :
      (((X + 2 * Nat.lcm q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        / (2 * ramanujanGcdClassJointModulus q q' g h)
        = 1 := by
    simpa [centeredRamanujanPairBlockPeriod] using hdiv
  have hmod' :
      (((X + 2 * Nat.lcm q q' - 1) / Nat.lcm g h + 1)
          - (X ⌈/⌉ Nat.lcm g h))
        % (2 * ramanujanGcdClassJointModulus q q' g h)
        = 0 := by
    simpa [centeredRamanujanPairBlockPeriod] using hmod
  rw [rawEvenRamanujanGcdClassPairBlockSum_eq_count hg hh]
  rw [rawEvenRamanujanGcdClassPairBlockCount_eq_periodicCount hq hq' hg hh hcompat]
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_odd_lcm_totient_main_add_remainder_of_odd_jointModulus
    X q q' g h hLpos hPpos hcompat hOddL hMpos hMOdd]
  dsimp
  rw [hdiv', hmod']
  simp [hphi]

theorem rawCore_divisors_filter_not_isEven_eq_self_of_odd
    {q : ℕ} (hqOdd : Odd q) :
    q.divisors.filter (fun g => ¬ Goldbach.Windows.IsEven g) = q.divisors := by
  ext g
  constructor
  · intro hg
    exact (Finset.mem_filter.mp hg).1
  · intro hg
    exact Finset.mem_filter.mpr
      ⟨hg, rawCore_not_isEven_of_mem_divisors_odd hqOdd hg⟩

theorem rawEvenRamanujanPairBlockSum_eq_oddOddParityFactor_mul_of_odd_coprime_moduli
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q') (hqOdd : Odd q) (hq'Odd : Odd q') :
    rawEvenRamanujanPairBlockSum X q q'
      =
    centeredRamanujanPairOddOddParityFactor q
      * centeredRamanujanPairOddOddParityFactor q' := by
  let G := q.divisors
  let H' := q'.divisors
  let aq : ℕ → ℝ := fun g =>
    ramanujanGcdClassCoeff q g * (Nat.totient (q / g) : ℝ)
  let bq : ℕ → ℝ := fun h =>
    ramanujanGcdClassCoeff q' h * (Nat.totient (q' / h) : ℝ)
  have hprod :
      (∑ g ∈ G, aq g) * (∑ h ∈ H', bq h)
        =
      ∑ g ∈ G, ∑ h ∈ H', aq g * bq h := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro g _hg
    rw [Finset.mul_sum]
  rw [rawEvenRamanujanPairBlockSum_eq_sum_gcdClassPairBlockSums hq hq']
  calc
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * rawEvenRamanujanGcdClassPairBlockSum X q q' g h
      =
    ∑ g ∈ G, ∑ h ∈ H', aq g * bq h := by
        refine Finset.sum_congr rfl ?_
        intro g hg
        refine Finset.sum_congr rfl ?_
        intro h hh
        rw [rawEvenRamanujanGcdClassPairBlockSum_eq_totient_mul_of_odd_coprime_moduli_divisors
          hq hq' hcop hqOdd hq'Odd hg hh]
        dsimp [aq, bq]
        ring
    _ = (∑ g ∈ G, aq g) * (∑ h ∈ H', bq h) := hprod.symm
    _ =
      centeredRamanujanPairOddOddParityFactor q
        * centeredRamanujanPairOddOddParityFactor q' := by
        unfold centeredRamanujanPairOddOddParityFactor
        rw [rawCore_divisors_filter_not_isEven_eq_self_of_odd hqOdd]
        rw [rawCore_divisors_filter_not_isEven_eq_self_of_odd hq'Odd]

theorem rawEvenRamanujanPairBlockSum_eq_zero_of_odd_squarefree_coprime_offDiagonal
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q') (hqOdd : Odd q) (hq'Odd : Odd q')
    (hsq : Squarefree q) (hsq' : Squarefree q') (hneq : q ≠ q') :
    rawEvenRamanujanPairBlockSum X q q' = 0 := by
  rw [rawEvenRamanujanPairBlockSum_eq_oddOddParityFactor_mul_of_odd_coprime_moduli
    hq hq' hcop hqOdd hq'Odd]
  by_cases hq1 : q = 1
  · have hq'ne1 : q' ≠ 1 := by
      intro hq'1
      exact hneq (hq1.trans hq'1.symm)
    rw [centeredRamanujanPairOddOddParityFactor_eq_zero_of_odd_squarefree_ne_one
      hq'Odd hsq' hq'ne1]
    ring
  · rw [centeredRamanujanPairOddOddParityFactor_eq_zero_of_odd_squarefree_ne_one
      hqOdd hsq hq1]
    ring

private theorem rawCore_forall_mem_of_bad_filter_card_zero
    {α : Type*} [DecidableEq α] {s : Finset α} {P : α → Prop}
    [DecidablePred P]
    (hcard : (s.filter (fun x => ! decide (P x))).card = 0) :
    ∀ x ∈ s, P x := by
  intro x hx
  by_contra hPx
  have hxBad : x ∈ s.filter (fun x => ! decide (P x)) := by
    exact Finset.mem_filter.mpr ⟨hx, by simp [hPx]⟩
  have hEmpty : s.filter (fun x => ! decide (P x)) = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hEmpty] at hxBad
  simp at hxBad

def bothThreeCoprimeCoreSquarefreeGood (p : ℕ × ℕ) : Prop :=
  Squarefree (bothThreeOddCore p.1) ∧ Squarefree (bothThreeOddCore p.2)

instance instDecidableBothThreeCoprimeCoreSquarefreeGood
    (p : ℕ × ℕ) : Decidable (bothThreeCoprimeCoreSquarefreeGood p) := by
  unfold bothThreeCoprimeCoreSquarefreeGood
  infer_instance

private theorem rawCore_dyadicException_mem_of_bothThreeCoprimeCore_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    p ∈ PeriodicMainZeroDyadicExceptionPairs := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  have hpCoreResidual :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs :=
    (Finset.mem_filter.mp hpBoth).1
  have hpResidual :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs :=
    (Finset.mem_filter.mp hpCoreResidual).1
  have hpNonCoprime :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimePairs :=
    (Finset.mem_filter.mp hpResidual).1
  exact (Finset.mem_filter.mp hpNonCoprime).1

private theorem rawCore_left_squarefree_of_mem_fullBlockSquarefree
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit) :
    Squarefree p.1 := by
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hp).1
  have hpLeft : p.1 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).1
  exact (Finset.mem_filter.mp hpLeft).2

private theorem rawCore_right_squarefree_of_mem_fullBlockSquarefree
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit) :
    Squarefree p.2 := by
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hp).1
  have hpRight : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  exact (Finset.mem_filter.mp hpRight).2

private theorem rawCore_squarefree_core_of_squarefree_side
    {q : ℕ} (hsq : Squarefree q)
    (hshape : q = 3 * bothThreeOddCore q ∨ q = 6 * bothThreeOddCore q) :
    Squarefree (bothThreeOddCore q) := by
  refine hsq.squarefree_of_dvd ?_
  rcases hshape with hshape | hshape
  · refine ⟨3, ?_⟩
    simpa [Nat.mul_comm] using hshape
  · refine ⟨6, ?_⟩
    simpa [Nat.mul_comm] using hshape

theorem bothThreeCoprimeCoreSquarefreeGood_of_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    bothThreeCoprimeCoreSquarefreeGood p := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  have hpFullSq :
      p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit :=
    PeriodicMainZeroDyadicExceptionPairs_subset_fullBlockSquarefreeExplicit
      (rawCore_dyadicException_mem_of_bothThreeCoprimeCore_mem hp)
  have hsqLeft : Squarefree p.1 :=
    rawCore_left_squarefree_of_mem_fullBlockSquarefree hpFullSq
  have hsqRight : Squarefree p.2 :=
    rawCore_right_squarefree_of_mem_fullBlockSquarefree hpFullSq
  have hleftShape :
      p.1 = 3 * bothThreeOddCore p.1 ∨
        p.1 = 6 * bothThreeOddCore p.1 :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_eq_three_or_six_mul_core
      p hpBoth
  have hrightShape :
      p.2 = 3 * bothThreeOddCore p.2 ∨
        p.2 = 6 * bothThreeOddCore p.2 :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
      p hpBoth
  exact
    ⟨rawCore_squarefree_core_of_squarefree_side hsqLeft hleftShape,
      rawCore_squarefree_core_of_squarefree_side hsqRight hrightShape⟩

theorem bothThreeCoprimeCoreRawGood_of_squarefreeGood
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hsqGood : bothThreeCoprimeCoreSquarefreeGood p) :
    bothThreeCoprimeCoreRawGood p := by
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  have hsqA : Squarefree a := by
    simpa [a, bothThreeCoprimeCoreSquarefreeGood] using hsqGood.1
  have hsqB : Squarefree b := by
    simpa [b, bothThreeCoprimeCoreSquarefreeGood] using hsqGood.2
  have hapos : 1 ≤ a := by
    have hpos : 0 < a := by
      simpa [a] using
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_pos hpBoth
    omega
  have hbpos : 1 ≤ b := by
    have hpos : 0 < b := by
      simpa [b] using
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_pos hpBoth
    omega
  have haOdd : Odd a := by
    refine Nat.not_even_iff_odd.mp ?_
    intro hEven
    exact
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_odd
        p hpBoth) (by
          simpa [a] using Goldbach.Windows.isEven_of_even hEven)
  have hbOdd : Odd b := by
    refine Nat.not_even_iff_odd.mp ?_
    intro hEven
    exact
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_odd
        p hpBoth) (by
          simpa [b] using Goldbach.Windows.isEven_of_even hEven)
  have hcop : Nat.Coprime a b := by
    simpa [a, b] using
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_cores_coprime
        hp
  have hne : a ≠ b := by
    simpa [a, b] using
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_odd_cores_ne
        p hpBoth
  have hreal :
      rawEvenRamanujanPairBlockSum X0 a b = 0 :=
    rawEvenRamanujanPairBlockSum_eq_zero_of_odd_squarefree_coprime_offDiagonal
      (X := X0) hapos hbpos hcop haOdd hbOdd hsqA hsqB hne
  have hratCast : (rawEvenRamanujanPairBlockSumRat X0 a b : ℝ) = 0 := by
    rw [← rawEvenRamanujanPairBlockSum_eq_ratCast (X := X0) (q := a) (q' := b)]
    exact hreal
  unfold bothThreeCoprimeCoreRawGood
  exact Rat.cast_eq_zero.mp hratCast

theorem bothThreeCoprimeCoreRawGood_of_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    bothThreeCoprimeCoreRawGood p :=
  bothThreeCoprimeCoreRawGood_of_squarefreeGood hp
    (bothThreeCoprimeCoreSquarefreeGood_of_mem hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
