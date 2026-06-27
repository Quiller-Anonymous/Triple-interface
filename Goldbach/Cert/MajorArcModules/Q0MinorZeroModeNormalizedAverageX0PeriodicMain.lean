import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable def PeriodicMainCoeffSupportExplicit : Finset ℕ :=
  normalizedSigmaTruncSummandCoeffSupportUpToQ0

noncomputable def PeriodicMainActiveSupportExplicit : Finset ℕ :=
  PeriodicMainCoeffSupportExplicit.filter
    (fun q => q ≤ (H + 1) / 2)

noncomputable def surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat
    (X : ℕ) : ℚ :=
  ∑ q ∈ PeriodicMainCoeffSupportExplicit,
    ∑ q' ∈ PeriodicMainCoeffSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q'

noncomputable def surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat
    (X : ℕ) : ℚ :=
  ∑ q ∈ PeriodicMainActiveSupportExplicit,
    ∑ q' ∈ PeriodicMainActiveSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q'

noncomputable def PeriodicMainActiveOrderedPairSupportExplicit : Finset (ℕ × ℕ) :=
  PeriodicMainActiveSupportExplicit ×ˢ PeriodicMainActiveSupportExplicit

noncomputable def PeriodicMainFullBlockOrderedPairSupportExplicit : Finset (ℕ × ℕ) :=
  PeriodicMainActiveOrderedPairSupportExplicit.filter
    (fun p =>
      p.1 ≠ p.2 ∧ centeredRamanujanPairBlockPeriod p.1 p.2 ≤ H + 1)

def PeriodicMainActiveSupportSquarefreeExplicit : Finset ℕ :=
  (Finset.Icc (1 : ℕ) ((H + 1) / 2)).filter Squarefree

def PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit : Finset (ℕ × ℕ) :=
  (PeriodicMainActiveSupportSquarefreeExplicit ×ˢ PeriodicMainActiveSupportSquarefreeExplicit).filter
    (fun p =>
      p.1 ≠ p.2 ∧ centeredRamanujanPairBlockPeriod p.1 p.2 ≤ H + 1)

def PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit
    (lo : ℕ) : Finset (ℕ × ℕ) :=
  PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.filter
    (fun p => lo ≤ p.1)

def PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
    (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  (PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit lo).filter
    (fun p => p.1 < hi)

def surrogatePeriodicMainActiveOrderedPairSummandRat
    (X : ℕ) (p : ℕ × ℕ) : ℚ :=
  if p.1 = p.2 then 0
  else
    surrogateNormalizedSigmaTruncSummandCoeffRat p.1
      * surrogateNormalizedSigmaTruncSummandCoeffRat p.2
      * centeredRamanujanPairPeriodicMainTermRat X p.1 p.2

theorem surrogateNormalizedSigmaTruncSummandCoeffRat_eq_zero_of_not_squarefree
    {q : ℕ} (hnot : ¬ Squarefree q) :
    surrogateNormalizedSigmaTruncSummandCoeffRat q = 0 := by
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hnot]

theorem PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit :
    PeriodicMainActiveSupportExplicit = PeriodicMainActiveSupportSquarefreeExplicit := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqCoeff, hqActive⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨hqIcc, hsq⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqIcc).1, hqActive⟩, hsq⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hqOne, hqActive⟩
    have hqActiveNum : q ≤ 5000 := by
      simpa [H] using hqActive
    have hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
      change q ≤ 30000
      omega
    have hqCoeff : q ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨hqOne, hqQ0⟩, hsq⟩
    exact Finset.mem_filter.mpr ⟨hqCoeff, hqActive⟩

theorem PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit :
    PeriodicMainFullBlockOrderedPairSupportExplicit =
      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit
    PeriodicMainActiveOrderedPairSupportExplicit
  rw [PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit]

theorem PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainder_sum_split
    (lo hi : ℕ) (hlohi : lo ≤ hi) (f : ℕ × ℕ → ℚ) :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit lo, f p) =
      (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit lo hi, f p)
        + (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit hi, f p) := by
  unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
    PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.filter (fun p => lo ≤ p.1))
    (p := fun p => p.1 < hi)
    (f := f)]
  have hset :
      (PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.filter (fun p => lo ≤ p.1)).filter
          (fun p => ¬p.1 < hi) =
        PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.filter (fun p => hi ≤ p.1) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact ⟨hp.1.1, by omega⟩
    · intro hp
      exact ⟨⟨hp.1, by omega⟩, by omega⟩
  rw [hset]

theorem PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainder_one :
    PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit 1 =
      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit
  ext p
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).1
  · intro hp
    have hpActive :
        p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
          PeriodicMainActiveSupportSquarefreeExplicit := by
      exact (Finset.mem_filter.mp hp).1
    have hpLeft : p.1 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
      (Finset.mem_product.mp hpActive).1
    have hpIcc : p.1 ∈ Finset.Icc (1 : ℕ) ((H + 1) / 2) :=
      (Finset.mem_filter.mp hpLeft).1
    exact Finset.mem_filter.mpr ⟨hp, (Finset.mem_Icc.mp hpIcc).1⟩

theorem PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainder_5001_eq_empty :
    PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit 5001 = ∅ := by
  unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpFull, hpLo⟩
  have hpActive :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit := by
    exact (Finset.mem_filter.mp hpFull).1
  have hpLeft : p.1 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpActive).1
  have hpIcc : p.1 ∈ Finset.Icc (1 : ℕ) ((H + 1) / 2) :=
    (Finset.mem_filter.mp hpLeft).1
  have hpHi : p.1 ≤ 5000 := by
    have hpHi' := (Finset.mem_Icc.mp hpIcc).2
    norm_num [H] at hpHi' ⊢
    exact hpHi'
  omega

theorem centeredRamanujanPairPeriodicMainTermRat_eq_zero_of_blockPeriod_gt
    {X q q' : ℕ}
    (hP : H + 1 < centeredRamanujanPairBlockPeriod q q') :
    centeredRamanujanPairPeriodicMainTermRat X q q' = 0 := by
  have hdiv : (H + 1) / (2 * Nat.lcm q q') = 0 := by
    simpa [centeredRamanujanPairBlockPeriod] using Nat.div_eq_of_lt hP
  unfold centeredRamanujanPairPeriodicMainTermRat
  simp [hdiv]

theorem surrogatePeriodicMainPairSummandRat_eq_zero_of_blockPeriod_gt
    {X q q' : ℕ}
    (hP : H + 1 < centeredRamanujanPairBlockPeriod q q') :
    surrogateNormalizedSigmaTruncSummandCoeffRat q
      * surrogateNormalizedSigmaTruncSummandCoeffRat q'
      * centeredRamanujanPairPeriodicMainTermRat X q q' = 0 := by
  rw [centeredRamanujanPairPeriodicMainTermRat_eq_zero_of_blockPeriod_gt hP]
  ring

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder
    (X q q' q0 g0 : ℕ) (hgEven : Goldbach.Windows.IsEven g0)
    (hMpos : 0 < q0 / g0) :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g0
      =
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    ((((L / M) * Nat.totient M
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card)) : ℕ) : ℚ) := by
  have hReal :=
    Q0MinorZeroModeNormalizedAverage.rawEvenRamanujanGcdClassBlockPeriodicCount_eq_even_totient_main_add_remainder
      X q q' q0 g0 hgEven hMpos
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast] at hReal
  exact Rat.cast_injective (α := ℝ) hReal

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder
    (X q q' g h : ℕ) (hEvenL : Goldbach.Windows.IsEven (Nat.lcm g h))
    (hMpos : 0 < ramanujanGcdClassJointModulus q q' g h) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q q' g h
      =
    let A := X ⌈/⌉ Nat.lcm g h
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    ((((L / M) * Nat.totient M
        + (((Finset.range (L % M)).filter
            (fun t => Nat.Coprime M (A + (L / M) * M + t))).card)) : ℕ) : ℚ) := by
  have hReal :=
    Q0MinorZeroModeNormalizedAverage.rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_even_lcm_totient_main_add_remainder
      X q q' g h hEvenL hMpos
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_ratCast] at hReal
  exact Rat.cast_injective (α := ℝ) hReal

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder
    (X q q' q0 g0 : ℕ) (hg0pos : 0 < g0)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hgOdd : ¬ Goldbach.Windows.IsEven g0)
    (hMpos : 0 < q0 / g0) (hMOdd : Odd (q0 / g0)) :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g0
      =
    let A := X ⌈/⌉ g0
    let L := ((X + centeredRamanujanPairBlockPeriod q q' - 1) / g0 + 1) - A
    let M := q0 / g0
    ((((L / (2 * M)) * Nat.totient M
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card)) : ℕ) : ℚ) := by
  have hReal :=
    Q0MinorZeroModeNormalizedAverage.rawEvenRamanujanGcdClassBlockPeriodicCount_eq_odd_g_totient_main_add_remainder_of_odd_quotient
      X q q' q0 g0 hg0pos hPpos hgOdd hMpos hMOdd
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast] at hReal
  exact Rat.cast_injective (α := ℝ) hReal

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder
    (X q q' g h : ℕ) (hLpos : 0 < Nat.lcm g h)
    (hPpos : 0 < centeredRamanujanPairBlockPeriod q q')
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h)
    (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h))
    (hMpos : 0 < ramanujanGcdClassJointModulus q q' g h)
    (hMOdd : Odd (ramanujanGcdClassJointModulus q q' g h)) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q q' g h
      =
    let A := X ⌈/⌉ Nat.lcm g h
    let L :=
      ((X + centeredRamanujanPairBlockPeriod q q' - 1) / Nat.lcm g h + 1) - A
    let M := ramanujanGcdClassJointModulus q q' g h
    ((((L / (2 * M)) * Nat.totient M
        + (((Finset.range (L % (2 * M))).filter
            (fun t =>
              Goldbach.Windows.IsEven (A + (L / (2 * M)) * (2 * M) + t)
                ∧ Nat.Coprime M (A + (L / (2 * M)) * (2 * M) + t))).card)) : ℕ) : ℚ) := by
  have hReal :=
    Q0MinorZeroModeNormalizedAverage.rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_odd_lcm_totient_main_add_remainder_of_odd_jointModulus
      X q q' g h hLpos hPpos hcompat hOddL hMpos hMOdd
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_ratCast] at hReal
  exact Rat.cast_injective (α := ℝ) hReal

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient
    (X q q' q0 g0 : ℕ) (hgOdd : ¬ Goldbach.Windows.IsEven g0)
    (hMEven : Goldbach.Windows.IsEven (q0 / g0)) :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g0 = 0 := by
  have hReal :=
    Q0MinorZeroModeNormalizedAverage.rawEvenRamanujanGcdClassBlockPeriodicCount_eq_zero_of_not_isEven_g_of_isEven_quotient
      X q q' q0 g0 hgOdd hMEven
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast] at hReal
  have hReal' :
      (rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g0 : ℝ) =
        ((0 : ℚ) : ℝ) := by
    simpa using hReal
  exact Rat.cast_injective (α := ℝ) hReal'

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus
    (X q q' g h : ℕ) (hOddL : ¬ Goldbach.Windows.IsEven (Nat.lcm g h))
    (hMEven : Goldbach.Windows.IsEven (ramanujanGcdClassJointModulus q q' g h)) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q q' g h = 0 := by
  have hReal :=
    Q0MinorZeroModeNormalizedAverage.rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus
      X q q' g h hOddL hMEven
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_ratCast] at hReal
  have hReal' :
      (rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q q' g h : ℝ) =
        ((0 : ℚ) : ℝ) := by
    simpa using hReal
  exact Rat.cast_injective (α := ℝ) hReal'

theorem rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible
    {X q q' g h : ℕ}
    (hcompat : ¬ ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q q' g h = 0 := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCountRat
  simp [hcompat]

theorem rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible
    {X q q' g h : ℕ}
    (hcompat : ramanujanGcdClassJointCompatibility q q' g h) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q q' g h =
      rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q q' g h := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCountRat
  simp [hcompat]

private theorem even_window_card_ne_zero_unconditional
    (X : ℕ) :
    (EvenIn X H).card ≠ 0 := by
  refine Finset.card_ne_zero.mpr ?_
  by_cases hEven : Goldbach.Windows.IsEven X
  · exact ⟨X, Goldbach.Windows.mem_EvenIn_self (N := X) (H := H) hEven⟩
  · have h1 : 1 ∈ Finset.range (H + 1) := by
      norm_num [H]
    have hEvenSucc : Goldbach.Windows.IsEven (X + 1) := by
      dsimp [Goldbach.Windows.IsEven] at hEven ⊢
      omega
    unfold Goldbach.Windows.EvenIn Goldbach.Windows.IccShift
    refine ⟨X + 1, Finset.mem_filter.mpr ?_⟩
    refine ⟨Finset.mem_image.mpr ?_, hEvenSucc⟩
    exact ⟨1, h1, by simp⟩

theorem ramanujanGcdClassWindowAverageRat_one_one
    (X : ℕ) :
    ramanujanGcdClassWindowAverageRat X 1 1 = 1 := by
  unfold ramanujanGcdClassWindowAverageRat
  have hfilter :
      (EvenIn X H).filter (fun N => Nat.gcd 1 N = 1) = EvenIn X H := by
    ext N
    simp
  rw [hfilter]
  have hcard : (((EvenIn X H).card : ℚ) ≠ 0) := by
    exact_mod_cast even_window_card_ne_zero_unconditional X
  field_simp [hcard]

private theorem isEven_of_mem_EvenIn {X H N : ℕ}
    (hN : N ∈ EvenIn X H) :
    Goldbach.Windows.IsEven N :=
  (Finset.mem_filter.mp (by simpa [EvenIn] using hN)).2

private theorem gcd_two_eq_two_of_isEven {N : ℕ}
    (hEven : Goldbach.Windows.IsEven N) :
    Nat.gcd 2 N = 2 := by
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left 2 N
  · exact Nat.dvd_gcd (dvd_refl 2) (by
      dsimp [Goldbach.Windows.IsEven] at hEven
      exact Nat.dvd_of_mod_eq_zero hEven)

private theorem gcd_two_ne_one_of_isEven {N : ℕ}
    (hEven : Goldbach.Windows.IsEven N) :
    Nat.gcd 2 N ≠ 1 := by
  rw [gcd_two_eq_two_of_isEven hEven]
  norm_num

theorem ramanujanGcdClassWindowAverageRat_two_two
    (X : ℕ) :
    ramanujanGcdClassWindowAverageRat X 2 2 = 1 := by
  unfold ramanujanGcdClassWindowAverageRat
  have hfilter :
      (EvenIn X H).filter (fun N => Nat.gcd 2 N = 2) = EvenIn X H := by
    ext N
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hN
      exact ⟨hN, gcd_two_eq_two_of_isEven (isEven_of_mem_EvenIn hN)⟩
  rw [hfilter]
  have hcard : (((EvenIn X H).card : ℚ) ≠ 0) := by
    exact_mod_cast even_window_card_ne_zero_unconditional X
  field_simp [hcard]

theorem ramanujanGcdClassWindowAverageRat_two_one
    (X : ℕ) :
    ramanujanGcdClassWindowAverageRat X 2 1 = 0 := by
  unfold ramanujanGcdClassWindowAverageRat
  have hfilter :
      (EvenIn X H).filter (fun N => Nat.gcd 2 N = 1) = ∅ := by
    ext N
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · intro hN
      exact (gcd_two_ne_one_of_isEven (isEven_of_mem_EvenIn hN.1)) hN.2
    · intro h
      cases h
  rw [hfilter]
  change ((0 : ℕ) : ℚ) / ((EvenIn X H).card : ℚ) = 0
  exact zero_div _

theorem centeredRamanujanGcdClassObservable_two_one_of_isEven
    (X N : ℕ) (hEven : Goldbach.Windows.IsEven N) :
    centeredRamanujanGcdClassObservable X 2 1 N = 0 := by
  rw [centeredRamanujanGcdClassObservable_eq_ratCast]
  unfold centeredRamanujanGcdClassObservableRat ramanujanGcdClassIndicatorRat
  rw [ramanujanGcdClassWindowAverageRat_two_one]
  have hgcd : Nat.gcd 2 N ≠ 1 := gcd_two_ne_one_of_isEven hEven
  simp [hgcd]

theorem centeredRamanujanGcdClassObservable_two_two_of_isEven
    (X N : ℕ) (hEven : Goldbach.Windows.IsEven N) :
    centeredRamanujanGcdClassObservable X 2 2 N = 0 := by
  rw [centeredRamanujanGcdClassObservable_eq_ratCast]
  unfold centeredRamanujanGcdClassObservableRat ramanujanGcdClassIndicatorRat
  rw [ramanujanGcdClassWindowAverageRat_two_two]
  have hgcd : Nat.gcd 2 N = 2 := gcd_two_eq_two_of_isEven hEven
  simp [hgcd]

theorem centeredRamanujanGcdClassObservable_two_left_of_isEven
    (X N g : ℕ) (hg : g ∈ Nat.divisors 2)
    (hEven : Goldbach.Windows.IsEven N) :
    centeredRamanujanGcdClassObservable X 2 g N = 0 := by
  have hDivLeft : Nat.divisors 2 = ({1, 2} : Finset ℕ) := by
    native_decide
  rw [hDivLeft] at hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · exact centeredRamanujanGcdClassObservable_two_one_of_isEven X N hEven
  · exact centeredRamanujanGcdClassObservable_two_two_of_isEven X N hEven

theorem centeredEvenRamanujanGcdClassPairOffset_two_left_zero
    (X q' g h k : ℕ) (hg : g ∈ Nat.divisors 2) :
    centeredEvenRamanujanGcdClassPairOffset X 2 q' g h k = 0 := by
  unfold centeredEvenRamanujanGcdClassPairOffset centeredRamanujanGcdClassPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos hEven]
    rw [centeredRamanujanGcdClassObservable_two_left_of_isEven X (X + k) g hg hEven]
    ring
  · rw [if_neg hEven]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_two_left_zero
    (X q' g h : ℕ) (hg : g ∈ Nat.divisors 2) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X 2 q' g h = 0 := by
  unfold centeredRamanujanGcdClassPairFullEvenBlockSum
  refine Finset.sum_eq_zero ?_
  intro k _hk
  exact centeredEvenRamanujanGcdClassPairOffset_two_left_zero X q' g h k hg

theorem centeredRamanujanPairPeriodicMainTerm_two_left
    (X q' : ℕ) (hq' : 1 ≤ q') :
    centeredRamanujanPairPeriodicMainTerm X 2 q' = 0 := by
  have hmain :
      centeredRamanujanPairPeriodicMainTerm X 2 q'
        =
      ∑ g ∈ Nat.divisors 2, ∑ h ∈ q'.divisors,
        ramanujanGcdClassCoeff 2 g * ramanujanGcdClassCoeff q' h
          * ((((H + 1) / centeredRamanujanPairBlockPeriod 2 q') : ℕ)
              • centeredRamanujanGcdClassPairFullEvenBlockSum X 2 q' g h) := by
    unfold centeredRamanujanPairPeriodicMainTerm
    refine Finset.sum_congr rfl ?_
    intro g hg
    refine Finset.sum_congr rfl ?_
    intro h hh
    rw [← centeredRamanujanGcdClassPairFullEvenBlockSum_eq_resolved_periodic_comparison
      (X := X) (q := 2) (q' := q') (g := g) (h := h) (by norm_num) hq' hg hh]
  rw [hmain]
  refine Finset.sum_eq_zero ?_
  intro g hg
  refine Finset.sum_eq_zero ?_
  intro h _hh
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_two_left_zero X q' g h hg]
  simp

theorem centeredRamanujanPairPeriodicMainTermRat_two_left
    (X q' : ℕ) (hq' : 0 < q') :
    centeredRamanujanPairPeriodicMainTermRat X 2 q' = 0 := by
  have hreal : centeredRamanujanPairPeriodicMainTerm X 2 q' = 0 :=
    centeredRamanujanPairPeriodicMainTerm_two_left X q' hq'
  rw [centeredRamanujanPairPeriodicMainTerm_eq_ratCast] at hreal
  have hreal' :
      ((centeredRamanujanPairPeriodicMainTermRat X 2 q') : ℝ) =
        ((0 : ℚ) : ℝ) := by
    simpa using hreal
  exact Rat.cast_injective (α := ℝ) hreal'

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_two_left_zero
    (X : ℕ) (p : ℕ × ℕ) (hp1 : p.1 = 2) (hp2pos : 0 < p.2) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p = 0 := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · rw [if_neg hdiag]
    rw [hp1]
    rw [centeredRamanujanPairPeriodicMainTermRat_two_left X p.2 hp2pos]
    ring

theorem centeredEvenRamanujanGcdClassPairOffset_two_right_zero
    (X q g h k : ℕ) (hh : h ∈ Nat.divisors 2) :
    centeredEvenRamanujanGcdClassPairOffset X q 2 g h k = 0 := by
  unfold centeredEvenRamanujanGcdClassPairOffset centeredRamanujanGcdClassPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos hEven]
    rw [centeredRamanujanGcdClassObservable_two_left_of_isEven X (X + k) h hh hEven]
    ring
  · rw [if_neg hEven]

theorem centeredRamanujanGcdClassPairFullEvenBlockSum_two_right_zero
    (X q g h : ℕ) (hh : h ∈ Nat.divisors 2) :
    centeredRamanujanGcdClassPairFullEvenBlockSum X q 2 g h = 0 := by
  unfold centeredRamanujanGcdClassPairFullEvenBlockSum
  refine Finset.sum_eq_zero ?_
  intro k _hk
  exact centeredEvenRamanujanGcdClassPairOffset_two_right_zero X q g h k hh

theorem centeredRamanujanPairPeriodicMainTerm_two_right
    (X q : ℕ) (hq : 1 ≤ q) :
    centeredRamanujanPairPeriodicMainTerm X q 2 = 0 := by
  have hmain :
      centeredRamanujanPairPeriodicMainTerm X q 2
        =
      ∑ g ∈ q.divisors, ∑ h ∈ Nat.divisors 2,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff 2 h
          * ((((H + 1) / centeredRamanujanPairBlockPeriod q 2) : ℕ)
              • centeredRamanujanGcdClassPairFullEvenBlockSum X q 2 g h) := by
    unfold centeredRamanujanPairPeriodicMainTerm
    refine Finset.sum_congr rfl ?_
    intro g hg
    refine Finset.sum_congr rfl ?_
    intro h hh
    rw [← centeredRamanujanGcdClassPairFullEvenBlockSum_eq_resolved_periodic_comparison
      (X := X) (q := q) (q' := 2) (g := g) (h := h) hq (by norm_num) hg hh]
  rw [hmain]
  refine Finset.sum_eq_zero ?_
  intro g _hg
  refine Finset.sum_eq_zero ?_
  intro h hh
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_two_right_zero X q g h hh]
  simp

theorem centeredRamanujanPairPeriodicMainTermRat_two_right
    (X q : ℕ) (hq : 0 < q) :
    centeredRamanujanPairPeriodicMainTermRat X q 2 = 0 := by
  have hreal : centeredRamanujanPairPeriodicMainTerm X q 2 = 0 :=
    centeredRamanujanPairPeriodicMainTerm_two_right X q hq
  rw [centeredRamanujanPairPeriodicMainTerm_eq_ratCast] at hreal
  have hreal' :
      ((centeredRamanujanPairPeriodicMainTermRat X q 2) : ℝ) =
        ((0 : ℚ) : ℝ) := by
    simpa using hreal
  exact Rat.cast_injective (α := ℝ) hreal'

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_two_right_zero
    (X : ℕ) (p : ℕ × ℕ) (hp2 : p.2 = 2) (hp1pos : 0 < p.1) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p = 0 := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · rw [if_neg hdiag]
    rw [hp2]
    rw [centeredRamanujanPairPeriodicMainTermRat_two_right X p.1 hp1pos]
    ring

private theorem even_filter_range_two_card
    (X : ℕ) :
    ((Finset.range 2).filter (fun t => Goldbach.Windows.IsEven (X + t))).card = 1 := by
  by_cases hEvenX : Goldbach.Windows.IsEven X
  · have hOddSucc : ¬ Goldbach.Windows.IsEven (X + 1) := by
      dsimp [Goldbach.Windows.IsEven] at hEvenX ⊢
      omega
    have hset :
        (Finset.range 2).filter (fun t => Goldbach.Windows.IsEven (X + t)) =
          ({0} : Finset ℕ) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · intro ht
        have htlt : t < 2 := ht.1
        have hteven : Goldbach.Windows.IsEven (X + t) := ht.2
        interval_cases t
        · rfl
        · exfalso
          exact hOddSucc hteven
      · intro ht
        subst t
        exact ⟨by norm_num, by simpa using hEvenX⟩
    rw [hset]
    simp
  · have hEvenSucc : Goldbach.Windows.IsEven (X + 1) := by
      dsimp [Goldbach.Windows.IsEven] at hEvenX ⊢
      omega
    have hset :
        (Finset.range 2).filter (fun t => Goldbach.Windows.IsEven (X + t)) =
          ({1} : Finset ℕ) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · intro ht
        have htlt : t < 2 := ht.1
        have hteven : Goldbach.Windows.IsEven (X + t) := ht.2
        interval_cases t
        · exfalso
          exact hEvenX (by simpa using hteven)
        · rfl
      · intro ht
        subst t
        exact ⟨by norm_num, hEvenSucc⟩
    rw [hset]
    simp

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_one_one_left
    (X q' : ℕ) (hq' : 0 < q') :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X 1 q' 1 1 =
      evenRamanujanBlockCountRat 1 q' := by
  unfold rawEvenRamanujanGcdClassBlockPeriodicCountRat evenRamanujanBlockCountRat
  have hOdd1 : ¬ Goldbach.Windows.IsEven 1 := by
    dsimp [Goldbach.Windows.IsEven]
    norm_num
  simp [hOdd1, centeredRamanujanPairBlockPeriod]
  have hL : X + 2 * q' - 1 + 1 - X = 2 * q' := by
    omega
  rw [hL]
  rw [even_filter_range_two_card X]
  norm_num [hq']

theorem rawEvenRamanujanGcdClassPairBlockResolvedCountRat_one_left
    (X q' h : ℕ) (hh : h ∈ q'.divisors) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X 1 q' 1 h =
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X 1 q' q' h := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCountRat
  have hhpos : 0 < h := Nat.pos_of_mem_divisors hh
  have hcompat : ramanujanGcdClassJointCompatibility 1 q' 1 h := by
    unfold ramanujanGcdClassJointCompatibility
    simp [Nat.div_self hhpos]
  simp [hcompat]
  unfold rawEvenRamanujanGcdClassPairBlockPeriodicCountRat
    rawEvenRamanujanGcdClassBlockPeriodicCountRat
    ramanujanGcdClassJointModulus
  simp

theorem centeredRamanujanPairPeriodicMainTermRat_one_left_of_counts
    (X q' : ℕ)
    (hleft :
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X 1 q' 1 1 =
        evenRamanujanBlockCountRat 1 q')
    (hpair :
      ∀ h ∈ q'.divisors,
        rawEvenRamanujanGcdClassPairBlockResolvedCountRat X 1 q' 1 h =
          rawEvenRamanujanGcdClassBlockPeriodicCountRat X 1 q' q' h) :
    centeredRamanujanPairPeriodicMainTermRat X 1 q' = 0 := by
  have hDivLeft : Nat.divisors 1 = ({1} : Finset ℕ) := by
    native_decide
  unfold centeredRamanujanPairPeriodicMainTermRat
  rw [hDivLeft]
  rw [Finset.sum_singleton]
  refine Finset.sum_eq_zero ?_
  intro h hh
  rw [hpair h hh, ramanujanGcdClassWindowAverageRat_one_one X, hleft]
  ring

theorem centeredRamanujanPairPeriodicMainTermRat_one_left
    (X q' : ℕ) (hq' : 0 < q') :
    centeredRamanujanPairPeriodicMainTermRat X 1 q' = 0 :=
  centeredRamanujanPairPeriodicMainTermRat_one_left_of_counts X q'
    (rawEvenRamanujanGcdClassBlockPeriodicCountRat_one_one_left X q' hq')
    (rawEvenRamanujanGcdClassPairBlockResolvedCountRat_one_left X q')

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_one_left_zero
    (X : ℕ) (p : ℕ × ℕ) (hp1 : p.1 = 1) (hp2pos : 0 < p.2) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p = 0 := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · rw [if_neg hdiag]
    rw [hp1]
    rw [centeredRamanujanPairPeriodicMainTermRat_one_left X p.2 hp2pos]
    ring

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_one_one_right
    (X q : ℕ) (hq : 0 < q) :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X q 1 1 1 =
      evenRamanujanBlockCountRat q 1 := by
  unfold rawEvenRamanujanGcdClassBlockPeriodicCountRat evenRamanujanBlockCountRat
  have hOdd1 : ¬ Goldbach.Windows.IsEven 1 := by
    dsimp [Goldbach.Windows.IsEven]
    norm_num
  simp [hOdd1, centeredRamanujanPairBlockPeriod]
  have hL : X + 2 * q - 1 + 1 - X = 2 * q := by
    omega
  rw [hL]
  rw [even_filter_range_two_card X]
  norm_num [hq]

theorem rawEvenRamanujanGcdClassPairBlockResolvedCountRat_one_right
    (X q g : ℕ) (hg : g ∈ q.divisors) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q 1 g 1 =
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X q 1 q g := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCountRat
  have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
  have hcompat : ramanujanGcdClassJointCompatibility q 1 g 1 := by
    unfold ramanujanGcdClassJointCompatibility
    simp [Nat.div_self hgpos]
  simp [hcompat]
  unfold rawEvenRamanujanGcdClassPairBlockPeriodicCountRat
    rawEvenRamanujanGcdClassBlockPeriodicCountRat
    ramanujanGcdClassJointModulus
  simp

theorem centeredRamanujanPairPeriodicMainTermRat_one_right_of_counts
    (X q : ℕ)
    (hright :
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X q 1 1 1 =
        evenRamanujanBlockCountRat q 1)
    (hpair :
      ∀ g ∈ q.divisors,
        rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q 1 g 1 =
          rawEvenRamanujanGcdClassBlockPeriodicCountRat X q 1 q g) :
    centeredRamanujanPairPeriodicMainTermRat X q 1 = 0 := by
  have hDivRight : Nat.divisors 1 = ({1} : Finset ℕ) := by
    native_decide
  unfold centeredRamanujanPairPeriodicMainTermRat
  rw [hDivRight]
  simp only [Finset.sum_singleton]
  refine Finset.sum_eq_zero ?_
  intro g hg
  rw [hpair g hg, ramanujanGcdClassWindowAverageRat_one_one X, hright]
  ring

theorem centeredRamanujanPairPeriodicMainTermRat_one_right
    (X q : ℕ) (hq : 0 < q) :
    centeredRamanujanPairPeriodicMainTermRat X q 1 = 0 :=
  centeredRamanujanPairPeriodicMainTermRat_one_right_of_counts X q
    (rawEvenRamanujanGcdClassBlockPeriodicCountRat_one_one_right X q hq)
    (rawEvenRamanujanGcdClassPairBlockResolvedCountRat_one_right X q)

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_one_right_zero
    (X : ℕ) (p : ℕ × ℕ) (hp2 : p.2 = 1) (hp1pos : 0 < p.1) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p = 0 := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · rw [if_neg hdiag]
    rw [hp2]
    rw [centeredRamanujanPairPeriodicMainTermRat_one_right X p.1 hp1pos]
    ring

private theorem centeredRamanujanPairBlockPeriod_gt_of_left_gt_active
    {q q' : ℕ}
    (hq'pos : 0 < q')
    (hqgt : (H + 1) / 2 < q) :
    H + 1 < centeredRamanujanPairBlockPeriod q q' := by
  have hlcm : q ≤ Nat.lcm q q' := Nat.le_lcm_left q hq'pos
  dsimp [centeredRamanujanPairBlockPeriod]
  norm_num [H] at hqgt ⊢
  have h2q : 10001 < 2 * q := by omega
  have hle : 2 * q ≤ 2 * Nat.lcm q q' := Nat.mul_le_mul_left 2 hlcm
  omega

private theorem centeredRamanujanPairBlockPeriod_gt_of_right_gt_active
    {q q' : ℕ}
    (hqpos : 0 < q)
    (hq'gt : (H + 1) / 2 < q') :
    H + 1 < centeredRamanujanPairBlockPeriod q q' := by
  simpa [centeredRamanujanPairBlockPeriod, Nat.lcm_comm] using
    (centeredRamanujanPairBlockPeriod_gt_of_left_gt_active
      (q := q') (q' := q) hqpos hq'gt)

private theorem surrogatePeriodicMainRat_row_eq_coeffSupported
    (X q : ℕ) :
    (∑ q' ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q')
      =
    (∑ q' ∈ PeriodicMainCoeffSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q') := by
  symm
  apply Finset.sum_subset
  · intro q' hq'
    unfold PeriodicMainCoeffSupportExplicit at hq'
    exact (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hq').1
  · intro q' hq'Icc hq'not
    by_cases hsq : Squarefree q'
    · have hmem : q' ∈ PeriodicMainCoeffSupportExplicit := by
        unfold PeriodicMainCoeffSupportExplicit
        exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨hq'Icc, hsq⟩
      exact False.elim (hq'not hmem)
    · simp [surrogateNormalizedSigmaTruncSummandCoeffRat_eq_zero_of_not_squarefree hsq]

private theorem surrogatePeriodicMainRat_row_over_active_eq_zero_of_not_active
    (X q : ℕ)
    (hqcoeff : q ∈ PeriodicMainCoeffSupportExplicit)
    (hqnot : q ∉ PeriodicMainActiveSupportExplicit) :
    (∑ q' ∈ PeriodicMainActiveSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q') = 0 := by
  have hqgt : (H + 1) / 2 < q := by
    by_contra hnotgt
    have hqle : q ≤ (H + 1) / 2 := Nat.le_of_not_gt hnotgt
    exact hqnot (Finset.mem_filter.mpr ⟨hqcoeff, hqle⟩)
  have hqpos : 0 < q := by
    unfold PeriodicMainCoeffSupportExplicit at hqcoeff
    have hIcc := (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqcoeff).1
    exact Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hIcc).1
  apply Finset.sum_eq_zero
  intro q' hq'
  have hq'pos : 0 < q' := by
    have hq'coeff := (Finset.mem_filter.mp hq').1
    unfold PeriodicMainCoeffSupportExplicit at hq'coeff
    have hIcc := (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hq'coeff).1
    exact Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hIcc).1
  have hneq : q ≠ q' := by
    intro h
    subst q
    exact hqnot hq'
  have hP : H + 1 < centeredRamanujanPairBlockPeriod q q' :=
    centeredRamanujanPairBlockPeriod_gt_of_left_gt_active hq'pos hqgt
  simp [hneq, surrogatePeriodicMainPairSummandRat_eq_zero_of_blockPeriod_gt hP]

private theorem surrogatePeriodicMainRat_row_over_coeff_eq_zero_of_not_active
    (X q : ℕ)
    (hqcoeff : q ∈ PeriodicMainCoeffSupportExplicit)
    (hqnot : q ∉ PeriodicMainActiveSupportExplicit) :
    (∑ q' ∈ PeriodicMainCoeffSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q') = 0 := by
  have hqgt : (H + 1) / 2 < q := by
    by_contra hnotgt
    have hqle : q ≤ (H + 1) / 2 := Nat.le_of_not_gt hnotgt
    exact hqnot (Finset.mem_filter.mpr ⟨hqcoeff, hqle⟩)
  have hqpos : 0 < q := by
    unfold PeriodicMainCoeffSupportExplicit at hqcoeff
    have hIcc := (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqcoeff).1
    exact Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hIcc).1
  apply Finset.sum_eq_zero
  intro q' hq'
  have hq'pos : 0 < q' := by
    unfold PeriodicMainCoeffSupportExplicit at hq'
    have hIcc := (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hq').1
    exact Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hIcc).1
  by_cases hqq' : q = q'
  · simp [hqq']
  · have hP : H + 1 < centeredRamanujanPairBlockPeriod q q' :=
      centeredRamanujanPairBlockPeriod_gt_of_left_gt_active hq'pos hqgt
    simp [hqq', surrogatePeriodicMainPairSummandRat_eq_zero_of_blockPeriod_gt hP]

private theorem surrogatePeriodicMainRat_row_eq_active
    (X q : ℕ)
    (hqcoeff : q ∈ PeriodicMainCoeffSupportExplicit) :
    (∑ q' ∈ PeriodicMainCoeffSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q')
      =
    (∑ q' ∈ PeriodicMainActiveSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * centeredRamanujanPairPeriodicMainTermRat X q q') := by
  by_cases hqactive : q ∈ PeriodicMainActiveSupportExplicit
  · symm
    apply Finset.sum_subset
    · intro q' hq'
      exact (Finset.mem_filter.mp hq').1
    · intro q' hq'coeff hq'not
      by_cases hqq' : q = q'
      · simp [hqq']
      · have hq'gt : (H + 1) / 2 < q' := by
          by_contra hnotgt
          have hq'le : q' ≤ (H + 1) / 2 := Nat.le_of_not_gt hnotgt
          exact hq'not (Finset.mem_filter.mpr ⟨hq'coeff, hq'le⟩)
        have hq'pos : 0 < q' := by
          unfold PeriodicMainCoeffSupportExplicit at hq'coeff
          have hIcc := (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hq'coeff).1
          exact Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hIcc).1
        have hqpos : 0 < q := by
          unfold PeriodicMainCoeffSupportExplicit at hqcoeff
          have hIcc := (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqcoeff).1
          exact Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hIcc).1
        have hP : H + 1 < centeredRamanujanPairBlockPeriod q q' :=
          centeredRamanujanPairBlockPeriod_gt_of_right_gt_active hqpos hq'gt
        simp [hqq', surrogatePeriodicMainPairSummandRat_eq_zero_of_blockPeriod_gt hP]
  · rw [surrogatePeriodicMainRat_row_over_coeff_eq_zero_of_not_active X q hqcoeff hqactive]
    rw [surrogatePeriodicMainRat_row_over_active_eq_zero_of_not_active X q hqcoeff hqactive]

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat_eq_active
    (X : ℕ) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat X =
      surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat X := by
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat
    surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat
  rw [Finset.sum_congr rfl (fun q hq => surrogatePeriodicMainRat_row_eq_active X q hq)]
  symm
  apply Finset.sum_subset
  · intro q hq
    exact (Finset.mem_filter.mp hq).1
  · intro q hqcoeff hqnot
    exact surrogatePeriodicMainRat_row_over_active_eq_zero_of_not_active X q hqcoeff hqnot

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_coeffSupported
    (X : ℕ) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X =
      surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat X := by
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat
    surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat
  rw [Finset.sum_congr rfl (fun q _ => surrogatePeriodicMainRat_row_eq_coeffSupported X q)]
  symm
  apply Finset.sum_subset
  · intro q hq
    unfold PeriodicMainCoeffSupportExplicit at hq
    exact (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hq).1
  · intro q hqIcc hqnot
    by_cases hsq : Squarefree q
    · have hmem : q ∈ PeriodicMainCoeffSupportExplicit := by
        unfold PeriodicMainCoeffSupportExplicit
        exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨hqIcc, hsq⟩
      exact False.elim (hqnot hmem)
    · simp [surrogateNormalizedSigmaTruncSummandCoeffRat_eq_zero_of_not_squarefree hsq]

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_active
    (X : ℕ) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X =
      surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat X := by
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_coeffSupported,
    surrogateCenteredNormalizedSigmaTruncPeriodicMainCoeffSupportedPairSumUpToQ0Rat_eq_active]

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_orderedPairs
    (X : ℕ) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat X =
      ∑ p ∈ PeriodicMainActiveOrderedPairSupportExplicit,
        surrogatePeriodicMainActiveOrderedPairSummandRat X p := by
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat
    PeriodicMainActiveOrderedPairSupportExplicit
    surrogatePeriodicMainActiveOrderedPairSummandRat
  rw [← Finset.sum_product']

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_fullBlockOrderedPairs
    (X : ℕ) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat X =
      ∑ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
        surrogatePeriodicMainActiveOrderedPairSummandRat X p := by
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_orderedPairs]
  symm
  apply Finset.sum_subset
  · intro p hp
    exact (Finset.mem_filter.mp hp).1
  · intro p hpactive hpnot
    have hpnotFull :
        ¬ (p.1 ≠ p.2 ∧ centeredRamanujanPairBlockPeriod p.1 p.2 ≤ H + 1) := by
      intro h
      exact hpnot (Finset.mem_filter.mpr ⟨hpactive, h⟩)
    by_cases hdiag : p.1 = p.2
    · simp [surrogatePeriodicMainActiveOrderedPairSummandRat, hdiag]
    · have hPeriodNotLe : ¬ centeredRamanujanPairBlockPeriod p.1 p.2 ≤ H + 1 := by
        intro hle
        exact hpnotFull ⟨hdiag, hle⟩
      have hPeriodGt : H + 1 < centeredRamanujanPairBlockPeriod p.1 p.2 := by
        omega
      unfold surrogatePeriodicMainActiveOrderedPairSummandRat
      simp [hdiag, surrogatePeriodicMainPairSummandRat_eq_zero_of_blockPeriod_gt hPeriodGt]

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_cert_of_squarefreeFullBlockSum
    (hfull :
      (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        = surrogatePeriodicMainX0RatCert) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =
      surrogatePeriodicMainX0RatCert := by
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_active]
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_fullBlockOrderedPairs]
  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact hfull

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_sparse
    (X : ℕ)
    (pairs : Finset (ℕ × ℕ))
    (value : ℕ × ℕ → ℚ)
    (hsub : pairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit)
    (hzero :
      ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
        p ∉ pairs →
          surrogatePeriodicMainActiveOrderedPairSummandRat X p = 0)
    (hvalue :
      ∀ p ∈ pairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X p = value p) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat X =
      ∑ p ∈ pairs, value p := by
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_fullBlockOrderedPairs]
  calc
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
        surrogatePeriodicMainActiveOrderedPairSummandRat X p)
        =
      ∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X p := by
        symm
        exact Finset.sum_subset hsub hzero
    _ = ∑ p ∈ pairs, value p := by
        exact Finset.sum_congr rfl hvalue

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    {X q q' : ℕ} {cq cq' term value : ℚ}
    (hneq : q ≠ q')
    (hcq :
      surrogateNormalizedSigmaTruncSummandCoeffRat q = cq)
    (hcq' :
      surrogateNormalizedSigmaTruncSummandCoeffRat q' = cq')
    (hterm :
      centeredRamanujanPairPeriodicMainTermRat X q q' = term)
    (hvalue : cq * cq' * term = value) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X (Prod.mk q q') = value := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  simp [hneq, hcq, hcq', hterm, hvalue]

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
    {X : ℕ} {p : ℕ × ℕ}
    (hreal :
      (if p.1 = p.2 then (0 : ℝ) else
        surrogateNormalizedSigmaTruncSummandRealCoeff p.1
          * surrogateNormalizedSigmaTruncSummandRealCoeff p.2
          * centeredRamanujanPairPeriodicMainTerm X p.1 p.2) = 0) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p = 0 := by
  apply Rat.cast_injective (α := ℝ)
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · simp [hdiag, surrogateNormalizedSigmaTruncSummandRealCoeff_eq_ratCast,
      centeredRamanujanPairPeriodicMainTerm_eq_ratCast] at hreal ⊢
    exact hreal

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_sparse_cert
    (pairs : Finset (ℕ × ℕ))
    (value : ℕ × ℕ → ℚ)
    (hsub : pairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit)
    (hzero :
      ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
        p ∉ pairs →
          surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0)
    (hvalue :
      ∀ p ∈ pairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = value p)
    (hsum : (∑ p ∈ pairs, value p) = surrogatePeriodicMainX0RatCert) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =
      surrogatePeriodicMainX0RatCert := by
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_active]
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicMainActivePairSumUpToQ0Rat_eq_sparse
    X0 pairs value hsub hzero hvalue]
  exact hsum

structure PeriodicMainSparseOrderedCertificateAtX0 where
  pairs : Finset (ℕ × ℕ)
  value : ℕ × ℕ → ℚ
  support_subset :
    pairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit
  zero_off_records :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ pairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  value_on_records :
    ∀ p ∈ pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = value p
  records_sum :
    (∑ p ∈ pairs, value p) = surrogatePeriodicMainX0RatCert

theorem surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_cert_of_sparseOrderedCertificate
    (cert : PeriodicMainSparseOrderedCertificateAtX0) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =
      surrogatePeriodicMainX0RatCert := by
  exact surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_sparse_cert
    cert.pairs
    cert.value
    cert.support_subset
    cert.zero_off_records
    cert.value_on_records
    cert.records_sum

theorem centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_eq_cert
    (hcert :
      surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0
        = surrogatePeriodicMainX0RatCert) :
    CenteredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_exactCertificate
    (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactRatCertificateAtX0_of_eq_cert hcert)

theorem centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_sparseOrderedCertificate
    (cert : PeriodicMainSparseOrderedCertificateAtX0) :
    CenteredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_eq_cert
    (surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_cert_of_sparseOrderedCertificate cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
