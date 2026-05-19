import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def tailChunk000Sub000Part000SupportExplicit : Finset ℕ :=
  ([51] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part000 : ℚ :=
  (1999275 : ℚ) / 524288

def tailChunk000Sub000Part001SupportExplicit : Finset ℕ :=
  ([53] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part001 : ℚ :=
  (16364882875 : ℚ) / 18282695808

def tailChunk000Sub000Part002SupportExplicit : Finset ℕ :=
  ([59] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part002 : ℚ :=
  (9091066625 : ℚ) / 14148449124

def tailChunk000Sub000Part003SupportExplicit : Finset ℕ :=
  ([61] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part003 : ℚ :=
  (750447559 : ℚ) / 1296259200

def tailChunk000Sub000Part004SupportExplicit : Finset ℕ :=
  ([67] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part004 : ℚ :=
  (2303418125 : ℚ) / 5271814152

def tailChunk000Sub000Part005SupportExplicit : Finset ℕ :=
  ([71] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part005 : ℚ :=
  (24857171 : ℚ) / 68613720

def tailChunk000Sub000Part006SupportExplicit : Finset ℕ :=
  ([73] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part006 : ℚ :=
  (11172381725 : ℚ) / 33599038464

def tailChunk000Sub000Part007SupportExplicit : Finset ℕ :=
  ([79] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part007 : ℚ :=
  (898860025 : ℚ) / 3428005464

def tailChunk000Sub000Part008SupportExplicit : Finset ℕ :=
  ([83] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part008 : ℚ :=
  (4254818625 : ℚ) / 18842174348

def tailChunk000Sub000Part009SupportExplicit : Finset ℕ :=
  ([89] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part009 : ℚ :=
  (1162604775 : ℚ) / 6248076032

private theorem evenIn_X0_H_card_eq_5001_explicit :
    ((EvenIn X0 H).card : ℚ) = 5001 := by
  native_decide

private theorem isEven_of_mem_EvenIn_explicit
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    Goldbach.Windows.IsEven N := by
  unfold EvenIn IccShift at hN
  exact (Finset.mem_filter.mp hN).2

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyOne_one_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 1 N) = 3138 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyOne_three_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 3 N) = 1569 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyOne_seventeen_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 17 N) = 196 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyOne_fiftyOne_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 51 N) = 98 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_fiftyOne_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 51 1 = (3138 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 1)).card : ℚ) = 3138 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 1)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 1 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 51 N = 1 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 1))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 3138 := sum_ramanujanGcdClassIndicatorRat_fiftyOne_one_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_fiftyOne_three_X0 :
    ramanujanGcdClassWindowAverageRat X0 51 3 = (1569 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 3)).card : ℚ) = 1569 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 3)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 3 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 51 N = 3 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 3))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 1569 := sum_ramanujanGcdClassIndicatorRat_fiftyOne_three_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_fiftyOne_seventeen_X0 :
    ramanujanGcdClassWindowAverageRat X0 51 17 = (196 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 17)).card : ℚ) = 196 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 17)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 17 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 51 N = 17 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 17))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 196 := sum_ramanujanGcdClassIndicatorRat_fiftyOne_seventeen_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_fiftyOne_fiftyOne_X0 :
    ramanujanGcdClassWindowAverageRat X0 51 51 = (98 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 51)).card : ℚ) = 98 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 51)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 51 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 51 N = 51 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 51 N = 51))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 98 := sum_ramanujanGcdClassIndicatorRat_fiftyOne_fiftyOne_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_fiftyOne_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 51 1 N
      + ramanujanGcdClassIndicatorRat 51 3 N
      + ramanujanGcdClassIndicatorRat 51 17 N
      + ramanujanGcdClassIndicatorRat 51 51 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h51 : Nat.gcd 51 N = 51
  · simp [h51]
  · by_cases h17 : Nat.gcd 51 N = 17
    · simp [h51, h17]
    · by_cases h3 : Nat.gcd 51 N = 3
      · simp [h51, h17, h3]
      · have hdivs : (51 : ℕ).divisors = ({1, 3, 17, 51} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 51 N ∈ ({1, 3, 17, 51} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 51 N, by norm_num⟩
        have h1 : Nat.gcd 51 N = 1 := by
          simpa [h51, h17, h3] using hmem
        simp [h51, h17, h3, h1]

private theorem centeredRamanujanObservableRat_X0_51_eq_indicator51
    (N : ℕ) :
    centeredRamanujanObservableRat X0 51 N
      = (1 : ℚ)
          - 3 * ramanujanGcdClassIndicatorRat 51 3 N
          - 17 * ramanujanGcdClassIndicatorRat 51 17 N
          + 31 * ramanujanGcdClassIndicatorRat 51 51 N := by
  have hdivs : (51 : ℕ).divisors = ({1, 3, 17, 51} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 51 1 = 1 := by native_decide
  have hcoeff3 : ramanujanGcdClassCoeffRat 51 3 = -2 := by native_decide
  have hcoeff17 : ramanujanGcdClassCoeffRat 51 17 = -16 := by native_decide
  have hcoeff51 : ramanujanGcdClassCoeffRat 51 51 = 32 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff3, hcoeff17, hcoeff51,
    ramanujanGcdClassWindowAverageRat_fiftyOne_one_X0,
    ramanujanGcdClassWindowAverageRat_fiftyOne_three_X0,
    ramanujanGcdClassWindowAverageRat_fiftyOne_seventeen_X0,
    ramanujanGcdClassWindowAverageRat_fiftyOne_fiftyOne_X0]
  linarith [ramanujanGcdClassIndicatorRat_fiftyOne_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_51_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 51 N) ^ 2
      =
    (1 : ℚ)
      + (3 : ℚ) * ramanujanGcdClassIndicatorRat 51 3 N
      + (255 : ℚ) * ramanujanGcdClassIndicatorRat 51 17 N
      + (1023 : ℚ) * ramanujanGcdClassIndicatorRat 51 51 N := by
  rw [centeredRamanujanObservableRat_X0_51_eq_indicator51]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h51 : Nat.gcd 51 N = 51
  · simp [h51]
    norm_num
  · by_cases h17 : Nat.gcd 51 N = 17
    · simp [h51, h17]
      norm_num
    · by_cases h3 : Nat.gcd 51 N = 3
      · simp [h51, h17, h3]
        norm_num
      · have hdivs : (51 : ℕ).divisors = ({1, 3, 17, 51} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 51 N ∈ ({1, 3, 17, 51} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 51 N, by norm_num⟩
        have h1 : Nat.gcd 51 N = 1 := by
          simpa [h51, h17, h3] using hmem
        simp [h51, h17, h3, h1]

private theorem centeredRamanujanWindowEnergyRat_X0_51_eq_cert :
    centeredRamanujanWindowEnergyRat X0 51 = (159942 : ℚ) := by
  calc
    centeredRamanujanWindowEnergyRat X0 51
        =
      ∑ N ∈ EvenIn X0 H,
        ((1 : ℚ)
          + (3 : ℚ) * ramanujanGcdClassIndicatorRat 51 3 N
          + (255 : ℚ) * ramanujanGcdClassIndicatorRat 51 17 N
          + (1023 : ℚ) * ramanujanGcdClassIndicatorRat 51 51 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_51_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (1 : ℚ)
        + (3 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 3 N
        + (255 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 17 N
        + (1023 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 51 51 N := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = (159942 : ℚ) := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (1 : ℚ) = (5001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst,
            sum_ramanujanGcdClassIndicatorRat_fiftyOne_three_X0,
            sum_ramanujanGcdClassIndicatorRat_fiftyOne_seventeen_X0,
            sum_ramanujanGcdClassIndicatorRat_fiftyOne_fiftyOne_X0]
          norm_num

theorem surrogateDiagonalTailTerm51_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 51
      = (1999275 : ℚ) / 524288 := by
  have hsqfree : Squarefree 51 := by native_decide
  have hphi51 : Nat.totient 51 = 32 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_51_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi51]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part000_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part000 := by
  simp [tailChunk000Sub000Part000SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part000,
    surrogateDiagonalTailTerm51_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyThree_one_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 53 1 N) = 4906 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyThree_fiftyThree_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 53 53 N) = 95 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_fiftyThree_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 53 1 = (4906 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 53 N = 1)).card : ℚ) = 4906 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 53 N = 1)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 53 1 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 53 N = 1 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 53 N = 1))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 4906 := sum_ramanujanGcdClassIndicatorRat_fiftyThree_one_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_fiftyThree_fiftyThree_X0 :
    ramanujanGcdClassWindowAverageRat X0 53 53 = (95 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 53 N = 53)).card : ℚ) = 95 := by
    calc
      (((EvenIn X0 H).filter (fun N => Nat.gcd 53 N = 53)).card : ℚ)
          = ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 53 53 N := by
              unfold ramanujanGcdClassIndicatorRat
              have hsum :
                  ∑ N ∈ EvenIn X0 H, (if Nat.gcd 53 N = 53 then (1 : ℚ) else 0)
                    =
                  Finset.sum ((EvenIn X0 H).filter (fun N => Nat.gcd 53 N = 53))
                    (fun _ => (1 : ℚ)) := by
                      rw [Finset.sum_filter]
              rw [hsum]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 95 := sum_ramanujanGcdClassIndicatorRat_fiftyThree_fiftyThree_X0
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_fiftyThree_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 53 1 N
      + ramanujanGcdClassIndicatorRat 53 53 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h53 : Nat.gcd 53 N = 53
  · simp [h53]
  · have hdivs : (53 : ℕ).divisors = ({1, 53} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 53 N ∈ ({1, 53} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 53 N, by norm_num⟩
    have h1 : Nat.gcd 53 N = 1 := by
      simpa [h53] using hmem
    simp [h53, h1]

private theorem centeredRamanujanObservableRat_X0_53_eq_indicator53
    (N : ℕ) :
    centeredRamanujanObservableRat X0 53 N
      = (-5035 / 5001 : ℚ)
          + 53 * ramanujanGcdClassIndicatorRat 53 53 N := by
  have hdivs : (53 : ℕ).divisors = ({1, 53} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 53 1 = -1 := by native_decide
  have hcoeff53 : ramanujanGcdClassCoeffRat 53 53 = 52 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff53,
    ramanujanGcdClassWindowAverageRat_fiftyThree_one_X0,
    ramanujanGcdClassWindowAverageRat_fiftyThree_fiftyThree_X0]
  linarith [ramanujanGcdClassIndicatorRat_fiftyThree_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_53_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 53 N) ^ 2
      =
    (25351225 / 25010001 : ℚ)
      + (13514099 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 53 53 N := by
  rw [centeredRamanujanObservableRat_X0_53_eq_indicator53]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h53 : Nat.gcd 53 N = 53
  · simp [h53]
    norm_num
  · have hdivs : (53 : ℕ).divisors = ({1, 53} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 53 N ∈ ({1, 53} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 53 N, by norm_num⟩
    have h1 : Nat.gcd 53 N = 1 := by
      simpa [h53] using hmem
    simp [h53, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_53_eq_cert :
    centeredRamanujanWindowEnergyRat X0 53 = (1309190630 : ℚ) / 5001 := by
  calc
    centeredRamanujanWindowEnergyRat X0 53
        =
      ∑ N ∈ EvenIn X0 H,
        ((25351225 / 25010001 : ℚ)
          + (13514099 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 53 53 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_53_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (25351225 / 25010001 : ℚ)
        + (13514099 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 53 53 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1309190630 : ℚ) / 5001 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (25351225 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (25351225 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_fiftyThree_fiftyThree_X0]
          norm_num

theorem surrogateDiagonalTailTerm53_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 53
      = (16364882875 : ℚ) / 18282695808 := by
  have hsqfree : Squarefree 53 := by native_decide
  have hphi53 : Nat.totient 53 = 52 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_53_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi53]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part001_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part001 := by
  simp [tailChunk000Sub000Part001SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part001,
    surrogateDiagonalTailTerm53_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_fiftyNine_fiftyNine_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 59 59 N) = 85 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_fiftyNine_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 59 1 = (4916 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 59 N = 1)).card : ℚ) = 4916 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_fiftyNine_fiftyNine_X0 :
    ramanujanGcdClassWindowAverageRat X0 59 59 = (85 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 59 N = 59)).card : ℚ) = 85 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_fiftyNine_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 59 1 N
      + ramanujanGcdClassIndicatorRat 59 59 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h59 : Nat.gcd 59 N = 59
  · simp [h59]
  · have hdivs : (59 : ℕ).divisors = ({1, 59} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 59 N ∈ ({1, 59} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 59 N, by norm_num⟩
    have h1 : Nat.gcd 59 N = 1 := by
      simpa [h59] using hmem
    simp [h59, h1]

private theorem centeredRamanujanObservableRat_X0_59_eq_indicator59
    (N : ℕ) :
    centeredRamanujanObservableRat X0 59 N
      = (-5015 / 5001 : ℚ)
          + 59 * ramanujanGcdClassIndicatorRat 59 59 N := by
  have hdivs : (59 : ℕ).divisors = ({1, 59} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 59 1 = -1 := by native_decide
  have hcoeff59 : ramanujanGcdClassCoeffRat 59 59 = 58 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff59,
    ramanujanGcdClassWindowAverageRat_fiftyNine_one_X0,
    ramanujanGcdClassWindowAverageRat_fiftyNine_fiftyNine_X0]
  linarith [ramanujanGcdClassIndicatorRat_fiftyNine_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_59_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 59 N) ^ 2
      =
    (25150225 / 25010001 : ℚ)
      + (16816711 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 59 59 N := by
  rw [centeredRamanujanObservableRat_X0_59_eq_indicator59]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h59 : Nat.gcd 59 N = 59
  · simp [h59]
    norm_num
  · have hdivs : (59 : ℕ).divisors = ({1, 59} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 59 N ∈ ({1, 59} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 59 N, by norm_num⟩
    have h1 : Nat.gcd 59 N = 1 := by
      simpa [h59] using hmem
    simp [h59, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_59_eq_cert :
    centeredRamanujanWindowEnergyRat X0 59 = (1454570660 : ℚ) / 5001 := by
  calc
    centeredRamanujanWindowEnergyRat X0 59
        =
      ∑ N ∈ EvenIn X0 H,
        ((25150225 / 25010001 : ℚ)
          + (16816711 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 59 59 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_59_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (25150225 / 25010001 : ℚ)
        + (16816711 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 59 59 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1454570660 : ℚ) / 5001 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (25150225 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (25150225 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_fiftyNine_fiftyNine_X0]
          norm_num

theorem surrogateDiagonalTailTerm59_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 59
      = (9091066625 : ℚ) / 14148449124 := by
  have hsqfree : Squarefree 59 := by native_decide
  have hphi59 : Nat.totient 59 = 58 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_59_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi59]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part002_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part002 := by
  simp [tailChunk000Sub000Part002SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part002,
    surrogateDiagonalTailTerm59_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_sixtyOne_sixtyOne_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 61 61 N) = 82 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_sixtyOne_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 61 1 = (4919 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 61 N = 1)).card : ℚ) = 4919 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_sixtyOne_sixtyOne_X0 :
    ramanujanGcdClassWindowAverageRat X0 61 61 = (82 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 61 N = 61)).card : ℚ) = 82 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_sixtyOne_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 61 1 N
      + ramanujanGcdClassIndicatorRat 61 61 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h61 : Nat.gcd 61 N = 61
  · simp [h61]
  · have hdivs : (61 : ℕ).divisors = ({1, 61} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 61 N ∈ ({1, 61} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 61 N, by norm_num⟩
    have h1 : Nat.gcd 61 N = 1 := by
      simpa [h61] using hmem
    simp [h61, h1]

private theorem centeredRamanujanObservableRat_X0_61_eq_indicator61
    (N : ℕ) :
    centeredRamanujanObservableRat X0 61 N
      = (-5002 / 5001 : ℚ)
          + 61 * ramanujanGcdClassIndicatorRat 61 61 N := by
  have hdivs : (61 : ℕ).divisors = ({1, 61} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 61 1 = -1 := by native_decide
  have hcoeff61 : ramanujanGcdClassCoeffRat 61 61 = 60 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff61,
    ramanujanGcdClassWindowAverageRat_sixtyOne_one_X0,
    ramanujanGcdClassWindowAverageRat_sixtyOne_sixtyOne_X0]
  linarith [ramanujanGcdClassIndicatorRat_sixtyOne_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_61_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 61 N) ^ 2
      =
    (25020004 / 25010001 : ℚ)
      + (17998477 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 61 61 N := by
  rw [centeredRamanujanObservableRat_X0_61_eq_indicator61]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h61 : Nat.gcd 61 N = 61
  · simp [h61]
    norm_num
  · have hdivs : (61 : ℕ).divisors = ({1, 61} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 61 N ∈ ({1, 61} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 61 N, by norm_num⟩
    have h1 : Nat.gcd 61 N = 1 := by
      simpa [h61] using hmem
    simp [h61, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_61_eq_cert :
    centeredRamanujanWindowEnergyRat X0 61 = (1500895118 : ℚ) / 5001 := by
  calc
    centeredRamanujanWindowEnergyRat X0 61
        =
      ∑ N ∈ EvenIn X0 H,
        ((25020004 / 25010001 : ℚ)
          + (17998477 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 61 61 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_61_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (25020004 / 25010001 : ℚ)
        + (17998477 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 61 61 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1500895118 : ℚ) / 5001 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (25020004 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (25020004 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_sixtyOne_sixtyOne_X0]
          norm_num

theorem surrogateDiagonalTailTerm61_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 61
      = (750447559 : ℚ) / 1296259200 := by
  have hsqfree : Squarefree 61 := by native_decide
  have hphi61 : Nat.totient 61 = 60 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_61_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi61]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part003_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part003 := by
  simp [tailChunk000Sub000Part003SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part003,
    surrogateDiagonalTailTerm61_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_sixtySeven_sixtySeven_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 67 67 N) = 75 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_sixtySeven_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 67 1 = (4926 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 67 N = 1)).card : ℚ) = 4926 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_sixtySeven_sixtySeven_X0 :
    ramanujanGcdClassWindowAverageRat X0 67 67 = (75 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 67 N = 67)).card : ℚ) = 75 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_sixtySeven_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 67 1 N
      + ramanujanGcdClassIndicatorRat 67 67 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h67 : Nat.gcd 67 N = 67
  · simp [h67]
  · have hdivs : (67 : ℕ).divisors = ({1, 67} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 67 N ∈ ({1, 67} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 67 N, by norm_num⟩
    have h1 : Nat.gcd 67 N = 1 := by
      simpa [h67] using hmem
    simp [h67, h1]

private theorem centeredRamanujanObservableRat_X0_67_eq_indicator67
    (N : ℕ) :
    centeredRamanujanObservableRat X0 67 N
      = (-1675 / 1667 : ℚ)
          + 67 * ramanujanGcdClassIndicatorRat 67 67 N := by
  have hdivs : (67 : ℕ).divisors = ({1, 67} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 67 1 = -1 := by native_decide
  have hcoeff67 : ramanujanGcdClassCoeffRat 67 67 = 66 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff67,
    ramanujanGcdClassWindowAverageRat_sixtySeven_one_X0,
    ramanujanGcdClassWindowAverageRat_sixtySeven_sixtySeven_X0]
  linarith [ramanujanGcdClassIndicatorRat_sixtySeven_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_67_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 67 N) ^ 2
      =
    (2805625 / 2778889 : ℚ)
      + (7258713 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 67 67 N := by
  rw [centeredRamanujanObservableRat_X0_67_eq_indicator67]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h67 : Nat.gcd 67 N = 67
  · simp [h67]
    norm_num
  · have hdivs : (67 : ℕ).divisors = ({1, 67} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 67 N ∈ ({1, 67} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 67 N, by norm_num⟩
    have h1 : Nat.gcd 67 N = 1 := by
      simpa [h67] using hmem
    simp [h67, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_67_eq_cert :
    centeredRamanujanWindowEnergyRat X0 67 = (552820350 : ℚ) / 1667 := by
  calc
    centeredRamanujanWindowEnergyRat X0 67
        =
      ∑ N ∈ EvenIn X0 H,
        ((2805625 / 2778889 : ℚ)
          + (7258713 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 67 67 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_67_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (2805625 / 2778889 : ℚ)
        + (7258713 / 1667 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 67 67 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (552820350 : ℚ) / 1667 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (2805625 / 2778889 : ℚ)
                =
              (5001 : ℚ) * (2805625 / 2778889 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_sixtySeven_sixtySeven_X0]
          norm_num

theorem surrogateDiagonalTailTerm67_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 67
      = (2303418125 : ℚ) / 5271814152 := by
  have hsqfree : Squarefree 67 := by native_decide
  have hphi67 : Nat.totient 67 = 66 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_67_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi67]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part004_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part004 := by
  simp [tailChunk000Sub000Part004SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part004,
    surrogateDiagonalTailTerm67_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_seventyOne_seventyOne_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 71 71 N) = 70 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_seventyOne_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 71 1 = (4931 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 71 N = 1)).card : ℚ) = 4931 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_seventyOne_seventyOne_X0 :
    ramanujanGcdClassWindowAverageRat X0 71 71 = (70 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 71 N = 71)).card : ℚ) = 70 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_seventyOne_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 71 1 N
      + ramanujanGcdClassIndicatorRat 71 71 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h71 : Nat.gcd 71 N = 71
  · simp [h71]
  · have hdivs : (71 : ℕ).divisors = ({1, 71} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 71 N ∈ ({1, 71} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 71 N, by norm_num⟩
    have h1 : Nat.gcd 71 N = 1 := by
      simpa [h71] using hmem
    simp [h71, h1]

private theorem centeredRamanujanObservableRat_X0_71_eq_indicator71
    (N : ℕ) :
    centeredRamanujanObservableRat X0 71 N
      = (-4970 / 5001 : ℚ)
          + 71 * ramanujanGcdClassIndicatorRat 71 71 N := by
  have hdivs : (71 : ℕ).divisors = ({1, 71} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 71 1 = -1 := by native_decide
  have hcoeff71 : ramanujanGcdClassCoeffRat 71 71 = 70 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff71,
    ramanujanGcdClassWindowAverageRat_seventyOne_one_X0,
    ramanujanGcdClassWindowAverageRat_seventyOne_seventyOne_X0]
  linarith [ramanujanGcdClassIndicatorRat_seventyOne_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_71_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 71 N) ^ 2
      =
    (24700900 / 25010001 : ℚ)
      + (24504301 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 71 71 N := by
  rw [centeredRamanujanObservableRat_X0_71_eq_indicator71]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h71 : Nat.gcd 71 N = 71
  · simp [h71]
    norm_num
  · have hdivs : (71 : ℕ).divisors = ({1, 71} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 71 N ∈ ({1, 71} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 71 N, by norm_num⟩
    have h1 : Nat.gcd 71 N = 1 := by
      simpa [h71] using hmem
    simp [h71, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_71_eq_cert :
    centeredRamanujanWindowEnergyRat X0 71 = (1740001970 : ℚ) / 5001 := by
  calc
    centeredRamanujanWindowEnergyRat X0 71
        =
      ∑ N ∈ EvenIn X0 H,
        ((24700900 / 25010001 : ℚ)
          + (24504301 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 71 71 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_71_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (24700900 / 25010001 : ℚ)
        + (24504301 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 71 71 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1740001970 : ℚ) / 5001 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (24700900 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (24700900 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_seventyOne_seventyOne_X0]
          norm_num

theorem surrogateDiagonalTailTerm71_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 71
      = (24857171 : ℚ) / 68613720 := by
  have hsqfree : Squarefree 71 := by native_decide
  have hphi71 : Nat.totient 71 = 70 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_71_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi71]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part005_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part005 := by
  simp [tailChunk000Sub000Part005SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part005,
    surrogateDiagonalTailTerm71_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_seventyThree_seventyThree_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 73 73 N) = 68 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_seventyThree_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 73 1 = (4933 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 73 N = 1)).card : ℚ) = 4933 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_seventyThree_seventyThree_X0 :
    ramanujanGcdClassWindowAverageRat X0 73 73 = (68 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 73 N = 73)).card : ℚ) = 68 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_seventyThree_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 73 1 N
      + ramanujanGcdClassIndicatorRat 73 73 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h73 : Nat.gcd 73 N = 73
  · simp [h73]
  · have hdivs : (73 : ℕ).divisors = ({1, 73} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 73 N ∈ ({1, 73} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 73 N, by norm_num⟩
    have h1 : Nat.gcd 73 N = 1 := by
      simpa [h73] using hmem
    simp [h73, h1]

private theorem centeredRamanujanObservableRat_X0_73_eq_indicator73
    (N : ℕ) :
    centeredRamanujanObservableRat X0 73 N
      = (-4964 / 5001 : ℚ)
          + 73 * ramanujanGcdClassIndicatorRat 73 73 N := by
  have hdivs : (73 : ℕ).divisors = ({1, 73} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 73 1 = -1 := by native_decide
  have hcoeff73 : ramanujanGcdClassCoeffRat 73 73 = 72 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff73,
    ramanujanGcdClassWindowAverageRat_seventyThree_one_X0,
    ramanujanGcdClassWindowAverageRat_seventyThree_seventyThree_X0]
  linarith [ramanujanGcdClassIndicatorRat_seventyThree_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_73_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 73 N) ^ 2
      =
    (24641296 / 25010001 : ℚ)
      + (25925585 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 73 73 N := by
  rw [centeredRamanujanObservableRat_X0_73_eq_indicator73]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h73 : Nat.gcd 73 N = 73
  · simp [h73]
    norm_num
  · have hdivs : (73 : ℕ).divisors = ({1, 73} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 73 N ∈ ({1, 73} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 73 N, by norm_num⟩
    have h1 : Nat.gcd 73 N = 1 := by
      simpa [h73] using hmem
    simp [h73, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_73_eq_cert :
    centeredRamanujanWindowEnergyRat X0 73 = (1787581076 : ℚ) / 5001 := by
  calc
    centeredRamanujanWindowEnergyRat X0 73
        =
      ∑ N ∈ EvenIn X0 H,
        ((24641296 / 25010001 : ℚ)
          + (25925585 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 73 73 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_73_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (24641296 / 25010001 : ℚ)
        + (25925585 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 73 73 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1787581076 : ℚ) / 5001 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (24641296 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (24641296 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_seventyThree_seventyThree_X0]
          norm_num

theorem surrogateDiagonalTailTerm73_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 73
      = (11172381725 : ℚ) / 33599038464 := by
  have hsqfree : Squarefree 73 := by native_decide
  have hphi73 : Nat.totient 73 = 72 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_73_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi73]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part006_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part006 := by
  simp [tailChunk000Sub000Part006SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part006,
    surrogateDiagonalTailTerm73_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_seventyNine_seventyNine_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 79 79 N) = 63 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_seventyNine_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 79 1 = (4938 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 79 N = 1)).card : ℚ) = 4938 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_seventyNine_seventyNine_X0 :
    ramanujanGcdClassWindowAverageRat X0 79 79 = (21 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 79 N = 79)).card : ℚ) = 63 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassIndicatorRat_seventyNine_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 79 1 N
      + ramanujanGcdClassIndicatorRat 79 79 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h79 : Nat.gcd 79 N = 79
  · simp [h79]
  · have hdivs : (79 : ℕ).divisors = ({1, 79} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 79 N ∈ ({1, 79} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 79 N, by norm_num⟩
    have h1 : Nat.gcd 79 N = 1 := by
      simpa [h79] using hmem
    simp [h79, h1]

private theorem centeredRamanujanObservableRat_X0_79_eq_indicator79
    (N : ℕ) :
    centeredRamanujanObservableRat X0 79 N
      = (-1659 / 1667 : ℚ)
          + 79 * ramanujanGcdClassIndicatorRat 79 79 N := by
  have hdivs : (79 : ℕ).divisors = ({1, 79} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 79 1 = -1 := by native_decide
  have hcoeff79 : ramanujanGcdClassCoeffRat 79 79 = 78 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff79,
    ramanujanGcdClassWindowAverageRat_seventyNine_one_X0,
    ramanujanGcdClassWindowAverageRat_seventyNine_seventyNine_X0]
  linarith [ramanujanGcdClassIndicatorRat_seventyNine_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_79_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 79 N) ^ 2
      =
    (2752281 / 2778889 : ℚ)
      + (10141625 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 79 79 N := by
  rw [centeredRamanujanObservableRat_X0_79_eq_indicator79]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h79 : Nat.gcd 79 N = 79
  · simp [h79]
    norm_num
  · have hdivs : (79 : ℕ).divisors = ({1, 79} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 79 N ∈ ({1, 79} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 79 N, by norm_num⟩
    have h1 : Nat.gcd 79 N = 1 := by
      simpa [h79] using hmem
    simp [h79, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_79_eq_cert :
    centeredRamanujanWindowEnergyRat X0 79 = (647179218 : ℚ) / 1667 := by
  calc
    centeredRamanujanWindowEnergyRat X0 79
        =
      ∑ N ∈ EvenIn X0 H,
        ((2752281 / 2778889 : ℚ)
          + (10141625 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 79 79 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_79_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (2752281 / 2778889 : ℚ)
        + (10141625 / 1667 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 79 79 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (647179218 : ℚ) / 1667 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (2752281 / 2778889 : ℚ)
                =
              (5001 : ℚ) * (2752281 / 2778889 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_seventyNine_seventyNine_X0]
          norm_num

theorem surrogateDiagonalTailTerm79_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 79
      = (898860025 : ℚ) / 3428005464 := by
  have hsqfree : Squarefree 79 := by native_decide
  have hphi79 : Nat.totient 79 = 78 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_79_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi79]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part007_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part007 := by
  simp [tailChunk000Sub000Part007SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part007,
    surrogateDiagonalTailTerm79_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_eightyThree_eightyThree_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 83 83 N) = 60 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_eightyThree_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 83 1 = (4941 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 83 N = 1)).card : ℚ) = 4941 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_eightyThree_eightyThree_X0 :
    ramanujanGcdClassWindowAverageRat X0 83 83 = (20 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 83 N = 83)).card : ℚ) = 60 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassIndicatorRat_eightyThree_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 83 1 N
      + ramanujanGcdClassIndicatorRat 83 83 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h83 : Nat.gcd 83 N = 83
  · simp [h83]
  · have hdivs : (83 : ℕ).divisors = ({1, 83} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 83 N ∈ ({1, 83} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 83 N, by norm_num⟩
    have h1 : Nat.gcd 83 N = 1 := by
      simpa [h83] using hmem
    simp [h83, h1]

private theorem centeredRamanujanObservableRat_X0_83_eq_indicator83
    (N : ℕ) :
    centeredRamanujanObservableRat X0 83 N
      = (-1660 / 1667 : ℚ)
          + 83 * ramanujanGcdClassIndicatorRat 83 83 N := by
  have hdivs : (83 : ℕ).divisors = ({1, 83} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 83 1 = -1 := by native_decide
  have hcoeff83 : ramanujanGcdClassCoeffRat 83 83 = 82 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff83,
    ramanujanGcdClassWindowAverageRat_eightyThree_one_X0,
    ramanujanGcdClassWindowAverageRat_eightyThree_eightyThree_X0]
  linarith [ramanujanGcdClassIndicatorRat_eightyThree_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_83_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 83 N) ^ 2
      =
    (2755600 / 2778889 : ℚ)
      + (11208403 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 83 83 N := by
  rw [centeredRamanujanObservableRat_X0_83_eq_indicator83]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h83 : Nat.gcd 83 N = 83
  · simp [h83]
    norm_num
  · have hdivs : (83 : ℕ).divisors = ({1, 83} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 83 N ∈ ({1, 83} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 83 N, by norm_num⟩
    have h1 : Nat.gcd 83 N = 1 := by
      simpa [h83] using hmem
    simp [h83, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_83_eq_cert :
    centeredRamanujanWindowEnergyRat X0 83 = (680770980 : ℚ) / 1667 := by
  calc
    centeredRamanujanWindowEnergyRat X0 83
        =
      ∑ N ∈ EvenIn X0 H,
        ((2755600 / 2778889 : ℚ)
          + (11208403 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 83 83 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_83_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (2755600 / 2778889 : ℚ)
        + (11208403 / 1667 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 83 83 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (680770980 : ℚ) / 1667 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (2755600 / 2778889 : ℚ)
                =
              (5001 : ℚ) * (2755600 / 2778889 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_eightyThree_eightyThree_X0]
          norm_num

theorem surrogateDiagonalTailTerm83_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 83
      = (4254818625 : ℚ) / 18842174348 := by
  have hsqfree : Squarefree 83 := by native_decide
  have hphi83 : Nat.totient 83 = 82 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_83_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi83]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part008_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part008 := by
  simp [tailChunk000Sub000Part008SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part008,
    surrogateDiagonalTailTerm83_X0_eq_cert]

private theorem sum_ramanujanGcdClassIndicatorRat_eightyNine_eightyNine_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 89 89 N) = 57 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_eightyNine_one_X0 :
    ramanujanGcdClassWindowAverageRat X0 89 1 = (4944 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 89 N = 1)).card : ℚ) = 4944 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_eightyNine_eightyNine_X0 :
    ramanujanGcdClassWindowAverageRat X0 89 89 = (19 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 89 N = 89)).card : ℚ) = 57 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassIndicatorRat_eightyNine_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 89 1 N
      + ramanujanGcdClassIndicatorRat 89 89 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h89 : Nat.gcd 89 N = 89
  · simp [h89]
  · have hdivs : (89 : ℕ).divisors = ({1, 89} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 89 N ∈ ({1, 89} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 89 N, by norm_num⟩
    have h1 : Nat.gcd 89 N = 1 := by
      simpa [h89] using hmem
    simp [h89, h1]

private theorem centeredRamanujanObservableRat_X0_89_eq_indicator89
    (N : ℕ) :
    centeredRamanujanObservableRat X0 89 N
      = (-1691 / 1667 : ℚ)
          + 89 * ramanujanGcdClassIndicatorRat 89 89 N := by
  have hdivs : (89 : ℕ).divisors = ({1, 89} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 89 1 = -1 := by native_decide
  have hcoeff89 : ramanujanGcdClassCoeffRat 89 89 = 88 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff89,
    ramanujanGcdClassWindowAverageRat_eightyNine_one_X0,
    ramanujanGcdClassWindowAverageRat_eightyNine_eightyNine_X0]
  linarith [ramanujanGcdClassIndicatorRat_eightyNine_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_89_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 89 N) ^ 2
      =
    (2859481 / 2778889 : ℚ)
      + (12903309 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 89 89 N := by
  rw [centeredRamanujanObservableRat_X0_89_eq_indicator89]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h89 : Nat.gcd 89 N = 89
  · simp [h89]
    norm_num
  · have hdivs : (89 : ℕ).divisors = ({1, 89} : Finset ℕ) := by native_decide
    have hmem : Nat.gcd 89 N ∈ ({1, 89} : Finset ℕ) := by
      rw [← hdivs]
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 89 N, by norm_num⟩
    have h1 : Nat.gcd 89 N = 1 := by
      simpa [h89] using hmem
    simp [h89, h1]
    norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_89_eq_cert :
    centeredRamanujanWindowEnergyRat X0 89 = (744067056 : ℚ) / 1667 := by
  calc
    centeredRamanujanWindowEnergyRat X0 89
        =
      ∑ N ∈ EvenIn X0 H,
        ((2859481 / 2778889 : ℚ)
          + (12903309 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 89 89 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_89_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (2859481 / 2778889 : ℚ)
        + (12903309 / 1667 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 89 89 N := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (744067056 : ℚ) / 1667 := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (2859481 / 2778889 : ℚ)
                =
              (5001 : ℚ) * (2859481 / 2778889 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst, sum_ramanujanGcdClassIndicatorRat_eightyNine_eightyNine_X0]
          norm_num

theorem surrogateDiagonalTailTerm89_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 89
      = (1162604775 : ℚ) / 6248076032 := by
  have hsqfree : Squarefree 89 := by native_decide
  have hphi89 : Nat.totient 89 = 88 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_89_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi89]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part009_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part009 := by
  simp [tailChunk000Sub000Part009SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part009,
    surrogateDiagonalTailTerm89_X0_eq_cert]

private theorem gcd_odd_two_mul_eq
    {n k : ℕ} (hnOdd : Odd n) :
    Nat.gcd n (2 * k) = Nat.gcd n k := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  have h := Nat.Coprime.gcd_mul_left_cancel (k := 2) (m := k) (n := n) hcop
  simpa [Nat.gcd_comm, Nat.mul_comm] using h

private theorem totient_two_mul_eq_of_odd
    {n : ℕ} (hnOdd : Odd n) :
    Nat.totient (2 * n) = Nat.totient n := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  rw [Nat.totient_mul hcop]
  norm_num

private theorem ramanujanR_two_mul_eq_of_isEven_of_odd
    {n N : ℕ} (hnOdd : Odd n) (hNEven : Goldbach.Windows.IsEven N) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N := by
  have hnpos : 0 < n := hnOdd.pos
  rcases (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hNEven) with ⟨k, hk⟩
  subst hk
  set d : ℕ := Nat.gcd n k
  have hgcdn : Nat.gcd n (2 * k) = d := by
    simpa [d] using gcd_odd_two_mul_eq (n := n) (k := k) hnOdd
  have hgcd2n : Nat.gcd (2 * n) (2 * k) = 2 * d := by
    simpa [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.gcd_mul_left 2 n k)
  have hdvd : d ∣ n := by
    simpa [d] using Nat.gcd_dvd_left n k
  have hdpos : 0 < d := by
    simpa [d] using Nat.gcd_pos_of_pos_left k hnpos
  have hdOdd : Odd d := by
    have hnotEven : ¬ Even d := by
      intro hdEven
      rcases hdvd with ⟨m, hm⟩
      rcases hdEven with ⟨c, hc⟩
      have hnEven : Even n := by
        refine ⟨c * m, ?_⟩
        rw [hm, hc]
        ring
      exact (Nat.not_even_iff_odd.mpr hnOdd) hnEven
    exact Nat.not_even_iff_odd.mp hnotEven
  have hquot : (2 * n) / (2 * d) = n / d := by
    apply Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 * d)
    calc
      2 * n = 2 * ((n / d) * d) := by rw [Nat.div_mul_cancel hdvd]
      _ = (n / d) * (2 * d) := by ring
  have hphi : Nat.totient (2 * d) = Nat.totient d := totient_two_mul_eq_of_odd hdOdd
  rw [ramanujanR_eq_moebius_mul_totient_gcd, ramanujanR_eq_moebius_mul_totient_gcd]
  rw [hgcd2n, hgcdn, hquot, hphi]

private theorem ramanujanWindowAverage_two_mul_eq_of_odd
    {X n : ℕ} (hnOdd : Odd n) :
    ramanujanWindowAverage X (2 * n) = ramanujanWindowAverage X n := by
  unfold ramanujanWindowAverage
  refine congrArg ((((EvenIn X H).card : ℝ)⁻¹) * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact ramanujanR_two_mul_eq_of_isEven_of_odd hnOdd (isEven_of_mem_EvenIn_explicit hN)

private theorem centeredRamanujanObservable_two_mul_eq_of_odd
    {n N : ℕ} (hnOdd : Odd n) (hN : N ∈ EvenIn X0 H) :
    centeredRamanujanObservable X0 (2 * n) N
      = centeredRamanujanObservable X0 n N := by
  calc
    centeredRamanujanObservable X0 (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
          - ramanujanWindowAverage X0 n := by
            simp [centeredRamanujanObservable, ramanujanWindowAverage_two_mul_eq_of_odd hnOdd]
    _ = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N
          - ramanujanWindowAverage X0 n := by
            rw [ramanujanR_two_mul_eq_of_isEven_of_odd hnOdd (isEven_of_mem_EvenIn_explicit hN)]
    _ = centeredRamanujanObservable X0 n N := by
            rfl

private theorem centeredRamanujanWindowEnergyRat_two_mul_eq_of_odd
    {n : ℕ} (hnOdd : Odd n) :
    centeredRamanujanWindowEnergyRat X0 (2 * n)
      = centeredRamanujanWindowEnergyRat X0 n := by
  have hnle : 1 ≤ n := Nat.succ_le_of_lt hnOdd.pos
  have h2nle : 1 ≤ 2 * n := by omega
  have hreal :
      centeredRamanujanWindowEnergy X0 (2 * n)
        = centeredRamanujanWindowEnergy X0 n := by
    unfold centeredRamanujanWindowEnergy
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [centeredRamanujanObservable_two_mul_eq_of_odd hnOdd hN]
  have hcast :
      (centeredRamanujanWindowEnergyRat X0 (2 * n) : ℝ)
        = ((centeredRamanujanWindowEnergyRat X0 n : ℚ) : ℝ) := by
    rw [← centeredRamanujanWindowEnergy_eq_ratCast (X := X0) (q := 2 * n) h2nle]
    rw [hreal]
    rw [centeredRamanujanWindowEnergy_eq_ratCast (X := X0) (q := n) hnle]
  exact Rat.cast_inj.mp hcast

private theorem surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    {n : ℕ} (hnOdd : Odd n) (hsq2n : Squarefree (2 * n)) :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 (2 * n)
      = surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 n := by
  have hsqn : Squarefree n := by
    exact hsq2n.squarefree_of_dvd ⟨2, by ring⟩
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_two_mul_eq_of_odd hnOdd]
  unfold surrogateNormalizedSigmaTruncSummandCoeffRat
  simp [hsq2n, hsqn, totient_two_mul_eq_of_odd hnOdd]

def tailChunk000Sub000Part010SupportExplicit : Finset ℕ :=
  ([58] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part010 : ℚ :=
  (4365778175 : ℚ) / 768473664

def tailChunk000Sub000Part011SupportExplicit : Finset ℕ :=
  ([62] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part011 : ℚ :=
  (18721241 : ℚ) / 4050810

def tailChunk000Sub000Part012SupportExplicit : Finset ℕ :=
  ([66] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part012 : ℚ :=
  (50105507 : ℚ) / 3200640

def tailChunk000Sub000Part013SupportExplicit : Finset ℕ :=
  ([70] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part013 : ℚ :=
  (104257825 : ℚ) / 11522304

def tailChunk000Sub000Part014SupportExplicit : Finset ℕ :=
  ([74] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part014 : ℚ :=
  (138782375 : ℚ) / 51850368

def tailChunk000Sub000Part015SupportExplicit : Finset ℕ :=
  ([78] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part015 : ℚ :=
  (117180625 : ℚ) / 12962592

def tailChunk000Sub000Part016SupportExplicit : Finset ℕ :=
  ([82] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part016 : ℚ :=
  (500297539 : ℚ) / 256051200

def tailChunk000Sub000Part017SupportExplicit : Finset ℕ :=
  ([86] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part017 : ℚ :=
  (244576475 : ℚ) / 144088812

private theorem surrogateDiagonalTailTerm58_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 58
      = (4365778175 : ℚ) / 768473664 := by
  have hsqfree : Squarefree 58 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 29) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm29_X0_eq_cert

private theorem surrogateDiagonalTailTerm62_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 62
      = (18721241 : ℚ) / 4050810 := by
  have hsqfree : Squarefree 62 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 31) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm31_X0_eq_cert

private theorem surrogateDiagonalTailTerm66_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 66
      = (50105507 : ℚ) / 3200640 := by
  have hsqfree : Squarefree 66 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 33) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm33_X0_eq_cert

private theorem surrogateDiagonalTailTerm70_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 70
      = (104257825 : ℚ) / 11522304 := by
  have hsqfree : Squarefree 70 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 35) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm35_X0_eq_cert

private theorem surrogateDiagonalTailTerm74_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 74
      = (138782375 : ℚ) / 51850368 := by
  have hsqfree : Squarefree 74 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 37) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm37_X0_eq_cert

private theorem surrogateDiagonalTailTerm78_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 78
      = (117180625 : ℚ) / 12962592 := by
  have hsqfree : Squarefree 78 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 39) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm39_X0_eq_cert

private theorem surrogateDiagonalTailTerm82_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 82
      = (500297539 : ℚ) / 256051200 := by
  have hsqfree : Squarefree 82 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 41) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm41_X0_eq_cert

private theorem surrogateDiagonalTailTerm86_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 86
      = (244576475 : ℚ) / 144088812 := by
  have hsqfree : Squarefree 86 := by native_decide
  rw [surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    (n := 43) (by native_decide) hsqfree]
  exact surrogateDiagonalSmallRestTerm43_X0_eq_cert

theorem surrogateDiagonalTailChunk000Sub000Part010_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part010 := by
  simp [tailChunk000Sub000Part010SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part010,
    surrogateDiagonalTailTerm58_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part011_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part011 := by
  simp [tailChunk000Sub000Part011SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part011,
    surrogateDiagonalTailTerm62_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part012_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part012 := by
  simp [tailChunk000Sub000Part012SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part012,
    surrogateDiagonalTailTerm66_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part013_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part013 := by
  simp [tailChunk000Sub000Part013SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part013,
    surrogateDiagonalTailTerm70_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part014_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part014 := by
  simp [tailChunk000Sub000Part014SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part014,
    surrogateDiagonalTailTerm74_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part015_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part015 := by
  simp [tailChunk000Sub000Part015SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part015,
    surrogateDiagonalTailTerm78_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part016_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part016 := by
  simp [tailChunk000Sub000Part016SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part016,
    surrogateDiagonalTailTerm82_X0_eq_cert]

theorem surrogateDiagonalTailChunk000Sub000Part017_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part017 := by
  simp [tailChunk000Sub000Part017SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part017,
    surrogateDiagonalTailTerm86_X0_eq_cert]

def tailChunk000Sub000Part018SupportExplicit : Finset ℕ :=
  ([55] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part018 : ℚ :=
  (50059009 / 25605120 : ℚ)

private theorem sum_ramanujanGcdClassIndicatorRat_q55_5_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 55 5 N) = 910 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q55_11_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 55 11 N) = 364 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q55_55_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 55 55 N) = 91 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_q55_1_X0 :
    ramanujanGcdClassWindowAverageRat X0 55 1 = (1212 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 55 N = 1)).card : ℚ) = 3636 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassWindowAverageRat_q55_5_X0 :
    ramanujanGcdClassWindowAverageRat X0 55 5 = (910 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 55 N = 5)).card : ℚ) = 910 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_q55_11_X0 :
    ramanujanGcdClassWindowAverageRat X0 55 11 = (364 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 55 N = 11)).card : ℚ) = 364 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_q55_55_X0 :
    ramanujanGcdClassWindowAverageRat X0 55 55 = (91 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 55 N = 55)).card : ℚ) = 91 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_q55_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 55 1 N
      + ramanujanGcdClassIndicatorRat 55 5 N
      + ramanujanGcdClassIndicatorRat 55 11 N
      + ramanujanGcdClassIndicatorRat 55 55 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h55 : Nat.gcd 55 N = 55
  · simp [h55]
  · by_cases h11 : Nat.gcd 55 N = 11
    · simp [h55, h11]
    · by_cases h5 : Nat.gcd 55 N = 5
      · simp [h55, h11, h5]
      · have hdivs : (55 : ℕ).divisors = ({1, 5, 11, 55} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 55 N ∈ ({1, 5, 11, 55} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 55 N, by norm_num⟩
        have h1 : Nat.gcd 55 N = 1 := by
          simpa [h55, h11, h5] using hmem
        simp [h55, h11, h5, h1]

private theorem centeredRamanujanObservableRat_X0_q55_eq_indicator
    (N : ℕ) :
    centeredRamanujanObservableRat X0 55 N
      = (5005 / 5001 : ℚ)
          - 5 * ramanujanGcdClassIndicatorRat 55 5 N
          - 11 * ramanujanGcdClassIndicatorRat 55 11 N
          + 39 * ramanujanGcdClassIndicatorRat 55 55 N := by
  have hdivs : (55 : ℕ).divisors = ({1, 5, 11, 55} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 55 1 = 1 := by native_decide
  have hcoeff5 : ramanujanGcdClassCoeffRat 55 5 = -4 := by native_decide
  have hcoeff11 : ramanujanGcdClassCoeffRat 55 11 = -10 := by native_decide
  have hcoeff55 : ramanujanGcdClassCoeffRat 55 55 = 40 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff5, hcoeff11, hcoeff55,
    ramanujanGcdClassWindowAverageRat_q55_1_X0,
    ramanujanGcdClassWindowAverageRat_q55_5_X0,
    ramanujanGcdClassWindowAverageRat_q55_11_X0,
    ramanujanGcdClassWindowAverageRat_q55_55_X0]
  linarith [ramanujanGcdClassIndicatorRat_q55_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_q55_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 55 N) ^ 2
      = (25050025 / 25010001 : ℚ)
      + (74975 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 55 5 N
      + (495011 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 55 11 N
      + (2665637 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 55 55 N := by
  rw [centeredRamanujanObservableRat_X0_q55_eq_indicator]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h55 : Nat.gcd 55 N = 55
  · simp [h55]
    norm_num
  · by_cases h11 : Nat.gcd 55 N = 11
    · simp [h55, h11]
      norm_num
    · by_cases h5 : Nat.gcd 55 N = 5
      · simp [h55, h11, h5]
        norm_num
      · have hdivs : (55 : ℕ).divisors = ({1, 5, 11, 55} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 55 N ∈ ({1, 5, 11, 55} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 55 N, by norm_num⟩
        have h1 : Nat.gcd 55 N = 1 := by
          simpa [h55, h11, h5] using hmem
        simp [h55, h11, h5, h1]
        norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_q55_eq_cert :
    centeredRamanujanWindowEnergyRat X0 55 = (1001180180 / 5001 : ℚ) := by
  calc
    centeredRamanujanWindowEnergyRat X0 55
        =
      ∑ N ∈ EvenIn X0 H,
        ((25050025 / 25010001 : ℚ)
          + (74975 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 55 5 N
          + (495011 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 55 11 N
          + (2665637 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 55 55 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_q55_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (25050025 / 25010001 : ℚ)
        + (74975 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 55 5 N
        + (495011 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 55 11 N
        + (2665637 / 1667 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 55 55 N := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = (1001180180 / 5001 : ℚ) := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (25050025 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (25050025 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst,
            sum_ramanujanGcdClassIndicatorRat_q55_5_X0,
            sum_ramanujanGcdClassIndicatorRat_q55_11_X0,
            sum_ramanujanGcdClassIndicatorRat_q55_55_X0]
          norm_num

private theorem surrogateDiagonalTailTerm55_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 55
      = (50059009 / 25605120 : ℚ) := by
  have hsqfree : Squarefree 55 := by native_decide
  have hphi : Nat.totient 55 = 40 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_q55_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part018_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part018 := by
  simp [tailChunk000Sub000Part018SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part018,
    surrogateDiagonalTailTerm55_X0_eq_cert]

def tailChunk000Sub000Part019SupportExplicit : Finset ℕ :=
  ([57] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part019 : ℚ :=
  (11266185775 / 4199879808 : ℚ)

private theorem sum_ramanujanGcdClassIndicatorRat_q57_3_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 57 3 N) = 1579 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q57_19_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 57 19 N) = 175 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q57_57_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 57 57 N) = 88 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_q57_1_X0 :
    ramanujanGcdClassWindowAverageRat X0 57 1 = (1053 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 57 N = 1)).card : ℚ) = 3159 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassWindowAverageRat_q57_3_X0 :
    ramanujanGcdClassWindowAverageRat X0 57 3 = (1579 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 57 N = 3)).card : ℚ) = 1579 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_q57_19_X0 :
    ramanujanGcdClassWindowAverageRat X0 57 19 = (175 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 57 N = 19)).card : ℚ) = 175 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_q57_57_X0 :
    ramanujanGcdClassWindowAverageRat X0 57 57 = (88 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 57 N = 57)).card : ℚ) = 88 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_q57_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 57 1 N
      + ramanujanGcdClassIndicatorRat 57 3 N
      + ramanujanGcdClassIndicatorRat 57 19 N
      + ramanujanGcdClassIndicatorRat 57 57 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h57 : Nat.gcd 57 N = 57
  · simp [h57]
  · by_cases h19 : Nat.gcd 57 N = 19
    · simp [h57, h19]
    · by_cases h3 : Nat.gcd 57 N = 3
      · simp [h57, h19, h3]
      · have hdivs : (57 : ℕ).divisors = ({1, 3, 19, 57} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 57 N ∈ ({1, 3, 19, 57} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 57 N, by norm_num⟩
        have h1 : Nat.gcd 57 N = 1 := by
          simpa [h57, h19, h3] using hmem
        simp [h57, h19, h3, h1]

private theorem centeredRamanujanObservableRat_X0_q57_eq_indicator
    (N : ℕ) :
    centeredRamanujanObservableRat X0 57 N
      = (4982 / 5001 : ℚ)
          - 3 * ramanujanGcdClassIndicatorRat 57 3 N
          - 19 * ramanujanGcdClassIndicatorRat 57 19 N
          + 35 * ramanujanGcdClassIndicatorRat 57 57 N := by
  have hdivs : (57 : ℕ).divisors = ({1, 3, 19, 57} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 57 1 = 1 := by native_decide
  have hcoeff3 : ramanujanGcdClassCoeffRat 57 3 = -2 := by native_decide
  have hcoeff19 : ramanujanGcdClassCoeffRat 57 19 = -18 := by native_decide
  have hcoeff57 : ramanujanGcdClassCoeffRat 57 57 = 36 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff3, hcoeff19, hcoeff57,
    ramanujanGcdClassWindowAverageRat_q57_1_X0,
    ramanujanGcdClassWindowAverageRat_q57_3_X0,
    ramanujanGcdClassWindowAverageRat_q57_19_X0,
    ramanujanGcdClassWindowAverageRat_q57_57_X0]
  linarith [ramanujanGcdClassIndicatorRat_q57_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_q57_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 57 N) ^ 2
      = (24820324 / 25010001 : ℚ)
      + (5039 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 57 3 N
      + (1616045 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 57 19 N
      + (6474965 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 57 57 N := by
  rw [centeredRamanujanObservableRat_X0_q57_eq_indicator]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h57 : Nat.gcd 57 N = 57
  · simp [h57]
    norm_num
  · by_cases h19 : Nat.gcd 57 N = 19
    · simp [h57, h19]
      norm_num
    · by_cases h3 : Nat.gcd 57 N = 3
      · simp [h57, h19, h3]
        norm_num
      · have hdivs : (57 : ℕ).divisors = ({1, 3, 19, 57} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 57 N ∈ ({1, 3, 19, 57} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 57 N, by norm_num⟩
        have h1 : Nat.gcd 57 N = 1 := by
          simpa [h57, h19, h3] using hmem
        simp [h57, h19, h3, h1]
        norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_q57_eq_cert :
    centeredRamanujanWindowEnergyRat X0 57 = (901294862 / 5001 : ℚ) := by
  calc
    centeredRamanujanWindowEnergyRat X0 57
        =
      ∑ N ∈ EvenIn X0 H,
        ((24820324 / 25010001 : ℚ)
          + (5039 / 1667 : ℚ) * ramanujanGcdClassIndicatorRat 57 3 N
          + (1616045 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 57 19 N
          + (6474965 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 57 57 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_q57_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (24820324 / 25010001 : ℚ)
        + (5039 / 1667 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 57 3 N
        + (1616045 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 57 19 N
        + (6474965 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 57 57 N := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = (901294862 / 5001 : ℚ) := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (24820324 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (24820324 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst,
            sum_ramanujanGcdClassIndicatorRat_q57_3_X0,
            sum_ramanujanGcdClassIndicatorRat_q57_19_X0,
            sum_ramanujanGcdClassIndicatorRat_q57_57_X0]
          norm_num

private theorem surrogateDiagonalTailTerm57_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 57
      = (11266185775 / 4199879808 : ℚ) := by
  have hsqfree : Squarefree 57 := by native_decide
  have hphi : Nat.totient 57 = 36 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_q57_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part019_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part019 := by
  simp [tailChunk000Sub000Part019SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part019,
    surrogateDiagonalTailTerm57_X0_eq_cert]

def tailChunk000Sub000Part020SupportExplicit : Finset ℕ :=
  ([65] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part020 : ℚ :=
  (7508876375 / 6636847104 : ℚ)

private theorem sum_ramanujanGcdClassIndicatorRat_q65_5_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 65 5 N) = 924 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q65_13_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 65 13 N) = 308 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q65_65_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 65 65 N) = 77 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_q65_1_X0 :
    ramanujanGcdClassWindowAverageRat X0 65 1 = (3692 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 65 N = 1)).card : ℚ) = 3692 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_q65_5_X0 :
    ramanujanGcdClassWindowAverageRat X0 65 5 = (308 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 65 N = 5)).card : ℚ) = 924 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassWindowAverageRat_q65_13_X0 :
    ramanujanGcdClassWindowAverageRat X0 65 13 = (308 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 65 N = 13)).card : ℚ) = 308 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassWindowAverageRat_q65_65_X0 :
    ramanujanGcdClassWindowAverageRat X0 65 65 = (77 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 65 N = 65)).card : ℚ) = 77 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]

private theorem ramanujanGcdClassIndicatorRat_q65_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 65 1 N
      + ramanujanGcdClassIndicatorRat 65 5 N
      + ramanujanGcdClassIndicatorRat 65 13 N
      + ramanujanGcdClassIndicatorRat 65 65 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h65 : Nat.gcd 65 N = 65
  · simp [h65]
  · by_cases h13 : Nat.gcd 65 N = 13
    · simp [h65, h13]
    · by_cases h5 : Nat.gcd 65 N = 5
      · simp [h65, h13, h5]
      · have hdivs : (65 : ℕ).divisors = ({1, 5, 13, 65} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 65 N ∈ ({1, 5, 13, 65} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 65 N, by norm_num⟩
        have h1 : Nat.gcd 65 N = 1 := by
          simpa [h65, h13, h5] using hmem
        simp [h65, h13, h5, h1]

private theorem centeredRamanujanObservableRat_X0_q65_eq_indicator
    (N : ℕ) :
    centeredRamanujanObservableRat X0 65 N
      = (5005 / 5001 : ℚ)
          - 5 * ramanujanGcdClassIndicatorRat 65 5 N
          - 13 * ramanujanGcdClassIndicatorRat 65 13 N
          + 47 * ramanujanGcdClassIndicatorRat 65 65 N := by
  have hdivs : (65 : ℕ).divisors = ({1, 5, 13, 65} : Finset ℕ) := by native_decide
  have hcoeff1 : ramanujanGcdClassCoeffRat 65 1 = 1 := by native_decide
  have hcoeff5 : ramanujanGcdClassCoeffRat 65 5 = -4 := by native_decide
  have hcoeff13 : ramanujanGcdClassCoeffRat 65 13 = -12 := by native_decide
  have hcoeff65 : ramanujanGcdClassCoeffRat 65 65 = 48 := by native_decide
  unfold centeredRamanujanObservableRat centeredRamanujanGcdClassObservableRat
  rw [hdivs]
  simp [hcoeff1, hcoeff5, hcoeff13, hcoeff65,
    ramanujanGcdClassWindowAverageRat_q65_1_X0,
    ramanujanGcdClassWindowAverageRat_q65_5_X0,
    ramanujanGcdClassWindowAverageRat_q65_13_X0,
    ramanujanGcdClassWindowAverageRat_q65_65_X0]
  linarith [ramanujanGcdClassIndicatorRat_q65_sum_eq_one N]

private theorem centeredRamanujanObservableRat_X0_q65_sq
    (N : ℕ) :
    (centeredRamanujanObservableRat X0 65 N) ^ 2
      = (25050025 / 25010001 : ℚ)
      + (74975 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 65 5 N
      + (715039 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 65 13 N
      + (11517679 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 65 65 N := by
  rw [centeredRamanujanObservableRat_X0_q65_eq_indicator]
  unfold ramanujanGcdClassIndicatorRat
  by_cases h65 : Nat.gcd 65 N = 65
  · simp [h65]
    norm_num
  · by_cases h13 : Nat.gcd 65 N = 13
    · simp [h65, h13]
      norm_num
    · by_cases h5 : Nat.gcd 65 N = 5
      · simp [h65, h13, h5]
        norm_num
      · have hdivs : (65 : ℕ).divisors = ({1, 5, 13, 65} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 65 N ∈ ({1, 5, 13, 65} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 65 N, by norm_num⟩
        have h1 : Nat.gcd 65 N = 1 := by
          simpa [h65, h13, h5] using hmem
        simp [h65, h13, h5, h1]
        norm_num

private theorem centeredRamanujanWindowEnergyRat_X0_q65_eq_cert :
    centeredRamanujanWindowEnergyRat X0 65 = (1201420220 / 5001 : ℚ) := by
  calc
    centeredRamanujanWindowEnergyRat X0 65
        =
      ∑ N ∈ EvenIn X0 H,
        ((25050025 / 25010001 : ℚ)
          + (74975 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 65 5 N
          + (715039 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 65 13 N
          + (11517679 / 5001 : ℚ) * ramanujanGcdClassIndicatorRat 65 65 N) := by
            unfold centeredRamanujanWindowEnergyRat
            refine Finset.sum_congr rfl ?_
            intro N hN
            exact centeredRamanujanObservableRat_X0_q65_sq N
    _ =
      ∑ N ∈ EvenIn X0 H, (25050025 / 25010001 : ℚ)
        + (74975 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 65 5 N
        + (715039 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 65 13 N
        + (11517679 / 5001 : ℚ) * ∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 65 65 N := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = (1201420220 / 5001 : ℚ) := by
          have hconst :
              ∑ N ∈ EvenIn X0 H, (25050025 / 25010001 : ℚ)
                =
              (5001 : ℚ) * (25050025 / 25010001 : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, evenIn_X0_H_card_eq_5001_explicit]
          rw [hconst,
            sum_ramanujanGcdClassIndicatorRat_q65_5_X0,
            sum_ramanujanGcdClassIndicatorRat_q65_13_X0,
            sum_ramanujanGcdClassIndicatorRat_q65_65_X0]
          norm_num

private theorem surrogateDiagonalTailTerm65_X0_eq_cert :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 65
      = (7508876375 / 6636847104 : ℚ) := by
  have hsqfree : Squarefree 65 := by native_decide
  have hphi : Nat.totient 65 = 48 := by native_decide
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_X0_q65_eq_cert]
  simp [surrogateNormalizedSigmaTruncSummandCoeffRat, hsqfree, hphi]
  norm_num

theorem surrogateDiagonalTailChunk000Sub000Part020_eq_cert_explicit :
    (∑ q ∈ tailChunk000Sub000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Part020 := by
  simp [tailChunk000Sub000Part020SupportExplicit,
    surrogateDiagTailX0RatChunk000Sub000Part020,
    surrogateDiagonalTailTerm65_X0_eq_cert]

def tailChunk000Sub000Part021SupportExplicit : Finset ℕ :=
  ([69] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Part021 : ℚ :=
  (6849522575 / 4686057024 : ℚ)

private theorem sum_ramanujanGcdClassIndicatorRat_q69_3_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 69 3 N) = 1595 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q69_23_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 69 23 N) = 145 := by
  native_decide

private theorem sum_ramanujanGcdClassIndicatorRat_q69_69_X0 :
    (∑ N ∈ EvenIn X0 H, ramanujanGcdClassIndicatorRat 69 69 N) = 72 := by
  native_decide

private theorem ramanujanGcdClassWindowAverageRat_q69_1_X0 :
    ramanujanGcdClassWindowAverageRat X0 69 1 = (1063 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 69 N = 1)).card : ℚ) = 3189 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassWindowAverageRat_q69_3_X0 :
    ramanujanGcdClassWindowAverageRat X0 69 3 = (1595 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 69 N = 3)).card : ℚ) = 1595 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassWindowAverageRat_q69_23_X0 :
    ramanujanGcdClassWindowAverageRat X0 69 23 = (145 / 5001 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 69 N = 23)).card : ℚ) = 145 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassWindowAverageRat_q69_69_X0 :
    ramanujanGcdClassWindowAverageRat X0 69 69 = (24 / 1667 : ℚ) := by
  have hcount :
      (((EvenIn X0 H).filter (fun N => Nat.gcd 69 N = 69)).card : ℚ) = 72 := by
    native_decide
  unfold ramanujanGcdClassWindowAverageRat
  rw [evenIn_X0_H_card_eq_5001_explicit, hcount]
  norm_num

private theorem ramanujanGcdClassIndicatorRat_q69_sum_eq_one
    (N : ℕ) :
    ramanujanGcdClassIndicatorRat 69 1 N
      + ramanujanGcdClassIndicatorRat 69 3 N
      + ramanujanGcdClassIndicatorRat 69 23 N
      + ramanujanGcdClassIndicatorRat 69 69 N = 1 := by
  unfold ramanujanGcdClassIndicatorRat
  by_cases h69 : Nat.gcd 69 N = 69
  · simp [h69]
  · by_cases h23 : Nat.gcd 69 N = 23
    · simp [h69, h23]
    · by_cases h3 : Nat.gcd 69 N = 3
      · simp [h69, h23, h3]
      · have hdivs : (69 : ℕ).divisors = ({1, 3, 23, 69} : Finset ℕ) := by native_decide
        have hmem : Nat.gcd 69 N ∈ ({1, 3, 23, 69} : Finset ℕ) := by
          rw [← hdivs]
          exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left 69 N, by norm_num⟩
        have h1 : Nat.gcd 69 N = 1 := by
          simpa [h69, h23, h3] using hmem
        simp [h69, h23, h3, h1]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
