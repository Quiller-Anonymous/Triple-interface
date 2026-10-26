import Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
import Mathlib.Tactic

/-!
Positivity of every divisor coefficient in the fixed Ramanujan truncation.

The sole numerical input is a single exact rational sum of reciprocal totient squares through
`30000`.  It is not a list of coefficient certificates.  A generic divisor argument then bounds
all negative contributions to any coefficient by less than its positive diagonal term.
-/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorPositivity

open scoped BigOperators ArithmeticFunction.Moebius
open Q0SigmaTruncScalarBounds

/-- The nonnegative majorant for an odd squarefree Möbius summand. -/
def reciprocalTotientSquareRat (k : ℕ) : ℚ :=
  if Odd k ∧ Squarefree k then 1 / (totientFast k : ℚ) ^ 2 else 0

/-- The mass away from `k = 1`; this is one scalar computation at the fixed cutoff. -/
def tailMassRat : ℚ :=
  ∑ k ∈ Finset.Icc 2 cutoff, reciprocalTotientSquareRat k

theorem tailMassRat_lt : tailMassRat < (7 : ℚ) / 8 := by
  native_decide

theorem reciprocalTotientSquareRat_nonneg (k : ℕ) :
    0 ≤ reciprocalTotientSquareRat k := by
  unfold reciprocalTotientSquareRat
  split_ifs <;> positivity

theorem evenMultiplicity_nonneg (r : ℕ) : 0 ≤ evenMultiplicity r := by
  unfold evenMultiplicity
  split_ifs <;> norm_num

theorem evenMultiplicity_antitone {d r : ℕ} (hdr : d ≤ r) :
    evenMultiplicity r ≤ evenMultiplicity d := by
  unfold evenMultiplicity
  split_ifs <;> norm_num at * <;> omega

theorem oddWeightRat_nonneg (r : ℕ) : 0 ≤ oddWeightRat r := by
  unfold oddWeightRat
  split_ifs
  · exact div_nonneg (evenMultiplicity_nonneg r) (sq_nonneg _)
  · norm_num

private theorem oddWeightRat_mul_le {d k : ℕ}
    (h : Odd (d * k) ∧ Squarefree (d * k)) :
    oddWeightRat (d * k) ≤ oddWeightRat d * reciprocalTotientSquareRat k := by
  have hd : Odd d ∧ Squarefree d := ⟨(Nat.odd_mul.mp h.1).1, h.2.of_mul_left⟩
  have hk : Odd k ∧ Squarefree k := ⟨(Nat.odd_mul.mp h.1).2, h.2.of_mul_right⟩
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk.2.ne_zero
  have hdk : d ≤ d * k := by nlinarith
  have hc : d.Coprime k := Nat.coprime_of_squarefree_mul h.2
  simp only [oddWeightRat, reciprocalTotientSquareRat, if_pos h, if_pos hd,
    if_pos hk, totientFast_eq, Nat.totient_mul hc, Nat.cast_mul]
  calc
    evenMultiplicity (d * k) / ((Nat.totient d : ℚ) * Nat.totient k) ^ 2
        ≤ evenMultiplicity d / ((Nat.totient d : ℚ) * Nat.totient k) ^ 2 :=
      div_le_div_of_nonneg_right (evenMultiplicity_antitone hdk) (sq_nonneg _)
    _ = evenMultiplicity d / (Nat.totient d : ℚ) ^ 2 *
          (1 / (Nat.totient k : ℚ) ^ 2) := by
      simp [div_eq_mul_inv, mul_pow, mul_comm, mul_left_comm, mul_assoc]

private theorem quotient_good {d r : ℕ} (hdr : d ∣ r)
    (hr : Odd r ∧ Squarefree r) :
    (Odd d ∧ Squarefree d) ∧ (Odd (r / d) ∧ Squarefree (r / d)) := by
  have hmul : d * (r / d) = r := Nat.mul_div_cancel' hdr
  rw [← hmul] at hr
  exact ⟨⟨(Nat.odd_mul.mp hr.1).1, hr.2.of_mul_left⟩,
    ⟨(Nat.odd_mul.mp hr.1).2, hr.2.of_mul_right⟩⟩

theorem divisorCoefficientRat_eq_zero_of_not_good {d : ℕ}
    (hd : ¬(Odd d ∧ Squarefree d)) : divisorCoefficientRat d = 0 := by
  unfold divisorCoefficientRat
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hdr : d ∣ r
  · by_cases hgood : Odd r ∧ Squarefree r
    · exact (hd (quotient_good hdr hgood).1).elim
    · simp [hdr, oddWeightRat, hgood]
  · simp [hdr]

/-- The positive `r=d` term dominates all negative quotient terms, uniformly in `d`. -/
theorem divisorCoefficientRat_nonneg (d : ℕ) (hdQ : d ≤ cutoff) :
    0 ≤ divisorCoefficientRat d := by
  classical
  by_cases hd : Odd d ∧ Squarefree d
  · have hd0 : d ≠ 0 := hd.2.ne_zero
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    let s : Finset ℕ := (Finset.Icc 1 cutoff).filter
      (fun r => d ∣ r ∧ Odd r ∧ Squarefree r)
    let A : ℚ := oddWeightRat d * d
    have hA : 0 ≤ A := mul_nonneg (oddWeightRat_nonneg d) (Nat.cast_nonneg d)
    have hdmem : d ∈ s := by simp [s, hd, hd1, hdQ]
    have hsum : divisorCoefficientRat d =
        ∑ r ∈ s, oddWeightRat r * d * (μ (r / d) : ℚ) := by
      rw [divisorCoefficientRat, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hdr : d ∣ r <;> by_cases hgood : Odd r ∧ Squarefree r <;>
        simp [hdr, hgood, oddWeightRat]
    have hqinj : Set.InjOn (fun r : ℕ => r / d) (↑(s.erase d) : Set ℕ) := by
      intro r hr u hu hru
      change r ∈ s.erase d at hr
      change u ∈ s.erase d at hu
      change r ∈ ((Finset.Icc 1 cutoff).filter
        (fun r => d ∣ r ∧ Odd r ∧ Squarefree r)).erase d at hr
      change u ∈ ((Finset.Icc 1 cutoff).filter
        (fun r => d ∣ r ∧ Odd r ∧ Squarefree r)).erase d at hu
      have hrdiv := (Finset.mem_filter.mp (Finset.mem_erase.mp hr).2).2.1
      have hudiv := (Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).2.1
      have hrmul := Nat.mul_div_cancel' hrdiv
      have humul := Nat.mul_div_cancel' hudiv
      change r / d = u / d at hru
      calc
        r = d * (r / d) := hrmul.symm
        _ = d * (u / d) := by rw [hru]
        _ = u := humul
    have hqsubset : (s.erase d).image (fun r => r / d) ⊆ Finset.Icc 2 cutoff := by
      intro k hk
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hrne, hrs⟩ := Finset.mem_erase.mp hr
      obtain ⟨hrIcc, hdr, hrgood⟩ := Finset.mem_filter.mp hrs
      have hqgood := (quotient_good hdr hrgood).2
      have hqpos : 0 < r / d := Nat.pos_of_ne_zero hqgood.2.ne_zero
      have hqne : r / d ≠ 1 := by
        intro hq
        have := Nat.mul_div_cancel' hdr
        simp only [hq, mul_one] at this
        exact hrne this.symm
      exact Finset.mem_Icc.mpr ⟨by omega,
        (Nat.div_le_self r d).trans (Finset.mem_Icc.mp hrIcc).2⟩
    have hmass : (∑ r ∈ s.erase d, reciprocalTotientSquareRat (r / d)) ≤ tailMassRat := by
      rw [← Finset.sum_image hqinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hqsubset
        (fun k _ _ => reciprocalTotientSquareRat_nonneg k)
    have hterm : ∀ r ∈ s.erase d,
        -(A * reciprocalTotientSquareRat (r / d)) ≤
          oddWeightRat r * d * (μ (r / d) : ℚ) := by
      intro r hr
      obtain ⟨hrIcc, hdr, hrgood⟩ := Finset.mem_filter.mp (Finset.mem_erase.mp hr).2
      have hmul : d * (r / d) = r := Nat.mul_div_cancel' hdr
      have hw := oddWeightRat_mul_le (d := d) (k := r / d) (by simpa [hmul] using hrgood)
      rw [hmul] at hw
      have hwd := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg d : (0 : ℚ) ≤ d)
      have hμ : -(1 : ℚ) ≤ (μ (r / d) : ℚ) := by
        exact_mod_cast (abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := r / d))).1
      have hprod := mul_le_mul_of_nonneg_left hμ
        (mul_nonneg (oddWeightRat_nonneg r) (Nat.cast_nonneg d))
      dsimp [A]
      nlinarith
    have hrest := Finset.sum_le_sum hterm
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum] at hrest
    have hmassA := mul_le_mul_of_nonneg_left hmass hA
    have htail := tailMassRat_lt
    rw [hsum, ← Finset.add_sum_erase _ _ hdmem]
    simp only [Nat.div_self (Nat.pos_of_ne_zero hd0)]
    norm_num only [ArithmeticFunction.moebius_apply_one, Int.cast_one, mul_one]
    change 0 ≤ A + _
    nlinarith
  · rw [divisorCoefficientRat_eq_zero_of_not_good hd]

theorem divisorCoefficientRat_cast_nonneg (d : ℕ) (hd : d ∈ Finset.Icc 1 cutoff) :
    0 ≤ (divisorCoefficientRat d : ℝ) := by
  exact_mod_cast divisorCoefficientRat_nonneg d (Finset.mem_Icc.mp hd).2

end Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorPositivity
