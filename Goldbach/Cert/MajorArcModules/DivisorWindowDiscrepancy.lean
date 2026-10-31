import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
Generic finite-divisor discrepancy lemmas for the proposed uniform truncation proof.

This module contains no numerical certificate and makes no claim about the canonical
Ramanujan truncation until its divisor expansion, density identity and interval-count
bound have been supplied. It is intentionally independent of the Route A envelope.
-/

open scoped BigOperators

namespace Goldbach.Cert.DivisorWindowDiscrepancy

/-- A diagonal moment kernel collapses a weighted double sum. -/
theorem weighted_orthogonal_kernel_sum
    {κ : Type*} [DecidableEq κ] (R : Finset κ)
    (b diagonal : κ → ℝ) (K : κ → κ → ℝ)
    (hdiagonal : ∀ r ∈ R, ∀ t ∈ R,
      K r t = if r = t then diagonal r else 0) :
    (∑ r ∈ R, ∑ t ∈ R, (b r * b t) * K r t)
      = ∑ r ∈ R, (b r) ^ 2 * diagonal r := by
  classical
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single r]
  · rw [hdiagonal r hr r hr]
    simp [pow_two]
  · intro t ht htr
    rw [hdiagonal r hr t ht]
    simp [Ne.symm htr]
  · intro hr'
    exact False.elim (hr' hr)

/-- Exact second moment of a finite orthogonal family. -/
theorem weighted_square_sum_of_orthogonal
    {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (R : Finset κ)
    (b diagonal : κ → ℝ) (u : κ → ι → ℝ)
    (horthogonal : ∀ r ∈ R, ∀ t ∈ R,
      (∑ n ∈ s, u r n * u t n) = if r = t then diagonal r else 0) :
    (∑ n ∈ s, (∑ r ∈ R, b r * u r n) ^ 2)
      = ∑ r ∈ R, (b r) ^ 2 * diagonal r := by
  classical
  calc
    (∑ n ∈ s, (∑ r ∈ R, b r * u r n) ^ 2)
        = ∑ n ∈ s, ∑ r ∈ R, ∑ t ∈ R,
            (b r * b t) * (u r n * u t n) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [pow_two, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
    _ = ∑ r ∈ R, ∑ t ∈ R,
          (b r * b t) * (∑ n ∈ s, u r n * u t n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
    _ = ∑ r ∈ R, (b r) ^ 2 * diagonal r :=
      weighted_orthogonal_kernel_sum R b diagonal (fun r t => ∑ n ∈ s, u r n * u t n)
        horthogonal

/-- Exact finite variance decomposition around any reference value. -/
theorem sum_sq_sub_eq_centered_add
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) (μ c : ℝ)
    (hmean : (∑ n ∈ s, f n) = (s.card : ℝ) * μ) :
    (∑ n ∈ s, (f n - c) ^ 2)
      = (∑ n ∈ s, (f n - μ) ^ 2) + (s.card : ℝ) * (μ - c) ^ 2 := by
  have hzero : (∑ n ∈ s, (f n - μ)) = 0 := by
    rw [Finset.sum_sub_distrib, hmean]
    simp [nsmul_eq_mul]
  calc
    (∑ n ∈ s, (f n - c) ^ 2)
        = ∑ n ∈ s, ((f n - μ) ^ 2
            + (2 * (μ - c)) * (f n - μ) + (μ - c) ^ 2) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
    _ = (∑ n ∈ s, (f n - μ) ^ 2) + (s.card : ℝ) * (μ - c) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hzero]
      simp [nsmul_eq_mul]

/-- Centering at the actual window mean minimizes its squared energy. -/
theorem centered_energy_le_reference
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) (μ c : ℝ)
    (hmean : (∑ n ∈ s, f n) = (s.card : ℝ) * μ) :
    (∑ n ∈ s, (f n - μ) ^ 2) ≤ ∑ n ∈ s, (f n - c) ^ 2 := by
  rw [sum_sq_sub_eq_centered_add s f μ c hmean]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Divisibility count in an arbitrary finite set. -/
def divisorCount (s : Finset ℕ) (d : ℕ) : ℕ :=
  (s.filter fun n => d ∣ n).card

/-- Exact multiple count in a positive half-open integer interval. -/
theorem divisorCount_Ioc_add (A m d : ℕ) :
    A / d + divisorCount (Finset.Ioc A (A + m)) d = (A + m) / d := by
  classical
  have hdisjoint :
      Disjoint ((Finset.Ioc 0 A).filter fun n => d ∣ n)
        ((Finset.Ioc A (A + m)).filter fun n => d ∣ n) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hnle := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    have hnlt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn').1).1
    omega
  have hunion :
      ((Finset.Ioc 0 A).filter fun n => d ∣ n)
        ∪ ((Finset.Ioc A (A + m)).filter fun n => d ∣ n)
      = (Finset.Ioc 0 (A + m)).filter fun n => d ∣ n := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hc := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hc
  simpa only [Nat.Ioc_filter_dvd_card_eq_div, divisorCount] using hc.symm

/-- Divisibility has discrepancy at most one in every positive integer window. -/
theorem abs_divisorCount_Ioc_sub_density_le_one
    (A m d : ℕ) (hd : 0 < d) :
    |(divisorCount (Finset.Ioc A (A + m)) d : ℝ) - (m : ℝ) / d| ≤ 1 := by
  have hc := divisorCount_Ioc_add A m d
  have hcmul := congrArg (fun k : ℕ => d * k) hc
  have heq :
      d * divisorCount (Finset.Ioc A (A + m)) d + (A + m) % d = m + A % d := by
    nlinarith [Nat.mod_add_div A d, Nat.mod_add_div (A + m) d]
  have heqR :
      (d : ℝ) * (divisorCount (Finset.Ioc A (A + m)) d : ℝ)
        + ((A + m) % d : ℕ) = (m : ℝ) + (A % d : ℕ) := by
    exact_mod_cast heq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hra : ((A % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt A hd
  have hrb : (((A + m) % d : ℕ) : ℝ) < d := by
    exact_mod_cast Nat.mod_lt (A + m) hd
  have hra0 : (0 : ℝ) ≤ (A % d : ℕ) := Nat.cast_nonneg _
  have hrb0 : (0 : ℝ) ≤ ((A + m) % d : ℕ) := Nat.cast_nonneg _
  have hidentity :
      (divisorCount (Finset.Ioc A (A + m)) d : ℝ) - (m : ℝ) / d
        = ((A % d : ℕ) - (((A + m) % d : ℕ) : ℝ)) / d := by
    field_simp [ne_of_gt hdR]
    nlinarith
  rw [hidentity, abs_le]
  constructor
  · apply (le_div_iff₀ hdR).2
    nlinarith
  · apply (div_le_iff₀ hdR).2
    nlinarith

/-- Swap a divisor expansion with the finite window sum. -/
theorem sum_divisor_expansion
    (s D : Finset ℕ) (C : ℕ → ℝ) :
    (∑ n ∈ s, ∑ d ∈ D, if d ∣ n then C d else 0)
      = ∑ d ∈ D, C d * (divisorCount s d : ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp [divisorCount, nsmul_eq_mul, mul_comm]

/-- Exact separation of the mean density and the residue-count discrepancies. -/
theorem sum_divisor_expansion_sub_density
    (s D : Finset ℕ) (C : ℕ → ℝ) :
    (∑ n ∈ s, ∑ d ∈ D, if d ∣ n then C d else 0)
        - (s.card : ℝ) * (∑ d ∈ D, C d / (d : ℝ))
      = ∑ d ∈ D, C d * ((divisorCount s d : ℝ) - (s.card : ℝ) / d) := by
  rw [sum_divisor_expansion, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- A unit discrepancy for each divisor costs at most the coefficient `ℓ¹` norm. -/
theorem sum_divisor_expansion_le_density_add_l1
    (s D : Finset ℕ) (C : ℕ → ℝ)
    (hcount : ∀ d ∈ D,
      |(divisorCount s d : ℝ) - (s.card : ℝ) / d| ≤ 1) :
    (∑ n ∈ s, ∑ d ∈ D, if d ∣ n then C d else 0)
      ≤ (s.card : ℝ) * (∑ d ∈ D, C d / (d : ℝ)) + ∑ d ∈ D, |C d| := by
  have hterm : ∀ d ∈ D,
      C d * ((divisorCount s d : ℝ) - (s.card : ℝ) / d) ≤ |C d| := by
    intro d hd
    calc
      C d * ((divisorCount s d : ℝ) - (s.card : ℝ) / d)
          ≤ |C d * ((divisorCount s d : ℝ) - (s.card : ℝ) / d)| := le_abs_self _
      _ = |C d| * |(divisorCount s d : ℝ) - (s.card : ℝ) / d| := abs_mul _ _
      _ ≤ |C d| * 1 := mul_le_mul_of_nonneg_left (hcount d hd) (abs_nonneg _)
      _ = |C d| := mul_one _
  have hsum := Finset.sum_le_sum hterm
  rw [← sum_divisor_expansion_sub_density] at hsum
  linarith

/-- Structural endpoint: center, expand the reference square, and control residues. -/
theorem centered_energy_le_density_add_l1
    (s D : Finset ℕ) (f C : ℕ → ℝ) (μ c v : ℝ)
    (hmean : (∑ n ∈ s, f n) = (s.card : ℝ) * μ)
    (hexpand : ∀ n ∈ s,
      (f n - c) ^ 2 = ∑ d ∈ D, if d ∣ n then C d else 0)
    (hdensity : (∑ d ∈ D, C d / (d : ℝ)) = v)
    (hcount : ∀ d ∈ D,
      |(divisorCount s d : ℝ) - (s.card : ℝ) / d| ≤ 1) :
    (∑ n ∈ s, (f n - μ) ^ 2)
      ≤ (s.card : ℝ) * v + ∑ d ∈ D, |C d| := by
  calc
    (∑ n ∈ s, (f n - μ) ^ 2) ≤ ∑ n ∈ s, (f n - c) ^ 2 :=
      centered_energy_le_reference s f μ c hmean
    _ = ∑ n ∈ s, ∑ d ∈ D, if d ∣ n then C d else 0 :=
      Finset.sum_congr rfl hexpand
    _ ≤ (s.card : ℝ) * (∑ d ∈ D, C d / (d : ℝ)) + ∑ d ∈ D, |C d| :=
      sum_divisor_expansion_le_density_add_l1 s D C hcount
    _ = (s.card : ℝ) * v + ∑ d ∈ D, |C d| := by rw [hdensity]

/-- The coefficient `ℓ¹` norm can be checked using only its negative part. -/
theorem sum_abs_eq_sum_add_two_mul_negativePart
    {ι : Type*} (D : Finset ι) (C : ι → ℝ) :
    (∑ d ∈ D, |C d|)
      = (∑ d ∈ D, C d) + 2 * ∑ d ∈ D, max (-(C d)) 0 := by
  have hpoint : ∀ x : ℝ, |x| = x + 2 * max (-x) 0 := by
    intro x
    by_cases hx : x ≤ 0
    · rw [abs_of_nonpos hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
    · have hx' : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
      rw [abs_of_nonneg hx', max_eq_right (neg_nonpos.mpr hx')]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Nonnegative coefficients beyond the cutoff contribute no negative mass. -/
theorem negativePart_sum_eq_filter
    (D : Finset ℕ) (C : ℕ → ℝ) (Q : ℕ)
    (houtside : ∀ d ∈ D, Q < d → 0 ≤ C d) :
    (∑ d ∈ D, max (-(C d)) 0)
      = ∑ d ∈ D.filter (fun d => d ≤ Q), max (-(C d)) 0 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsmall : d ≤ Q
  · simp [hsmall]
  · have hpos := houtside d hd (Nat.lt_of_not_ge hsmall)
    simp [hsmall, max_eq_right (neg_nonpos.mpr hpos)]

/-- Small rational scalar bounds suffice for the desired coefficient estimate. -/
theorem sum_abs_lt_one_hundred_of_negativePart
    {ι : Type*} (D : Finset ι) (C : ι → ℝ) (g0 : ℝ)
    (htotal : (∑ d ∈ D, C d) = (g0 - 2) ^ 2)
    (hg0lo : 2 ≤ g0) (hg0hi : g0 ≤ (11642 : ℝ) / 1000)
    (hnegative : (∑ d ∈ D, max (-(C d)) 0) ≤ (7 : ℝ) / 2) :
    (∑ d ∈ D, |C d|) < 100 := by
  rw [sum_abs_eq_sum_add_two_mul_negativePart, htotal]
  have hproduct :
      0 ≤ ((11642 : ℝ) / 1000 - g0) * ((11642 : ℝ) / 1000 + g0 - 4) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Numerical endpoint after the raw variance and coefficient bounds are established. -/
theorem normalized_energy_lt_1795
    (E C2 : ℝ)
    (hE : E ≤ 5001 * ((301 : ℝ) / 500) + 100)
    (hC2 : (33 : ℝ) / 50 ≤ C2) :
    E / (2 * C2) ^ 2 < 1795 := by
  have hC2pos : 0 < C2 := by linarith
  have hdenpos : 0 < (2 * C2) ^ 2 := sq_pos_of_pos (by linarith)
  apply (div_lt_iff₀ hdenpos).2
  have hproduct : 0 ≤ (C2 - (33 : ℝ) / 50) * (C2 + (33 : ℝ) / 50) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

end Goldbach.Cert.DivisorWindowDiscrepancy
