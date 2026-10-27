import Goldbach.Cert.MajorArcModules.RouteASignedMoebiusTotientKernel
import Mathlib.Analysis.PSeries

/-!
# A finite Euler-product bound for the signed conductor kernel

This module proves the universal finite-prime product estimate needed by the elementary
Mobius/totient prefix bound.  It is deliberately finite: no infinite Euler product or analytic
continuation is used.
-/

namespace Goldbach.Cert.MajorArcModules.RouteASignedMoebiusEulerProduct

open scoped BigOperators
open Goldbach.Cert.MajorArcModules.RouteASignedMoebiusTotientKernel

noncomputable section

/-- The absolute local Euler factor at a prime not dividing the fixed conductor. -/
noncomputable def signedMoebiusTotientPrimeEulerFactor (p : ℕ) : ℝ :=
  1 + 1 / (((p - 1 : ℕ) : ℝ) ^ 2)

theorem signedMoebiusTotientPrimeEulerFactor_one_le (p : ℕ) :
    1 ≤ signedMoebiusTotientPrimeEulerFactor p := by
  unfold signedMoebiusTotientPrimeEulerFactor
  have h : 0 ≤ 1 / (((p - 1 : ℕ) : ℝ) ^ 2) := by positivity
  linarith

private theorem one_le_real_prod
    {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, 1 ≤ f j := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hprod := ih hfs
      nlinarith [mul_nonneg (sub_nonneg.mpr hfi) (sub_nonneg.mpr hprod)]

private theorem real_prod_le_prod_of_subset_of_one_le
    {ι : Type*} [DecidableEq ι] {s t : Finset ι} {f : ι → ℝ}
    (hst : s ⊆ t) (hf : ∀ i ∈ t, 1 ≤ f i) :
    (∏ i ∈ s, f i) ≤ ∏ i ∈ t, f i := by
  let extra := t \ s
  have hdisj : Disjoint extra s := Finset.sdiff_disjoint
  have hdecomp : extra ∪ s = t := Finset.sdiff_union_of_subset hst
  have hextra : 1 ≤ ∏ i ∈ extra, f i := by
    apply one_le_real_prod
    intro i hi
    exact hf i (Finset.mem_sdiff.mp hi).1
  have hsnonneg : 0 ≤ ∏ i ∈ s, f i := by
    exact le_trans (by norm_num) (one_le_real_prod fun i hi => hf i (hst hi))
  calc
    (∏ i ∈ s, f i) = 1 * ∏ i ∈ s, f i := by ring
    _ ≤ (∏ i ∈ extra, f i) * ∏ i ∈ s, f i :=
      mul_le_mul_of_nonneg_right hextra hsnonneg
    _ = ∏ i ∈ t, f i := by rw [← Finset.prod_union hdisj, hdecomp]

private theorem exp_seven_eighteenths_le :
    Real.exp (7 / 18 : ℝ) ≤ 18 / 11 := by
  have hpos : (0 : ℝ) < 1 - 7 / 18 := by norm_num
  have hlin : (1 - 7 / 18 : ℝ) ≤ Real.exp (-(7 / 18 : ℝ)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Real.add_one_le_exp (-(7 / 18 : ℝ)))
  have hinv :
      1 / Real.exp (-(7 / 18 : ℝ)) ≤ 1 / (1 - 7 / 18 : ℝ) :=
    one_div_le_one_div_of_le hpos hlin
  calc
    Real.exp (7 / 18 : ℝ) = 1 / Real.exp (-(7 / 18 : ℝ)) := by
      simp [Real.exp_neg]
    _ ≤ 1 / (1 - 7 / 18 : ℝ) := hinv
    _ = 18 / 11 := by norm_num

private theorem signedMoebiusTotientPrimeEulerFactor_le_exp_large
    {p : ℕ} (hp : 7 ≤ p) :
    signedMoebiusTotientPrimeEulerFactor p ≤
      Real.exp ((49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹)) := by
  have hpR : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < p := by positivity
  have hpm1Pos : (0 : ℝ) < p - 1 := by linarith
  have hratioNonneg : 0 ≤ (p : ℝ) / (p - 1) := by positivity
  have hratio : (p : ℝ) / (p - 1) ≤ 7 / 6 := by
    apply (div_le_iff₀ hpm1Pos).2
    nlinarith
  have hsq : ((p : ℝ) / (p - 1)) ^ 2 ≤ (7 / 6 : ℝ) ^ 2 :=
    (sq_le_sq₀ hratioNonneg (by norm_num : (0 : ℝ) ≤ 7 / 6)).2 hratio
  have hlocal :
      1 / (((p - 1 : ℕ) : ℝ) ^ 2) ≤
        (49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num only [Nat.cast_one]
    calc
      1 / ((p : ℝ) - 1) ^ 2 =
          ((p : ℝ) / (p - 1)) ^ 2 * (((p : ℝ) ^ 2)⁻¹) := by
            field_simp
      _ ≤ (7 / 6 : ℝ) ^ 2 * (((p : ℝ) ^ 2)⁻¹) := by
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹) := by norm_num
  calc
    signedMoebiusTotientPrimeEulerFactor p =
        1 / (((p - 1 : ℕ) : ℝ) ^ 2) + 1 := by
      simp [signedMoebiusTotientPrimeEulerFactor, add_comm]
    _ ≤ Real.exp (1 / (((p - 1 : ℕ) : ℝ) ^ 2)) :=
      Real.add_one_le_exp _
    _ ≤ Real.exp ((49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹)) :=
      Real.exp_le_exp.mpr hlocal

/-- Every finite product of the off-conductor local factors is at most six. -/
theorem signedMoebiusTotientPrimeEulerFactor_product_le_six
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, signedMoebiusTotientPrimeEulerFactor p) ≤ 6 := by
  classical
  let small : Finset ℕ := {2, 3, 5}
  let T : Finset ℕ := S ∪ small
  let large : Finset ℕ := T \ small
  have hST : S ⊆ T := Finset.subset_union_left
  have hprodST :
      (∏ p ∈ S, signedMoebiusTotientPrimeEulerFactor p) ≤
        ∏ p ∈ T, signedMoebiusTotientPrimeEulerFactor p :=
    real_prod_le_prod_of_subset_of_one_le hST fun p _hpT =>
      signedMoebiusTotientPrimeEulerFactor_one_le p
  have hsmallT : small ⊆ T := Finset.subset_union_right
  have hdisj : Disjoint large small := Finset.sdiff_disjoint
  have hdecomp : large ∪ small = T := Finset.sdiff_union_of_subset hsmallT
  have hsmallProd :
      (∏ p ∈ small, signedMoebiusTotientPrimeEulerFactor p) = (85 / 32 : ℝ) := by
    norm_num [small, signedMoebiusTotientPrimeEulerFactor]
  have hlargePrime : ∀ p ∈ large, p.Prime := by
    intro p hpL
    have hpT : p ∈ T := (Finset.mem_sdiff.mp hpL).1
    have hpNotSmall : p ∉ small := (Finset.mem_sdiff.mp hpL).2
    have hpS : p ∈ S := by
      rcases Finset.mem_union.mp hpT with hpS | hpSmall
      · exact hpS
      · exact False.elim (hpNotSmall hpSmall)
    exact hprime p hpS
  have hlargeSeven : ∀ p ∈ large, 7 ≤ p := by
    intro p hpL
    have hpPrime := hlargePrime p hpL
    have hpNotSmall : p ∉ small := (Finset.mem_sdiff.mp hpL).2
    have hpNe2 : p ≠ 2 := by
      intro h
      subst p
      exact hpNotSmall (by simp [small])
    have hpNe3 : p ≠ 3 := by
      intro h
      subst p
      exact hpNotSmall (by simp [small])
    have hpNe5 : p ≠ 5 := by
      intro h
      subst p
      exact hpNotSmall (by simp [small])
    have hpNe4 : p ≠ 4 := by
      intro h
      subst p
      norm_num at hpPrime
    have hpNe6 : p ≠ 6 := by
      intro h
      subst p
      norm_num at hpPrime
    have hpTwo : 2 ≤ p := hpPrime.two_le
    omega
  have hlargeSum :
      (∑ p ∈ large, (49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹)) ≤ 7 / 18 := by
    by_cases hlarge : large = ∅
    · rw [hlarge]
      norm_num
    · have hTNonempty : T.Nonempty := by
        exact ⟨2, Finset.mem_union_right S (by simp [small])⟩
      let N := T.max' hTNonempty + 1
      have hsubset : large ⊆ Finset.Ioo 6 N := by
        intro p hpL
        have hpT : p ∈ T := (Finset.mem_sdiff.mp hpL).1
        have hpMax : p ≤ T.max' hTNonempty := Finset.le_max' T p hpT
        have hpSeven := hlargeSeven p hpL
        refine Finset.mem_Ioo.mpr ⟨by omega, ?_⟩
        change p < T.max' hTNonempty + 1
        exact Nat.lt_succ_of_le hpMax
      have hsquares :
          (∑ p ∈ large, (((p : ℝ) ^ 2)⁻¹)) ≤ 2 / 7 := by
        calc
          (∑ p ∈ large, (((p : ℝ) ^ 2)⁻¹)) ≤
              ∑ p ∈ Finset.Ioo 6 N, (((p : ℝ) ^ 2)⁻¹) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
            intro p hpIoo hpNot
            positivity
          _ ≤ 2 / 7 := by
            convert (sum_Ioo_inv_sq_le (α := ℝ) 6 N) using 1 <;> norm_num
      rw [← Finset.mul_sum]
      nlinarith
  have hlargeProd :
      (∏ p ∈ large, signedMoebiusTotientPrimeEulerFactor p) ≤ 18 / 11 := by
    calc
      (∏ p ∈ large, signedMoebiusTotientPrimeEulerFactor p) ≤
          ∏ p ∈ large, Real.exp ((49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹)) := by
        apply Finset.prod_le_prod
        · intro p hpL
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
            (signedMoebiusTotientPrimeEulerFactor_one_le p)
        · intro p hpL
          exact signedMoebiusTotientPrimeEulerFactor_le_exp_large (hlargeSeven p hpL)
      _ = Real.exp (∑ p ∈ large, (49 / 36 : ℝ) * (((p : ℝ) ^ 2)⁻¹)) := by
        rw [Real.exp_sum]
      _ ≤ Real.exp (7 / 18 : ℝ) := Real.exp_le_exp.mpr hlargeSum
      _ ≤ 18 / 11 := exp_seven_eighteenths_le
  calc
    (∏ p ∈ S, signedMoebiusTotientPrimeEulerFactor p) ≤
        ∏ p ∈ T, signedMoebiusTotientPrimeEulerFactor p := hprodST
    _ = (∏ p ∈ large, signedMoebiusTotientPrimeEulerFactor p) *
        (∏ p ∈ small, signedMoebiusTotientPrimeEulerFactor p) := by
      rw [← Finset.prod_union hdisj, hdecomp]
    _ ≤ (18 / 11 : ℝ) * (85 / 32 : ℝ) := by
      rw [hsmallProd]
      gcongr
    _ ≤ 6 := by norm_num

/-- The pointwise absolute value of the signed convolution kernel. -/
noncomputable def absSignedMoebiusTotientKernel (m : ℕ) : ArithmeticFunction ℝ where
  toFun n := |signedMoebiusTotientKernel m n|
  map_zero' := by simp

theorem absSignedMoebiusTotientKernel_isMultiplicative (m : ℕ) :
    (absSignedMoebiusTotientKernel m).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [absSignedMoebiusTotientKernel,
      signedMoebiusTotientKernel_isMultiplicative m]
  · intro a b ha hb hab
    simp only [absSignedMoebiusTotientKernel, ArithmeticFunction.coe_mk]
    rw [(signedMoebiusTotientKernel_isMultiplicative m).map_mul_of_coprime hab]
    exact abs_mul _ _

/-- Enlarge a finite prefix to the divisor set of `X!`. -/
theorem prefix_kernel_mass_le_factorial_divisor_sum (m X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, |signedMoebiusTotientKernel m d|) ≤
      ∑ d ∈ X.factorial.divisors, absSignedMoebiusTotientKernel m d := by
  change (∑ d ∈ Finset.Icc 1 X, absSignedMoebiusTotientKernel m d) ≤ _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hdIcc := Finset.mem_Icc.mp hd
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_factorial (by omega) hdIcc.2, Nat.factorial_ne_zero X⟩
  · intro d hdDiv hdNot
    simp [absSignedMoebiusTotientKernel]

private theorem cast_pow_reciprocal {p e : ℕ} :
    1 / ((p ^ e : ℕ) : ℝ) = (1 / (p : ℝ)) ^ e := by
  push_cast
  simp [one_div, inv_pow]

/-- The absolute prime-power sum at a conductor prime is at most `p / (p - 1)`. -/
theorem local_kernel_mass_le_of_dvd
    (m k : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    (∑ e ∈ Finset.range (k + 1),
      |signedMoebiusTotientKernel m (p ^ e)|) ≤
      (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have heq :
      (∑ e ∈ Finset.range (k + 1),
        |signedMoebiusTotientKernel m (p ^ e)|) =
        ∑ e ∈ Finset.range (k + 1), (1 / (p : ℝ)) ^ e := by
    apply Finset.sum_congr rfl
    intro e he
    cases e with
    | zero =>
        simp [signedMoebiusTotientKernel_isMultiplicative m]
    | succ j =>
        rw [signedMoebiusTotientKernel_prime_pow_of_dvd m j hp hpm]
        rw [abs_of_nonneg (by positivity)]
        exact cast_pow_reciprocal
  rw [heq]
  have hxNonneg : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hxLt : (1 / (p : ℝ)) < 1 := by
    rw [div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1R : (p : ℝ) - 1 ≠ 0 := by
    have hpRgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact ne_of_gt this
  calc
    (∑ e ∈ Finset.range (k + 1), (1 / (p : ℝ)) ^ e) =
        ∑ e ∈ Finset.Ico 0 (k + 1), (1 / (p : ℝ)) ^ e := by
      rw [Finset.range_eq_Ico]
    _ ≤ (1 / (p : ℝ)) ^ 0 / (1 - 1 / (p : ℝ)) :=
      geom_sum_Ico_le_of_lt_one hxNonneg hxLt
    _ = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hp.one_le]
      norm_num only [Nat.cast_one]
      field_simp [hpR, hpm1R]

/-- The absolute prime-power sum off the conductor is bounded by the universal local factor. -/
theorem local_kernel_mass_le_of_not_dvd
    (m k : ℕ) {p : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) :
    (∑ e ∈ Finset.range (k + 1),
      |signedMoebiusTotientKernel m (p ^ e)|) ≤
      signedMoebiusTotientPrimeEulerFactor p := by
  have heq :
      (∑ e ∈ Finset.range (k + 1),
        |signedMoebiusTotientKernel m (p ^ e)|) =
        1 + (1 / (((p - 1 : ℕ) : ℝ))) *
          (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ (j + 1)) := by
    rw [Finset.sum_range_succ']
    have htail :
        (∑ j ∈ Finset.range k,
          |signedMoebiusTotientKernel m (p ^ (j + 1))|) =
          (1 / (((p - 1 : ℕ) : ℝ))) *
            ∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [signedMoebiusTotientKernel_prime_pow_of_not_dvd m j hp hpm]
      have hpm1Nonneg : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by positivity
      have hdenNonneg :
          (0 : ℝ) ≤ ((p ^ (j + 1) : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) :=
        mul_nonneg (by positivity) hpm1Nonneg
      rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) hdenNonneg)]
      rw [neg_div, neg_neg]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpm1N : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
      have hpm1R : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpm1N
      push_cast
      rw [← cast_pow_reciprocal]
      field_simp [hpR, hpm1R]
      norm_num
    rw [htail]
    simp [signedMoebiusTotientKernel_isMultiplicative m, add_comm]
  rw [heq]
  have hxNonneg : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hxLt : (1 / (p : ℝ)) < 1 := by
    rw [div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have hgeom :
      (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ (j + 1)) ≤
        (1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) := by
    have hbound := geom_sum_Ico_le_of_lt_one
      (m := 1) (n := k + 1) hxNonneg hxLt
    rw [Finset.sum_Ico_eq_sum_range] at hbound
    simpa [Nat.add_sub_cancel, add_comm] using hbound
  unfold signedMoebiusTotientPrimeEulerFactor
  have hpm1Pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1R : (p : ℝ) - 1 ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.one_le]
    exact ne_of_gt hpm1Pos
  calc
    1 + 1 / (((p - 1 : ℕ) : ℝ)) *
        (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ (j + 1)) ≤
        1 + 1 / (((p - 1 : ℕ) : ℝ)) *
          ((1 / (p : ℝ)) / (1 - 1 / (p : ℝ))) := by
      gcongr
    _ = 1 + 1 / (((p - 1 : ℕ) : ℝ) ^ 2) := by
      rw [Nat.cast_sub hp.one_le]
      norm_num only [Nat.cast_one]
      field_simp [hpR, hpm1R]

/-- The divisor mass of `X!` factors into finite prime-power masses. -/
theorem factorial_divisor_kernel_mass_eq_factorization (m X : ℕ) :
    (∑ d ∈ X.factorial.divisors, absSignedMoebiusTotientKernel m d) =
      X.factorial.factorization.prod fun p k =>
        ∑ e ∈ Finset.range (k + 1),
          |signedMoebiusTotientKernel m (p ^ e)| := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  have hmult :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        absSignedMoebiusTotientKernel m).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      (absSignedMoebiusTotientKernel_isMultiplicative m)
  rw [hmult.multiplicative_factorization _ (Nat.factorial_ne_zero X)]
  apply Finsupp.prod_congr
  intro p hpSupport
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpPrime]
  rfl

/-- Replace each prime-power mass by its conductor or off-conductor local factor. -/
theorem factorial_divisor_kernel_mass_le_local_product (m X : ℕ) :
    (∑ d ∈ X.factorial.divisors, absSignedMoebiusTotientKernel m d) ≤
      ∏ p ∈ X.factorial.primeFactors,
        if p ∣ m then
          (p : ℝ) / ((p - 1 : ℕ) : ℝ)
        else signedMoebiusTotientPrimeEulerFactor p := by
  rw [factorial_divisor_kernel_mass_eq_factorization]
  rw [Nat.prod_primeFactors_prod_factorization]
  simp only [Finsupp.prod]
  apply Finset.prod_le_prod
  · intro p hpSupport
    positivity
  · intro p hpSupport
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
    by_cases hpm : p ∣ m
    · rw [if_pos hpm]
      exact local_kernel_mass_le_of_dvd m _ hpPrime hpm
    · rw [if_neg hpm]
      exact local_kernel_mass_le_of_not_dvd m _ hpPrime hpm

/-- Euler's product formula in the ratio form used for conductor primes. -/
theorem prime_ratio_product_eq (m : ℕ) (hm : 0 < m) :
    (∏ p ∈ m.primeFactors, (p : ℝ) / ((p - 1 : ℕ) : ℝ)) =
      (m : ℝ) / (Nat.totient m : ℝ) := by
  have hphiPos : 0 < Nat.totient m := Nat.totient_pos.2 hm
  have hphiNe : (Nat.totient m : ℝ) ≠ 0 := by exact_mod_cast hphiPos.ne'
  have hqNe :
      (∏ p ∈ m.primeFactors, ((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    have hqPos : 0 < (∏ p ∈ m.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
      refine Finset.prod_pos ?_
      intro p hpMem
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt
    exact ne_of_gt hqPos
  have hEuler :
      (Nat.totient m : ℝ) * (∏ p ∈ m.primeFactors, (p : ℝ)) =
        (m : ℝ) * (∏ p ∈ m.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
    have hNat := Nat.totient_mul_prod_primeFactors m
    have hCast :
        ((Nat.totient m * ∏ p ∈ m.primeFactors, p : ℕ) : ℝ) =
          ((m * ∏ p ∈ m.primeFactors, (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    simpa [Nat.cast_mul, Nat.cast_prod, mul_assoc, mul_left_comm, mul_comm] using hCast
  rw [Finset.prod_div_distrib]
  field_simp [hphiNe, hqNe]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hEuler

private theorem prime_ratio_one_le {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤ (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have hdenPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  apply (le_div_iff₀ hdenPos).2
  have hsplit : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hp.one_le
  linarith

/-- The combined local-factor product is controlled by `6 * m / phi(m)`. -/
theorem local_factor_product_le (m N : ℕ) (hm : 0 < m) :
    (∏ p ∈ N.primeFactors,
        if p ∣ m then
          (p : ℝ) / ((p - 1 : ℕ) : ℝ)
        else signedMoebiusTotientPrimeEulerFactor p) ≤
      6 * (m : ℝ) / (Nat.totient m : ℝ) := by
  classical
  let conductorPrimes := N.primeFactors.filter (· ∣ m)
  let offConductorPrimes := N.primeFactors.filter (fun p => ¬p ∣ m)
  have hconductorSubset : conductorPrimes ⊆ m.primeFactors := by
    intro p hpMem
    have hpData := Finset.mem_filter.mp hpMem
    have hpPrime := Nat.prime_of_mem_primeFactors hpData.1
    exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpData.2, hm.ne'⟩
  have hconductor :
      (∏ p ∈ conductorPrimes, (p : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤
        (m : ℝ) / (Nat.totient m : ℝ) := by
    rw [← prime_ratio_product_eq m hm]
    exact real_prod_le_prod_of_subset_of_one_le hconductorSubset fun p hpMem =>
      prime_ratio_one_le (Nat.prime_of_mem_primeFactors hpMem)
  have hoffPrime : ∀ p ∈ offConductorPrimes, p.Prime := by
    intro p hpMem
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpMem).1
  have hoff :
      (∏ p ∈ offConductorPrimes, signedMoebiusTotientPrimeEulerFactor p) ≤ 6 :=
    signedMoebiusTotientPrimeEulerFactor_product_le_six offConductorPrimes hoffPrime
  have hoffNonneg :
      0 ≤ ∏ p ∈ offConductorPrimes, signedMoebiusTotientPrimeEulerFactor p := by
    exact le_trans (by norm_num) (one_le_real_prod fun p hpMem =>
      signedMoebiusTotientPrimeEulerFactor_one_le p)
  have hratioNonneg : 0 ≤ (m : ℝ) / (Nat.totient m : ℝ) := by positivity
  rw [Finset.prod_ite]
  change
    (∏ p ∈ conductorPrimes, (p : ℝ) / ((p - 1 : ℕ) : ℝ)) *
      (∏ p ∈ offConductorPrimes, signedMoebiusTotientPrimeEulerFactor p) ≤ _
  calc
    (∏ p ∈ conductorPrimes, (p : ℝ) / ((p - 1 : ℕ) : ℝ)) *
        (∏ p ∈ offConductorPrimes, signedMoebiusTotientPrimeEulerFactor p) ≤
        ((m : ℝ) / (Nat.totient m : ℝ)) * 6 := by
      exact mul_le_mul hconductor hoff hoffNonneg hratioNonneg
    _ = 6 * (m : ℝ) / (Nat.totient m : ℝ) := by ring

/-- The explicit kernel satisfies the mass estimate left open by the convolution module. -/
theorem signedMoebiusTotientKernelMassBound_proved :
    SignedMoebiusTotientKernelMassBound := by
  intro m X hm
  calc
    (∑ d ∈ Finset.Icc 1 X, |signedMoebiusTotientKernel m d|) ≤
        ∑ d ∈ X.factorial.divisors, absSignedMoebiusTotientKernel m d :=
      prefix_kernel_mass_le_factorial_divisor_sum m X
    _ ≤ ∏ p ∈ X.factorial.primeFactors,
        if p ∣ m then
          (p : ℝ) / ((p - 1 : ℕ) : ℝ)
        else signedMoebiusTotientPrimeEulerFactor p :=
      factorial_divisor_kernel_mass_le_local_product m X
    _ ≤ 6 * (m : ℝ) / (Nat.totient m : ℝ) :=
      local_factor_product_le m X.factorial hm

/-- The specialist's uniform signed Mobius/totient partial-sum bound, now proved in Lean. -/
theorem signedMoebiusTotientSixBound :
    Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor.SignedMoebiusTotientSixBound :=
  signedMoebiusTotientSixBound_of_kernelMassBound
    signedMoebiusTotientKernelMassBound_proved

end

end Goldbach.Cert.MajorArcModules.RouteASignedMoebiusEulerProduct
