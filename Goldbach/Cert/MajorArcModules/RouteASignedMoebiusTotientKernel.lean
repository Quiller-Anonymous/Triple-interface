import Goldbach.Cert.MajorArcModules.RouteASignedMoebiusPartialSums

/-!
# The signed Mobius/totient convolution kernel

This module isolates the second, purely arithmetic part of the proposed signed-conductor bound.
It constructs the exact Dirichlet-convolution kernel which converts `mu(n) / n` into
`mu(n) 1_(n,m)=1 / phi(n)`, proves the corresponding finite prefix identity, and reduces the
constant-six theorem to an absolute-mass estimate for that concrete kernel.

No mass estimate is asserted here. In particular, the Euler-product inequality needed to prove
the constant `6` remains a visible theorem obligation rather than an axiom.
-/

namespace Goldbach.Cert.MajorArcModules.RouteASignedMoebiusTotientKernel

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteASignedMoebiusPartialSums

noncomputable section

/-- Divide the `n`-th coefficient of an arithmetic function by `n`. -/
noncomputable def divideByIndex (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := f n / (n : ℝ)
  map_zero' := by simp

/-- Dividing coefficients by their indices respects Dirichlet convolution. -/
theorem divideByIndex_mul (f g : ArithmeticFunction ℝ) :
    divideByIndex (f * g) = divideByIndex f * divideByIndex g := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [divideByIndex]
  change (f * g) n / (n : ℝ) =
    ∑ x ∈ n.divisorsAntidiagonal, (f x.1 / (x.1 : ℝ)) * (g x.2 / (x.2 : ℝ))
  rw [ArithmeticFunction.mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpair := Nat.mem_divisorsAntidiagonal.mp hp
  have hprod : p.1 * p.2 = n := hpair.1
  have hmulNe : p.1 * p.2 ≠ 0 := by simpa [hprod] using hn
  have hfstNe : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (left_ne_zero_of_mul hmulNe)
  have hsndNe : (p.2 : ℝ) ≠ 0 := by
    exact_mod_cast (right_ne_zero_of_mul hmulNe)
  rw [← hprod, Nat.cast_mul]
  field_simp

private theorem divideByIndex_one :
    divideByIndex (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : n = 1
  · subst n
    simp [divideByIndex]
  · simp [divideByIndex, hn]

/-- The harmonic Mobius arithmetic function `mu(n) / n`. -/
noncomputable def harmonicMoebius : ArithmeticFunction ℝ :=
  divideByIndex (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

/-- The reciprocal arithmetic function `1 / n` for positive `n`. -/
noncomputable def harmonicZeta : ArithmeticFunction ℝ :=
  divideByIndex (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- `mu(n) / n` and `1 / n` are Dirichlet-convolution inverses. -/
theorem harmonicMoebius_mul_harmonicZeta :
    harmonicMoebius * harmonicZeta = 1 := by
  unfold harmonicMoebius harmonicZeta
  rw [← divideByIndex_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  exact divideByIndex_one

/-- The target coefficient `mu(n) / phi(n)`, restricted to integers coprime to `m`. -/
noncomputable def coprimeMoebiusTotient (m : ℕ) : ArithmeticFunction ℝ where
  toFun n :=
    if n.Coprime m then
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (Nat.totient n : ℝ)
    else 0
  map_zero' := by simp

/-- The concrete convolution kernel occurring in the specialist's proof of the constant-six bound. -/
noncomputable def signedMoebiusTotientKernel (m : ℕ) : ArithmeticFunction ℝ :=
  harmonicZeta * coprimeMoebiusTotient m

private theorem prime_pow_div_prime_pow
    {p e i : ℕ} (hp : Nat.Prime p) (hi : i ≤ e) :
    p ^ e / p ^ i = p ^ (e - i) := by
  refine Nat.div_eq_of_eq_mul_left (pow_pos hp.pos i) ?_
  calc
    p ^ e = p ^ ((e - i) + i) := by rw [Nat.sub_add_cancel hi]
    _ = p ^ (e - i) * p ^ i := by rw [pow_add]

/-- Only the constant and linear Mobius terms survive at a prime power. -/
theorem signedMoebiusTotientKernel_prime_pow_expand
    (m j : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    signedMoebiusTotientKernel m (p ^ (j + 1)) =
      1 / ((p ^ (j + 1) : ℕ) : ℝ) +
        1 / ((p ^ j : ℕ) : ℝ) *
          (if p.Coprime m then -1 / ((p - 1 : ℕ) : ℝ) else 0) := by
  rw [signedMoebiusTotientKernel, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal'
    (fun a b => harmonicZeta a * coprimeMoebiusTotient m b)]
  rw [Nat.sum_divisors_prime_pow hp]
  have hsplit : j + 1 + 1 = 2 + j := by omega
  rw [hsplit, Finset.sum_range_add]
  have htail :
      ∑ x ∈ Finset.range j,
        harmonicZeta (p ^ (j + 1) / p ^ (2 + x)) *
          coprimeMoebiusTotient m (p ^ (2 + x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    simp only [coprimeMoebiusTotient, ArithmeticFunction.coe_mk]
    split_ifs
    · rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      have hexp : 2 + x ≠ 1 := by omega
      simp [hexp]
    · simp
  rw [htail, add_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hdiv0 : p ^ (j + 1) / p ^ 0 = p ^ (j + 1) := by simp
  have hdiv1 : p ^ (j + 1) / p ^ 1 = p ^ j := by
    simpa using prime_pow_div_prime_pow hp (e := j + 1) (i := 1) (by omega)
  rw [hdiv0, hdiv1]
  simp [harmonicZeta, divideByIndex, coprimeMoebiusTotient,
    ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, hp.ne_zero]

/-- At primes dividing `m`, the coprimality restriction leaves a positive geometric factor. -/
theorem signedMoebiusTotientKernel_prime_pow_of_dvd
    (m j : ℕ) {p : ℕ} (hp : Nat.Prime p) (hpm : p ∣ m) :
    signedMoebiusTotientKernel m (p ^ (j + 1)) =
      1 / ((p ^ (j + 1) : ℕ) : ℝ) := by
  rw [signedMoebiusTotientKernel_prime_pow_expand m j hp]
  have hnot : ¬p.Coprime m := by
    intro hcop
    exact (hp.coprime_iff_not_dvd.mp hcop) hpm
  simp [hnot]

/-- Away from `m`, the two surviving Mobius terms give the negative local factor. -/
theorem signedMoebiusTotientKernel_prime_pow_of_not_dvd
    (m j : ℕ) {p : ℕ} (hp : Nat.Prime p) (hpm : ¬p ∣ m) :
    signedMoebiusTotientKernel m (p ^ (j + 1)) =
      -1 / (((p ^ (j + 1) : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
  rw [signedMoebiusTotientKernel_prime_pow_expand m j hp]
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hpm
  rw [if_pos hcop]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1N : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
  have hpm1R : ((p - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpm1N
  have hpowR : ((p ^ (j + 1) : ℕ) : ℝ) = ((p ^ j : ℕ) : ℝ) * (p : ℝ) := by
    norm_num [pow_succ]
  rw [hpowR]
  field_simp
  rw [Nat.cast_sub hp.one_le]
  ring

/-- The reciprocal arithmetic function is multiplicative. -/
theorem harmonicZeta_isMultiplicative : harmonicZeta.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [harmonicZeta, divideByIndex]
  · intro a b ha hb hab
    simp [harmonicZeta, divideByIndex, ha, hb, Nat.mul_ne_zero ha hb,
      Nat.cast_mul]
    ring

/-- The coprimality-restricted Mobius/totient weight remains multiplicative. -/
theorem coprimeMoebiusTotient_isMultiplicative (m : ℕ) :
    (coprimeMoebiusTotient m).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [coprimeMoebiusTotient]
  · intro a b ha hb hab
    simp only [coprimeMoebiusTotient, ArithmeticFunction.coe_mk]
    simp only [Nat.coprime_mul_iff_left]
    by_cases ham : a.Coprime m <;> by_cases hbm : b.Coprime m
    · rw [if_pos ⟨ham, hbm⟩, if_pos ham, if_pos hbm]
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab,
        Nat.totient_mul hab]
      push_cast
      ring
    · rw [if_neg (fun h => hbm h.2), if_pos ham, if_neg hbm, mul_zero]
    · rw [if_neg (fun h => ham h.1), if_neg ham, zero_mul]
    · rw [if_neg (fun h => ham h.1), if_neg ham, zero_mul]

/-- The signed Mobius/totient convolution kernel is multiplicative. -/
theorem signedMoebiusTotientKernel_isMultiplicative (m : ℕ) :
    (signedMoebiusTotientKernel m).IsMultiplicative := by
  unfold signedMoebiusTotientKernel
  exact harmonicZeta_isMultiplicative.mul
    (coprimeMoebiusTotient_isMultiplicative m)

/-- The concrete kernel converts the harmonic Mobius function into the coprime totient weight. -/
theorem harmonicMoebius_mul_signedMoebiusTotientKernel (m : ℕ) :
    harmonicMoebius * signedMoebiusTotientKernel m = coprimeMoebiusTotient m := by
  unfold signedMoebiusTotientKernel
  rw [← mul_assoc, harmonicMoebius_mul_harmonicZeta, one_mul]

/-- Finite hyperbola identity for a Dirichlet convolution. -/
theorem sum_Icc_dirichletConvolution
    (a g : ArithmeticFunction ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (a * g) n) =
      ∑ d ∈ Finset.Icc 1 X, g d * (∑ k ∈ Finset.Icc 1 (X / d), a k) := by
  classical
  let source : Finset (Σ _n : ℕ, ℕ × ℕ) :=
    (Finset.Icc 1 X).sigma fun n => n.divisorsAntidiagonal
  let target : Finset (Σ _d : ℕ, ℕ) :=
    (Finset.Icc 1 X).sigma fun d => Finset.Icc 1 (X / d)
  calc
    (∑ n ∈ Finset.Icc 1 X, (a * g) n) =
        ∑ z ∈ source, a z.2.1 * g z.2.2 := by
      simp only [ArithmeticFunction.mul_apply, source, Finset.sum_sigma']
    _ = ∑ z ∈ target, g z.1 * a z.2 := by
      refine Finset.sum_bij
        (s := source) (t := target)
        (f := fun z => a z.2.1 * g z.2.2)
        (g := fun z => g z.1 * a z.2)
        (i := fun z _hz => ⟨z.2.2, z.2.1⟩) ?_ ?_ ?_ ?_
      · intro z hz
        have hzMem := Finset.mem_sigma.mp hz
        have hnMem : z.1 ∈ Finset.Icc 1 X := hzMem.1
        have hpMem : z.2 ∈ z.1.divisorsAntidiagonal := hzMem.2
        have hp := Nat.mem_divisorsAntidiagonal.mp hpMem
        have hmulNe : z.2.1 * z.2.2 ≠ 0 := by
          intro hzero
          apply hp.2
          rw [← hp.1]
          exact hzero
        have hkPos : 0 < z.2.1 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hmulNe)
        have hdPos : 0 < z.2.2 := Nat.pos_of_ne_zero (right_ne_zero_of_mul hmulNe)
        have hnLe : z.1 ≤ X := (Finset.mem_Icc.mp hnMem).2
        have hprodLe : z.2.1 * z.2.2 ≤ X := by simpa [hp.1] using hnLe
        exact Finset.mem_sigma.mpr ⟨
          Finset.mem_Icc.mpr ⟨hdPos, (le_trans (Nat.le_mul_of_pos_left z.2.2 hkPos) hprodLe)⟩,
          Finset.mem_Icc.mpr ⟨hkPos, (Nat.le_div_iff_mul_le hdPos).2 hprodLe⟩⟩
      · intro z₁ hz₁ z₂ hz₂ heq
        have hz₁Mem := Finset.mem_sigma.mp hz₁
        have hz₂Mem := Finset.mem_sigma.mp hz₂
        have hp₁ := Nat.mem_divisorsAntidiagonal.mp hz₁Mem.2
        have hp₂ := Nat.mem_divisorsAntidiagonal.mp hz₂Mem.2
        have hfst : z₁.2.2 = z₂.2.2 := congrArg Sigma.fst heq
        have hsnd : z₁.2.1 = z₂.2.1 := congrArg Sigma.snd heq
        apply Sigma.ext
        · calc
            z₁.1 = z₁.2.1 * z₁.2.2 := hp₁.1.symm
            _ = z₂.2.1 * z₂.2.2 := by rw [hfst, hsnd]
            _ = z₂.1 := hp₂.1
        · exact heq_of_eq (Prod.ext hsnd hfst)
      · intro z hz
        have hzMem := Finset.mem_sigma.mp hz
        have hdMem : z.1 ∈ Finset.Icc 1 X := hzMem.1
        have hkMem : z.2 ∈ Finset.Icc 1 (X / z.1) := hzMem.2
        have hdPos : 0 < z.1 := (Finset.mem_Icc.mp hdMem).1
        have hkPos : 0 < z.2 := (Finset.mem_Icc.mp hkMem).1
        have hprodLe : z.2 * z.1 ≤ X :=
          (Nat.le_div_iff_mul_le hdPos).1 (Finset.mem_Icc.mp hkMem).2
        let preimage : Σ _n : ℕ, ℕ × ℕ := ⟨z.2 * z.1, (z.2, z.1)⟩
        have hpreimage : preimage ∈ source := by
          apply Finset.mem_sigma.mpr
          constructor
          · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hkPos hdPos, hprodLe⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.mul_ne_zero hkPos.ne' hdPos.ne'⟩
        exact ⟨preimage, hpreimage, rfl⟩
      · intro z hz
        simp [mul_comm]
    _ = ∑ d ∈ Finset.Icc 1 X, g d * (∑ k ∈ Finset.Icc 1 (X / d), a k) := by
      simp only [target, Finset.sum_sigma, Finset.mul_sum]

theorem sum_coprimeMoebiusTotient_eq (m X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, coprimeMoebiusTotient m n) =
      signedMoebiusTotientPartialSum m X := by
  unfold signedMoebiusTotientPartialSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp only [coprimeMoebiusTotient, ArithmeticFunction.coe_mk]
  simp [Nat.coprime_comm]

/--
Exact finite prefix identity behind the constant-six estimate. Every partial sum on the right is
already bounded by `abs_signedMoebiusHarmonicPartialSum_le_one`.
-/
theorem signedMoebiusTotientPartialSum_eq_kernelSum (m X : ℕ) :
    signedMoebiusTotientPartialSum m X =
      ∑ d ∈ Finset.Icc 1 X,
        signedMoebiusTotientKernel m d * signedMoebiusHarmonicPartialSum (X / d) := by
  rw [← sum_coprimeMoebiusTotient_eq]
  conv_lhs =>
    enter [2, n]
    rw [← harmonicMoebius_mul_signedMoebiusTotientKernel m]
  rw [sum_Icc_dirichletConvolution]
  rfl

/-- The exact remaining Euler-product obligation for the elementary constant-six theorem. -/
def SignedMoebiusTotientKernelMassBound : Prop :=
  ∀ m X : ℕ, 0 < m →
    (∑ d ∈ Finset.Icc 1 X, |signedMoebiusTotientKernel m d|) ≤
      6 * (m : ℝ) / (Nat.totient m : ℝ)

/-- The concrete kernel mass estimate implies the specialist's Mobius/totient bound. -/
theorem signedMoebiusTotientSixBound_of_kernelMassBound
    (hMass : SignedMoebiusTotientKernelMassBound) :
    SignedMoebiusTotientSixBound := by
  intro m X hm
  rw [signedMoebiusTotientPartialSum_eq_kernelSum]
  calc
    |∑ d ∈ Finset.Icc 1 X,
        signedMoebiusTotientKernel m d * signedMoebiusHarmonicPartialSum (X / d)| ≤
        ∑ d ∈ Finset.Icc 1 X,
          |signedMoebiusTotientKernel m d * signedMoebiusHarmonicPartialSum (X / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 X, |signedMoebiusTotientKernel m d| := by
      refine Finset.sum_le_sum fun d _hd => ?_
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (abs_signedMoebiusHarmonicPartialSum_le_one (X / d))
    _ ≤ 6 * (m : ℝ) / (Nat.totient m : ℝ) := hMass m X hm

end

end Goldbach.Cert.MajorArcModules.RouteASignedMoebiusTotientKernel
