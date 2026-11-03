import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor
import Goldbach.AO_OffDiag.SigmaTailEuler_Analytic

/-!
# A logarithmic reciprocal-totient prefix bound

The direct large-conductor Type-I estimate uses

`sum_{k <= K} 1 / phi(k)`.

This file proves a finite logarithmic bound for that prefix.  The proof expands `n / phi(n)` as a
squarefree-divisor sum, applies the exact finite Dirichlet hyperbola identity, and bounds the
remaining squarefree Euler kernel by the finite constant-six product already used in the signed
conductor argument.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAReciprocalTotientPrefix

open scoped BigOperators
open ArithmeticFunction
open Goldbach.AO_OffDiag
open Goldbach.Cert.MajorArcModules.RouteASignedMoebiusTotientKernel
open Goldbach.Cert.MajorArcModules.RouteASignedMoebiusEulerProduct
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype

noncomputable section

/-- Positive squarefree Euler kernel in the reciprocal-totient divisor expansion. -/
noncomputable def reciprocalTotientEulerKernel : ArithmeticFunction ℝ where
  toFun d := muSq d / ((d : ℝ) * (Nat.totient d : ℝ))
  map_zero' := by simp [muSq]

/-- Reciprocal totient, extended by zero at the arithmetic-function zero index. -/
noncomputable def reciprocalTotientArithmetic : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else 1 / (Nat.totient n : ℝ)
  map_zero' := by simp

theorem reciprocalTotientEulerKernel_nonneg (d : ℕ) :
    0 ≤ reciprocalTotientEulerKernel d := by
  unfold reciprocalTotientEulerKernel
  simp only [ArithmeticFunction.coe_mk]
  unfold muSq
  split_ifs <;> positivity

/-- The totient divisor identity in Dirichlet-convolution form. -/
theorem harmonicZeta_mul_reciprocalTotientEulerKernel :
    harmonicZeta * reciprocalTotientEulerKernel = reciprocalTotientArithmetic := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [reciprocalTotientArithmetic]
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hPhi : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 hnPos).ne'
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal'
    (fun a b => harmonicZeta a * reciprocalTotientEulerKernel b)]
  have hTerm : ∀ d ∈ n.divisors,
      harmonicZeta (n / d) * reciprocalTotientEulerKernel d =
        (1 / (n : ℝ)) * (muSq d * (1 / (Nat.totient d : ℝ))) := by
    intro d hd
    have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDvd hnPos
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
    have hDivPos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnPos hdDvd) hdPos
    have hDivR : ((n / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hDivPos.ne'
    have hMul : (n / d) * d = n := Nat.div_mul_cancel hdDvd
    have hMulR : ((n / d : ℕ) : ℝ) * (d : ℝ) = (n : ℝ) := by
      exact_mod_cast hMul
    simp only [harmonicZeta, divideByIndex, reciprocalTotientEulerKernel,
      ArithmeticFunction.coe_mk]
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hDivPos.ne', Nat.cast_one]
    norm_num
    rw [← hMulR]
    field_simp [hdR, hDivR]
  calc
    (∑ d ∈ n.divisors,
        harmonicZeta (n / d) * reciprocalTotientEulerKernel d) =
        ∑ d ∈ n.divisors,
          (1 / (n : ℝ)) * (muSq d * (1 / (Nat.totient d : ℝ))) := by
      apply Finset.sum_congr rfl
      exact hTerm
    _ = (1 / (n : ℝ)) *
        (∑ d ∈ n.divisors, muSq d * (1 / (Nat.totient d : ℝ))) := by
      rw [Finset.mul_sum]
    _ = (1 / (n : ℝ)) * ((n : ℝ) / (Nat.totient n : ℝ)) := by
      rw [← totient_divisor_expansion n hn]
    _ = reciprocalTotientArithmetic n := by
      simp only [reciprocalTotientArithmetic, ArithmeticFunction.coe_mk, if_neg hn]
      field_simp

/-- Exact finite hyperbola formula for the reciprocal-totient prefix. -/
theorem reciprocalTotientPrefix_eq_eulerKernel_harmonic (K : ℕ) :
    reciprocalTotientPrefix K =
      ∑ d ∈ Finset.Icc 1 K, reciprocalTotientEulerKernel d * (harmonic (K / d) : ℝ) := by
  unfold reciprocalTotientPrefix
  calc
    (∑ n ∈ Finset.Icc 1 K, 1 / (Nat.totient n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 K, reciprocalTotientArithmetic n := by
      apply Finset.sum_congr rfl
      intro n hnMem
      have hn : n ≠ 0 := (Nat.ne_of_gt (Finset.mem_Icc.mp hnMem).1)
      simp [reciprocalTotientArithmetic, hn]
    _ = ∑ n ∈ Finset.Icc 1 K,
        (harmonicZeta * reciprocalTotientEulerKernel) n := by
      rw [harmonicZeta_mul_reciprocalTotientEulerKernel]
    _ = ∑ d ∈ Finset.Icc 1 K, reciprocalTotientEulerKernel d *
          (∑ k ∈ Finset.Icc 1 (K / d), harmonicZeta k) := by
      exact sum_Icc_dirichletConvolution harmonicZeta reciprocalTotientEulerKernel K
    _ = ∑ d ∈ Finset.Icc 1 K,
        reciprocalTotientEulerKernel d * (harmonic (K / d) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      congr 1
      rw [harmonic_eq_sum_Icc]
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hkMem
      have hk : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hkMem).1
      simp [harmonicZeta, divideByIndex, hk, div_eq_mul_inv]

private theorem inv_index_totient_prod_primes
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    1 / (((∏ p ∈ s, p : ℕ) : ℝ) *
        (Nat.totient (∏ p ∈ s, p) : ℝ)) =
      ∏ p ∈ s, 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    norm_num
  · intro p s hpNotMem ih hs
    have hpPrime : p.Prime := hs p (by simp [hpNotMem])
    have hsPrime : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hs q (by simp [hq])
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine (Nat.coprime_prod_right_iff (x := p) (t := s) (s := fun q : ℕ => q)).2 ?_
      intro q hq
      have hqPrime := hsPrime q hq
      exact (hpPrime.coprime_iff_not_dvd).2 fun hpq =>
        hpNotMem ((Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).1 hpq ▸ hq)
    have htot :
        Nat.totient (p * (∏ q ∈ s, q)) =
          Nat.totient p * Nat.totient (∏ q ∈ s, q) :=
      Nat.totient_mul hcop
    have hpNe : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    have hpm1Ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hpPrime.one_lt).ne'
    have hprodPos : 0 < ∏ q ∈ s, q := by
      exact Finset.prod_pos fun q hq => (hsPrime q hq).pos
    have hprodNe : ((∏ q ∈ s, q : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hprodPos.ne'
    have hphiProdNe : (Nat.totient (∏ q ∈ s, q) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 hprodPos).ne'
    rw [Finset.prod_insert hpNotMem, Finset.prod_insert hpNotMem,
      Nat.cast_mul, htot, Nat.cast_mul, Nat.totient_prime hpPrime]
    calc
      1 / ((p : ℝ) * (∏ q ∈ s, q : ℕ) *
          (((p - 1 : ℕ) : ℝ) * (Nat.totient (∏ q ∈ s, q) : ℝ))) =
          1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) *
            (1 / (((∏ q ∈ s, q : ℕ) : ℝ) *
              (Nat.totient (∏ q ∈ s, q) : ℝ))) := by
        field_simp [hpNe, hpm1Ne, hprodNe, hphiProdNe]
      _ = 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) *
          ∏ q ∈ s, 1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) := by
        rw [ih hsPrime]

/-- Enlarge the positive Euler-kernel prefix to the divisor set of `K!`. -/
theorem eulerKernel_prefix_le_factorial_divisor_sum (K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K, reciprocalTotientEulerKernel d) ≤
      ∑ d ∈ K.factorial.divisors, reciprocalTotientEulerKernel d := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hdIcc := Finset.mem_Icc.mp hd
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_factorial (by omega) hdIcc.2, Nat.factorial_ne_zero K⟩
  · intro d _hd _hdNot
    exact reciprocalTotientEulerKernel_nonneg d

/-- The factorial divisor mass is the finite product of the positive local factors. -/
theorem factorial_divisor_eulerKernel_eq_local_product (K : ℕ) :
    (∑ d ∈ K.factorial.divisors, reciprocalTotientEulerKernel d) =
      ∏ p ∈ K.factorial.primeFactors,
        (1 + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  classical
  let n := K.factorial
  have hn : n ≠ 0 := Nat.factorial_ne_zero K
  have hsq :
      (∑ d ∈ n.divisors, reciprocalTotientEulerKernel d) =
        ∑ d ∈ n.divisors with Squarefree d,
          1 / ((d : ℝ) * (Nat.totient d : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _hd
    by_cases hsqD : Squarefree d
    · simp [reciprocalTotientEulerKernel, muSq, hsqD]
    · simp [reciprocalTotientEulerKernel, muSq, hsqD]
  have hS :
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    ext p
    change (p ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset) ↔
      p ∈ n.primeFactorsList.toFinset
    constructor
    · intro hp
      have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors n := by
        simpa using
          (Multiset.mem_toFinset (a := p)
            (s := UniqueFactorizationMonoid.normalizedFactors n)).1 hp
      have hp'' : p ∈ (n.primeFactorsList : Multiset ℕ) := by
        simpa [Nat.factors_eq n] using hp'
      exact List.mem_toFinset.2 (by simpa using hp'')
    · intro hp
      have hpList : p ∈ n.primeFactorsList := List.mem_toFinset.1 hp
      have hp'' : p ∈ (n.primeFactorsList : Multiset ℕ) := by simpa using hpList
      have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors n := by
        simpa [Nat.factors_eq n] using hp''
      exact (Multiset.mem_toFinset (a := p)
        (s := UniqueFactorizationMonoid.normalizedFactors n)).2 hp'
  have hpow :
      (∑ d ∈ n.divisors with Squarefree d,
          1 / ((d : ℝ) * (Nat.totient d : ℝ))) =
        ∑ s ∈ n.primeFactors.powerset,
          1 / (((∏ p ∈ s, p : ℕ) : ℝ) *
            (Nat.totient (∏ p ∈ s, p) : ℝ)) := by
    have h := Nat.sum_divisors_filter_squarefree (n := n) hn
      (f := fun d : ℕ => 1 / ((d : ℝ) * (Nat.totient d : ℝ)))
    simpa [hS] using h
  have hterm :
      (∑ s ∈ n.primeFactors.powerset,
          1 / (((∏ p ∈ s, p : ℕ) : ℝ) *
            (Nat.totient (∏ p ∈ s, p) : ℝ))) =
        ∑ s ∈ n.primeFactors.powerset,
          ∏ p ∈ s, 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro s hsMem
    apply inv_index_totient_prod_primes
    intro p hp
    exact Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hsMem) hp)
  have hprod :
      (∑ s ∈ n.primeFactors.powerset,
          ∏ p ∈ s, 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) =
        ∏ p ∈ n.primeFactors,
          (1 + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
    simpa using (Finset.prod_one_add (s := n.primeFactors)
      (f := fun p : ℕ => 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))).symm
  change (∑ d ∈ n.divisors, reciprocalTotientEulerKernel d) = _
  exact hsq.trans (hpow.trans (hterm.trans hprod))

theorem reciprocalTotientEulerLocalFactor_le_signedFactor
    {p : ℕ} (hp : p.Prime) :
    1 + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
      signedMoebiusTotientPrimeEulerFactor p := by
  unfold signedMoebiusTotientPrimeEulerFactor
  have hpm1Pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hpm1Le : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.sub_le p 1
  have hden :
      (((p - 1 : ℕ) : ℝ) ^ 2) ≤
        (p : ℝ) * ((p - 1 : ℕ) : ℝ) := by
    nlinarith
  have hinv :
      1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
        1 / (((p - 1 : ℕ) : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (sq_pos_of_pos hpm1Pos) hden
  linarith

/-- The positive Euler kernel has universal finite prefix mass at most six. -/
theorem reciprocalTotientEulerKernel_prefix_le_six (K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K, reciprocalTotientEulerKernel d) ≤ 6 := by
  calc
    (∑ d ∈ Finset.Icc 1 K, reciprocalTotientEulerKernel d) ≤
        ∑ d ∈ K.factorial.divisors, reciprocalTotientEulerKernel d :=
      eulerKernel_prefix_le_factorial_divisor_sum K
    _ = ∏ p ∈ K.factorial.primeFactors,
        (1 + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) :=
      factorial_divisor_eulerKernel_eq_local_product K
    _ ≤ ∏ p ∈ K.factorial.primeFactors,
        signedMoebiusTotientPrimeEulerFactor p := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p hpMem
        exact reciprocalTotientEulerLocalFactor_le_signedFactor
          (Nat.prime_of_mem_primeFactors hpMem)
    _ ≤ 6 := signedMoebiusTotientPrimeEulerFactor_product_le_six _
      (fun p hp => Nat.prime_of_mem_primeFactors hp)

private theorem harmonic_cast_nonneg (K : ℕ) :
    0 ≤ (harmonic K : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  positivity

private theorem harmonic_cast_mono {K M : ℕ} (hKM : K ≤ M) :
    (harmonic K : ℝ) ≤ (harmonic M : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnData := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hnData.1, hnData.2.trans hKM⟩
  · intro n _hn _hnNot
    positivity

/-- The reciprocal-totient prefix is at most six harmonic numbers. -/
theorem reciprocalTotientPrefix_le_six_mul_harmonic (K : ℕ) :
    reciprocalTotientPrefix K ≤ 6 * (harmonic K : ℝ) := by
  rw [reciprocalTotientPrefix_eq_eulerKernel_harmonic]
  calc
    (∑ d ∈ Finset.Icc 1 K,
        reciprocalTotientEulerKernel d * (harmonic (K / d) : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 K,
          reciprocalTotientEulerKernel d * (harmonic K : ℝ) := by
      apply Finset.sum_le_sum
      intro d _hd
      exact mul_le_mul_of_nonneg_left
        (harmonic_cast_mono (Nat.div_le_self K d))
        (reciprocalTotientEulerKernel_nonneg d)
    _ = (∑ d ∈ Finset.Icc 1 K, reciprocalTotientEulerKernel d) *
        (harmonic K : ℝ) := by rw [Finset.sum_mul]
    _ ≤ 6 * (harmonic K : ℝ) :=
      mul_le_mul_of_nonneg_right
        (reciprocalTotientEulerKernel_prefix_le_six K)
        (harmonic_cast_nonneg K)

/-- Explicit logarithmic estimate used by the direct large-conductor branch. -/
theorem reciprocalTotientPrefix_le_six_mul_one_add_log (K : ℕ) :
    reciprocalTotientPrefix K ≤ 6 * (1 + Real.log (K : ℝ)) := by
  exact (reciprocalTotientPrefix_le_six_mul_harmonic K).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K) (by norm_num))

/-- The direct primitive-conductor cost with the reciprocal-totient input discharged. -/
theorem directPrimitiveConductorAnalyticCost_le_explicitLargeConductorWeight
    {N u R r : ℕ}
    (hN : 0 < N) (hR : 0 < R) (hRr : R < r) :
    directPrimitiveConductorAnalyticCost N u r ≤
      largeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) *
        ((r : ℝ) / (Nat.totient r : ℝ)) :=
  directPrimitiveConductorAnalyticCost_le_largeConductorWeight
    hN hR hRr (reciprocalTotientPrefix_le_six_mul_one_add_log u)

/-- The exact large-conductor allowance with only its character mean-value mass left open. -/
theorem input_directAllowanceAbove_le_explicitMeanValueMass
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hN : 0 < N) (hR : 0 < R) :
    nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax ≤
      largeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) *
        largeConductorPrimitiveMeanValueMass N u R input.primitiveMax :=
  input_directAllowanceAbove_le_meanValueMass input hN hR
    (reciprocalTotientPrefix_le_six_mul_one_add_log u)

/-- Hybrid coprime endpoint with the elementary reciprocal-totient estimate inserted. -/
theorem norm_activeCoprimeProgressionError_le_explicitHybridMeanValueAllowance
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hMass :
      largeConductorPrimitiveMeanValueMass N u R input.primitiveMax ≤ massBound) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
        (largeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) :=
  norm_activeCoprimeProgressionError_le_hybridMeanValueAllowance
    input hL hu hTwoL hR hStable
      (reciprocalTotientPrefix_le_six_mul_one_add_log u) hSmall hMass

/--
Complete short Type-I convolution theorem with the reciprocal-totient arithmetic fully proved.
The remaining hypotheses are the primitive-character level transport and the small/large
character estimates; no reciprocal-totient estimate is assumed.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_explicitHybridMeanValueAllowance
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hMass :
      largeConductorPrimitiveMeanValueMass N u R input.primitiveMax ≤ massBound) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (largeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) :=
  abs_typeIPrimeConvolution_sub_activeMain_le_hybridMeanValueAllowance
    input hL hu hTwoL hR hStable
      (reciprocalTotientPrefix_le_six_mul_one_add_log u) hSmall hMass

end

end Goldbach.Cert.MajorArcModules.RouteAReciprocalTotientPrefix
