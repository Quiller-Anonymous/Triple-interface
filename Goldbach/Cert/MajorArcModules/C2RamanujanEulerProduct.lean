import Mathlib.NumberTheory.EulerProduct.Basic
import Goldbach.BankPieces.Cert.RamanujanOddZero
import Goldbach.BankPieces.Cert.TrueSingularSeries
import Goldbach.Cert.MajorArcModules.C2EulerProductLowerBound

/-! The absolutely convergent Ramanujan series at two has the classical prime Euler product. -/

namespace Goldbach.Cert.MajorArcModules.C2RamanujanEulerProduct

open scoped BigOperators Topology
open Goldbach.AO_OffDiag
open Goldbach.BankPieces.Cert
open Filter

noncomputable section

theorem ramanujanZ_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) (N : ℕ) :
    TailBlockFun.ramanujanZ (a * b) N
      = TailBlockFun.ramanujanZ a N * TailBlockFun.ramanujanZ b N := by
  have hgcd : Nat.gcd (a * b) N = Nat.gcd a N * Nat.gcd b N := by
    simpa only [Nat.gcd_comm] using (Nat.Coprime.gcd_mul N hab)
  have hdiv : (a * b) / (Nat.gcd a N * Nat.gcd b N)
      = (a / Nat.gcd a N) * (b / Nat.gcd b N) :=
    Nat.mul_div_mul_comm (Nat.gcd_dvd_left a N) (Nat.gcd_dvd_left b N)
  have hcdiv : (a / Nat.gcd a N).Coprime (b / Nat.gcd b N) :=
    hab.of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a N))
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left b N))
  have hcgcd : (Nat.gcd a N).Coprime (Nat.gcd b N) :=
    hab.of_dvd (Nat.gcd_dvd_left a N) (Nat.gcd_dvd_left b N)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcdiv
  have hphi := Nat.totient_mul hcgcd
  simp only [TailBlockFun.ramanujanZ, hgcd, hdiv, hmu, hphi,
    Int.ofNat_eq_natCast, Int.natCast_mul]
  ring

theorem sigmaTerm_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) (N : ℕ) :
    SigmaTailReindexFun.sigmaTerm (a * b) N
      = SigmaTailReindexFun.sigmaTerm a N * SigmaTailReindexFun.sigmaTerm b N := by
  have hsf : Squarefree (a * b) ↔ Squarefree a ∧ Squarefree b := Nat.squarefree_mul hab
  have hmu : AO_OffDiag.muSq (a * b) = AO_OffDiag.muSq a * AO_OffDiag.muSq b := by
    simp only [AO_OffDiag.muSq, hsf]
    split_ifs <;> simp_all
  have hram : TailBlockFun.ramanujanR (a * b) N
      = TailBlockFun.ramanujanR a N * TailBlockFun.ramanujanR b N := by
    simp only [TailBlockFun.ramanujanR, ramanujanZ_mul_of_coprime hab, Int.cast_mul]
  simp only [SigmaTailReindexFun.sigmaTerm, hmu, hram, Nat.totient_mul hab,
    Nat.cast_mul, mul_pow, one_div, mul_inv]
  ring

theorem sigmaTerm_one (N : ℕ) : SigmaTailReindexFun.sigmaTerm 1 N = 1 := by
  simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq,
    TailBlockFun.ramanujanR, TailBlockFun.ramanujanZ]

theorem sigmaTerm_zero (N : ℕ) : SigmaTailReindexFun.sigmaTerm 0 N = 0 := by
  simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq]

theorem sigmaTerm_prime_pow_eq_zero {p e N : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    SigmaTailReindexFun.sigmaTerm (p ^ e) N = 0 := by
  have hnot : ¬ Squarefree (p ^ e) := by
    intro h
    have he1 := ((Nat.squarefree_pow_iff hp.ne_one (by omega : e ≠ 0)).mp h).2
    omega
  simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, hnot]

theorem sigmaTerm_two_two : SigmaTailReindexFun.sigmaTerm 2 2 = 1 := by
  norm_num [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, Nat.prime_two.squarefree,
    TailBlockFun.ramanujanR, TailBlockFun.ramanujanZ]

theorem sigmaTerm_odd_prime_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    SigmaTailReindexFun.sigmaTerm p 2 = -(1 / ((p : ℝ) - 1) ^ 2) := by
  have hcop : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.two_le
  simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, hp.squarefree,
    TailBlockFun.ramanujanR, TailBlockFun.ramanujanZ, hcop.gcd_eq_one,
    ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, Nat.cast_sub hp1]

/-- The prime-two factor is two; every other prime contributes the twin-prime factor. -/
theorem primePowerSum_at_two (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, SigmaTailReindexFun.sigmaTerm (p ^ e) 2)
      = if p = 2 then 2 else 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hfinite : (∑' e : ℕ, SigmaTailReindexFun.sigmaTerm (p ^ e) 2)
      = ∑ e ∈ ({0, 1} : Finset ℕ), SigmaTailReindexFun.sigmaTerm (p ^ e) 2 := by
    apply tsum_eq_sum
    intro e he
    have he2 : 2 ≤ e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
    exact sigmaTerm_prime_pow_eq_zero hp he2
  rw [hfinite]
  by_cases hp2 : p = 2
  · subst p
    norm_num [sigmaTerm_one, sigmaTerm_two_two]
  · simp [hp2, sigmaTerm_one, sigmaTerm_odd_prime_two hp hp2, sub_eq_add_neg]

/-- Prime partial products converge to the series-defined normalizer at two. -/
theorem primeProduct_tendsto_sigmaSeries_two :
    Tendsto (fun n : ℕ => ∏ p ∈ Nat.primesBelow n,
      (if p = 2 then (2 : ℝ) else 1 - 1 / ((p : ℝ) - 1) ^ 2))
      atTop (𝓝 (SingularSeriesRamanujanBridge.sigmaSeriesRamanujan 2)) := by
  have hsum : Summable (fun q : ℕ => ‖SigmaTailReindexFun.sigmaTerm q 2‖) :=
    (RamanujanOddZero.summable_sigmaTerm 2 (by decide)).norm
  have h := EulerProduct.eulerProduct (f := fun q : ℕ => SigmaTailReindexFun.sigmaTerm q 2)
    (sigmaTerm_one 2)
    (fun {a b} hab => sigmaTerm_mul_of_coprime hab 2) hsum (sigmaTerm_zero 2)
  rw [← RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm (by decide : (2 : ℕ) ≠ 0)] at h
  convert h using 1
  funext n
  apply Finset.prod_congr rfl
  intro p hp
  exact (primePowerSum_at_two p (Nat.prime_of_mem_primesBelow hp)).symm

theorem primeProduct_succ_eq_two_mul_partialProduct {n : ℕ} (hn : 2 ≤ n) :
    (∏ p ∈ Nat.primesBelow (n + 1),
      (if p = 2 then (2 : ℝ) else 1 - 1 / ((p : ℝ) - 1) ^ 2))
      = 2 * Goldbach.Cert.C2EulerProductLowerBound.partialProduct n := by
  classical
  have hset : Nat.primesBelow (n + 1)
      = insert 2 (Goldbach.Cert.C2EulerProductLowerBound.oddPrimesThrough n) := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_insert,
      Goldbach.Cert.C2EulerProductLowerBound.oddPrimesThrough,
      Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpn, hp⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · exact Or.inr ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩
    · rintro (rfl | ⟨⟨hp3, hpn⟩, hp⟩)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, hp⟩
  have hnot : 2 ∉ Goldbach.Cert.C2EulerProductLowerBound.oddPrimesThrough n := by
    simp [Goldbach.Cert.C2EulerProductLowerBound.oddPrimesThrough]
  rw [hset, Finset.prod_insert hnot]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  simp only [if_neg (by omega : p ≠ 2)]

/-- The classical odd-prime partial products converge to the actual constant used by the
canonical on-window Ramanujan-series package. -/
theorem partialProduct_tendsto_ramanujanC2 :
    Tendsto Goldbach.Cert.C2EulerProductLowerBound.partialProduct atTop
      (𝓝 TrueSingularSeries.ramanujanSeriesOnWindow.C.C2) := by
  have hdiv := (primeProduct_tendsto_sigmaSeries_two.comp (tendsto_add_atTop_nat 1)).div_const 2
  have hC : TrueSingularSeries.ramanujanSeriesOnWindow.C.C2
      = SingularSeriesRamanujanBridge.sigmaSeriesRamanujan 2 / 2 := by rfl
  rw [hC]
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  simp only [Function.comp_apply]
  rw [primeProduct_succ_eq_two_mul_partialProduct hn]
  ring

/-- Genuine canonical `C2 > 0.66`; the series/Euler-product bridge is included. -/
theorem ramanujanSeriesOnWindow_C2_gt_33_50 :
    (33 : ℝ) / 50 < TrueSingularSeries.ramanujanSeriesOnWindow.C.C2 :=
  Goldbach.Cert.C2EulerProductLowerBound.lower_of_tendsto partialProduct_tendsto_ramanujanC2

end
end Goldbach.Cert.MajorArcModules.C2RamanujanEulerProduct
