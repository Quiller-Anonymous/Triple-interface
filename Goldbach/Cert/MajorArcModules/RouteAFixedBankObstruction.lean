import Goldbach.Cert.MajorArcModules.Q0MinorRouteADenseGridTargets

/-!
# Fixed-width Route A bank obstruction

The current bank is supported on the fixed interval
`[X / 2 - H, X / 2 + H]`.  A factorial construction produces arbitrarily large
centres for which every integer in that interval is composite.  This file proves
that obstruction and transports it through the exact route-visible statistic.

This is an obstruction to a *strictly positive* Route A grid mean for every
`X >= X0`.  It does not invalidate upper bounds, the uniform truncation theorem,
or the finite `X0` certificate.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAFixedBankObstruction

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorRouteADenseGridTargets
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleAnalysis
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition

noncomputable section

set_option maxRecDepth 100000

/-- Factorial used to manufacture a composite interval of radius `h`. -/
def fixedBankObstructionFactorial (h : ℕ) : ℕ :=
  Nat.factorial (2 * h + 2)

/-- Centre of the manufactured composite interval. -/
def fixedBankObstructionCenter (h k : ℕ) : ℕ :=
  k * fixedBankObstructionFactorial h + h + 2

/-- Even scale whose half is `fixedBankObstructionCenter h k`. -/
def fixedBankObstructionScale (h k : ℕ) : ℕ :=
  2 * fixedBankObstructionCenter h k

@[simp] theorem fixedBankObstructionScale_div_two (h k : ℕ) :
    fixedBankObstructionScale h k / 2 = fixedBankObstructionCenter h k := by
  simp [fixedBankObstructionScale]

/-- Every integer in the fixed-radius interval around the constructed centre is composite. -/
theorem not_prime_of_mem_fixedBankObstructionInterval
    {h k n : ℕ} (hk : 0 < k)
    (hn : n ∈ Finset.Icc
      (fixedBankObstructionScale h k / 2 - h)
      (fixedBankObstructionScale h k / 2 + h)) :
    ¬ Nat.Prime n := by
  let b := k * fixedBankObstructionFactorial h
  let j := n - b
  have hFpos : 0 < fixedBankObstructionFactorial h := by
    exact Nat.factorial_pos _
  have hbpos : 0 < b := Nat.mul_pos hk hFpos
  have hnI := Finset.mem_Icc.mp hn
  rw [fixedBankObstructionScale_div_two] at hnI
  dsimp [fixedBankObstructionCenter] at hnI
  have hnlo : b + 2 ≤ n := by
    dsimp [b]
    omega
  have hnhi : n ≤ b + (2 * h + 2) := by
    dsimp [b]
    omega
  have hb_le_n : b ≤ n := by omega
  have hn_eq : n = b + j := by
    simp [j, Nat.add_sub_of_le hb_le_n]
  have hjlo : 2 ≤ j := by omega
  have hjhi : j ≤ 2 * h + 2 := by omega
  have hjdvdF : j ∣ fixedBankObstructionFactorial h := by
    simpa [fixedBankObstructionFactorial] using Nat.dvd_factorial (by omega) hjhi
  have hjdvdb : j ∣ b := by
    exact dvd_mul_of_dvd_right hjdvdF k
  have hjdvdn : j ∣ n := by
    rw [hn_eq]
    exact dvd_add hjdvdb (dvd_refl j)
  have hjlt : j < n := by omega
  exact Nat.not_prime_of_dvd_of_lt hjdvdn hjlo hjlt

/-- The canonical fixed bank is empty of primes at every constructed scale. -/
theorem fixedBankObstruction_bankTerm_eq_zero
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Goldbach.BG_Bank.wX (fixedBankObstructionScale Goldbach.BG_Bank.H k) n
        * Goldbach.BG_Bank.Λ n = 0 := by
  by_cases hn : n ∈ Finset.Icc
      (fixedBankObstructionScale Goldbach.BG_Bank.H k / 2 - Goldbach.BG_Bank.H)
      (fixedBankObstructionScale Goldbach.BG_Bank.H k / 2 + Goldbach.BG_Bank.H)
  · have hnp : ¬ Nat.Prime n :=
      not_prime_of_mem_fixedBankObstructionInterval hk hn
    simp [Goldbach.BG_Bank.Λ, hnp]
  · unfold Goldbach.BG_Bank.wX
    rw [if_neg hn]
    simp

/-- Empty canonical fixed banks occur beyond every prescribed scale. -/
theorem exists_empty_fixedBank_scale_ge (B : ℕ) :
    ∃ X : ℕ, B ≤ X ∧
      ∀ n : ℕ, Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n = 0 := by
  let k := B + 1
  have hk : 0 < k := by omega
  have hfactorial : 1 ≤ fixedBankObstructionFactorial Goldbach.BG_Bank.H := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.factorial_pos _))
  have hmul : B + 1 ≤ (B + 1) * fixedBankObstructionFactorial Goldbach.BG_Bank.H := by
    have h := Nat.mul_le_mul_left (B + 1) hfactorial
    simpa using h
  refine ⟨fixedBankObstructionScale Goldbach.BG_Bank.H k, ?_, ?_⟩
  · dsimp [fixedBankObstructionScale, fixedBankObstructionCenter, k]
    omega
  · intro n
    exact fixedBankObstruction_bankTerm_eq_zero hk n

/-- The exact prime-bank coefficient vanishes at every index on a counterexample scale. -/
theorem fixedBankObstruction_aTerm_eq_zero
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
      (fixedBankObstructionScale Goldbach.BG_Bank.H k) n = 0 := by
  change ((Goldbach.BG_Bank.wX (fixedBankObstructionScale Goldbach.BG_Bank.H k) n
    * Goldbach.BG_Bank.Λ n : ℝ) : ℂ) = 0
  rw [fixedBankObstruction_bankTerm_eq_zero hk n]
  norm_num

/-- Every exact minor coefficient vanishes when every bank coefficient vanishes. -/
theorem weightedMinorCoeff_eq_zero_of_aTerm_eq_zero
    {X : ℕ}
    (ha : ∀ n : ℕ, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n = 0)
    (N : ℕ) (t : ℤ) :
    weightedMinorCoeff X N t = 0 := by
  unfold weightedMinorCoeff coeff atom
  simp [ha]

/-- The exact route-visible scalar vanishes whenever every bank coefficient vanishes. -/
theorem routeVisibleScalar_eq_zero_of_aTerm_eq_zero
    {X : ℕ}
    (ha : ∀ n : ℕ, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n = 0)
    (N : ℕ) :
    routeVisibleScalar X N = 0 := by
  have hcoeff (t : ℤ) :
      weightedMinorCoeff X N t = 0 :=
    weightedMinorCoeff_eq_zero_of_aTerm_eq_zero ha N t
  unfold routeVisibleScalar routeVisibleValue routeVisibleZeroCoeff
  unfold familySliceSumOn meanChannelSlice
  rw [sum_meanChannelOn_eq_sum]
  rw [hcoeff 0]
  have hsum :
      (∑ t ∈ Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X,
        weightedMinorCoeff X N t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact hcoeff t
  rw [hsum, add_zero]

/-- On an empty bank, the exact residual cancels the frozen `G + SS` model. -/
theorem frozenModel_cancels_on_empty_bank
    {X N : ℕ}
    (ha : ∀ n : ℕ, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n = 0) :
    G_formula X N + R_formula X N = -SS_formula X N := by
  have hdecomp := routeVisibleScalar_eq_G_formula_add_SS_formula_add_R_formula X N
  rw [routeVisibleScalar_eq_zero_of_aTerm_eq_zero ha N] at hdecomp
  linear_combination -hdecomp

/-- A pointwise-zero route-visible scalar has zero band-limited statistic. -/
theorem routeABandLimitedStatistic_eq_zero_of_routeVisibleScalar_eq_zero
    {X : ℕ} (K : ℤ → ℝ) (y : ℕ)
    (hvisible : ∀ N : ℕ, routeVisibleScalar X N = 0) :
    routeABandLimitedStatistic K X y = 0 := by
  unfold routeABandLimitedStatistic
  apply Finset.sum_eq_zero
  intro N hN
  rw [hvisible N]
  simp

/-- The canonical counterexample scales lie above `X0`. -/
theorem fixedBankObstructionScale_ge_X0
    {k : ℕ} (hk : 0 < k) :
    X0 ≤ fixedBankObstructionScale Goldbach.BG_Bank.H k := by
  have hfac : Nat.factorial 10 ≤ fixedBankObstructionFactorial Goldbach.BG_Bank.H := by
    exact Nat.factorial_le (by norm_num [Goldbach.BG_Bank.H, Goldbach.BankParams.H])
  have hkfac : Nat.factorial 10 ≤ k * fixedBankObstructionFactorial Goldbach.BG_Bank.H := by
    calc
      Nat.factorial 10 ≤ fixedBankObstructionFactorial Goldbach.BG_Bank.H := hfac
      _ = 1 * fixedBankObstructionFactorial Goldbach.BG_Bank.H := by simp
      _ ≤ k * fixedBankObstructionFactorial Goldbach.BG_Bank.H := by
        exact Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
  have hhalfMillion : 500000 ≤ k * fixedBankObstructionFactorial Goldbach.BG_Bank.H := by
    norm_num [Nat.factorial] at hkfac ⊢
    exact le_trans (by norm_num) hkfac
  norm_num [X0, Goldbach.BankParams.X0, fixedBankObstructionScale,
    fixedBankObstructionCenter, Goldbach.BG_Bank.H, Goldbach.BankParams.H] at hhalfMillion ⊢
  omega

/-- The exact route-visible window sum vanishes on every counterexample scale. -/
theorem fixedBankObstruction_routeVisibleWindowSum_eq_zero
    {k : ℕ} (hk : 0 < k) :
    Finset.sum (EvenIn (fixedBankObstructionScale Goldbach.BG_Bank.H k) H)
      (fun N => (routeVisibleScalar
        (fixedBankObstructionScale Goldbach.BG_Bank.H k) N).re) = 0 := by
  apply Finset.sum_eq_zero
  intro N hN
  rw [routeVisibleScalar_eq_zero_of_aTerm_eq_zero
    (fun n => fixedBankObstruction_aTerm_eq_zero hk n) N]
  rfl

/--
The exact PSB source sum cannot have a strictly positive lower profile for every `X >= X0` with
the current fixed-width bank.
-/
theorem no_uniformly_positive_routeVisibleWindowMean :
    ¬ ∃ M : ℕ → ℝ,
        (∀ {X : ℕ}, X0 ≤ X →
          M X ≤ Finset.sum (EvenIn X H) (fun N => (routeVisibleScalar X N).re))
          ∧ (∀ {X : ℕ}, X0 ≤ X → 0 < M X) := by
  rintro ⟨M, hmean, hpos⟩
  let X := fixedBankObstructionScale Goldbach.BG_Bank.H 1
  have hX : X0 ≤ X := by
    simpa [X] using fixedBankObstructionScale_ge_X0 (k := 1) (by norm_num)
  have hbound := hmean hX
  have hzero : Finset.sum (EvenIn X H) (fun N => (routeVisibleScalar X N).re) = 0 := by
    simpa [X] using fixedBankObstruction_routeVisibleWindowSum_eq_zero (k := 1) (by norm_num)
  rw [hzero] at hbound
  exact (not_lt_of_ge hbound) (hpos hX)

end

end Goldbach.Cert.MajorArcModules.RouteAFixedBankObstruction
