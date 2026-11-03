import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface
import Goldbach.Cert.MajorArcStep4FullExpSum

/-!
# Elementary noncoprime correction for the balanced Vaughan Type-I term

The noncoprime fixed-center progressions contain only prime powers supported on primes dividing the
modulus. This module connects that observation to the explicit prime-power counting estimate already
proved in `MajorArcStep4FullExpSum`.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface

noncomputable section

/-- The unweighted von Mangoldt mass in one fixed-center residue progression. -/
noncomputable def noncoprimeResidueVonMangoldtMass
    (L N d : ℕ) : ℝ :=
  ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
    broadVonMangoldtWeight p

/--
The existing explicit bad-residue estimate controls the mass in each noncoprime fixed-center
progression. The bound is intentionally coarse but fully effective.
-/
theorem noncoprimeResidueVonMangoldtMass_le
    {L N d : ℕ} (hLN : L ≤ N) (hd : 1 ≤ d) (hNd : ¬Nat.Coprime N d) :
    noncoprimeResidueVonMangoldtMass L N d ≤
      (((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ) := by
  classical
  let target : ℕ → ℝ := fun p =>
    if ¬Nat.Coprime (p % d) d then |broadVonMangoldtWeight p| else 0
  have hsubset :
      balancedVaughanTypeIPrimeResidueSupport L N d ⊆ Finset.Ico L (N + 1) := by
    intro p hp
    have hpSupport := (Finset.mem_filter.mp hp).1
    have hpBounds := Finset.mem_Icc.mp hpSupport
    exact Finset.mem_Ico.mpr ⟨hpBounds.1, Nat.lt_succ_of_le
      (le_trans hpBounds.2 (Nat.sub_le N L))⟩
  have hterm {p : ℕ} (hp : p ∈ balancedVaughanTypeIPrimeResidueSupport L N d) :
      broadVonMangoldtWeight p = target p := by
    have hpcoprime : ¬Nat.Coprime p d :=
      not_coprime_of_mem_primeResidueSupport hp hNd
    have hpmod : ¬Nat.Coprime (p % d) d := by
      intro hcop
      exact hpcoprime
        (coprime_center_of_modEq_of_coprime (Nat.mod_modEq p d) hcop)
    have hnonneg := broadVonMangoldtWeight_nonneg p
    simp [target, hpmod, abs_of_nonneg hnonneg]
  calc
    noncoprimeResidueVonMangoldtMass L N d =
        ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d, target p := by
      unfold noncoprimeResidueVonMangoldtMass
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm hp
    _ ≤ ∑ p ∈ Finset.Ico L (N + 1), target p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _hp _ => by
        by_cases hcop : Nat.Coprime (p % d) d <;> simp [target, hcop])
    _ ≤ (((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ) := by
      simpa [target] using
        (Goldbach.Cert.MajorArcStep4FullExpSum.sum_Ico_bad_vonMangoldt_le
          (q := d) hd (L := L) (U := N) hLN)

/-- The logarithmic Type-I weight lies between zero and `log N` on its congruence support. -/
theorem log_fixedCenterQuotient_nonneg_and_le
    {L N d p : ℕ} (hL : 1 ≤ L) (hd : 1 ≤ d)
    (hp : p ∈ balancedVaughanTypeIPrimeResidueSupport L N d) :
    0 ≤ Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) ∧
      Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) ≤ Real.log (N : ℝ) := by
  have hpData := Finset.mem_filter.mp hp
  have hpBounds := Finset.mem_Icc.mp hpData.1
  have hpN : p ≤ N := le_trans hpBounds.2 (Nat.sub_le N L)
  have hgapPos : 0 < N - p := by omega
  have hdDvd : d ∣ N - p :=
    (Nat.modEq_iff_dvd' hpN).mp hpData.2
  have hdLeGap : d ≤ N - p := Nat.le_of_dvd hgapPos hdDvd
  have hdPosReal : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdLeGapReal : (d : ℝ) ≤ (N : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_sub hpN]
    exact_mod_cast hdLeGap
  have hratioOne : (1 : ℝ) ≤ ((N : ℝ) - (p : ℝ)) / (d : ℝ) :=
    (one_le_div₀ hdPosReal).2 hdLeGapReal
  have hgapNonneg : 0 ≤ (N : ℝ) - (p : ℝ) := sub_nonneg.mpr (by exact_mod_cast hpN)
  have hdOneReal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hratioLeGap : ((N : ℝ) - (p : ℝ)) / (d : ℝ) ≤ (N : ℝ) - (p : ℝ) :=
    div_le_self hgapNonneg hdOneReal
  have hgapLeN : (N : ℝ) - (p : ℝ) ≤ (N : ℝ) := by
    have hpNonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
    linarith
  exact ⟨Real.log_nonneg hratioOne,
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hratioOne)
      (hratioLeGap.trans hgapLeN)⟩

/-- The weighted contribution of one noncoprime modulus is controlled by its prime-power mass. -/
theorem abs_noncoprimeModulusContribution_le_mass_mul_log
    {L N d : ℕ} (hL : 1 ≤ L) (hd : 1 ≤ d) :
    |∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| ≤
      noncoprimeResidueVonMangoldtMass L N d * Real.log (N : ℝ) := by
  have hsumNonneg :
      0 ≤ ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) := by
    exact Finset.sum_nonneg fun p hp =>
      mul_nonneg (broadVonMangoldtWeight_nonneg p)
        (log_fixedCenterQuotient_nonneg_and_le hL hd hp).1
  rw [abs_of_nonneg hsumNonneg]
  calc
    (∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))) ≤
        ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
          broadVonMangoldtWeight p * Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (log_fixedCenterQuotient_nonneg_and_le hL hd hp).2
        (broadVonMangoldtWeight_nonneg p)
    _ = noncoprimeResidueVonMangoldtMass L N d * Real.log (N : ℝ) := by
      unfold noncoprimeResidueVonMangoldtMass
      rw [Finset.sum_mul]

/-- Fully explicit per-modulus bound for the logarithmically weighted noncoprime term. -/
theorem abs_noncoprimeModulusContribution_le
    {L N d : ℕ} (hL : 1 ≤ L) (hLN : L ≤ N)
    (hd : 1 ≤ d) (hNd : ¬Nat.Coprime N d) :
    |∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| ≤
      ((((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ)) *
        Real.log (N : ℝ) := by
  calc
    |∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| ≤
        noncoprimeResidueVonMangoldtMass L N d * Real.log (N : ℝ) :=
      abs_noncoprimeModulusContribution_le_mass_mul_log hL hd
    _ ≤ ((((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ)) *
        Real.log (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right
        (noncoprimeResidueVonMangoldtMass_le hLN hd hNd)
      exact Real.log_nonneg (by exact_mod_cast hLN.trans' hL)

/--
An explicit finite upper bound for the complete noncoprime Type-I correction.  Keeping the
modulus sum visible avoids replacing its arithmetic structure by an unnecessarily large cardinality
bound.
-/
noncomputable def balancedVaughanTypeINoncoprimeExplicitBound
    (N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (fun d => ¬Nat.Coprime N d),
    ((((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ)) *
      Real.log (N : ℝ)

/-- Summing the per-modulus estimate controls the exact noncoprime correction. -/
theorem abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
    {L N u : ℕ} (hL : 1 ≤ L) (hLN : L ≤ N) :
    |balancedVaughanTypeINoncoprimeProgressionContribution L N u| ≤
      balancedVaughanTypeINoncoprimeExplicitBound N u := by
  classical
  unfold balancedVaughanTypeINoncoprimeProgressionContribution
    balancedVaughanTypeINoncoprimeExplicitBound
  calc
    |∑ d ∈ (Finset.Icc 1 u).filter (fun d => ¬Nat.Coprime N d),
        ((moebius d : ℤ) : ℝ) *
          ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
            broadVonMangoldtWeight p * Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| ≤
        ∑ d ∈ (Finset.Icc 1 u).filter (fun d => ¬Nat.Coprime N d),
          |((moebius d : ℤ) : ℝ) *
            ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
              broadVonMangoldtWeight p *
                Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Finset.Icc 1 u).filter (fun d => ¬Nat.Coprime N d),
        ((((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ)) *
          Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro d hdMem
      have hdData := Finset.mem_filter.mp hdMem
      have hdOne : 1 ≤ d := (Finset.mem_Icc.mp hdData.1).1
      have hNd : ¬Nat.Coprime N d := hdData.2
      have hMoebius : |(((moebius d : ℤ) : ℝ))| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      rw [abs_mul]
      calc
        |(((moebius d : ℤ) : ℝ))| *
            |∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
              broadVonMangoldtWeight p *
                Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| ≤
            1 *
              (((((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ)) *
                Real.log (N : ℝ)) := by
          exact mul_le_mul hMoebius
            (abs_noncoprimeModulusContribution_le hL hLN hdOne hNd)
            (abs_nonneg _) zero_le_one
        _ = ((((d + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * Real.log (d : ℝ)) *
            Real.log (N : ℝ) := one_mul _

/--
The elementary prime-power estimate supplies the noncoprime half of the abstract Type-I
progression interface.  No parity hypothesis is needed for this half.
-/
theorem balancedVaughanTypeINoncoprimeProgressionBound_explicit
    {L Xmin : ℕ} (u : ℕ → ℕ) (hL : 1 ≤ L) (hLXmin : L ≤ Xmin) :
    BalancedVaughanTypeINoncoprimeProgressionBound
      L Xmin u (fun N => balancedVaughanTypeINoncoprimeExplicitBound N (u N)) := by
  refine ⟨?_⟩
  intro N hN _hEven
  exact abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
    hL (hLXmin.trans hN)

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime
