import Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrection
import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion

/-!
# Sharp arithmetic bound for induced-character corrections

The older correction bound counts every possible prime power separately and then bounds the
underlying prime by the modulus.  For the signed-conductor Type-I route that is unnecessarily
expensive.  This module instead groups prime powers by their unique base prime.  The von Mangoldt
mass contributed by all powers of one prime up to `x` is at most `log x`, and only the distinct
prime divisors of the level can occur.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrection
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor

noncomputable section

/-- Positive powers of `p` whose exponent is small enough for the value to be at most `x`. -/
def primePowersOfUpTo (p x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.log p x)).image fun k => p ^ k

/-- The candidate prime-power set has at most `log_p x` elements. -/
theorem card_primePowersOfUpTo_le (p x : ℕ) :
    (primePowersOfUpTo p x).card ≤ Nat.log p x := by
  unfold primePowersOfUpTo
  calc
    ((Finset.Icc 1 (Nat.log p x)).image fun k => p ^ k).card ≤
        (Finset.Icc 1 (Nat.log p x)).card :=
      Finset.card_image_le
    _ = Nat.log p x := by simp

/-- All von Mangoldt mass on powers of one prime up to `x` is at most `log x`. -/
theorem sum_primePowersOfUpTo_vonMangoldt_le_log
    {p x : ℕ} (hp : p.Prime) :
    (∑ n ∈ primePowersOfUpTo p x, ΛVM n) ≤ Real.log (x : ℝ) := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [primePowersOfUpTo]
  have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hterm : ∀ n ∈ primePowersOfUpTo p x, ΛVM n ≤ Real.log (p : ℝ) := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hkPos : 0 < k := (Finset.mem_Icc.mp hk).1
    simp [ΛVM, ArithmeticFunction.vonMangoldt_apply_pow hkPos.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hcard : ((primePowersOfUpTo p x).card : ℝ) ≤ Nat.log p x := by
    exact_mod_cast card_primePowersOfUpTo_le p x
  have hpow : p ^ Nat.log p x ≤ x := Nat.pow_log_le_self p hx
  have hlogPow :
      (Nat.log p x : ℝ) * Real.log (p : ℝ) ≤ Real.log (x : ℝ) := by
    have hpowPos : 0 < p ^ Nat.log p x := Nat.pow_pos hp.pos
    have hpowRealPos : 0 < ((p ^ Nat.log p x : ℕ) : ℝ) := by
      exact_mod_cast hpowPos
    have hpowReal : ((p ^ Nat.log p x : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast hpow
    have h := Real.log_le_log hpowRealPos hpowReal
    simpa [Nat.cast_pow, Real.log_pow] using h
  calc
    (∑ n ∈ primePowersOfUpTo p x, ΛVM n) ≤
        ∑ _n ∈ primePowersOfUpTo p x, Real.log (p : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ((primePowersOfUpTo p x).card : ℝ) * Real.log (p : ℝ) := by simp
    _ ≤ (Nat.log p x : ℝ) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hcard hlogp_nonneg
    _ ≤ Real.log (x : ℝ) := hlogPow

/-- Prime-power indices up to `x` whose base prime divides `q`. -/
def badPrimePowersUpTo (x q : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun n => ¬Nat.Coprime n q ∧ IsPrimePow n

/-- A bad prime power has its unique base prime among the prime divisors of the level. -/
theorem minFac_mem_primeFactors_of_mem_badPrimePowersUpTo
    {x q n : ℕ} (hq : 0 < q) (hn : n ∈ badPrimePowersUpTo x q) :
    n.minFac ∈ q.primeFactors := by
  have hnData := Finset.mem_filter.mp hn
  have hbad : ¬Nat.Coprime n q := hnData.2.1
  have hnpp : IsPrimePow n := hnData.2.2
  rcases hnpp with ⟨p, k, hp, hk, hnEq⟩
  have hpPrime : p.Prime := Nat.prime_iff.mpr hp
  have hpq : p ∣ q := by
    rcases (Nat.Prime.not_coprime_iff_dvd.mp hbad) with ⟨r, hr, hrn, hrq⟩
    have hrp : r ∣ p := by
      apply hr.dvd_of_dvd_pow
      exact hnEq.symm ▸ hrn
    have hrEq : r = p := (Nat.prime_dvd_prime_iff_eq hr hpPrime).mp hrp
    simpa [hrEq] using hrq
  have hminFac : n.minFac = p := by
    rw [← hnEq, hpPrime.pow_minFac hk.ne']
  rw [hminFac]
  exact Nat.mem_primeFactors.mpr ⟨hpPrime, hpq, hq.ne'⟩

/-- Each minimum-prime fiber of the bad set lies in the corresponding power set. -/
theorem badPrimePowers_minFacFiber_subset
    {x q p : ℕ} (hp : p.Prime) :
    (badPrimePowersUpTo x q).filter (fun n => n.minFac = p) ⊆
      primePowersOfUpTo p x := by
  intro n hn
  have hnOuter := Finset.mem_filter.mp hn
  have hnBad := Finset.mem_filter.mp hnOuter.1
  have hnLe : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnBad.1)
  have hnpp : IsPrimePow n := hnBad.2.2
  have hminFac : n.minFac = p := hnOuter.2
  let k := n.factorization n.minFac
  have hkPos : 0 < k :=
    Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero hnpp.one_lt)
  have hpow : p ^ k = n := by
    rw [← hminFac]
    exact hnpp.minFac_pow_factorization_eq
  have hkLog : k ≤ Nat.log p x := by
    apply Nat.le_log_of_pow_le hp.one_lt
    exact hpow.le.trans hnLe
  exact Finset.mem_image.mpr
    ⟨k, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hkPos.ne', hkLog⟩, hpow⟩

/-- The bad von Mangoldt mass is bounded by one `log x` for each prime divisor of `q`. -/
theorem sum_badPrimePowersUpTo_vonMangoldt_le
    {x q : ℕ} (hq : 0 < q) :
    (∑ n ∈ badPrimePowersUpTo x q, ΛVM n) ≤
      (q.primeFactors.card : ℝ) * Real.log (x : ℝ) := by
  classical
  have hMinFac : ∀ n ∈ badPrimePowersUpTo x q, n.minFac ∈ q.primeFactors :=
    fun n hn => minFac_mem_primeFactors_of_mem_badPrimePowersUpTo hq hn
  have hFilter :
      (badPrimePowersUpTo x q).filter (fun n => n.minFac ∈ q.primeFactors) =
        badPrimePowersUpTo x q :=
    Finset.filter_eq_self.mpr hMinFac
  calc
    (∑ n ∈ badPrimePowersUpTo x q, ΛVM n) =
        ∑ n ∈ (badPrimePowersUpTo x q).filter
          (fun n => n.minFac ∈ q.primeFactors), ΛVM n := by
      rw [hFilter]
    _ = ∑ p ∈ q.primeFactors,
          ∑ n ∈ (badPrimePowersUpTo x q).filter (fun n => n.minFac = p), ΛVM n :=
      (Finset.sum_fiberwise_eq_sum_filter
        (badPrimePowersUpTo x q) q.primeFactors Nat.minFac ΛVM).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log (x : ℝ) := by
      apply Finset.sum_le_sum
      intro p hpq
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (badPrimePowers_minFacFiber_subset (q := q) hp)
        (fun n _hn _hnot => ArithmeticFunction.vonMangoldt_nonneg)).trans
          (sum_primePowersOfUpTo_vonMangoldt_le_log hp)
    _ = (q.primeFactors.card : ℝ) * Real.log (x : ℝ) := by simp

/-- The correction mass is exactly the bad prime-power mass. -/
theorem inducedCharacterCorrectionMass_eq_badPrimePowers
    (x q : ℕ) :
    inducedCharacterCorrectionMass x q =
      ∑ n ∈ badPrimePowersUpTo x q, ΛVM n := by
  classical
  unfold inducedCharacterCorrectionMass badPrimePowersUpTo
  have habs : ∀ n : ℕ, |ΛVM n| = ΛVM n := by
    intro n
    exact abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg
  calc
    (∑ n ∈ Finset.range (x + 1), if ¬Nat.Coprime n q then |ΛVM n| else 0) =
        ∑ n ∈ Finset.range (x + 1),
          if ¬Nat.Coprime n q ∧ IsPrimePow n then ΛVM n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hcop : Nat.Coprime n q
      · simp [hcop]
      · by_cases hnpp : IsPrimePow n
        · simp [hcop, hnpp, habs]
        · have hz : ΛVM n = 0 := by
            simpa [ΛVM] using ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnpp
          simp [hcop, hnpp, hz]
    _ = ∑ n ∈ (Finset.range (x + 1)).filter
          (fun n => ¬Nat.Coprime n q ∧ IsPrimePow n), ΛVM n := by
      rw [Finset.sum_filter]

/-- Sharp bad-mass bound in terms of the number of distinct prime divisors. -/
theorem inducedCharacterCorrectionMass_le_primeFactors
    {x q : ℕ} (hq : 0 < q) :
    inducedCharacterCorrectionMass x q ≤
      (q.primeFactors.card : ℝ) * Real.log (x : ℝ) := by
  rw [inducedCharacterCorrectionMass_eq_badPrimePowers]
  exact sum_badPrimePowersUpTo_vonMangoldt_le hq

/-- The number of distinct prime divisors is at most `log q / log 2`. -/
theorem primeFactors_card_le_log_div_log_two
    {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have htwoPow : 2 ^ q.primeFactors.card ≤ q := by
    calc
      2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
        apply Finset.pow_card_le_prod
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog :
      (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
    have hpowPos : 0 < 2 ^ q.primeFactors.card := by positivity
    have hpowRealPos : 0 < (((2 : ℕ) ^ q.primeFactors.card : ℕ) : ℝ) := by
      exact_mod_cast hpowPos
    have htwoPowReal : (((2 : ℕ) ^ q.primeFactors.card : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast htwoPow
    have h := Real.log_le_log hpowRealPos htwoPowReal
    simpa [Nat.cast_pow, Real.log_pow] using h
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

/-- The sharp elementary correction-mass estimate used by the signed-conductor reduction. -/
theorem inducedCharacterCorrectionMass_le_log_div_log_two
    {x q : ℕ} (hq : 0 < q) :
    inducedCharacterCorrectionMass x q ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log (x : ℝ) := by
  calc
    inducedCharacterCorrectionMass x q ≤
        (q.primeFactors.card : ℝ) * Real.log (x : ℝ) :=
      inducedCharacterCorrectionMass_le_primeFactors hq
    _ ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log (x : ℝ) := by
      have hlogx : 0 ≤ Real.log (x : ℝ) := by
        rcases x with _ | x
        · simp
        · exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos x)
      exact mul_le_mul_of_nonneg_right (primeFactors_card_le_log_div_log_two hq)
        hlogx

/-- The exact induced-character correction inherits the sharp distinct-prime bound. -/
theorem norm_inducedCharacterCorrection_le_log_div_log_two
    {x q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) :
    ‖RouteADirichletCharacterExpansion.inducedCharacterCorrection x q χ‖ ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log (x : ℝ) :=
  (norm_inducedCharacterCorrection_le_mass x q χ).trans
    (inducedCharacterCorrectionMass_le_log_div_log_two hq)

/-- One active occurrence's induced-character correction, with its signed logarithmic weight. -/
noncomputable def activeCharacterOccurrenceInducedCorrectionTerm
    (N p : ℕ) (occurrence : CharacterOccurrence) : ℂ :=
  (activeCharacterOccurrenceCoefficient N p occurrence : ℂ) *
    occurrence.2 ((N : ZMod occurrence.1)⁻¹) *
      activeInducedCharacterPointCorrection p occurrence

/-- A fiber correction is the sum of its occurrence-level corrections. -/
theorem activePrimitiveCharacterFiberInducedCorrectionAt_eq_occurrenceSum
    (N u p : ℕ) (key : PrimitiveCharacterKey) :
    activePrimitiveCharacterFiberInducedCorrectionAt N u p key =
      ∑ occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key,
        activeCharacterOccurrenceInducedCorrectionTerm N p occurrence := by
  classical
  unfold activePrimitiveCharacterFiberInducedCorrectionAt
    activeCharacterOccurrenceInducedCorrectionTerm
  apply Finset.sum_congr rfl
  intro occurrence hOccurrence
  rw [activeOccurrence_inv_eq_key_inv hOccurrence]

/-- Total induced-character correction at one active prime index. -/
noncomputable def activePrimitiveCharacterTotalInducedCorrectionAt
    (N u p : ℕ) : ℂ :=
  ∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
    activePrimitiveCharacterFiberInducedCorrectionAt N u p key

/-- The pointwise total correction is the corresponding sum over all active occurrences. -/
theorem activePrimitiveCharacterTotalInducedCorrectionAt_eq_occurrenceSum
    (N u p : ℕ) :
    activePrimitiveCharacterTotalInducedCorrectionAt N u p =
      ∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
        activeCharacterOccurrenceInducedCorrectionTerm N p occurrence := by
  classical
  unfold activePrimitiveCharacterTotalInducedCorrectionAt
  calc
    (∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
        activePrimitiveCharacterFiberInducedCorrectionAt N u p key) =
        ∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
          ∑ occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key,
            activeCharacterOccurrenceInducedCorrectionTerm N p occurrence := by
      apply Finset.sum_congr rfl
      intro key hKey
      exact activePrimitiveCharacterFiberInducedCorrectionAt_eq_occurrenceSum N u p key
    _ = ∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
          activeCharacterOccurrenceInducedCorrectionTerm N p occurrence :=
      (sum_activeCharacterOccurrences_eq_sum_primitiveCharacterFibers
        N u p (activeCharacterOccurrenceInducedCorrectionTerm N p)).symm

/-- The point correction is bounded by its bad-coprimality von Mangoldt mass. -/
theorem norm_activeInducedCharacterPointCorrection_le
    (p : ℕ) (occurrence : CharacterOccurrence) :
    ‖activeInducedCharacterPointCorrection p occurrence‖ ≤
      if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0 := by
  unfold activeInducedCharacterPointCorrection
  by_cases hcop : Nat.Coprime p occurrence.1
  · simp [hcop]
  · simp only [hcop, if_false, not_false_eq_true, if_true, norm_mul]
    rw [show ‖(ΛVM p : ℂ)‖ = |ΛVM p| by exact Complex.norm_real (ΛVM p)]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (DirichletCharacter.norm_le_one occurrence.2.primitiveCharacter _)

/-- One active occurrence retains the exact logarithmic coefficient in its correction bound. -/
theorem norm_activeCharacterOccurrenceInducedCorrectionTerm_le
    (N p : ℕ) (occurrence : CharacterOccurrence) :
    ‖activeCharacterOccurrenceInducedCorrectionTerm N p occurrence‖ ≤
      |activeCharacterOccurrenceCoefficient N p occurrence| *
        (if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0) := by
  unfold activeCharacterOccurrenceInducedCorrectionTerm
  rw [norm_mul, norm_mul]
  have hInv := DirichletCharacter.norm_le_one occurrence.2
    ((N : ZMod occurrence.1)⁻¹)
  have hCorrection := norm_activeInducedCharacterPointCorrection_le p occurrence
  have hCoefficient :
      ‖(activeCharacterOccurrenceCoefficient N p occurrence : ℂ)‖ =
        |activeCharacterOccurrenceCoefficient N p occurrence| :=
    Complex.norm_real _
  rw [hCoefficient]
  calc
    |activeCharacterOccurrenceCoefficient N p occurrence| *
          ‖occurrence.2 ((N : ZMod occurrence.1)⁻¹)‖ *
          ‖activeInducedCharacterPointCorrection p occurrence‖ ≤
        |activeCharacterOccurrenceCoefficient N p occurrence| * 1 *
          (if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0) := by
      gcongr
    _ = |activeCharacterOccurrenceCoefficient N p occurrence| *
          (if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0) := by ring

/-- The norm of the pointwise total correction is bounded occurrence by occurrence. -/
theorem norm_activePrimitiveCharacterTotalInducedCorrectionAt_le_occurrences
    (N u p : ℕ) :
    ‖activePrimitiveCharacterTotalInducedCorrectionAt N u p‖ ≤
      ∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
        |activeCharacterOccurrenceCoefficient N p occurrence| *
          (if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0) := by
  rw [activePrimitiveCharacterTotalInducedCorrectionAt_eq_occurrenceSum]
  calc
    ‖∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
        activeCharacterOccurrenceInducedCorrectionTerm N p occurrence‖ ≤
        ∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
          ‖activeCharacterOccurrenceInducedCorrectionTerm N p occurrence‖ :=
      norm_sum_le _ _
    _ ≤ ∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
        |activeCharacterOccurrenceCoefficient N p occurrence| *
          (if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0) := by
      apply Finset.sum_le_sum
      intro occurrence hOccurrence
      exact norm_activeCharacterOccurrenceInducedCorrectionTerm_le N p occurrence

/-- Summing all level characters cancels the exact `1 / φ(d)` normalization. -/
theorem sum_activeOccurrenceCorrectionMajorant_le_moduli
    (N u p : ℕ) :
    (∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
        |activeCharacterOccurrenceCoefficient N p occurrence| *
          (if ¬Nat.Coprime p occurrence.1 then |ΛVM p| else 0)) ≤
      ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
        Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
          (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
  classical
  unfold activeCharacterOccurrencesAt
  rw [Finset.sum_sigma]
  apply Finset.sum_le_sum
  intro d hd
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdPos : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdInner.1).1
  have hdLe : d ≤ N - p := hdOuter.2
  have hpN : p ≤ N := by omega
  have hCastSub : ((N - p : ℕ) : ℝ) = (N : ℝ) - (p : ℝ) := by
    exact Nat.cast_sub hpN
  have hdRealPos : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hRatio :
      (1 : ℝ) ≤ ((N : ℝ) - (p : ℝ)) / (d : ℝ) := by
    rw [← hCastSub]
    apply (le_div_iff₀ hdRealPos).2
    simpa using (show (d : ℝ) ≤ ((N - p : ℕ) : ℝ) by exact_mod_cast hdLe)
  have hLog : 0 ≤ Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) :=
    Real.log_nonneg hRatio
  have hTotient : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hdPos
  have hMoebius :
      |(((ArithmeticFunction.moebius d : ℤ) : ℝ))| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hCoefficient (χ : DirichletCharacter ℂ d) :
      |activeCharacterOccurrenceCoefficient N p
          (⟨d, χ⟩ : CharacterOccurrence)| ≤
        Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) /
          (Nat.totient d : ℝ) := by
    unfold activeCharacterOccurrenceCoefficient
    change
      |(((ArithmeticFunction.moebius d : ℤ) : ℝ)) /
          (Nat.totient d : ℝ) *
            Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ))| ≤ _
    rw [abs_mul, abs_div, abs_of_pos hTotient, abs_of_nonneg hLog]
    calc
      |(((ArithmeticFunction.moebius d : ℤ) : ℝ))| /
            (Nat.totient d : ℝ) *
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) ≤
          1 / (Nat.totient d : ℝ) *
            Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) := by
        gcongr
      _ = Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) /
          (Nat.totient d : ℝ) := by ring
  letI : NeZero d := ⟨hdPos.ne'⟩
  have hcard : Nat.card (DirichletCharacter ℂ d) = Nat.totient d :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  calc
    (∑ χ : DirichletCharacter ℂ d,
        |activeCharacterOccurrenceCoefficient N p
          (⟨d, χ⟩ : CharacterOccurrence)| *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0)) ≤
        ∑ _χ : DirichletCharacter ℂ d,
          (Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) /
            (Nat.totient d : ℝ)) *
              (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact mul_le_mul_of_nonneg_right (hCoefficient χ) (by split_ifs <;> positivity)
    _ = Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
          (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, hcard]
      field_simp

/-- Pointwise active induced corrections are controlled by one bad-prime term per modulus. -/
theorem norm_activePrimitiveCharacterTotalInducedCorrectionAt_le_moduli
    (N u p : ℕ) :
    ‖activePrimitiveCharacterTotalInducedCorrectionAt N u p‖ ≤
      ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
        Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
          (if ¬Nat.Coprime p d then |ΛVM p| else 0) :=
  (norm_activePrimitiveCharacterTotalInducedCorrectionAt_le_occurrences N u p).trans
    (sum_activeOccurrenceCorrectionMajorant_le_moduli N u p)

/-- On active support, the logarithmic quotient is at most `log N`. -/
theorem active_log_weight_le_log_center
    {N u p d : ℕ} (hN : 0 < N)
    (hd : d ∈ activeCoprimeTypeIModuliAt N u p) :
    Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) ≤ Real.log (N : ℝ) := by
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdPos : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdInner.1).1
  have hdLe : d ≤ N - p := hdOuter.2
  have hpN : p ≤ N := by omega
  have hdRealPos : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hNRealPos : (0 : ℝ) < N := by exact_mod_cast hN
  have hSubNonneg : (0 : ℝ) ≤ (N : ℝ) - (p : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hpN)
  have hRatioPos :
      (0 : ℝ) < ((N : ℝ) - (p : ℝ)) / (d : ℝ) := by
    have hSubPosNat : 0 < N - p := lt_of_lt_of_le hdPos hdLe
    have hSubPos : (0 : ℝ) < (N : ℝ) - (p : ℝ) := by
      rw [← Nat.cast_sub hpN]
      exact_mod_cast hSubPosNat
    positivity
  have hRatioLe :
      ((N : ℝ) - (p : ℝ)) / (d : ℝ) ≤ (N : ℝ) := by
    apply (div_le_iff₀ hdRealPos).2
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPos
    nlinarith
  exact Real.log_le_log hRatioPos hRatioLe

/-- Total active induced-character correction over the balanced support. -/
noncomputable def activePrimitiveCharacterTotalInducedCorrection
    (L N u : ℕ) : ℂ :=
  ∑ p ∈ balancedCandidateSupport L N,
    activePrimitiveCharacterTotalInducedCorrectionAt N u p

/-- Primitive-character main obtained after the active conductor regrouping. -/
noncomputable def activePrimitiveCharacterTotalMain
    (L N u : ℕ) : ℂ :=
  ∑ p ∈ balancedCandidateSupport L N,
    ∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
      key.2 ((N : ZMod key.1)⁻¹) *
        ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
          (activePrimitiveCharacterFiberWeightAt N u p key : ℂ)

/-- Linear comparison term subtracted by the active character expansion. -/
noncomputable def activeCharacterLinearTotal
    (L N u : ℕ) : ℂ :=
  ∑ p ∈ balancedCandidateSupport L N,
    (activeCharacterLinearMainAt N u p : ℂ)

/--
Exact global primitive-character reduction of the active coprime Type-I progression error.
No character estimate or conductor-lift completeness theorem is used here.
-/
theorem activeCoprimeProgressionError_cast_eq_primitiveMain_sub_corrections
    {L N u : ℕ} (hL : 0 < L) :
    (balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ) =
      activePrimitiveCharacterTotalMain L N u
        - activePrimitiveCharacterTotalInducedCorrection L N u
        - activeCharacterLinearTotal L N u := by
  rw [activeCoprimeProgressionError_cast_eq_primitiveCharacterFibers hL]
  unfold activePrimitiveCharacterTotalMain
    activePrimitiveCharacterTotalInducedCorrection
    activePrimitiveCharacterTotalInducedCorrectionAt
    activeCharacterLinearTotal
  simp_rw [activePrimitiveCharacterFiberContributionAt_eq_main_sub_inducedCorrection]
  simp_rw [Finset.sum_sub_distrib]

/-- The global correction is bounded by its active pointwise modulus majorant. -/
theorem norm_activePrimitiveCharacterTotalInducedCorrection_le_pointwise
    (L N u : ℕ) :
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
      ∑ p ∈ balancedCandidateSupport L N,
        ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
  unfold activePrimitiveCharacterTotalInducedCorrection
  calc
    ‖∑ p ∈ balancedCandidateSupport L N,
        activePrimitiveCharacterTotalInducedCorrectionAt N u p‖ ≤
        ∑ p ∈ balancedCandidateSupport L N,
          ‖activePrimitiveCharacterTotalInducedCorrectionAt N u p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ balancedCandidateSupport L N,
        ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_activePrimitiveCharacterTotalInducedCorrectionAt_le_moduli N u p

/-- Finite Fubini exchange for the active correction majorant. -/
theorem activeCorrectionMajorant_sum_comm
    (L N u : ℕ) :
    (∑ p ∈ balancedCandidateSupport L N,
        ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0)) =
      ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
        ∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
  unfold activeCoprimeTypeIModuliAt
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcop : Nat.Coprime N d <;> simp [hcop]

/-- The balanced active support at a fixed modulus lies in the endpoint interval `[0, N]`. -/
theorem activeBalancedSupport_subset_range
    (L N d : ℕ) :
    (balancedCandidateSupport L N).filter (fun p => d ≤ N - p) ⊆
      Finset.range (N + 1) := by
  intro p hp
  have hpSupport := (Finset.mem_filter.mp hp).1
  have hpBounds := Finset.mem_Icc.mp hpSupport
  have hpN : p ≤ N := hpBounds.2.trans (Nat.sub_le N L)
  exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpN)

/-- One modulus contributes at most `log N` times its bad-prime mass. -/
theorem activeCorrectionMajorantAtModulus_le_mass
    {L N u d : ℕ} (hN : 0 < N)
    (hd : d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N)) :
    (∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
        Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
          (if ¬Nat.Coprime p d then |ΛVM p| else 0)) ≤
      Real.log (N : ℝ) * inducedCharacterCorrectionMass N d := by
  have hLogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hWeighted :
      (∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0)) ≤
        ∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          Real.log (N : ℝ) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    have hdActive : d ∈ activeCoprimeTypeIModuliAt N u p :=
      Finset.mem_filter.mpr ⟨hd, (Finset.mem_filter.mp hp).2⟩
    exact mul_le_mul_of_nonneg_right (active_log_weight_le_log_center hN hdActive)
      (by split_ifs <;> positivity)
  have hMass :
      (∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          (if ¬Nat.Coprime p d then |ΛVM p| else 0)) ≤
        inducedCharacterCorrectionMass N d := by
    unfold inducedCharacterCorrectionMass
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (activeBalancedSupport_subset_range L N d)
      (fun p _hpRange _hpOutside => by split_ifs <;> positivity)
  calc
    (∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
        Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
          (if ¬Nat.Coprime p d then |ΛVM p| else 0)) ≤
        ∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          Real.log (N : ℝ) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0) := hWeighted
    _ = Real.log (N : ℝ) *
        ∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          (if ¬Nat.Coprime p d then |ΛVM p| else 0) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log (N : ℝ) * inducedCharacterCorrectionMass N d :=
      mul_le_mul_of_nonneg_left hMass hLogN

/-- Global active corrections are bounded by a finite sum of sharp modulus masses. -/
theorem norm_activePrimitiveCharacterTotalInducedCorrection_le_massSum
    {L N u : ℕ} (hN : 0 < N) :
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
      ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
        Real.log (N : ℝ) * inducedCharacterCorrectionMass N d := by
  calc
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
        ∑ p ∈ balancedCandidateSupport L N,
          ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
            Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
              (if ¬Nat.Coprime p d then |ΛVM p| else 0) :=
      norm_activePrimitiveCharacterTotalInducedCorrection_le_pointwise L N u
    _ = ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
        ∑ p ∈ (balancedCandidateSupport L N).filter (fun p => d ≤ N - p),
          Real.log (((N : ℝ) - (p : ℝ)) / (d : ℝ)) *
            (if ¬Nat.Coprime p d then |ΛVM p| else 0) :=
      activeCorrectionMajorant_sum_comm L N u
    _ ≤ ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
        Real.log (N : ℝ) * inducedCharacterCorrectionMass N d := by
      apply Finset.sum_le_sum
      intro d hd
      exact activeCorrectionMajorantAtModulus_le_mass hN hd

/-- Substituting the distinct-prime estimate gives a fully explicit finite modulus sum. -/
theorem norm_activePrimitiveCharacterTotalInducedCorrection_le_sharpSum
    {L N u : ℕ} (hN : 0 < N) :
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
      ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
        Real.log (N : ℝ) *
          ((Real.log (d : ℝ) / Real.log 2) * Real.log (N : ℝ)) := by
  have hLogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  calc
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
        ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
          Real.log (N : ℝ) * inducedCharacterCorrectionMass N d :=
      norm_activePrimitiveCharacterTotalInducedCorrection_le_massSum hN
    _ ≤ ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
        Real.log (N : ℝ) *
          ((Real.log (d : ℝ) / Real.log 2) * Real.log (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdIcc := (Finset.mem_filter.mp hd).1
      have hdPos : 0 < d :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
      exact mul_le_mul_of_nonneg_left
        (inducedCharacterCorrectionMass_le_log_div_log_two hdPos) hLogN

/--
Coarse closed form for the complete active induced-character correction.  It is logarithmic in
the arithmetic complexity of the moduli and linear in the Type-I cutoff.
-/
theorem norm_activePrimitiveCharacterTotalInducedCorrection_le
    {L N u : ℕ} (hN : 0 < N) (hu : 0 < u) :
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
      (u : ℝ) *
        (Real.log (N : ℝ) *
          ((Real.log (u : ℝ) / Real.log 2) * Real.log (N : ℝ))) := by
  let C : ℝ :=
    Real.log (N : ℝ) *
      ((Real.log (u : ℝ) / Real.log 2) * Real.log (N : ℝ))
  have hLogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hLogU : 0 ≤ Real.log (u : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hu)
  have hLogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hTerm : ∀ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
      Real.log (N : ℝ) *
          ((Real.log (d : ℝ) / Real.log 2) * Real.log (N : ℝ)) ≤ C := by
    intro d hd
    have hdIcc := (Finset.mem_filter.mp hd).1
    have hdBounds := Finset.mem_Icc.mp hdIcc
    have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdBounds.1
    have hLogDU : Real.log (d : ℝ) ≤ Real.log (u : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hdPos) (by exact_mod_cast hdBounds.2)
    dsimp [C]
    have hDiv : Real.log (d : ℝ) / Real.log 2 ≤
        Real.log (u : ℝ) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hLogTwo).2 hLogDU
    gcongr
  have hCard : ((Finset.Icc 1 u).filter (Nat.Coprime N)).card ≤ u := by
    calc
      ((Finset.Icc 1 u).filter (Nat.Coprime N)).card ≤
          (Finset.Icc 1 u).card := Finset.card_filter_le _ _
      _ = u := by simp [Nat.card_Icc]
  calc
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
        ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
          Real.log (N : ℝ) *
            ((Real.log (d : ℝ) / Real.log 2) * Real.log (N : ℝ)) :=
      norm_activePrimitiveCharacterTotalInducedCorrection_le_sharpSum hN
    _ ≤ ∑ _d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N), C := by
      apply Finset.sum_le_sum
      exact hTerm
    _ = (((Finset.Icc 1 u).filter (Nat.Coprime N)).card : ℝ) * C := by simp
    _ ≤ (u : ℝ) * C := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hC
    _ = (u : ℝ) *
        (Real.log (N : ℝ) *
          ((Real.log (u : ℝ) / Real.log 2) * Real.log (N : ℝ))) := rfl

end

end Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp
