import Mathlib
import Goldbach.BankPieces.Cert.Projected
import Goldbach.AO_MajorSwapTenorAxiomsFunX
import Goldbach.Cert.SigmaUpperOnWindowCanon
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.SingularSeriesExtras
import Goldbach.Analytic.NumericSigma
import Goldbach.Cert.CanonLogBounds

namespace Goldbach.BankPieces.Cert.ProjectedInput

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.Singular
open Real

noncomputable section

private lemma oddFactor_le_self {p : ℕ} (hp : Nat.Prime p) (hne2 : p ≠ 2) :
    Goldbach.Singular.oddFactor p ≤ (p : ℝ) := by
  have hnum_nonneg : 0 ≤ (p - 1 : ℝ) := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    nlinarith
  have htwo_lt : 2 < p := lt_of_le_of_ne hp.two_le (by simpa using hne2.symm)
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt htwo_lt
  have hden_ge_one : (1 : ℝ) ≤ (p - 2 : ℝ) := by
    have h1le : (1 : ℝ) ≤ (p : ℝ) - 2 := by
      have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    simpa [Nat.cast_sub hp.two_le] using h1le
  have hdiv : Goldbach.Singular.oddFactor p ≤ (p - 1 : ℝ) := by
    simpa [Goldbach.Singular.oddFactor] using div_le_self hnum_nonneg hden_ge_one
  have hnum_le : (p - 1 : ℝ) ≤ (p : ℝ) := by
    nlinarith
  exact le_trans hdiv hnum_le

private lemma oddPrimeSupport_subset_primeFactors {n : ℕ} (hn : n ≠ 0) :
    Goldbach.Singular.oddPrimeSupport n ⊆ n.primeFactors := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_div, hp_odd⟩
  exact (Nat.mem_primeFactors).2 ⟨hp_odd.1, Nat.dvd_of_mem_divisors hp_div, hn⟩

private lemma prod_support_primes_le_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, p ≤ n := by
  have hsubset := oddPrimeSupport_subset_primeFactors hn
  have hdvd_subset :
      ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, p ∣ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_dvd_prod_of_subset
      (Goldbach.Singular.oddPrimeSupport n) n.primeFactors id hsubset
  have hdvd_n : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (dvd_trans hdvd_subset hdvd_n)

private lemma half_ne_zero_of_even_nonzero {n : ℕ} (he : Even n) (hn : n ≠ 0) :
    n / 2 ≠ 0 := by
  rcases he with ⟨m, hm⟩
  rw [hm]
  have hm0 : m ≠ 0 := by
    intro hm_zero
    apply hn
    simp [hm, hm_zero]
  have hhalf : (m + m) / 2 = m := by
    have : (2 * m) / 2 = m := by omega
    simpa [two_mul] using this
  rw [hhalf]
  exact hm0

private lemma oddPrimeSupport_subset_primeFactors_half {n : ℕ} (he : Even n) (hn : n ≠ 0) :
    Goldbach.Singular.oddPrimeSupport n ⊆ (n / 2).primeFactors := by
  rcases he with ⟨m, hm_even⟩
  rw [hm_even]
  have hm : m ≠ 0 := by
    intro hm0
    apply hn
    simp [hm_even, hm0]
  have hhalf : (m + m) / 2 = m := by
    have : (2 * m) / 2 = m := by omega
    simpa [two_mul] using this
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_div, hp_odd⟩
  have hp_prime : Nat.Prime p := hp_odd.1
  have hpdvd : p ∣ m + m := Nat.dvd_of_mem_divisors hp_div
  have hpm : p ∣ m := by
    have hpdvd' : p ∣ 2 * m := by simpa [two_mul] using hpdvd
    rcases hp_prime.dvd_mul.mp hpdvd' with hp2 | hpm
    · exfalso
      exact hp_odd.2 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).1 hp2)
    · exact hpm
  rw [hhalf]
  exact (Nat.mem_primeFactors).2 ⟨hp_prime, hpm, hm⟩

private lemma prod_support_primes_le_half {n : ℕ} (he : Even n) (hn : n ≠ 0) :
    ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, p ≤ n / 2 := by
  have hsubset := oddPrimeSupport_subset_primeFactors_half he hn
  have hdvd_subset :
      ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, p ∣ ∏ p ∈ (n / 2).primeFactors, p :=
    Finset.prod_dvd_prod_of_subset
      (Goldbach.Singular.oddPrimeSupport n) (n / 2).primeFactors id hsubset
  have hdvd_half : ∏ p ∈ (n / 2).primeFactors, p ∣ n / 2 := Nat.prod_primeFactors_dvd (n / 2)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (half_ne_zero_of_even_nonzero he hn))
    (dvd_trans hdvd_subset hdvd_half)

private lemma prod_le_prod_real {ι : Type} (s : Finset ι) (f g : ι → ℝ)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ f i)
    (hg_nonneg : ∀ i ∈ s, 0 ≤ g i)
    (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert hf_nonneg hg_nonneg hfg
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _
    simp
  · intro a s ha ih hf_nonneg hg_nonneg hfg
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfa0 : 0 ≤ f a := hf_nonneg a (Finset.mem_insert_self a s)
    have hga0 : 0 ≤ g a := hg_nonneg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf_nonneg i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg_nonneg i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul hfa (ih hfs hgs hfgs) (Finset.prod_nonneg hfs) hga0

private lemma sigma_upper_linear {n : ℕ} (hn : n ≠ 0) :
    Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric n
      ≤ Goldbach.Analytic.C2_numeric.C2 * (n : ℝ) := by
  by_cases he : Even n
  · have hprod1 :
        ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, Goldbach.Singular.oddFactor p
          ≤ ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, (p : ℝ) := by
      refine prod_le_prod_real (Goldbach.Singular.oddPrimeSupport n)
        Goldbach.Singular.oddFactor (fun p => (p : ℝ)) ?_ ?_ ?_
      · intro p hp
        have hone : (1 : ℝ) ≤ Goldbach.Singular.oddFactor p :=
          Goldbach.Singular.oddFactor_ge_one_of_prime_ne_two
            (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2
        linarith
      · intro p hp
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast Nat.Prime.one_le (Finset.mem_filter.mp hp).2.1
        linarith
      · intro p hp
        exact oddFactor_le_self (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2
    have hprod2_nat : ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, p ≤ n / 2 :=
      prod_support_primes_le_half he hn
    have hprod2 :
        ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, (p : ℝ) ≤ (n : ℝ) / 2 := by
      have htmp :
          (((∏ p ∈ Goldbach.Singular.oddPrimeSupport n, p : ℕ) : ℝ))
            ≤ ((n / 2 : ℕ) : ℝ) := by
        exact_mod_cast hprod2_nat
      have hcast :
          (((n / 2 : ℕ) : ℝ)) = (n : ℝ) / 2 := by
        rcases he with ⟨m, hm⟩
        rw [hm]
        have hhalf_nat : (m + m) / 2 = m := by
          have : (2 * m) / 2 = m := by omega
          simpa [two_mul] using this
        calc
          ((((m + m) / 2 : ℕ) : ℝ)) = (m : ℝ) := by exact_mod_cast hhalf_nat
          _ = ((m + m : ℕ) : ℝ) / 2 := by
            rw [show (m + m : ℕ) = 2 * m by omega]
            norm_num
      rw [hcast] at htmp
      simpa using htmp
    calc
      Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric n
          = (2 : ℝ) * Goldbach.Analytic.C2_numeric.C2
              * ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, Goldbach.Singular.oddFactor p := by
                simpa using Goldbach.Singular.sigma_even_expand (C := Goldbach.Analytic.C2_numeric) he
      _ ≤ (2 : ℝ) * Goldbach.Analytic.C2_numeric.C2
            * ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, (p : ℝ) := by
              have hCnonneg : 0 ≤ (2 : ℝ) * Goldbach.Analytic.C2_numeric.C2 := by
                nlinarith [Goldbach.Analytic.C2_numeric.pos]
              exact mul_le_mul_of_nonneg_left hprod1 hCnonneg
      _ ≤ (2 : ℝ) * Goldbach.Analytic.C2_numeric.C2 * ((n : ℝ) / 2) := by
              have hCnonneg : 0 ≤ (2 : ℝ) * Goldbach.Analytic.C2_numeric.C2 := by
                nlinarith [Goldbach.Analytic.C2_numeric.pos]
              exact mul_le_mul_of_nonneg_left hprod2 hCnonneg
      _ = Goldbach.Analytic.C2_numeric.C2 * (n : ℝ) := by ring
  · have hnonneg : 0 ≤ Goldbach.Analytic.C2_numeric.C2 * (n : ℝ) := by
      nlinarith [Goldbach.Analytic.C2_numeric.pos]
    simp [Goldbach.Singular.sigma, he, hnonneg]

private noncomputable def mainTermUpperEnv (X : ℕ) : ℝ :=
  Goldbach.Analytic.C2_numeric.C2
    * (((X + H : ℕ) : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2)

private noncomputable def convRefConstUpperEnv (X : ℕ) : ℝ :=
  (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X

private lemma mainTerm_upper_window {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |(Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N| ≤ mainTermUpperEnv X := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_le : N ≤ X + H := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) X
  have hN_ge_X0 : X0 ≤ N := le_trans hX hN_ge_X
  have hN_ne : N ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < X0) hN_ge_X0)
  have hsigma_nonneg : 0 ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N := by
    have heven := Goldbach.Analytic.even_of_window hX hN
    exact le_trans
      (by nlinarith [Goldbach.Analytic.C2_numeric.pos])
      (Goldbach.Singular.sigma_floor_even (C := Goldbach.Analytic.C2_numeric) heven)
  have hM_nonneg : 0 ≤ Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric N := by
    have hlog_ge_ten : (10 : ℝ) ≤ Real.log (N : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN_ge_X0
    have hlog_sq_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 := by positivity
    exact div_nonneg (mul_nonneg hsigma_nonneg (by positivity)) hlog_sq_nonneg
  have hsigma := sigma_upper_linear hN_ne
  have hlog_sq_pos_X : 0 < (Real.log (X : ℝ)) ^ 2 := by
    have hlog_ge_ten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
    nlinarith
  have hlog_sq_pos_N : 0 < (Real.log (N : ℝ)) ^ 2 := by
    have hlog_ge_ten : (10 : ℝ) ≤ Real.log (N : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN_ge_X0
    nlinarith
  have hXN_real : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_X
  have hlog_le : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    have hX_pos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    exact Real.log_le_log hX_pos hXN_real
  have hlog_sq_le : (Real.log (X : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
    have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) := by
      have hlog_ge_ten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
        Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
      linarith
    nlinarith
  have hN_sq_over :
      ((N : ℝ) ^ 2 / (Real.log (N : ℝ)) ^ 2)
        ≤ ((N : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
    have hInv :
        ((Real.log (N : ℝ)) ^ 2)⁻¹ ≤ ((Real.log (X : ℝ)) ^ 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlog_sq_pos_X hlog_sq_le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hInv (sq_nonneg (N : ℝ))
  have hN_sq_le : (N : ℝ) ^ 2 ≤ (((X + H : ℕ) : ℝ) ^ 2) := by
    have hbase : (N : ℝ) ≤ ((X + H : ℕ) : ℝ) := by exact_mod_cast hN_le
    nlinarith
  have hfrac_le :
      ((N : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2)
        ≤ ((((X + H : ℕ) : ℝ) ^ 2) / (Real.log (X : ℝ)) ^ 2) := by
    exact div_le_div_of_nonneg_right hN_sq_le (le_of_lt hlog_sq_pos_X)
  calc
    |(Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N|
        = (Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N := by
            simp [abs_of_nonneg hM_nonneg]
    _ = Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
          * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
            rw [Goldbach.MainTerm.M]
            ring
    _ ≤ (Goldbach.Analytic.C2_numeric.C2 * (N : ℝ))
          * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hsigma (by positivity)
    _ = Goldbach.Analytic.C2_numeric.C2
          * ((N : ℝ) ^ 2 / (Real.log (N : ℝ)) ^ 2) := by
            ring
    _ ≤ Goldbach.Analytic.C2_numeric.C2
          * ((N : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
            have hCnonneg : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := by
              nlinarith [Goldbach.Analytic.C2_numeric.pos]
            exact mul_le_mul_of_nonneg_left hN_sq_over hCnonneg
    _ ≤ Goldbach.Analytic.C2_numeric.C2
          * ((((X + H : ℕ) : ℝ) ^ 2) / (Real.log (X : ℝ)) ^ 2) := by
            have hCnonneg : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := by
              nlinarith [Goldbach.Analytic.C2_numeric.pos]
            exact mul_le_mul_of_nonneg_left hfrac_le hCnonneg
    _ = mainTermUpperEnv X := by
          simp [mainTermUpperEnv]

private lemma convRefConst_upper_window {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref_const X N| ≤ convRefConstUpperEnv X := by
  have hσ :
      |Goldbach.AO_SigmaModel.sigma N| ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
    exact Goldbach.AO_SigmaPos.SigmaUpperOnWindow.sigma_even_ub_on_window (X := X) (N := N) hX hN
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  have hconst :
      Goldbach.BG_Identity.conv_ref_const X N
        = Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X := by
    simpa using (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
  calc
    |Goldbach.BG_Identity.conv_ref_const X N|
        = |Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X| := by
            simp [hconst]
    _ = |Goldbach.AO_SigmaModel.sigma N| * Goldbach.AO_WeightMass.weight_mass X := by
          rw [abs_mul, abs_of_nonneg hwm_nonneg]
    _ ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X := by
          exact mul_le_mul_of_nonneg_right hσ hwm_nonneg
    _ = convRefConstUpperEnv X := by
          simp [convRefConstUpperEnv]

/-- Explicit `X`-only bound for `|conv_ref - MainTerm.M C2_numeric|` on the canonical window. -/
noncomputable def Δref_proj (X : ℕ) : ℝ :=
  Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
    + convRefConstUpperEnv X
    + mainTermUpperEnv X

theorem conv_ref_mainTerm_gap
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δref_proj X := by
  have hswap :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon :=
    Goldbach.AO_MajorSwapTenorAxiomsFunX.goldbach_major_arc_eval_on_window_canon (X := X) (N := N) hX hN
  have href_const :
      |Goldbach.BG_Identity.conv_ref_const X N| ≤ convRefConstUpperEnv X :=
    convRefConst_upper_window (X := X) (N := N) hX hN
  have hmain := mainTerm_upper_window hX hN
  have htri :
      |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N|
            + |(Goldbach.MainTerm.M C2_numeric) N| := by
    have hsplit :
        Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N
          = (Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
              + (Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N) := by
      ring
    calc
      |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
          = |(Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
              + (Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N)| := by
                rw [hsplit]
      _ ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N| := by
              simpa using abs_add_le
                (Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
                (Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N)
      _ ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
            + (|Goldbach.BG_Identity.conv_ref_const X N| + |(Goldbach.MainTerm.M C2_numeric) N|) := by
              have hsub :
                  |Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N|
                    ≤ |Goldbach.BG_Identity.conv_ref_const X N| + |(Goldbach.MainTerm.M C2_numeric) N| := by
                simpa [sub_eq_add_neg] using
                  abs_add_le
                    (Goldbach.BG_Identity.conv_ref_const X N)
                    (-(Goldbach.MainTerm.M C2_numeric N))
              exact add_le_add_left hsub _
      _ = |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N|
            + |(Goldbach.MainTerm.M C2_numeric) N| := by ring
  calc
    |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N|
            + |(Goldbach.MainTerm.M C2_numeric) N| := htri
    _ ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
          + convRefConstUpperEnv X
          + mainTermUpperEnv X := by
            gcongr
    _ = Δref_proj X := by
          simp [Δref_proj, add_assoc]

/-- Explicit `X`-only projected bank-gap cap obtained from the refactored route. -/
noncomputable def Δproj (X : ℕ) : ℝ :=
  Goldbach.AO_WeightMass.weight_mass X
    * (((1252 : ℝ) / 10 ^ 6)
        * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
    + Δref_proj X

theorem projected_bank_gap
    [Goldbach.BG_Calib.WeightsBridgeHyp] :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δproj X := by
  intro X N hX hN
  refine Goldbach.BankPieces.Cert.Projected.bank_gap
    (Δref := Δref_proj) (Δproj := Δproj)
    (hRef := by intro X N hX hN; exact conv_ref_mainTerm_gap hX hN)
    (hCal := by
      intro X N hX hN
      have hcap :
          Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
        Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
      have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
        have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
        simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
      have hconst_nonneg : 0 ≤ ((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed := by
        have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
          norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
        nlinarith
      have hmul :
          Goldbach.AO_WeightMass.weight_mass X
              * (Goldbach.BG_Bank.payload_cap X N
                  * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            ≤ Goldbach.AO_WeightMass.weight_mass X
                * (((1252 : ℝ) / 10 ^ 6)
                    * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcap hconst_nonneg) hwm_nonneg
      have := add_le_add_left hmul (Δref_proj X)
      simpa [Δproj, add_assoc, add_left_comm, add_comm] using this)
    (X := X) (N := N) hX hN

end

end Goldbach.BankPieces.Cert.ProjectedInput
