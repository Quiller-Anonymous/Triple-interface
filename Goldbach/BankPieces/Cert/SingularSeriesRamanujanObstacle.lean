import Goldbach.AO_OffDiag.SigmaTailEuler
import Goldbach.AO_OffDiag.SigmaTailTenorAxioms
import Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge
import Goldbach.Cert.SigmaLowerOnWindowCanonSpec
import Goldbach.SingularSeries
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.SingularSeriesRamanujanObstacle

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

private def Xpow : ℕ := 2 ^ 20

private lemma xpow_ge_bank_X0 : Goldbach.BankParams.X0 ≤ Xpow := by
  norm_num [Xpow, Goldbach.BankParams.X0]

private lemma xpow_ge_analytic_X0 : Goldbach.Analytic.X0 ≤ Xpow := by
  norm_num [Xpow, Goldbach.Analytic.X0]

private lemma xpow_isEven : Goldbach.Windows.IsEven Xpow := by
  native_decide

private lemma xpow_mem_even_window_bank :
    Xpow ∈ EvenIn Xpow Goldbach.BankParams.H :=
  Goldbach.Windows.mem_EvenIn_self xpow_isEven

private lemma xpow_mem_even_window_analytic :
    Xpow ∈ EvenIn Xpow Goldbach.Analytic.H := by
  simpa [Goldbach.Analytic.H, Goldbach.BankParams.H] using xpow_mem_even_window_bank

private lemma xpow_support_small :
    ∀ p, p ∈ (Nat.factorization Xpow).support →
      p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes := by
  intro p hp
  have htriple : p.Prime ∧ p ∣ Xpow ∧ Xpow ≠ 0 := by
    simpa [Xpow, Nat.support_factorization, Nat.mem_primeFactors] using hp
  have hp_prime : p.Prime := htriple.1
  have hp_dvd : p ∣ Xpow := htriple.2.1
  have hp_dvd_pow : p ∣ 2 ^ 20 := by simpa [Xpow] using hp_dvd
  have hp_dvd_two : p ∣ 2 := hp_prime.dvd_of_dvd_pow hp_dvd_pow
  have hp_eq_two : p = 2 := by
    have hcases : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).1 hp_dvd_two
    cases hcases with
    | inl h1 => exact (hp_prime.ne_one h1).elim
    | inr h2 => exact h2
  have htwo_mem :
      2 ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes := by
    native_decide
  simpa [hp_eq_two] using htwo_mem

private lemma sigmaTail_abs_le_eleven_thousandth :
    |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail Xpow| ≤ (11 : ℝ) / 1000 := by
  have htail :
      |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail Xpow|
        ≤ (1 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
            * Goldbach.AO_OffDiag.TailBlock.F_block Xpow := by
    simpa using
      (Goldbach.AO_OffDiag.sigmaTail_bound_on_window
        (K_tail := (1 : ℝ))
        (X := Xpow) (N := Xpow) xpow_ge_bank_X0 xpow_mem_even_window_bank)
  have hF :
      Goldbach.AO_OffDiag.TailBlock.F_block Xpow
        ≤ ((Goldbach.AO_OffDiag.TailBlock.FprodQ : ℚ) : ℝ) :=
    Goldbach.AO_OffDiag.SigmaTailEuler.F_block_le_FprodQ
      (N := Xpow) xpow_support_small
  have h330 : Goldbach.AO_OffDiag.TailBlock.F_block Xpow ≤ (330 : ℝ) := by
    exact le_trans hF (le_of_lt Goldbach.AO_OffDiag.TailBlock.numeric_eval_F_block)
  have hcoef_nonneg : 0 ≤ (1 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
    positivity
  calc
    |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail Xpow|
      ≤ (1 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
          * Goldbach.AO_OffDiag.TailBlock.F_block Xpow := htail
    _ ≤ (1 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (330 : ℝ) := by
          exact mul_le_mul_of_nonneg_left h330 hcoef_nonneg
    _ = (11 : ℝ) / 1000 := by
          norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]

private lemma sigmaSeriesRamanujan_lb_at_xpow :
    (1309 : ℝ) / 1000
      ≤ Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan Xpow := by
  have htrunc :
      (33 : ℝ) / 25 ≤ Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 Xpow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigma_trunc_lb_on_window_canon
      (X := Xpow) (N := Xpow) xpow_ge_bank_X0 xpow_mem_even_window_bank
  have htail_lower :
      -((11 : ℝ) / 1000) ≤ Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail Xpow := by
    exact (abs_le.mp sigmaTail_abs_le_eleven_thousandth).1
  rw [Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan]
  nlinarith

private lemma singular_sigma_at_xpow :
    Goldbach.Singular.sigma C2_numeric Xpow = (1 : ℝ) / 5 := by
  have h :=
    Goldbach.Singular.sigma_two_pow_succ (C := C2_numeric) 19
  calc
    Goldbach.Singular.sigma C2_numeric Xpow = (2 : ℝ) * C2_numeric.C2 := by
      simpa [Xpow] using h
    _ = (1 : ℝ) / 5 := by
      norm_num [Goldbach.Analytic.C2_numeric]

/--
The textbook identity `Singular.sigma C2_numeric = sigmaSeriesRamanujan` is false for the current
Lean object `C2_numeric`, because `C2_numeric` is only a conservative lower constant `1/10`,
not the true Euler-product constant.
-/
theorem not_SingularSigmaEqRamanujanSeriesOnWindow :
    ¬ Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.NumericSingularSigmaEqRamanujanSeriesOnWindow := by
  intro hσeq
  have hEq :
      Goldbach.Singular.sigma C2_numeric Xpow
        = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan Xpow :=
    hσeq (X := Xpow) (N := Xpow) xpow_ge_analytic_X0 xpow_mem_even_window_analytic
  have hlow :
      (1309 : ℝ) / 1000
        ≤ Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan Xpow :=
    sigmaSeriesRamanujan_lb_at_xpow
  have hsigma :
      Goldbach.Singular.sigma C2_numeric Xpow = (1 : ℝ) / 5 :=
    singular_sigma_at_xpow
  have : (1309 : ℝ) / 1000 ≤ (1 : ℝ) / 5 := by
    nlinarith [hlow, hEq, hsigma]
  norm_num at this

end

end Goldbach.BankPieces.Cert.SingularSeriesRamanujanObstacle
