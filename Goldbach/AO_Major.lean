
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Core
import Goldbach.AO_ErrorCore
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_SigmaPos

namespace Goldbach.AO_Major

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.AO_AssembleEnvelope
open Goldbach.AO_SigmaPos

/-- **Expansion identity** (by unfolding `AO_Core.errAO`). -/
theorem ao_expansion
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4)) :
  Goldbach.AO_Core.Mcanon N =
      Goldbach.AO_Core.sigma N * weight_mass X + errAO X N := by
  simp [Goldbach.AO_Major.errAO, Goldbach.AO_Major.weight_mass, Goldbach.AO_Core.errAO,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

/-- For `X ≥ 10^6`, we have `0 < log X`. -/
private lemma log_pos_of_large (hX : (10^6 : ℕ) ≤ X) : 0 < Real.log (X : ℝ) := by
  have h1 : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 10^6) hX
  have h1' : (1 : ℝ) < (X : ℝ) := by exact_mod_cast h1
  simpa using Real.log_pos h1'

/-- `(log X)^2 ≠ 0` when `X ≥ 10^6`. -/
private lemma logsq_ne_zero (hX : (10^6 : ℕ) ≤ X) :
    (Real.log (X : ℝ))^2 ≠ 0 := by
  have : 0 < Real.log (X : ℝ) := log_pos_of_large hX
  exact pow_ne_zero 2 (ne_of_gt this)

/-- `(log X)^2 > 0` when `X ≥ 10^6`. -/
private lemma logsq_pos (hX : (10^6 : ℕ) ≤ X) :
    0 < (Real.log (X : ℝ))^2 :=
  pow_pos (log_pos_of_large hX) 2

/-- PDF-scale main term. -/
noncomputable def MPDF (X N : ℕ) : ℝ :=
  if h : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) then
    (Goldbach.AO_Core.Mcanon N) / (Real.log (X : ℝ))^2
  else
    0

/-- On the canonical window: `Mcanon = (log X)^2 * MPDF`. -/
theorem canon_normalization
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4)) :
  Goldbach.AO_Core.Mcanon N = (Real.log (X : ℝ))^2 * MPDF X N := by
  have win : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) := ⟨hX, hN⟩
  have hne : (Real.log (X : ℝ))^2 ≠ 0 := logsq_ne_zero hX
  -- rewrite MPDF on the window
  simp only [MPDF, win, dif_pos, mul_div_assoc']
  exact (mul_div_cancel₀ _ hne).symm

/-- Calibrated AO constant, parameterized by caps: `cAO K := σ₀ − δAO K`. -/
noncomputable def cAO (K : Caps) : ℝ := sigma0 - δAO K

/-- From `|errAO| ≤ δAO K` we get `-δAO K ≤ errAO`. -/
lemma errAO_lower_of_bound {X N : ℕ} {K : Caps}
  (h : |errAO X N| ≤ δAO K) : -(δAO K) ≤ errAO X N :=
  (abs_le.mp h).1

/-- Ledger lower bound from σ-positivity + error envelope. -/
lemma ledger_lower_from_sigma_and_error
  (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4))
  (hσ : Goldbach.AO_Core.sigma N ≥ sigma0) (herr : |errAO X N| ≤ δAO K) :
  Goldbach.AO_Core.Mcanon N ≥ sigma0 - δAO K := by
  have hexp := ao_expansion (X:=X) (N:=N) hX hN
  have hW : weight_mass X = (1.0 : ℝ) := by simp [Goldbach.AO_Major.weight_mass]
  have herr_lo : -(δAO K) ≤ errAO X N := errAO_lower_of_bound herr
  have hone : (1.0 : ℝ) = 1 := by norm_num
  calc
    Goldbach.AO_Core.Mcanon N
        = Goldbach.AO_Core.sigma N * weight_mass X + errAO X N := by simpa using hexp
    _   = Goldbach.AO_Core.sigma N * 1.0 + errAO X N          := by simpa [hW]
    _   = Goldbach.AO_Core.sigma N + errAO X N                := by simpa [hone]
    _   ≥ Goldbach.AO_Core.sigma N + (-(δAO K))                := add_le_add_left herr_lo _
    _   = Goldbach.AO_Core.sigma N - δAO K                    := by simp [sub_eq_add_neg, add_assoc]
    _   ≥ sigma0 - δAO K                                      := sub_le_sub_right hσ _

/-- If `Mcanon N ≥ c` on a window, then `MPDF X N ≥ c/(log X)^2`. -/
lemma pdf_lower_from_ledger_lower
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4))
  {c : ℝ} (h : Goldbach.AO_Core.Mcanon N ≥ c) :
  MPDF X N ≥ c / (Real.log (X : ℝ))^2 := by
  have win : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) := ⟨hX, hN⟩
  have logsq_pos' : 0 < (Real.log (X : ℝ))^2 := logsq_pos hX
  have hnz : 0 ≤ (Real.log (X : ℝ))^2 := le_of_lt logsq_pos'
  have hdiv :
      c / (Real.log (X : ℝ))^2 ≤ (Goldbach.AO_Core.Mcanon N) / (Real.log (X : ℝ))^2 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right h (inv_nonneg.2 hnz))
  -- Now unfold MPDF in the correct branch
  simp only [MPDF, win, dif_pos]
  exact hdiv

/-- **Ledger AO lower bound** on the window, parameterized by channels/caps. -/
theorem ao_ledger_lower
  (C : Channels) (K : Caps) [Decomposition C] [Bounds C K] :
  ∀ {X N}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) →
    Goldbach.AO_Core.Mcanon N ≥ cAO K := by
  intro X N hX hN
  have hσ : Goldbach.AO_Core.sigma N ≥ sigma0 := by
    simpa using (AO_SigmaPos.sigma_even_lb_on_window (X:=X) (N:=N) hX hN)
  have herr : |errAO X N| ≤ δAO K :=
    Goldbach.AO_AssembleEnvelope.errAO_bound (C:=C) (K:=K) hX hN
  have hledger :=
    ledger_lower_from_sigma_and_error (C:=C) (K:=K) (X:=X) (N:=N) hX hN hσ herr
  simpa [cAO] using hledger

/-- Bridge-ready AO major bound on the window (ledger scale), parameterized. -/
theorem major_lb_window
  (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
  (hc0 : (0.05 : ℝ) ≤ cAO K) :
  ∀ {X N}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) →
    Goldbach.AO_Core.Mcanon N ≥ (0.05 : ℝ) * (1.0 : ℝ) := by
  intro X N hX hN
  have h := ao_ledger_lower (C:=C) (K:=K) (X:=X) (N:=N) hX hN
  have hone : (1.0 : ℝ) = 1 := by norm_num
  have : (0.05 : ℝ) * (1.0 : ℝ) ≤ cAO K := by simpa [hone] using hc0
  exact le_trans this h

end Goldbach.AO_Major
