/-
  Goldbach/AO_Major.lean  — axiom-free core (revised to use AO_SigmaPos)

  Depends on:
    • AO_ErrorEnvelope  (δAO, errAO_bound, δAO_nonneg)
    • AO_SigmaPos       (sigma, sigma0, c0, sigma_even_lb_on_window, sigma0_pos)
-/
import Mathlib
import Goldbach.Windows
import Goldbach.TenorCanon
import Goldbach.AO_ErrorEnvelope
import Goldbach.AO_SigmaPos

namespace Goldbach.AO_Major

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.TenorCanon
open Goldbach.AO_ErrorEnvelope
open Goldbach.AO_SigmaPos

/-- Major-arc weight mass (ledger normalization): define it to be 1. -/
@[simp] def weight_mass (_X : ℕ) : ℝ := 1.0

/-- Define the AO error as the algebraic remainder after the main term. -/
@[simp] def errAO (X N : ℕ) : ℝ := Mcanon N - sigma N * weight_mass X

/-- **Expansion identity** (by unfolding). -/
theorem ao_expansion
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4)) :
  Mcanon N = sigma N * weight_mass X + errAO X N := by
  unfold errAO; simp [weight_mass, sub_eq, add_comm, add_left_comm, add_assoc]

/-- For `X ≥ 10^6`, we have `0 < log X`. -/
private lemma log_pos_of_large (hX : (10^6 : ℕ) ≤ X) : 0 < Real.log (X : ℝ) := by
  have hx : (3 : ℝ) ≤ (X : ℝ) := by
    have : (3 : ℕ) ≤ X := le_trans (by decide : (3:ℕ) ≤ 10^6) hX
    exact_mod_cast this
  have : 1 < (X : ℝ) :=
    lt_of_le_of_lt (show (1:ℝ) ≤ (3:ℝ) by norm_num) (lt_of_le_of_ne hx (by decide))
  simpa using Real.log_pos_iff.mpr this

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
    (Mcanon N) / (Real.log (X : ℝ))^2
  else
    0

/-- On the canonical window: `Mcanon = (log X)^2 * MPDF`. -/
theorem canon_normalization
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4)) :
  Mcanon N = (Real.log (X : ℝ))^2 * MPDF X N := by
  unfold MPDF
  have h : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) := ⟨hX, hN⟩
  simp [h]
  have hne := logsq_ne_zero hX
  calc
    (Real.log (X : ℝ))^2 * (Mcanon N / (Real.log (X : ℝ))^2)
        = (Mcanon N / (Real.log (X : ℝ))^2) * (Real.log (X : ℝ))^2 := by
            ac_rfl
    _   = (Mcanon N * (Real.log (X : ℝ))^2) / (Real.log (X : ℝ))^2 := by
            simpa using (div_mul_eq_mul_div (Mcanon N) ((Real.log (X : ℝ))^2) ((Real.log (X : ℝ))^2)).symm
    _   = Mcanon N := by
            simpa using (mul_div_cancel' (Mcanon N) hne)

/-- Calibrated AO constant: cAO := σ₀ − δAO = c₀. -/
noncomputable def cAO : ℝ := sigma0 - δAO

lemma cAO_exact : cAO = c0 := by
  simpa [cAO, sigma0, c0, add_comm] using (add_sub_cancel c0 δAO)

/-- From `|errAO| ≤ δAO` we get `-δAO ≤ errAO`. -/
lemma errAO_lower_of_bound {X N : ℕ}
  (h : |errAO X N| ≤ δAO) : -δAO ≤ errAO X N :=
  (abs_le.mp h).1

/-- Ledger lower bound from σ-positivity + error envelope. -/
lemma ledger_lower_from_sigma_and_error
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4))
  (hσ : sigma N ≥ sigma0) (herr : |errAO X N| ≤ δAO) :
  Mcanon N ≥ sigma0 - δAO := by
  have hexp := ao_expansion (X:=X) (N:=N) hX hN
  have hW   : weight_mass X = (1.0 : ℝ) := by simp [weight_mass]
  have herr_lo : -δAO ≤ errAO X N := errAO_lower_of_bound herr
  calc
    Mcanon N
        = sigma N * weight_mass X + errAO X N := by simpa using hexp
    _   = sigma N * 1.0 + errAO X N          := by simpa [hW, mul_one]
    _   ≥ sigma N * 1.0 + (-δAO)             := add_le_add_left herr_lo _
    _   = sigma N - δAO                      := by ring
    _   ≥ sigma0 - δAO                       := sub_le_sub_right hσ _

/-- If `Mcanon N ≥ c` on a window, then `MPDF X N ≥ c/(log X)^2`. -/
lemma pdf_lower_from_ledger_lower
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4))
  {c : ℝ} (h : Mcanon N ≥ c) :
  MPDF X N ≥ c / (Real.log (X : ℝ))^2 := by
  have logsq_pos' : 0 < (Real.log (X : ℝ))^2 := logsq_pos hX
  have : (Mcanon N) / (Real.log (X : ℝ))^2 ≥ c / (Real.log (X : ℝ))^2 :=
    div_le_div_of_le_of_nonneg h (le_of_lt logsq_pos')
  unfold MPDF
  have win : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) := ⟨hX, hN⟩
  simpa [win]

/-- **Ledger AO lower bound** on the window. -/
theorem ao_ledger_lower :
  ∀ {X N}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) → Mcanon N ≥ cAO := by
  intro X N hX hN
  have hσ  : sigma N ≥ sigma0 := AO_SigmaPos.sigma_even_lb_on_window (X:=X) (N:=N) hX hN
  have herr : |errAO X N| ≤ δAO := AO_ErrorEnvelope.errAO_bound (X:=X) (N:=N) hX hN
  have := ledger_lower_from_sigma_and_error (X:=X) (N:=N) hX hN hσ herr
  simpa [cAO_exact] using this

/-- Bridge-ready AO major bound on the window (ledger scale). -/
theorem major_lb_window :
  ∀ {X N}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) →
    Mcanon N ≥ (0.05 : ℝ) * (1.0 : ℝ) := by
  intro X N hX hN
  have h := ao_ledger_lower (X:=X) (N:=N) hX hN
  have : (0.05 : ℝ) ≤ cAO := by simpa [cAO_exact, c0]
  exact le_trans this h

/-- **Corollary (PDF scale)** with κ := cAO (= c₀). -/
theorem cor_10_5_pdf :
  ∃ κ : ℝ, 0 < κ ∧
    ∀ {X N}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) →
      MPDF X N ≥ (κ : ℝ) / (Real.log (X : ℝ))^2 := by
  have cAO_pos : 0 < cAO := by
    -- cAO = c0 and c0 = 0.05
    simpa [cAO_exact, c0] using (by norm_num : (0:ℝ) < (0.05:ℝ))
  refine ⟨cAO, cAO_pos, ?_⟩
  intro X N hX hN
  exact pdf_lower_from_ledger_lower hX hN (ao_ledger_lower (X:=X) (N:=N) hX hN)

/-- Since κ = cAO and `cAO = c0`, we have κ ≥ c0 (trivial). -/
theorem kappa_ge_c0 :
  ∀ {κ : ℝ}, κ = cAO → (0.05 : ℝ) ≤ κ := by
  intro κ hκ
  have : (0.05 : ℝ) ≤ cAO := by simpa [cAO_exact, c0]
  simpa [hκ]

end Goldbach.AO_Major
