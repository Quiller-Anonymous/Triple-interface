
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
  Goldbach.AO_Core.Mcanon X N =
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
    (Goldbach.AO_Core.Mcanon X N) / (Real.log (X : ℝ))^2
  else
    0

/-- On the canonical window: `Mcanon = (log X)^2 * MPDF`. -/
theorem canon_normalization
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4)) :
  Goldbach.AO_Core.Mcanon X N = (Real.log (X : ℝ))^2 * MPDF X N := by
  have win : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) := ⟨hX, hN⟩
  have hne : (Real.log (X : ℝ))^2 ≠ 0 := logsq_ne_zero hX
  -- rewrite MPDF on the window
  simp only [MPDF, win, dif_pos, mul_div_assoc']
  exact (mul_div_cancel₀ _ hne).symm

/-!
AO ledger constant.

The lower bound on the σ-model on the canonical window is treated as an explicit input
(`AO_SigmaPos.SigmaLowerOnWindow`), and `cAO` packages the resulting “σ minus envelope” constant.
-/

/--
Calibrated AO constant.

With the bank normalization `wX`, the main term carries an additional (window-scale) factor
`weight_mass`, so the ledger lower bound is naturally `X`-dependent.
-/
noncomputable def cAO (K : Caps) [AO_SigmaPos.SigmaLowerOnWindow] (X : ℕ) : ℝ :=
  AO_SigmaPos.SigmaLowerOnWindow.σmin * weight_mass X - δAO K

/-- From `|errAO| ≤ δAO K` we get `-δAO K ≤ errAO`. -/
lemma errAO_lower_of_bound {X N : ℕ} {K : Caps}
  (h : |errAO X N| ≤ δAO K) : -(δAO K) ≤ errAO X N :=
  (abs_le.mp h).1

/-- Ledger lower bound from a σ-lower bound + error envelope. -/
lemma ledger_lower_from_sigma_and_error
  (C : Channels) (K : Caps) [Decomposition C] [Bounds C K] [AO_SigmaPos.SigmaLowerOnWindow]
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4))
  (herr : |errAO X N| ≤ δAO K) :
  Goldbach.AO_Core.Mcanon X N ≥ cAO K X := by
  have hexp := ao_expansion (X:=X) (N:=N) hX hN
  have hwm0 : 0 ≤ weight_mass X := by
    simpa [Goldbach.AO_Major.weight_mass, Goldbach.AO_WeightMass.weight_mass] using
      (sq_nonneg (Goldbach.BG_Bank.wScale X))
  have herr_lo : -(δAO K) ≤ errAO X N := errAO_lower_of_bound herr
  have hσ : AO_SigmaPos.SigmaLowerOnWindow.σmin ≤ Goldbach.AO_Core.sigma N := by
    -- `SigmaLowerOnWindow` is stated on the canonical window `(X0,H) = (10^6,10^4)`.
    have hX' : Goldbach.BankParams.X0 ≤ X := by simpa [Goldbach.BankParams.X0] using hX
    have hN' : N ∈ EvenIn X Goldbach.BankParams.H := by simpa [Goldbach.BankParams.H] using hN
    simpa [AO_SigmaPos.sigma] using
      (AO_SigmaPos.SigmaLowerOnWindow.sigma_even_lb_on_window (X := X) (N := N) hX' hN')
  calc
    Goldbach.AO_Core.Mcanon X N
        = Goldbach.AO_Core.sigma N * weight_mass X + errAO X N := by simpa using hexp
    _   ≥ Goldbach.AO_Core.sigma N * weight_mass X + (-(δAO K)) := add_le_add_left herr_lo _
    _   = Goldbach.AO_Core.sigma N * weight_mass X - δAO K := by simp [sub_eq_add_neg, add_assoc]
    _   ≥ AO_SigmaPos.SigmaLowerOnWindow.σmin * weight_mass X - δAO K := by
          exact sub_le_sub_right (mul_le_mul_of_nonneg_right hσ hwm0) _
    _   = cAO K X := by simp [cAO, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- If `Mcanon N ≥ c` on a window, then `MPDF X N ≥ c/(log X)^2`. -/
lemma pdf_lower_from_ledger_lower
  {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ EvenIn X (10^4))
  {c : ℝ} (h : Goldbach.AO_Core.Mcanon X N ≥ c) :
  MPDF X N ≥ c / (Real.log (X : ℝ))^2 := by
  have win : (10^6 : ℕ) ≤ X ∧ N ∈ EvenIn X (10^4) := ⟨hX, hN⟩
  have logsq_pos' : 0 < (Real.log (X : ℝ))^2 := logsq_pos hX
  have hnz : 0 ≤ (Real.log (X : ℝ))^2 := le_of_lt logsq_pos'
  have hdiv :
      c / (Real.log (X : ℝ))^2 ≤ (Goldbach.AO_Core.Mcanon X N) / (Real.log (X : ℝ))^2 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right h (inv_nonneg.2 hnz))
  -- Now unfold MPDF in the correct branch
  simp only [MPDF, win, dif_pos]
  exact hdiv

-- The windowed AO ledger lower bound is obtained by combining:
-- - the σ-lower input (`SigmaLowerOnWindow`), and
-- - the envelope bound `|errAO| ≤ δAO(K)`.
theorem ao_ledger_lower
  (C : Channels) (K : Caps) [Decomposition C] [Bounds C K] [AO_SigmaPos.SigmaLowerOnWindow] :
  ∀ {X N}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) →
    Goldbach.AO_Core.Mcanon X N ≥ cAO K X := by
  intro X N hX hN
  have herr : |errAO X N| ≤ δAO K :=
    Goldbach.AO_AssembleEnvelope.errAO_bound (C:=C) (K:=K) hX hN
  exact ledger_lower_from_sigma_and_error (C := C) (K := K) (X := X) (N := N) hX hN herr

end Goldbach.AO_Major
