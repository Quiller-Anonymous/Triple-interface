import Goldbach.ProofTools
import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
import Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
import Goldbach.BankPieces.Cert.RawScaleFrozenTrivialSmallBeta

namespace Goldbach.BankPieces.Cert.RawScaleFrozenLinearSmallBeta

open Goldbach
open Goldbach.Windows
open Goldbach.ProofTools.Windows
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
open Goldbach.BankPieces.Cert.RawScaleFrozenTrivialSmallBeta

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-- Window-uniform upper envelope for the sharpened `q ≥ 2` rescaled-gap budget. -/
noncomputable def etaLinearRescaledGapWindow (X q : ℕ) : ℝ :=
  etaLinearRescaledGap X (X + BankParams.H) q

/--
Window-uniform sharpened small-`β` budget:
- `q = 1` still uses the window-uniform trivial envelope,
- `q ≥ 2` uses the new linear `1 / (qX)` rescaled-gap budget.
-/
noncomputable def etaSmallFrozenLinear (ηres : ℕ → ℝ) (X : ℕ) : ℝ :=
  ηres X
    + Goldbach.AO_WeightMass.weight_mass X
        * (etaFreezeTrivialWindow X
            + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                    * (((q : ℝ) * (X : ℝ))⁻¹) * etaLinearRescaledGapWindow X q))
                  * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)))

private lemma weight_mass_nonneg (X : ℕ) : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_nonneg (Goldbach.BG_Bank.wScale X)

private lemma weight_mass_pos {X : ℕ} (hX : BankParams.X0 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    have hXreal : (BankParams.X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have h1lt : (1 : ℝ) < (X : ℝ) := by
      have hX0 : (1 : ℝ) < (BankParams.X0 : ℝ) := by norm_num [BankParams.X0]
      linarith
    exact Real.log_pos h1lt
  have hden_pos : 0 < Real.log (X : ℝ) * (2 * (BankParams.H : ℝ) + 1) := by
    positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    unfold Goldbach.BG_Bank.wScale
    exact one_div_pos.mpr hden_pos
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

private lemma tailWeight_nonneg {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
  have hphi_pos : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq)
  exact div_nonneg
    (by
      by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq])
    (le_of_lt hphi_pos)

theorem etaLinearRescaledGap_le_window
    {X N q : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ EvenIn X BankParams.H)
    (hq : 1 ≤ q) :
    etaLinearRescaledGap X N q ≤ etaLinearRescaledGapWindow X q := by
  have hNle : N ≤ X + BankParams.H := le_right_of_mem_EvenIn hN
  have hcard :
      (Finset.Ico 4 ((N - 2) + 1)).card
        ≤ (Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card := by
    have hup : (N - 2) + 1 ≤ ((X + BankParams.H) - 2) + 1 := by
      exact Nat.succ_le_succ (Nat.sub_le_sub_right hNle 2)
    have hcardN : (Finset.Ico 4 ((N - 2) + 1)).card = ((N - 2) + 1) - 4 := by simp
    have hcardTop :
        (Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card
          = (((X + BankParams.H) - 2) + 1) - 4 := by simp
    rw [hcardN, hcardTop]
    exact Nat.sub_le_sub_right hup 4
  have hcardR :
      ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
        ≤ ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) := by
    exact_mod_cast hcard
  have hcardSq :
      ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
        ≤ ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2 := by
    nlinarith
  have hlinNat :
      N + 2 * (N - 2) ≤ (X + BankParams.H) + 2 * ((X + BankParams.H) - 2) := by
    have hsub : N - 2 ≤ (X + BankParams.H) - 2 := Nat.sub_le_sub_right hNle 2
    omega
  have hlinR :
      ((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
        ≤ (((X + BankParams.H : ℕ) : ℝ) + 2 * (((X + BankParams.H) - 2 : ℕ) : ℝ)) := by
    exact_mod_cast hlinNat
  have hfac_nonneg : 0 ≤ 4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹) := by
    positivity
  have hlin_nonneg :
      0 ≤ ((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.zero_le (N + 2 * (N - 2)))
  have hlinTop_nonneg :
      0 ≤ (((X + BankParams.H : ℕ) : ℝ) + 2 * (((X + BankParams.H) - 2 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.zero_le ((X + BankParams.H) + 2 * ((X + BankParams.H) - 2)))
  have hmiddle :
      ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
        * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹)))
      ≤ ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2
          * ((((X + BankParams.H : ℕ) : ℝ) + 2 * (((X + BankParams.H) - 2 : ℕ) : ℝ))
              * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))) := by
    have hlinFac :
        ((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))
          ≤ (((X + BankParams.H : ℕ) : ℝ) + 2 * (((X + BankParams.H) - 2 : ℕ) : ℝ))
              * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹)) := by
      exact mul_le_mul_of_nonneg_right hlinR hfac_nonneg
    have hlinFac_nonneg :
        0 ≤ ((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹)) := by
      exact mul_nonneg hlin_nonneg hfac_nonneg
    have hcardTop_nonneg :
        0 ≤ ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2 := by
      exact sq_nonneg ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ)
    exact mul_le_mul hcardSq hlinFac hlinFac_nonneg hcardTop_nonneg
  unfold etaLinearRescaledGapWindow etaLinearRescaledGap
  have hcap_nonneg : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
  have hdiv : (0 : ℝ) ≤ 3 := by norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmiddle hcap_nonneg) hdiv

end

end Goldbach.BankPieces.Cert.RawScaleFrozenLinearSmallBeta
