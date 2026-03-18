import Mathlib
import Goldbach.AO_SigmaModel
import Goldbach.AO_WeightMass
import Goldbach.AO_OffDiag.EntryPoint
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.BG_Calib
import Goldbach.BG_Identity
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.Cert.SigmaUpperOnWindowCanon

namespace Goldbach.BankPieces.Cert.ProjectedSigmaBridge

open Goldbach
open Goldbach.Analytic
open Goldbach.Windows
open Real

noncomputable section

/--
The fixed scalar appearing in the staged AO σ-model.

This is the part of `AO_SigmaModel.sigma` that does not depend on `N`.
-/
noncomputable def sigmaModelCoeff : ℝ :=
  (1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even

/--
Weighted honest sigma model for the projected route.

This is the natural object obtained by replacing the truncated series in `conv_ref_const`
with the honest off-diagonal model `sigmaHonest`.
-/
noncomputable def sigmaHonestWeighted (X N : ℕ) : ℝ :=
  sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X * Goldbach.AO_OffDiag.sigmaHonest N

/-- The explicit weighted tail budget inherited from `AO_OffDiag.tail_bound_on_window`. -/
noncomputable def sigmaTailWeightedEnv (X : ℕ) : ℝ :=
  sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X * (3e-4 : ℝ)

/-- Crude `X`-only upper envelope for the weighted honest sigma model on the canonical window. -/
noncomputable def sigmaHonestWeightedUpperEnv (X : ℕ) : ℝ :=
  (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X
    + sigmaTailWeightedEnv X

private lemma sigmaModelCoeff_nonneg : 0 ≤ sigmaModelCoeff := by
  dsimp [sigmaModelCoeff]
  have h1 : 0 ≤ (1 / 800 : ℝ) := by norm_num
  have h2 : 0 ≤ Goldbach.AO_SigmaModel.Canon.mass_even := by
    dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
      Goldbach.AO_SigmaModel.Canon.Ucut]
    norm_num [Goldbach.BankParams.H]
  exact mul_nonneg h1 h2

private lemma weight_mass_nonneg (X : ℕ) : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
  have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs

lemma conv_ref_const_eq_sigmaTruncWeighted (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref_const X N
      = sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N := by
  calc
    Goldbach.BG_Identity.conv_ref_const X N
        = Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X := by
            simpa using (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
    _ = sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N := by
            simp [Goldbach.AO_SigmaModel.sigma, sigmaModelCoeff, mul_assoc, mul_left_comm, mul_comm]

lemma conv_ref_const_sub_sigmaHonestWeighted (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref_const X N - sigmaHonestWeighted X N
      = sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N - Goldbach.AO_OffDiag.sigmaHonest N) := by
  rw [conv_ref_const_eq_sigmaTruncWeighted]
  simp [sigmaHonestWeighted, sigmaModelCoeff, mul_assoc, mul_left_comm, mul_comm]
  ring

theorem conv_ref_const_sigmaHonest_gap
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref_const X N - sigmaHonestWeighted X N|
      ≤ sigmaTailWeightedEnv X := by
  have htail :
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N - Goldbach.AO_OffDiag.sigmaHonest N|
        ≤ (3e-4 : ℝ) := by
    have h :=
      Goldbach.AO_OffDiag.tail_bound_on_window (X := X) (N := N) hX hN
    simpa [abs_sub_comm] using h
  have hcoeff_nonneg : 0 ≤ sigmaModelCoeff := sigmaModelCoeff_nonneg
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := weight_mass_nonneg X
  calc
    |Goldbach.BG_Identity.conv_ref_const X N - sigmaHonestWeighted X N|
        = |sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N - Goldbach.AO_OffDiag.sigmaHonest N)| := by
              rw [conv_ref_const_sub_sigmaHonestWeighted]
    _ = sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X
          * |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N - Goldbach.AO_OffDiag.sigmaHonest N| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcoeff_nonneg, abs_of_nonneg hwm_nonneg]
    _ ≤ sigmaModelCoeff * Goldbach.AO_WeightMass.weight_mass X * (3e-4 : ℝ) := by
          exact mul_le_mul_of_nonneg_left htail (mul_nonneg hcoeff_nonneg hwm_nonneg)
    _ = sigmaTailWeightedEnv X := by
          simp [sigmaTailWeightedEnv]

theorem sigmaHonestWeighted_upper_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |sigmaHonestWeighted X N| ≤ sigmaHonestWeightedUpperEnv X := by
  have hconst :
      |Goldbach.BG_Identity.conv_ref_const X N|
        ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X := by
    have hσ :
        |Goldbach.AO_SigmaModel.sigma N| ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
      exact Goldbach.AO_SigmaPos.SigmaUpperOnWindow.sigma_even_ub_on_window (X := X) (N := N) hX hN
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := weight_mass_nonneg X
    have hconv :
        Goldbach.BG_Identity.conv_ref_const X N
          = Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X := by
      simpa using (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
    calc
      |Goldbach.BG_Identity.conv_ref_const X N|
          = |Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X| := by
              simp [hconv]
      _ = |Goldbach.AO_SigmaModel.sigma N| * Goldbach.AO_WeightMass.weight_mass X := by
            rw [abs_mul, abs_of_nonneg hwm_nonneg]
      _ ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X := by
            exact mul_le_mul_of_nonneg_right hσ hwm_nonneg
  have hgap := conv_ref_const_sigmaHonest_gap (X := X) (N := N) hX hN
  have htri :
      |sigmaHonestWeighted X N|
        ≤ |sigmaHonestWeighted X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N| := by
    calc
      |sigmaHonestWeighted X N|
          = |(sigmaHonestWeighted X N - Goldbach.BG_Identity.conv_ref_const X N)
              + Goldbach.BG_Identity.conv_ref_const X N| := by ring_nf
      _ ≤ |sigmaHonestWeighted X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N| := by
              simpa using
                (abs_add_le
                  (sigmaHonestWeighted X N - Goldbach.BG_Identity.conv_ref_const X N)
                  (Goldbach.BG_Identity.conv_ref_const X N))
  calc
    |sigmaHonestWeighted X N|
        ≤ |sigmaHonestWeighted X N - Goldbach.BG_Identity.conv_ref_const X N|
            + |Goldbach.BG_Identity.conv_ref_const X N| := htri
    _ = |Goldbach.BG_Identity.conv_ref_const X N - sigmaHonestWeighted X N|
          + |Goldbach.BG_Identity.conv_ref_const X N| := by
            rw [abs_sub_comm]
    _ ≤ sigmaTailWeightedEnv X
          + ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X) := by
            exact add_le_add hgap hconst
    _ = sigmaHonestWeightedUpperEnv X := by
          simp [sigmaHonestWeightedUpperEnv, add_comm]

/--
Reference-gap theorem against the weighted honest sigma model.

This is the cleanest theorem available from the current repo: the only remaining projected input is
the comparison between `sigmaHonestWeighted` and the Hardy–Littlewood main term.
-/
theorem conv_ref_mainTerm_gap_of_sigmaHonest_gap
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ sigmaTailWeightedEnv X
          + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
              * (Goldbach.BG_Bank.payload_cap X N
                  + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
          + Δhonest X := by
  intro X N hX hN
  have hswap :
      |Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N|
        ≤ sigmaTailWeightedEnv X
            + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
                * (Goldbach.BG_Bank.payload_cap X N
                    + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG) := by
    exact
      Goldbach.BG_Calib.ref_to_Mfun_bound_of_const_gap
        (Mfun := fun X N => sigmaHonestWeighted X N)
        (X := X) (N := N) hX hN
        (δ := sigmaTailWeightedEnv X)
        (hAO := conv_ref_const_sigmaHonest_gap (X := X) (N := N) hX hN)
  have hhonest :
      |sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X :=
    hHonest (X := X) (N := N) hX hN
  have hsplit :
      Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N
        = (Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N)
            + (sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N) := by
    ring
  have htri :
      |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ |Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N|
          + |sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N| := by
    calc
      |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
          = |(Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N)
              + (sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N)| := by
                rw [hsplit]
      _ ≤ |Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N|
            + |sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N| := by
              simpa using
                (abs_add_le
                  (Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N)
                  (sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N))
  calc
    |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ |Goldbach.BG_Identity.conv_ref X N - sigmaHonestWeighted X N|
            + |sigmaHonestWeighted X N - (Goldbach.MainTerm.M C2_numeric) N| := htri
    _ ≤ (sigmaTailWeightedEnv X
            + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
                * (Goldbach.BG_Bank.payload_cap X N
                    + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG))
          + Δhonest X := by
            exact add_le_add hswap hhonest
    _ = sigmaTailWeightedEnv X
          + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
              * (Goldbach.BG_Bank.payload_cap X N
                  + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
          + Δhonest X := by
            ring

end

end Goldbach.BankPieces.Cert.ProjectedSigmaBridge
