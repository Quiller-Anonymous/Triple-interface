import Goldbach.ProjectedMajorTermDirectProto
import Goldbach.BankPieces.Cert.ProjectedInput
import Goldbach.BankPieces.Cert.ProjectedSigmaBridge
import Goldbach.Cert.CanonLogBounds
import Goldbach.Cert.SigmaUpperOnWindowCanon

namespace Goldbach.ProjectedSigmaBridgeObstacle

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

private lemma weight_mass_le_inv20001_sq {X : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X) :
    Goldbach.AO_WeightMass.weight_mass X ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    exact le_trans (by norm_num)
      (Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX)
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hw :
      Goldbach.BG_Bank.wScale X ≤ (1 : ℝ) / (20001 : ℝ) := by
    have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    have hw_le_mul :
        Goldbach.BG_Bank.wScale X ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) := by
      nlinarith
    have hscale :
        Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / (20001 : ℝ) := by
      have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlog_pos
      have h20001r : (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1 = (20001 : ℝ) := by
        norm_num [Goldbach.BG_Bank.H, Goldbach.BankParams.H]
      unfold Goldbach.BG_Bank.wScale
      set d : ℝ := (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1
      have hd20001 : d = (20001 : ℝ) := by simpa [d] using h20001r
      calc
        (1 : ℝ) / (Real.log (X : ℝ) * (2 * Goldbach.BG_Bank.H + 1)) * Real.log (X : ℝ)
            = (1 : ℝ) / (Real.log (X : ℝ) * d) * Real.log (X : ℝ) := by
              simp [d, Nat.cast_add, Nat.cast_mul]
        _ = Real.log (X : ℝ) / (Real.log (X : ℝ) * d) := by
              simpa using
                (one_div_mul_eq_div (a := Real.log (X : ℝ) * d) (b := Real.log (X : ℝ)))
        _ = (Real.log (X : ℝ) * (1 : ℝ)) / (Real.log (X : ℝ) * d) := by
              simp [mul_assoc]
        _ = (1 : ℝ) / d := by
              simpa [mul_assoc] using
                (mul_div_mul_left (c := Real.log (X : ℝ)) (a := (1 : ℝ)) (b := d) hlogne)
        _ = (1 : ℝ) / (20001 : ℝ) := by
              simp [hd20001]
    exact le_trans hw_le_mul (by simpa [hscale])
  have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  have hcap0 : 0 ≤ (1 : ℝ) / (20001 : ℝ) := by norm_num
  have hsq :
      (Goldbach.BG_Bank.wScale X) ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    have :=
      mul_le_mul hw hw hw0 hcap0
    simpa [pow_two] using this
  simpa [Goldbach.AO_WeightMass.weight_mass] using hsq

private lemma sigmaHonestWeightedUpperEnv_le_swapGapUpperEnv {X : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X) :
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
      ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv := by
  have hweight := weight_mass_le_inv20001_sq hX
  have hcoeff_le_one :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff ≤ (1 : ℝ) := by
    dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff,
      Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
      Goldbach.AO_SigmaModel.Canon.Ucut]
    norm_num [Goldbach.BankParams.H]
  have htail_le :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
        ≤ Goldbach.AO_WeightMass.weight_mass X * (3e-4 : ℝ) := by
    dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv]
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    have hsmall :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
        ≤ Goldbach.AO_WeightMass.weight_mass X := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hcoeff_le_one hwm_nonneg
    nlinarith
  have hupper :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        ≤ (((30000 : ℝ) + (3e-4 : ℝ)) * (((1 : ℝ) / (20001 : ℝ)) ^ 2)) := by
    have hqpart :
        (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X
          ≤ (30000 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
      have hq0 : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) = (30000 : ℝ) := by
        norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
      rw [hq0]
      exact mul_le_mul_of_nonneg_left hweight (by positivity)
    have htailpart :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
          ≤ (3e-4 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hweight (by positivity : 0 ≤ (3e-4 : ℝ))
      nlinarith [htail_le, h]
    calc
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
          = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X
              + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
                simp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv]
      _ ≤ (30000 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2)
            + (3e-4 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
              exact add_le_add hqpart htailpart
      _ = (((30000 : ℝ) + (3e-4 : ℝ)) * (((1 : ℝ) / (20001 : ℝ)) ^ 2)) := by
            ring
  have hratio_ge_one :
      (1 : ℝ) ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    norm_num [Goldbach.BankParams.H, Goldbach.Analytic.H, Goldbach.BG_Identity.Ucut]
  have h1252 :
      (((30000 : ℝ) + (3e-4 : ℝ)) * (((1 : ℝ) / (20001 : ℝ)) ^ 2))
        ≤ ((1252 : ℝ) / 10 ^ 6) := by
    norm_num
  have hmain :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) * (((1252 : ℝ) / 10 ^ 6)) := by
    have hr :
        ((1252 : ℝ) / 10 ^ 6)
          ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) * (((1252 : ℝ) / 10 ^ 6)) := by
      have hpos : 0 < ((1252 : ℝ) / 10 ^ 6) := by positivity
      nlinarith
    exact le_trans hupper (le_trans h1252 hr)
  have hswap :
      ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) * (((1252 : ℝ) / 10 ^ 6))
        ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv := by
    have hmass_pos : 0 < Goldbach.BG_Identity.mass_BG := Goldbach.BG_Identity.mass_BG_pos
    have hsig_nonneg : 0 ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
      exact div_nonneg Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ_nonneg (le_of_lt hmass_pos)
    have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      have hnum_nonneg : 0 ≤ (2 * H + 1 : ℝ) := by
        norm_num [Goldbach.BankParams.H, Goldbach.Analytic.H]
      have hden_pos : 0 < (Goldbach.BG_Identity.Ucut : ℝ) := by
        norm_num [Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
      exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
    dsimp [Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv]
    have hinside :
        ((1252 : ℝ) / 10 ^ 6)
          ≤ ((1252 : ℝ) / 10 ^ 6)
              + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
      linarith
    exact mul_le_mul_of_nonneg_left hinside hratio_nonneg
  exact le_trans hmain hswap

private lemma mass_BG_le_one : Goldbach.BG_Identity.mass_BG ≤ (1 : ℝ) := by
  have hsplit := Goldbach.BG_Identity.sum_bandU_outer_inner (f := fun k => Goldbach.BG_Identity.K_full k)
  have houter_nonneg : 0 ≤ ∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k := by
    exact Finset.sum_nonneg (fun _ hk => Goldbach.BG_Identity.K_full_nonneg_outer hk)
  have hfull :
      (∑ k ∈ Goldbach.BG_Identity.bandU, Goldbach.BG_Identity.K_full k) = 1 := by
    simpa [Goldbach.BG_Identity.tentFullMass, Goldbach.BG_Identity.tentFullWeight] using
      Goldbach.BG_Identity.tentFullMass_eq_one
  have :
      (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k)
        ≤ (∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k)
          + (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) := by
    simpa using add_le_add_right houter_nonneg
  calc
    Goldbach.BG_Identity.mass_BG
        = (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) := by
            simp [Goldbach.BG_Identity.mass_BG]
    _ ≤ (∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k)
          + (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) := this
    _ = 1 := by simpa [hsplit] using hfull

private lemma sigmaHonestWeightedUpperEnv_le_swapGapUpperEnvWeighted {X : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X) :
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
      ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X := by
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  have hratio_ge_one :
      (1 : ℝ) ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    norm_num [Goldbach.BankParams.H, Goldbach.Analytic.H, Goldbach.BG_Identity.Ucut]
  have hcoeff_le_one :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff ≤ (1 : ℝ) := by
    dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff,
      Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
      Goldbach.AO_SigmaModel.Canon.Ucut]
    norm_num [Goldbach.BankParams.H]
  have htail_le :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
        ≤ Goldbach.AO_WeightMass.weight_mass X * (3e-4 : ℝ) := by
    dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv]
    have hsmall :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
        ≤ Goldbach.AO_WeightMass.weight_mass X := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hcoeff_le_one hwm_nonneg
    nlinarith
  have hupper :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        ≤ Goldbach.AO_WeightMass.weight_mass X * (((30000 : ℝ) + (3e-4 : ℝ))) := by
    have hqpart :
        (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X
          ≤ Goldbach.AO_WeightMass.weight_mass X * (30000 : ℝ) := by
      have hq0 : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) = (30000 : ℝ) := by
        norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
      rw [hq0]
      simpa [mul_comm]
    calc
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
          = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X
              + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
                simp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv]
      _ ≤ Goldbach.AO_WeightMass.weight_mass X * (30000 : ℝ)
            + Goldbach.AO_WeightMass.weight_mass X * (3e-4 : ℝ) := by
              exact add_le_add hqpart htail_le
      _ = Goldbach.AO_WeightMass.weight_mass X * (((30000 : ℝ) + (3e-4 : ℝ))) := by
            ring
  have hinside_ge :
      ((30000 : ℝ) + (3e-4 : ℝ))
        ≤ (((1252 : ℝ) / 10 ^ 6)
              + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
            * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    have hmass_pos : 0 < Goldbach.BG_Identity.mass_BG := Goldbach.BG_Identity.mass_BG_pos
    have hmass_le_one : Goldbach.BG_Identity.mass_BG ≤ (1 : ℝ) := by
      exact mass_BG_le_one
    have hCσ_ge :
        (30000 : ℝ) ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ := by
      have hCσ :
          Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ
            = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) :=
        rfl
      have hQ0 : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) = (30000 : ℝ) := by
        norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
      nlinarith [hCσ, hQ0]
    have hdiv_ge :
        (30000 : ℝ) ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
      have h : (1 : ℝ) ≤ (Goldbach.BG_Identity.mass_BG)⁻¹ := by
        exact (one_le_inv₀ hmass_pos).2 hmass_le_one
      have hσ_nonneg : 0 ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ := Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ_nonneg
      calc
        (30000 : ℝ) ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ := hCσ_ge
        _ = Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ * 1 := by ring
        _ ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ * (Goldbach.BG_Identity.mass_BG)⁻¹ := by
              exact mul_le_mul_of_nonneg_left h hσ_nonneg
        _ = Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
              rw [div_eq_mul_inv]
    have hinside :
        ((30000 : ℝ) + (3e-4 : ℝ))
          ≤ ((1252 : ℝ) / 10 ^ 6)
              + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
      nlinarith
    have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      have hnum_nonneg : 0 ≤ (2 * H + 1 : ℝ) := by
        norm_num [Goldbach.BankParams.H, Goldbach.Analytic.H]
      have hden_pos : 0 < (Goldbach.BG_Identity.Ucut : ℝ) := by
        norm_num [Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
      exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
    have hmul :
        ((1252 : ℝ) / 10 ^ 6)
            + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG
          ≤ ((((1252 : ℝ) / 10 ^ 6)
                + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
              * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))) := by
      have hpos :
          0 ≤ ((1252 : ℝ) / 10 ^ 6)
                + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
        have h1252 : 0 ≤ ((1252 : ℝ) / 10 ^ 6) := by positivity
        have hsig_nonneg :
            0 ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
          exact div_nonneg Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ_nonneg (le_of_lt hmass_pos)
        exact add_nonneg h1252 hsig_nonneg
      nlinarith
    exact le_trans hinside hmul
  have hscaled :
      Goldbach.AO_WeightMass.weight_mass X * (((30000 : ℝ) + (3e-4 : ℝ)))
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * ((((1252 : ℝ) / 10 ^ 6)
                  + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
                * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hinside_ge hwm_nonneg
  calc
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        ≤ Goldbach.AO_WeightMass.weight_mass X * (((30000 : ℝ) + (3e-4 : ℝ))) := hupper
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ((((1252 : ℝ) / 10 ^ 6)
                + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
              * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))) := hscaled
    _ = Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X := by
          simp [Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted,
            Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv, mul_assoc, mul_left_comm, mul_comm]

/--
Any projected bridge theorem routed through `sigmaHonestWeighted` is already too coarse to close
the canonical lower-gap comparison if one uses the legacy absolute swap budget.
-/
theorem Lproj_le_ΔsigmaHonest_proj_of_even
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X → N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
            - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    Goldbach.ProjectedMajorTermDirectProto.Lproj X
      ≤ Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj_abs Δhonest X := by
  have hmem : X ∈ EvenIn X Goldbach.Analytic.H :=
    Goldbach.Windows.mem_EvenIn_self hEven
  have hlower :
      Goldbach.ProjectedMajorTermDirectProto.Lproj X
        ≤ Goldbach.ProjectedMajorTermDirectProto.Mproj X X :=
    Goldbach.ProjectedMajorTermDirectProto.projected_major_lower hX hmem
  have hbridge :
      |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X
          - (Goldbach.MainTerm.M C2_numeric) X| ≤ Δhonest X :=
    hHonest (X := X) (N := X) hX hmem
  have hΔ_nonneg : 0 ≤ Δhonest X := le_trans (abs_nonneg _) hbridge
  have hmain_le :
      (Goldbach.MainTerm.M C2_numeric) X
        ≤ |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| + Δhonest X := by
    have htmp := (abs_sub_le_iff.mp hbridge).2
    have habs :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X
          ≤ |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| := by
      exact le_abs_self _
    linarith
  have hsigma_upper :
      |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X|
        ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X :=
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted_upper_window
      (X := X) (N := X) hX hmem
  have henv :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv := by
    exact sigmaHonestWeightedUpperEnv_le_swapGapUpperEnv hX
  calc
    Goldbach.ProjectedMajorTermDirectProto.Lproj X
        ≤ Goldbach.ProjectedMajorTermDirectProto.Mproj X X := hlower
    _ = (Goldbach.MainTerm.M C2_numeric) X := by rfl
    _ ≤ |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| + Δhonest X := hmain_le
    _ ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X + Δhonest X := by
          exact add_le_add_right hsigma_upper _
    _ ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv + Δhonest X := by
          exact add_le_add_right henv _
    _ ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
          + Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv + Δhonest X := by
            have htail_nonneg : 0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
              have hcoeff_nonneg :
                  0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff := by
                dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff]
                dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
                  Goldbach.AO_SigmaModel.Canon.Ucut]
                norm_num [Goldbach.BankParams.H]
              have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
                have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
                simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
              dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv]
              exact mul_nonneg (mul_nonneg hcoeff_nonneg hwm_nonneg) (by norm_num)
            linarith
    _ = Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj_abs Δhonest X := by
          simp [Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj_abs, add_assoc, add_left_comm, add_comm]

theorem not_ΔsigmaHonest_proj_lt_Lproj_of_even
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X → N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
            - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    ¬ Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj_abs Δhonest X
        < Goldbach.ProjectedMajorTermDirectProto.Lproj X := by
  exact not_lt_of_ge (Lproj_le_ΔsigmaHonest_proj_of_even (Δhonest := Δhonest)
    (hHonest := hHonest) hX hEven)

theorem not_ΔsigmaHonest_proj_lt_Lproj_at_X0
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X → N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
            - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X) :
    ¬ Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj_abs Δhonest Goldbach.Analytic.X0
        < Goldbach.ProjectedMajorTermDirectProto.Lproj Goldbach.Analytic.X0 := by
  have hX : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 := le_rfl
  have hEven : Goldbach.Windows.IsEven Goldbach.Analytic.X0 := by
    exact Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0)
  exact not_ΔsigmaHonest_proj_lt_Lproj_of_even (Δhonest := Δhonest)
    (hHonest := hHonest) hX hEven

/--
Even the sharpened weighted projected route through `sigmaHonestWeighted` cannot close on the
canonical window: the honest comparison budget already has to absorb the full projected lower term
up to the weighted sigma envelope, and all remaining terms in `Δproj_sigmaHonest` are nonnegative.
-/
theorem Lproj_le_Δproj_sigmaHonest_of_even
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X → N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
            - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    Goldbach.ProjectedMajorTermDirectProto.Lproj X
      ≤ Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest Δhonest X := by
  have hmem : X ∈ EvenIn X Goldbach.Analytic.H :=
    Goldbach.Windows.mem_EvenIn_self hEven
  have hlower :
      Goldbach.ProjectedMajorTermDirectProto.Lproj X
        ≤ Goldbach.ProjectedMajorTermDirectProto.Mproj X X :=
    Goldbach.ProjectedMajorTermDirectProto.projected_major_lower hX hmem
  have hbridge :
      |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X
          - (Goldbach.MainTerm.M C2_numeric) X| ≤ Δhonest X :=
    hHonest (X := X) (N := X) hX hmem
  have hmain_le :
      (Goldbach.MainTerm.M C2_numeric) X
        ≤ |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| + Δhonest X := by
    have htmp := (abs_sub_le_iff.mp hbridge).2
    have habs :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X
          ≤ |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| := by
      exact le_abs_self _
    linarith
  have hsigma_upper :
      |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X|
        ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X :=
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted_upper_window
      (X := X) (N := X) hX hmem
  have henv :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X :=
    sigmaHonestWeightedUpperEnv_le_swapGapUpperEnvWeighted hX
  have houter_nonneg :
      0 ≤ Goldbach.AO_WeightMass.weight_mass X
            * (((1252 : ℝ) / 10 ^ 6)
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    have hconst_nonneg :
        0 ≤ (((1252 : ℝ) / 10 ^ 6) * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
      have h1252 : 0 ≤ ((1252 : ℝ) / 10 ^ 6) := by positivity
      have htail : 0 ≤ ((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed := by
        have hclosed : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
          norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
        nlinarith
      exact mul_nonneg h1252 htail
    exact mul_nonneg hwm_nonneg hconst_nonneg
  have htail_nonneg : 0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
    have hcoeff_nonneg :
        0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff := by
      dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff,
        Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
        Goldbach.AO_SigmaModel.Canon.Ucut]
      norm_num [Goldbach.BankParams.H]
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv]
    exact mul_nonneg (mul_nonneg hcoeff_nonneg hwm_nonneg) (by norm_num)
  calc
    Goldbach.ProjectedMajorTermDirectProto.Lproj X
        ≤ Goldbach.ProjectedMajorTermDirectProto.Mproj X X := hlower
    _ = (Goldbach.MainTerm.M C2_numeric) X := by rfl
    _ ≤ |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| + Δhonest X := hmain_le
    _ ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X + Δhonest X := by
          exact add_le_add_right hsigma_upper _
    _ ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X + Δhonest X := by
          exact add_le_add_right henv _
    _ ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
          + Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X + Δhonest X := by
            linarith
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * (((1252 : ℝ) / 10 ^ 6)
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + (Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
              + Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X + Δhonest X) := by
            linarith
    _ = Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest Δhonest X := by
          simp [Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest,
            Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj,
            add_assoc, add_left_comm, add_comm]

theorem not_Δproj_sigmaHonest_lt_Lproj_of_even
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X → N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
            - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    ¬ Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest Δhonest X
        < Goldbach.ProjectedMajorTermDirectProto.Lproj X := by
  exact not_lt_of_ge (Lproj_le_Δproj_sigmaHonest_of_even (Δhonest := Δhonest)
    (hHonest := hHonest) hX hEven)

theorem not_Δproj_sigmaHonest_lt_Lproj_at_X0
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X → N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
            - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δhonest X) :
    ¬ Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest Δhonest Goldbach.Analytic.X0
        < Goldbach.ProjectedMajorTermDirectProto.Lproj Goldbach.Analytic.X0 := by
  have hX : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 := le_rfl
  have hEven : Goldbach.Windows.IsEven Goldbach.Analytic.X0 := by
    exact Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0)
  exact not_Δproj_sigmaHonest_lt_Lproj_of_even (Δhonest := Δhonest)
    (hHonest := hHonest) hX hEven

end

end Goldbach.ProjectedSigmaBridgeObstacle
