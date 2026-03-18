import Goldbach.CompleteTenorFunX_DirectProjectedTrueFunXCanon
import Goldbach.Cert.SigmaUpperOnWindowCanon

namespace Goldbach.ProjectedTrueScaleObstacle

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

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

private lemma sigmaModelCoeff_le_one :
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff ≤ (1 : ℝ) := by
  dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff,
    Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
    Goldbach.AO_SigmaModel.Canon.Ucut]
  norm_num [Goldbach.BankParams.H]

private lemma sigmaHonestWeightedUpperEnv_le_constSwapWeighted {X : ℕ} :
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
      ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X := by
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  have hCσ :
      Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ = (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) :=
    Goldbach.Cert.SigmaUpperOnWindowCanon.Cσ_eq_Q0
  have hQ0 :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) = (30000 : ℝ) := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  have hratio_ge_one :
      (1 : ℝ) ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    norm_num [Goldbach.BankParams.H, Goldbach.Analytic.H, Goldbach.BG_Identity.Ucut]
  have hdiv_ge :
      (30000 : ℝ)
        ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
    have hmass_pos : 0 < Goldbach.BG_Identity.mass_BG := Goldbach.BG_Identity.mass_BG_pos
    have hmass_le : Goldbach.BG_Identity.mass_BG ≤ (1 : ℝ) := mass_BG_le_one
    have hCσ_ge : (30000 : ℝ) ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ := by
      rw [hCσ, hQ0]
    have h : (1 : ℝ) ≤ (Goldbach.BG_Identity.mass_BG)⁻¹ := by
      exact (one_le_inv₀ hmass_pos).2 hmass_le
    calc
      (30000 : ℝ) ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ := hCσ_ge
      _ = Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ * 1 := by ring
      _ ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ * (Goldbach.BG_Identity.mass_BG)⁻¹ := by
            exact mul_le_mul_of_nonneg_left h Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ_nonneg
      _ = Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
            rw [div_eq_mul_inv]
  have hsigma_small :
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff * (3e-4 : ℝ)
        ≤ ((1252 : ℝ) / 10 ^ 6) := by
    have hmul :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff * (3e-4 : ℝ)
          ≤ (1 : ℝ) * (3e-4 : ℝ) := by
      exact mul_le_mul_of_nonneg_right sigmaModelCoeff_le_one (by positivity)
    nlinarith
  have hinside :
      (30000 : ℝ)
        + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff * (3e-4 : ℝ)
      ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnv := by
    have hbase :
        (30000 : ℝ)
          + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff * (3e-4 : ℝ)
        ≤ ((1252 : ℝ) / 10 ^ 6)
            + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
      nlinarith
    have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      positivity
    calc
      (30000 : ℝ)
          + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff * (3e-4 : ℝ)
        ≤ ((1252 : ℝ) / 10 ^ 6)
            + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := hbase
      _ ≤ (((1252 : ℝ) / 10 ^ 6)
            + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
            * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
              nlinarith
      _ = Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnv := by
            simp [Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnv, mul_comm]
  calc
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
        = Goldbach.AO_WeightMass.weight_mass X
            * ((30000 : ℝ)
                + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff * (3e-4 : ℝ)) := by
              simp only [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv,
                Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv, hQ0]
              ring
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnv := by
            exact mul_le_mul_of_nonneg_left hinside hwm_nonneg
    _ = Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X := by
          simp [Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted]

private lemma projectedScaleUpper_nonneg (X : ℕ) :
    0 ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.projectedScaleUpper X := by
  have hnum : 0 ≤ (((X + H : ℕ) : ℝ)) := by positivity
  have hden : 0 ≤ (Real.log (X : ℝ)) ^ 2 := by positivity
  exact div_nonneg hnum hden

private lemma sigmaHonest_fixed_eq_sigmaTrue {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.AO_OffDiag.sigmaHonest N
      = Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hN_ge_X
  have hN0 : N ≠ 0 := Nat.ne_of_gt <| lt_of_lt_of_le (by decide : 0 < X0) hN_ge_X0
  calc
    Goldbach.AO_OffDiag.sigmaHonest N
        = Goldbach.AO_OffDiag.EntryPointTenorFunX.sigmaHonest
            (fun _ => Goldbach.AO_OffDiag.TailBlock.Q0) X N := by
            simp [Goldbach.AO_OffDiag.sigmaHonest,
              Goldbach.AO_OffDiag.EntryPointTenorFunX.sigmaHonest,
              Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0,
              Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc,
              Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail,
              Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail,
              Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm,
              Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTerm,
              Goldbach.AO_OffDiag.TailBlock.ramanujanR,
              Goldbach.AO_OffDiag.TailBlockFun.ramanujanR,
              Goldbach.AO_OffDiag.TailBlock.ramanujanZ,
              Goldbach.AO_OffDiag.TailBlockFun.ramanujanZ,
              Goldbach.AO_OffDiag.muSq,
              Goldbach.AO_OffDiag.TailBlock.muSq,
              Goldbach.AO_OffDiag.TailBlockFun.muSq]
    _ = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N :=
          Goldbach.BankPieces.Cert.RamanujanSeriesCutoffBridge.sigmaHonest_eq_sigmaSeriesRamanujan
            (Q := fun _ => Goldbach.AO_OffDiag.TailBlock.Q0) hN0
    _ = Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal.sigma N := by
          symm
          exact Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal.sigma_eq_ramanujan_global N
    _ = Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N := by
          symm
          exact Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization.sigma_eq_euler_global
            (Nat.pos_of_ne_zero hN0)

private lemma ΔprojFunX_ge_scale_piece
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ) (X : ℕ) :
    Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X + Δscale X
      ≤ Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX Hoff
          (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
            (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)) X := by
  have hpayload_nonneg :
      0 ≤ Goldbach.AO_WeightMass.weight_mass X
            * (((1252 : ℝ) / 10 ^ 6)
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
    have hwm : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    have hconst : 0 ≤ (((1252 : ℝ) / 10 ^ 6) * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
      have hct : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
        norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
      positivity
    exact mul_nonneg hwm hconst
  have htail_nonneg :
      0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
    have hcoeff : 0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff := by
      dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff,
        Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
        Goldbach.AO_SigmaModel.Canon.Ucut]
      norm_num [Goldbach.BankParams.H]
    have hwm : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv]
    positivity
  have hΔtrue_nonneg :
      0 ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX Hoff X := by
    exact mul_nonneg (projectedScaleUpper_nonneg X) Hoff.eps_nonneg
  have hsum_nonneg :
      0 ≤
        Goldbach.AO_WeightMass.weight_mass X
              * (((1252 : ℝ) / 10 ^ 6)
                  * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
          + Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX Hoff X
          + Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX Hoff X := by
    nlinarith
  calc
    Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X + Δscale X
        ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X + Δscale X
          + (Goldbach.AO_WeightMass.weight_mass X
              * (((1252 : ℝ) / 10 ^ 6)
                  * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
            + Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX Hoff X
            + Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX Hoff X) := by
              exact le_add_of_nonneg_right hsum_nonneg
    _ = Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX Hoff
          (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
            (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)) X := by
          simp [Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX,
            Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔprojFunX,
            Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst,
            Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale]
          ring

/-- The remaining scale-gap input already forces the honest true projected route over budget. -/
theorem Mtrue_le_ΔprojFunX_of_scale_gap
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ)
    (hScale :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              - ((N : ℝ) / (Real.log (N : ℝ)) ^ 2))
            * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N|
            ≤ Δscale X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X
      ≤ Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX Hoff
          (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
            (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)) X := by
  let coeff :=
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
      * Goldbach.AO_WeightMass.weight_mass X
  have hmem : X ∈ EvenIn X Goldbach.Analytic.H := Goldbach.Windows.mem_EvenIn_self hEven
  have hcoeff_upper :
      |coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X|
        ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X := by
    have hsigma : Goldbach.AO_OffDiag.sigmaHonest X
        = Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X :=
      sigmaHonest_fixed_eq_sigmaTrue hX hmem
    have hupper :=
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted_upper_window
        (X := X) (N := X) hX hmem
    calc
      |coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X|
          = |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X X| := by
              simp [coeff, Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted,
                hsigma, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X := hupper
  have hM_vs_scale :
      |coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X
          - Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X|
        ≤ Δscale X := by
    have hsplit :
        coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X
          - Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X
          =
        (Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X
            - ((X : ℝ) / (Real.log (X : ℝ)) ^ 2))
          * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X := by
            simp [coeff, Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue,
              Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue,
              Goldbach.BankPieces.Cert.TrueSingularSeries.mainTermGlobal,
              Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal, Goldbach.MainTerm.M,
              div_eq_mul_inv]
            ring_nf
    calc
      |coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X
          - Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X|
          =
        |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X
            - ((X : ℝ) / (Real.log (X : ℝ)) ^ 2))
          * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X| := by
            rw [hsplit]
      _ ≤ Δscale X := hScale (X := X) (N := X) hX hmem
  have hcoeff_le :
      coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X
        ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X := by
    exact le_trans (le_abs_self _) hcoeff_upper
  have hM_le_swap :
      Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X
        ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X
            + Δscale X := by
    have hM_le_sigma :
        Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X
          ≤ coeff * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue X + Δscale X := by
      have hpair := abs_le.mp hM_vs_scale
      linarith
    have hupper :
        Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X
          ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X
              + Δscale X := by
      linarith
    have hswap :
        Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeightedUpperEnv X + Δscale X
          ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.constSwapGapUpperEnvWeighted X
              + Δscale X := by
      exact add_le_add_right (sigmaHonestWeightedUpperEnv_le_constSwapWeighted (X := X)) (Δscale X)
    exact le_trans hupper hswap
  exact le_trans hM_le_swap (ΔprojFunX_ge_scale_piece Hoff Δscale X)

theorem Ltrue_le_ΔprojFunX_of_even
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ)
    (hScale :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              - ((N : ℝ) / (Real.log (N : ℝ)) ^ 2))
            * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N|
            ≤ Δscale X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X
      ≤ Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX Hoff
          (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
            (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)) X := by
  have hmem : X ∈ EvenIn X Goldbach.Analytic.H := Goldbach.Windows.mem_EvenIn_self hEven
  have hlower :
      Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X
        ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X X :=
    Goldbach.ProjectedTrueMajorTermDirectProto.projected_true_major_lower hX hmem
  exact le_trans hlower (Mtrue_le_ΔprojFunX_of_scale_gap Hoff Δscale hScale hX hEven)

theorem not_ΔprojFunX_lt_Ltrue_of_even
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ)
    (hScale :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              - ((N : ℝ) / (Real.log (N : ℝ)) ^ 2))
            * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N|
            ≤ Δscale X)
    {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    ¬ Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX Hoff
          (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
            (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)) X
        < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X := by
  exact not_lt_of_ge (Ltrue_le_ΔprojFunX_of_even Hoff Δscale hScale hX hEven)

theorem not_ΔprojFunX_lt_Ltrue_at_X0
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ)
    (hScale :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              - ((N : ℝ) / (Real.log (N : ℝ)) ^ 2))
            * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N|
            ≤ Δscale X) :
    ¬ Goldbach.ProjectedTrueMajorTermDirectFunXCanon.ΔprojFunX Hoff
          (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
            (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale))
          Goldbach.Analytic.X0
        < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
  have hEven : Goldbach.Windows.IsEven Goldbach.Analytic.X0 := by
    exact Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0)
  exact not_ΔprojFunX_lt_Ltrue_of_even Hoff Δscale hScale le_rfl hEven

end

end Goldbach.ProjectedTrueScaleObstacle
