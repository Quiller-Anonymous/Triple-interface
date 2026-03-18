import Goldbach.ProofTools
import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
import Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge

namespace Goldbach.BankPieces.Cert.RawScaleFrozenTrivialSmallBeta

open Goldbach
open Goldbach.Windows
open Goldbach.ProofTools.Windows
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-- Window-uniform upper envelope for the trivial freeze budget. -/
noncomputable def etaFreezeTrivialWindow (X : ℕ) : ℝ :=
  etaFreezeTrivial X (X + BankParams.H)

/-- Coarse small-`β` budget obtained by combining residual and trivial freeze costs. -/
noncomputable def etaSmallFrozenTrivial (ηres : ℕ → ℝ) (X : ℕ) : ℝ :=
  ηres X
    + Goldbach.AO_WeightMass.weight_mass X
        * (etaFreezeTrivialWindow X
            * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst)

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

private lemma qaPhaseUpperConst_nonneg :
    0 ≤ Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst := by
  unfold Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst
  refine Finset.sum_nonneg ?_
  intro q hq
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_nonneg : 0 ≤ (Nat.totient q : ℝ) := by
    positivity
  exact div_nonneg hmu_nonneg hphi_nonneg

theorem etaFreezeTrivial_le_window
    {X N : ℕ} (_hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    etaFreezeTrivial X N ≤ etaFreezeTrivialWindow X := by
  have hNle : N ≤ X + BankParams.H := le_right_of_mem_EvenIn hN
  have hup : (N - 2) + 1 ≤ ((X + BankParams.H) - 2) + 1 := by
    exact Nat.succ_le_succ (Nat.sub_le_sub_right hNle 2)
  have hcard :
      (Finset.Ico 4 ((N - 2) + 1)).card
        ≤ (Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card := by
    have hcardN : (Finset.Ico 4 ((N - 2) + 1)).card = ((N - 2) + 1) - 4 := by
      simp
    have hcardTop :
        (Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card = (((X + BankParams.H) - 2) + 1) - 4 := by
      simp
    rw [hcardN, hcardTop]
    exact Nat.sub_le_sub_right hup 4
  have hcardR :
      ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
        ≤ ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) := by
    exact_mod_cast hcard
  have hsq :
      ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
        ≤ ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2 := by
    nlinarith
  have hmul_nonneg :
      0 ≤ (Goldbach.AO_WeightMass.weight_mass X)⁻¹
            * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := by
    have hcap_nonneg : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    exact mul_nonneg (inv_nonneg.mpr (weight_mass_nonneg X)) hcap_nonneg
  unfold etaFreezeTrivial etaFreezeTrivialWindow
  have hcap_nonneg : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
  have hmid :
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hsq hcap_nonneg
  exact mul_le_mul_of_nonneg_left hmid (inv_nonneg.mpr (weight_mass_nonneg X))

theorem etaSmallFrozenTrivial_eq_explicit
    {ηres : ℕ → ℝ} {X : ℕ} (hX : BankParams.X0 ≤ X) :
    etaSmallFrozenTrivial ηres X
      =
    ηres X
      + (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2)
          * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst := by
  have hwm_ne : Goldbach.AO_WeightMass.weight_mass X ≠ 0 := ne_of_gt (weight_mass_pos hX)
  unfold etaSmallFrozenTrivial etaFreezeTrivialWindow etaFreezeTrivial
  field_simp [hwm_ne]

theorem etaSmallFrozenTrivial_ge_explicit
    {ηres : ℕ → ℝ} {X : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hηres : 0 ≤ ηres X) :
    (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * ((Finset.Ico 4 (((X + BankParams.H) - 2) + 1)).card : ℝ) ^ 2)
        * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst
      ≤ etaSmallFrozenTrivial ηres X := by
  rw [etaSmallFrozenTrivial_eq_explicit hX]
  linarith [qaPhaseUpperConst_nonneg,
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg]

/--
Coarse frozen small-`β` certificate on the `κ`-main-term surface.

This uses the existing trivial freeze theorem without any sharpening, and makes the dependence on
`N` window-uniform by replacing it with the top endpoint `X + H`.
-/
theorem norm_corr_integral_major_Q0_small_sub_frozenWeightedMainTermKappaC_le_trivial
    {ηres : ℕ → ℝ}
    {X N : ℕ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ EvenIn X BankParams.H)
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          MeasureTheory.volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hres :
      ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖
        ≤ ηres X) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - frozenWeightedMainTermKappaC X N‖
      ≤ etaSmallFrozenTrivial ηres X := by
  have hX2 : 2 ≤ X := le_trans (by decide : 2 ≤ BankParams.X0) hX
  have hlocal :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
          - frozenWeightedMainTermC X N‖
        ≤ ηres X
            + Goldbach.AO_WeightMass.weight_mass X
                * (etaFreezeTrivial X N
                    * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
    simpa [frozenWeightedMainTermC] using
      (norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_freeze
        (X := X) (N := N)
        (ηres := ηres X) (ηA := etaFreezeTrivial X N)
        hX2 hsep hInner hOuter hres
        (AqLocalC_uniform_freeze_trivial X N hX2))
  have hkappa :
      frozenWeightedMainTermC X N = frozenWeightedMainTermKappaC X N :=
    frozenWeightedMainTermC_eq_kappa X N hX2
  have hlocal' :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
          - frozenWeightedMainTermKappaC X N‖
        ≤ ηres X
            + Goldbach.AO_WeightMass.weight_mass X
                * (etaFreezeTrivial X N
                    * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
    simpa [hkappa] using hlocal
  have hinner :
      etaFreezeTrivial X N * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst
        ≤ etaFreezeTrivialWindow X
            * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst := by
    exact mul_le_mul_of_nonneg_right
      (etaFreezeTrivial_le_window hX hN)
      qaPhaseUpperConst_nonneg
  have hprod :
      Goldbach.AO_WeightMass.weight_mass X
          * (etaFreezeTrivial X N
              * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst)
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (etaFreezeTrivialWindow X
                * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
    exact mul_le_mul_of_nonneg_left hinner (weight_mass_nonneg X)
  calc
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - frozenWeightedMainTermKappaC X N‖
      ≤ ηres X
          + Goldbach.AO_WeightMass.weight_mass X
              * (etaFreezeTrivial X N
                  * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := hlocal'
    _ ≤ ηres X
          + Goldbach.AO_WeightMass.weight_mass X
              * (etaFreezeTrivialWindow X
                  * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
          exact add_le_add_left hprod (ηres X)
    _ = etaSmallFrozenTrivial ηres X := by
          simp [etaSmallFrozenTrivial]

end

end Goldbach.BankPieces.Cert.RawScaleFrozenTrivialSmallBeta
