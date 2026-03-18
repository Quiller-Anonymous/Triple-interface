import Mathlib
import Goldbach.BankPieces.Cert.ProjectedSigmaBridge
import Goldbach.Cert.MajorArcModules.MainTermQ0
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Goldbach.Cert.MajorArcStep24MainTermIdentification
import Goldbach.MainTerm
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.ProjectedConstGapBridge

open Goldbach
open Goldbach.Analytic
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.MainTermQ0
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Complex

noncomputable section

private lemma sigmaModelCoeff_nonneg : 0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff := by
  dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff,
    Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
    Goldbach.AO_SigmaModel.Canon.Ucut]
  norm_num [Goldbach.BankParams.H]

/--
Step-24 q/a main term in the same scale as `conv_ref_const`.

This is the exact constant-model object on the projected route; it packages the weighted
`qa_mainTerm_Q0C` term rather than bounding `conv_ref_const` and `MainTerm.M` separately.
-/
noncomputable def qaMainTermWeightedC (X N : ℕ) : ℂ :=
  (((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
      * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ)
    * qa_mainTerm_Q0C N

/-- Arithmetic upper envelope for the Step-24 q/a main term. -/
noncomputable def qaPhaseUpperConst : ℝ :=
  (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0).sum (fun q =>
    Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))

/-- Weighted `X`-dependent envelope for the exact q/a main term. -/
noncomputable def qaMainTermWeightedUpperEnv (X : ℕ) : ℝ :=
  Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
    * Goldbach.AO_WeightMass.weight_mass X
    * qaPhaseUpperConst

private lemma qaPhaseUpperConst_nonneg : 0 ≤ qaPhaseUpperConst := by
  unfold qaPhaseUpperConst
  refine Finset.sum_nonneg ?_
  intro q hq
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_nonneg : 0 ≤ (Nat.totient q : ℝ) := by positivity
  exact div_nonneg hmu_nonneg hphi_nonneg

theorem qaMainTermWeightedUpperEnv_nonneg (X : ℕ) : 0 ≤ qaMainTermWeightedUpperEnv X := by
  have hcoeff_nonneg : 0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff :=
    sigmaModelCoeff_nonneg
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  exact mul_nonneg (mul_nonneg hcoeff_nonneg hwm_nonneg) qaPhaseUpperConst_nonneg

private theorem norm_phaseSum_neg_le_totient (q N : ℕ) :
    ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖ ≤ (Nat.totient q : ℝ) := by
  calc
    ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖
        = ‖star (ramanujanSumC q N)‖ := by
            rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.phaseSum_neg_eq_star_ramanujanSumC]
    _ = ‖ramanujanSumC q N‖ := by simp
    _ ≤ (Nat.totient q : ℝ) := norm_ramanujanSumC_le_totient q N

theorem norm_qa_mainTerm_Q0C_le_qaPhaseUpperConst (N : ℕ) :
    ‖qa_mainTerm_Q0C N‖ ≤ qaPhaseUpperConst := by
  rw [qa_mainTerm_Q0C_eq_sigma_mainTerm_Q0C]
  rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C_eq_sum_muSq_phaseSum_neg]
  refine le_trans (norm_sum_le (s := Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0)
    (f := fun q =>
      ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))))) ?_
  refine Finset.sum_le_sum ?_
  intro q hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_pos_nat : 0 < Nat.totient q := by
    exact Nat.totient_pos.mpr (lt_of_lt_of_le (by decide : 0 < 1) hq1)
  have hphi_pos : 0 < (Nat.totient q : ℝ) := by exact_mod_cast hphi_pos_nat
  have hfrac_nonneg : 0 ≤ (1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) := by positivity
  have hphase := norm_phaseSum_neg_le_totient q N
  calc
    ‖(((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) )‖
        =
      Goldbach.AO_OffDiag.TailBlock.muSq q
        * (1 / ((Nat.totient q : ℝ) ^ 2))
        * ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖ := by
          rw [norm_mul, norm_mul]
          simp [Real.norm_eq_abs, abs_of_nonneg hmu_nonneg, abs_of_nonneg hfrac_nonneg, mul_assoc]
    _ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q
          * (1 / ((Nat.totient q : ℝ) ^ 2))
          * (Nat.totient q : ℝ) := by
            exact mul_le_mul_of_nonneg_left hphase (mul_nonneg hmu_nonneg hfrac_nonneg)
    _ = Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
          field_simp [hphi_pos.ne']

theorem norm_qaMainTermWeightedC_le_upper (X N : ℕ) :
    ‖qaMainTermWeightedC X N‖ ≤ qaMainTermWeightedUpperEnv X := by
  have hcoeff_nonneg : 0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff := 
    sigmaModelCoeff_nonneg
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  have hcoeffwm_nonneg :
      0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X := by
    exact mul_nonneg hcoeff_nonneg hwm_nonneg
  have hcoeff_norm :
    ‖(((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ)‖
        =
      Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
        * Goldbach.AO_WeightMass.weight_mass X := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeffwm_nonneg]
  calc
    ‖qaMainTermWeightedC X N‖
        = ‖(((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
                * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ)‖
            * ‖qa_mainTerm_Q0C N‖ := by
              rw [qaMainTermWeightedC, norm_mul]
    _ = (Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X)
            * ‖qa_mainTerm_Q0C N‖ := by rw [hcoeff_norm]
    _ ≤ (Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X)
            * qaPhaseUpperConst := by
              exact mul_le_mul_of_nonneg_left
                (norm_qa_mainTerm_Q0C_le_qaPhaseUpperConst (N := N))
                (mul_nonneg hcoeff_nonneg hwm_nonneg)
    _ = qaMainTermWeightedUpperEnv X := by
          simp [qaMainTermWeightedUpperEnv]

theorem qaMainTermWeightedC_eq_sigmaTruncWeightedC (X N : ℕ) :
    qaMainTermWeightedC X N
      =
    (((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ)) : ℂ) := by
  rw [qaMainTermWeightedC, qa_mainTerm_Q0C_eq_sigma_trunc_Q0]
  simp [mul_assoc, mul_left_comm, mul_comm]

/--
Exact reduction of the q/a-vs-main-term comparison to the real weighted `sigma_trunc_Q0` seam.

After the q/a-envelope sharpening, this is the clean remaining comparison target.
-/
theorem qaMainTermWeighted_mainTerm_gap_of_sigmaTrunc_gap
    (Δqa : ℕ → ℝ)
    (hσ :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X
            * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δqa X)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖qaMainTermWeightedC X N - (((Goldbach.MainTerm.M C2_numeric) N : ℝ) : ℂ)‖ ≤ Δqa X := by
  have hσ' :
      |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
        - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δqa X :=
    hσ (X := X) (N := N) hX hN
  have hcast :
      ‖(((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
            - (Goldbach.MainTerm.M C2_numeric) N : ℝ)) : ℂ)‖
        =
      |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
        - (Goldbach.MainTerm.M C2_numeric) N| := by
    simpa [Real.norm_eq_abs] using
      (Complex.norm_real
        (Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - (Goldbach.MainTerm.M C2_numeric) N))
  have hσ'' :
      ‖(((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
            - (Goldbach.MainTerm.M C2_numeric) N : ℝ)) : ℂ)‖
        ≤ Δqa X := by
    rw [hcast]
    exact hσ'
  simpa [qaMainTermWeightedC_eq_sigmaTruncWeightedC (X := X) (N := N)] using hσ''

/-- The weighted q/a main term is exactly the constant reference operator. -/
theorem qaMainTermWeightedC_eq_conv_ref_const (X N : ℕ) :
    qaMainTermWeightedC X N = (Goldbach.BG_Identity.conv_ref_const X N : ℂ) := by
  rw [qaMainTermWeightedC, qa_mainTerm_Q0C_eq_sigma_trunc_Q0]
  have hconv :
      Goldbach.BG_Identity.conv_ref_const X N
        = Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X
            * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N :=
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.conv_ref_const_eq_sigmaTruncWeighted X N
  calc
    (((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ)
        * (((Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ))
        =
      ((Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
          * Goldbach.AO_WeightMass.weight_mass X
          * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (Goldbach.BG_Identity.conv_ref_const X N : ℂ) := by
          simpa [hconv] using congrArg (fun t : ℝ => (t : ℂ)) hconv.symm

/--
If the weighted Step-24 q/a main term is close to `MainTerm.M`, then the constant reference
operator is close to `MainTerm.M` by the same amount.

This is the precise remaining projected-constant seam: future work should target the q/a main term
directly, rather than the coarse triangle envelope used by `Δconst_proj`.
-/
theorem conv_ref_const_mainTerm_gap_of_qaMainTermWeighted_gap
    (Δqa : ℕ → ℝ)
    (hqa :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ‖qaMainTermWeightedC X N - (((Goldbach.MainTerm.M C2_numeric) N : ℝ) : ℂ)‖
            ≤ Δqa X)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N|
      ≤ Δqa X := by
  have hqa' := hqa (X := X) (N := N) hX hN
  have hcast :
      ‖((Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N : ℝ) : ℂ)‖
        =
      |Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N| := by
    simpa [Real.norm_eq_abs] using
      (Complex.norm_real
        (Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N))
  have hqa'' :
      ‖((Goldbach.BG_Identity.conv_ref_const X N - (Goldbach.MainTerm.M C2_numeric) N : ℝ) : ℂ)‖
        ≤ Δqa X := by
    simpa [qaMainTermWeightedC_eq_conv_ref_const (X := X) (N := N)] using hqa'
  rw [hcast] at hqa''
  exact hqa''

end

end Goldbach.BankPieces.Cert.ProjectedConstGapBridge
