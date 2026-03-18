import Goldbach.BankPieces.Cert.RawScaleSmallBetaModel
import Goldbach.Cert.MajorArcModules.MainTermQ0
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Goldbach.Cert.MajorArcStep24AnalyticMainTerm
import Goldbach.Cert.MajorArcExponentialPrelude

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex
open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcModules.MainTermQ0
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.BankPieces.Cert.ProjectedConstGapBridge

noncomputable section

/-- The exact `q`-level arithmetic factor appearing in the Step-24 reduced-residue main term. -/
noncomputable def qPhaseFactor (q N : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) ^ 2)
    * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
    * (∑ a ∈ Rcop q, e (-((N : ℝ) * (a : ℝ) / q)))

/-- A weighted `q`-dependent small-`β` model, allowing the archimedean scalar to vary with `q`. -/
noncomputable def smallBetaModelWeightedQ
    (Aq : ℕ → ℕ → ℕ → ℝ) (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        (((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N

private theorem norm_phaseSum_neg_le_totient (q N : ℕ) :
    ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖ ≤ (Nat.totient q : ℝ) := by
  calc
    ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖
        = ‖star (ramanujanSumC q N)‖ := by
            rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.phaseSum_neg_eq_star_ramanujanSumC]
    _ = ‖ramanujanSumC q N‖ := by simp
    _ ≤ (Nat.totient q : ℝ) := norm_ramanujanSumC_le_totient q N

private theorem norm_qPhaseFactor_le (q N : ℕ) :
    ‖qPhaseFactor q N‖ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [qPhaseFactor, Goldbach.AO_OffDiag.TailBlock.muSq]
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_pos_nat : 0 < Nat.totient q := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hphi_pos : 0 < (Nat.totient q : ℝ) := by exact_mod_cast hphi_pos_nat
  have hfrac_nonneg : 0 ≤ (1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) := by positivity
  calc
    ‖qPhaseFactor q N‖
        =
      Goldbach.AO_OffDiag.TailBlock.muSq q
        * (1 / ((Nat.totient q : ℝ) ^ 2))
        * ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖ := by
          rw [qPhaseFactor, norm_mul, norm_mul]
          rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.moebius_sq_cast_eq_muSq]
          simp [abs_of_nonneg hmu_nonneg, abs_of_nonneg hfrac_nonneg, mul_assoc]
    _ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q
          * (1 / ((Nat.totient q : ℝ) ^ 2))
          * (Nat.totient q : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (norm_phaseSum_neg_le_totient q N)
              (mul_nonneg hmu_nonneg hfrac_nonneg)
    _ = Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
          field_simp [show (Nat.totient q : ℝ) ≠ 0 by positivity]

theorem smallBetaModelWeightedQ_eq_smallBetaModelWeighted
    (Aq : ℕ → ℕ → ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    {X N : ℕ}
    (hAq :
      ∀ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, Aq X N q = A X N) :
    smallBetaModelWeightedQ Aq X N
      =
    Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N := by
  rw [smallBetaModelWeightedQ]
  rw [Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted]
  congr 1
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, (((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      (((A X N : ℝ) : ℂ)) * qPhaseFactor q N := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        simp [hAq q hq]
    _ = (((A X N : ℝ) : ℂ))
          * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, qPhaseFactor q N := by
            rw [Finset.mul_sum]
    _ = (((A X N : ℝ) : ℂ)) * qa_mainTerm_Q0C N := by
          simp [qa_mainTerm_Q0C, qPhaseFactor]

theorem smallBetaModelWeighted_eq_smallBetaModelWeightedQ_const
    (A : ℕ → ℕ → ℝ) (X N : ℕ) :
    Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N
      =
    smallBetaModelWeightedQ (fun X N _q => A X N) X N := by
  symm
  exact smallBetaModelWeightedQ_eq_smallBetaModelWeighted
    (Aq := fun X N _q => A X N) (A := A) (X := X) (N := N)
    (by intro q hq; rfl)

theorem norm_smallBetaModelWeightedQ_sub_smallBetaModelWeighted_le_of_uniform_scalar_gap
    (Aq : ℕ → ℕ → ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    {X N : ℕ} {ηA : ℝ}
    (hAq :
      ∀ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        |Aq X N q - A X N| ≤ ηA) :
    ‖smallBetaModelWeightedQ Aq X N
        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
  have hηA_nonneg : 0 ≤ ηA := by
    have h1 : 1 ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0 := by
      simp [Goldbach.AO_OffDiag.TailBlock.Q0]
    exact le_trans (abs_nonneg _) (hAq 1 h1)
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  calc
    ‖smallBetaModelWeightedQ Aq X N
        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
      =
    ‖smallBetaModelWeightedQ Aq X N
        - smallBetaModelWeightedQ (fun X N _q => A X N) X N‖ := by
          rw [smallBetaModelWeighted_eq_smallBetaModelWeightedQ_const (A := A) (X := X) (N := N)]
    _ =
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
        * (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
            ((((Aq X N q - A X N : ℝ)) : ℂ)) * qPhaseFactor q N)‖ := by
          unfold smallBetaModelWeightedQ
          have hsplit :
              (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                  * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                      (((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N
                -
              (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                  * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                      ((((fun X N _q => A X N) X N q : ℝ) : ℂ)) * qPhaseFactor q N
                =
              (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                * ((∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                      (((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N)
                    -
                    (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                      ((((fun X N _q => A X N) X N q : ℝ) : ℂ)) * qPhaseFactor q N)) := by
                ring
          rw [hsplit]
          have hsums :
              (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                  (((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N)
                -
              (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                  (((A X N : ℝ) : ℂ)) * qPhaseFactor q N)
                =
              ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                (((((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N)
                  - ((((A X N : ℝ) : ℂ)) * qPhaseFactor q N)) := by
                    rw [Finset.sum_sub_distrib]
          rw [hsums]
          have hterm :
              (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                  (((((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N)
                    - ((((A X N : ℝ) : ℂ)) * qPhaseFactor q N)))
                =
              ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
                  ((((Aq X N q - A X N : ℝ)) : ℂ)) * qPhaseFactor q N := by
                    refine Finset.sum_congr rfl ?_
                    intro q hq
                    calc
                      ((((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N)
                          - ((((A X N : ℝ) : ℂ)) * qPhaseFactor q N)
                        =
                      (((((Aq X N q : ℝ) : ℂ)) - (((A X N : ℝ) : ℂ))) * qPhaseFactor q N) := by
                        ring
                      _ = ((((Aq X N q - A X N : ℝ)) : ℂ)) * qPhaseFactor q N := by
                        simp
          rw [hterm]
    _ = Goldbach.AO_WeightMass.weight_mass X
          * ‖∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
              ((((Aq X N q - A X N : ℝ)) : ℂ)) * qPhaseFactor q N‖ := by
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwm_nonneg]
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
              ‖((((Aq X N q - A X N : ℝ)) : ℂ)) * qPhaseFactor q N‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
              ηA * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
            gcongr with q hq
            calc
              ‖((((Aq X N q - A X N : ℝ)) : ℂ)) * qPhaseFactor q N‖
                  = |Aq X N q - A X N| * ‖qPhaseFactor q N‖ := by
                      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              _ ≤ |Aq X N q - A X N|
                    * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
                      exact mul_le_mul_of_nonneg_left
                        (norm_qPhaseFactor_le q N)
                        (abs_nonneg _)
              _ ≤ ηA * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
                      have hterm_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
                        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
                        have hphi_pos : 0 < (Nat.totient q : ℝ) := by
                          exact_mod_cast Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq1)
                        exact div_nonneg
                          (by
                            by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq])
                          (le_of_lt hphi_pos)
                      exact mul_le_mul_of_nonneg_right
                        (hAq q hq)
                        hterm_nonneg
    _ = Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
          rw [← Finset.mul_sum]
          simp [qaPhaseUpperConst, mul_assoc, mul_left_comm, mul_comm]

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
