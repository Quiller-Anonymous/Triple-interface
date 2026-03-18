import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.Cert.MajorArcStep24MainTermIdentification
import Goldbach.BankPieces.Cert.RamanujanOddZero
import Goldbach.AO_OffDiag.SigmaTailEuler
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace Goldbach.BankPieces.Cert.RawScaleWeightedKernel

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex
open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.AO_OffDiag.SigmaTailReindexFun
open Goldbach.AO_OffDiag.SigmaTailReindex

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private lemma sigmaTermFun_eq_sigmaTerm (q N : ℕ) :
    Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTerm q N
      =
    Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N := rfl

private lemma muSq_mul_phaseSum_neg_eq_muSq_mul_ramanujanZ
    {q N : ℕ} (hq1 : 1 ≤ q) :
    ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
      =
    ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
  classical
  by_cases hq : Squarefree q
  · have hbridge :
        (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
          =
        (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) :=
      Goldbach.Cert.MajorArcStep24RamanujanBridge.ramanujanSumC_neg_eq_ramanujanZ_of_squarefree
        (q := q) (N := N) hq1 hq
    simp [Goldbach.AO_OffDiag.TailBlock.muSq, hq, hbridge]
  · simp [Goldbach.AO_OffDiag.TailBlock.muSq, hq]

private theorem qPhaseFactor_eq_ofReal_weighted_ramanujanR
    {q N : ℕ} (hq1 : 1 ≤ q) :
    Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor.qPhaseFactor q N
      =
    (((Goldbach.AO_OffDiag.TailBlock.muSq q
          * (1 / ((Nat.totient q : ℝ) ^ 2))
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ) := by
  have hbridge :
      ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
          * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
        =
      ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
          * (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) :=
    muSq_mul_phaseSum_neg_eq_muSq_mul_ramanujanZ (q := q) (N := N) hq1
  calc
    Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor.qPhaseFactor q N
        =
      ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) := by
          simp [Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor.qPhaseFactor,
            Goldbach.Cert.MajorArcStep24MainTermIdentification.moebius_sq_cast_eq_muSq,
            mul_assoc, mul_left_comm, mul_comm]
    _ =
      ((Goldbach.AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
          have hmul :=
            congrArg
              (fun z : ℂ => ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ) * z)
              hbridge
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ =
      (((Goldbach.AO_OffDiag.TailBlock.muSq q
            * (1 / ((Nat.totient q : ℝ) ^ 2))
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ) := by
          simp [Goldbach.AO_OffDiag.TailBlock.ramanujanR, mul_assoc]

/--
The honest finite weighted arithmetic kernel on the Ramanujan closed-form side.

This is the real-valued kernel naturally suggested by the exact post-freeze factor
`frozenQKernelC X N = X⁻¹ * kappaLeQ0C N`.
-/
noncomputable def kappaLeQ0R (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
    Goldbach.AO_OffDiag.TailBlock.muSq q
      * (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N

/--
The complex frozen kernel is exactly the complexification of the real weighted Ramanujan kernel.

This is the minimal bridge needed to move the post-freeze arithmetic endpoint onto a real-valued
series before building Euler-product and tail theory.
-/
theorem kappaLeQ0C_eq_ofReal_kappaLeQ0R (N : ℕ) :
    Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze.kappaLeQ0C N
      =
    ((kappaLeQ0R N : ℝ) : ℂ) := by
  unfold Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze.kappaLeQ0C kappaLeQ0R
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ((((q : ℝ) : ℂ))⁻¹)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor.qPhaseFactor q N
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ((((q : ℝ) : ℂ))⁻¹)
        * (((Goldbach.AO_OffDiag.TailBlock.muSq q
              * (1 / ((Nat.totient q : ℝ) ^ 2))
              * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          rw [qPhaseFactor_eq_ofReal_weighted_ramanujanR (N := N)
            ((Finset.mem_Icc.mp hq).1)]
    _ =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      (((Goldbach.AO_OffDiag.TailBlock.muSq q
            * (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hqpos : (0 : ℝ) < (q : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
          have hqneR : (q : ℝ) ≠ 0 := ne_of_gt hqpos
          have hphi_pos : 0 < (Nat.totient q : ℝ) := by
            exact_mod_cast Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq1)
          have hphi_neR : (Nat.totient q : ℝ) ≠ 0 := ne_of_gt hphi_pos
          calc
            ((((q : ℝ) : ℂ))⁻¹)
                * (((Goldbach.AO_OffDiag.TailBlock.muSq q
                      * (1 / ((Nat.totient q : ℝ) ^ 2))
                      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ)
              =
            ((((q : ℝ)⁻¹
                  * (Goldbach.AO_OffDiag.TailBlock.muSq q
                      * (1 / ((Nat.totient q : ℝ) ^ 2))
                      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N) : ℝ)) : ℂ) := by
                simp [Complex.ofReal_mul, hqneR, mul_assoc]
            _ =
            (((Goldbach.AO_OffDiag.TailBlock.muSq q
                  * (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
                  * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ) := by
                congr 1
                field_simp [hqneR, hphi_neR]
    _ = ((kappaLeQ0R N : ℝ) : ℂ) := by
          simpa [kappaLeQ0R] using
            (Complex.ofReal_sum
              (s := Finset.Icc (1 : ℕ) Q0)
              (f := fun q =>
                Goldbach.AO_OffDiag.TailBlock.muSq q
                  * (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
                  * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N))

/--
The frozen post-freeze `q`-kernel is the global `X⁻¹` normalization times the real weighted
Ramanujan kernel.
-/
theorem frozenQKernelC_eq_inv_X_mul_ofReal_kappaLeQ0R
    (X N : ℕ) (hX : 1 ≤ X) :
    Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze.frozenQKernelC X N
      =
    (((X : ℝ) : ℂ)⁻¹) * ((kappaLeQ0R N : ℝ) : ℂ) := by
  rw [Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze.frozenQKernelC_eq_inv_X_mul_kappaLeQ0C
      (X := X) (N := N) hX]
  rw [kappaLeQ0C_eq_ofReal_kappaLeQ0R]

/-- The infinite weighted kernel summand, with the harmless `q = 0` term set to `0`. -/
noncomputable def kappaTermR (q N : ℕ) : ℝ :=
  if q = 0 then 0
  else
    Goldbach.AO_OffDiag.TailBlock.muSq q
      * (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N

/-- The infinite weighted kernel suggested by the exact post-freeze arithmetic. -/
noncomputable def kappaSeriesR (N : ℕ) : ℝ :=
  ∑' q : ℕ, kappaTermR q N

private lemma kappaTermR_eq_zero (N : ℕ) :
    kappaTermR 0 N = 0 := by
  simp [kappaTermR]

private lemma kappaTermR_eq_of_pos {q N : ℕ} (hq : 0 < q) :
    kappaTermR q N
      =
    Goldbach.AO_OffDiag.TailBlock.muSq q
      * (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N := by
  simp [kappaTermR, Nat.ne_of_gt hq]

private lemma norm_kappaTermR_le_sigmaTerm
    (q N : ℕ) :
    ‖kappaTermR q N‖ ≤ ‖Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N‖ := by
  let s : ℝ :=
    Goldbach.AO_OffDiag.TailBlock.muSq q
      * (1 / ((Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
  by_cases hq0 : q = 0
  · subst q
    simp [kappaTermR, Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTerm,
      Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm, Goldbach.AO_OffDiag.muSq]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hqposR : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast hqpos
    have hqneR : (q : ℝ) ≠ 0 := ne_of_gt hqposR
    have hphi_pos : 0 < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    have hphi_neR : (Nat.totient q : ℝ) ≠ 0 := ne_of_gt hphi_pos
    have hsplit :
        (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
          = (1 / (q : ℝ)) * (1 / ((Nat.totient q : ℝ) ^ 2)) := by
      field_simp [hqneR, hphi_neR]
    have hsigma : Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N = s := by
      rfl
    calc
      ‖kappaTermR q N‖
          = ‖(1 / (q : ℝ)) * s‖ := by
            rw [kappaTermR_eq_of_pos hqpos]
            simp only [s]
            rw [hsplit]
            ring_nf
      _ = |(1 / (q : ℝ))| * ‖s‖ := by
            simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖s‖ := by
            have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hqpos)
            have hcoef_nonneg : 0 ≤ (1 / (q : ℝ)) := by positivity
            have hcoef_le_one : (1 / (q : ℝ)) ≤ 1 := by
              simpa using one_div_le_one_div_of_le (by positivity) hq_ge_one
            rw [abs_of_nonneg hcoef_nonneg]
            simpa [mul_comm] using
              (mul_le_of_le_one_right (norm_nonneg s)
                hcoef_le_one)
      _ = ‖Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N‖ := by
            rw [hsigma]

private lemma norm_phaseSum_neg_le_totient (q N : ℕ) :
    ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖ ≤ (Nat.totient q : ℝ) := by
  calc
    ‖∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))‖
        = ‖star (Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC q N)‖ := by
            rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.phaseSum_neg_eq_star_ramanujanSumC]
    _ = ‖Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC q N‖ := by simp
    _ ≤ (Nat.totient q : ℝ) := by
          exact Goldbach.Cert.MajorArcStep23RamanujanSum.norm_ramanujanSumC_le_totient q N

private lemma norm_ramanujanR_le_totient_of_squarefree
    {q N : ℕ} (hq1 : 1 ≤ q) (hqsf : Squarefree q) :
    |Goldbach.AO_OffDiag.TailBlock.ramanujanR q N| ≤ (Nat.totient q : ℝ) := by
  have hnormZ :
      ‖((Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℤ) : ℂ)‖ ≤ (Nat.totient q : ℝ) := by
    rw [← Goldbach.Cert.MajorArcStep24RamanujanBridge.ramanujanSumC_neg_eq_ramanujanZ_of_squarefree
      (q := q) (N := N) hq1 hqsf]
    exact norm_phaseSum_neg_le_totient q N
  have hnormR :
      ‖(((Goldbach.AO_OffDiag.TailBlock.ramanujanR q N : ℝ)) : ℂ)‖ ≤ (Nat.totient q : ℝ) := by
    simpa [Goldbach.AO_OffDiag.TailBlock.ramanujanR] using hnormZ
  simpa [Complex.norm_real, Real.norm_eq_abs] using hnormR

private lemma norm_if_tail_kappaTermR_le_eulerTailFun
    (R q N : ℕ) :
    ‖if R < q then kappaTermR q N else 0‖ ≤
      Goldbach.AO_OffDiag.SigmaTailEuler.eulerTailFun R 1 q := by
  by_cases hRq : R < q
  · have hqpos : 0 < q := Nat.zero_lt_of_lt hRq
    have hq1 : 1 ≤ q := Nat.succ_le_iff.mpr hqpos
    by_cases hqsf : Squarefree q
    · have hmu : Goldbach.AO_OffDiag.TailBlock.muSq q = 1 := by
        simp [Goldbach.AO_OffDiag.TailBlock.muSq, hqsf]
      have hram :
          |Goldbach.AO_OffDiag.TailBlock.ramanujanR q N| ≤ (Nat.totient q : ℝ) :=
        norm_ramanujanR_le_totient_of_squarefree hq1 hqsf
      have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      have hphi_pos : 0 < (Nat.totient q : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hphi_nonneg : 0 ≤ (Nat.totient q : ℝ) := le_of_lt hphi_pos
      have hcoef_nonneg : 0 ≤ (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2) : ℝ) := by positivity
      have habs :
          ‖kappaTermR q N‖
            =
          (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2))
            * |Goldbach.AO_OffDiag.TailBlock.ramanujanR q N| := by
        rw [Real.norm_eq_abs, kappaTermR_eq_of_pos hqpos, hmu]
        simp [abs_mul, hcoef_nonneg, hphi_nonneg, hqposR.le, mul_assoc, mul_left_comm, mul_comm]
      have hmiddle :
          ‖kappaTermR q N‖
            ≤
          (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2)) * (Nat.totient q : ℝ) := by
        rw [habs]
        exact mul_le_mul_of_nonneg_left hram hcoef_nonneg
      have htot_le_q : (Nat.totient q : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.totient_le q
      have hq_inv_le_phi_inv : (1 / (q : ℝ)) ≤ (1 / (Nat.totient q : ℝ)) := by
        simpa using one_div_le_one_div_of_le hphi_pos htot_le_q
      have hlast :
          (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2)) * (Nat.totient q : ℝ)
            ≤
          (1 / (Nat.totient q : ℝ) ^ 2) := by
        have hcalc :
            (1 / ((q : ℝ) * (Nat.totient q : ℝ) ^ 2)) * (Nat.totient q : ℝ)
              =
            (1 / (q : ℝ)) * (1 / (Nat.totient q : ℝ)) := by
          field_simp [ne_of_gt hqposR, ne_of_gt hphi_pos]
        rw [hcalc]
        have hphi_inv_nonneg : 0 ≤ (1 / (Nat.totient q : ℝ)) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hq_inv_le_phi_inv hphi_inv_nonneg
        simpa [pow_two, one_div, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hbound : ‖if R < q then kappaTermR q N else 0‖ ≤ (1 / (Nat.totient q : ℝ) ^ 2) := by
        simp [hRq]
        exact le_trans hmiddle (by simpa [one_div] using hlast)
      simpa [Goldbach.AO_OffDiag.SigmaTailEuler.eulerTailFun, hRq, hqsf] using hbound
    · simp [hRq, hqsf, kappaTermR_eq_of_pos hqpos, Goldbach.AO_OffDiag.TailBlock.muSq,
        Goldbach.AO_OffDiag.SigmaTailEuler.eulerTailFun]
  · simp [hRq, Goldbach.AO_OffDiag.SigmaTailEuler.eulerTailFun]

/-- Explicit weighted-kernel tail bound from the existing Euler-tail package at `N = 1`. -/
theorem tsum_norm_kappaTail_le_ninety_div (R N : ℕ) (hR : 1 ≤ R) :
    (∑' q : ℕ, ‖if R < q then kappaTermR q N else 0‖) ≤ (90 : ℝ) / R := by
  let f : ℕ → ℝ := fun q => ‖if R < q then kappaTermR q N else 0‖
  let g : ℕ → ℝ := Goldbach.AO_OffDiag.SigmaTailEuler.eulerTailFun R 1
  have hsum_g : Summable g :=
    (Goldbach.AO_OffDiag.SigmaTailEuler.euler_tail_bound_tsum R 1 hR).1
  have hsum_f : Summable f := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) ?_ hsum_g
    intro q
    simpa [f, g] using norm_if_tail_kappaTermR_le_eulerTailFun R q N
  have hle :
      ∑' q : ℕ, f q ≤ ∑' q : ℕ, g q :=
    Summable.tsum_le_tsum
      (h := fun q => by simpa [f, g] using norm_if_tail_kappaTermR_le_eulerTailFun R q N)
      hsum_f hsum_g
  exact hle.trans (by simpa [g] using (Goldbach.AO_OffDiag.SigmaTailEuler.euler_tail_bound_tsum R 1 hR).2)

/-- The weighted kernel series is summable whenever `N ≠ 0`. -/
theorem summable_kappaTermR (N : ℕ) (hN0 : N ≠ 0) :
    Summable (fun q : ℕ => kappaTermR q N) := by
  have hsigma_fun :
      Summable (fun q : ℕ => Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTerm q N) :=
    Goldbach.BankPieces.Cert.RamanujanOddZero.summable_sigmaTerm N hN0
  have hsigma :
      Summable (fun q : ℕ => Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N) := by
    rw [show (fun q : ℕ => Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTerm q N)
          = (fun q : ℕ => Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm q N) by
            funext q; exact sigmaTermFun_eq_sigmaTerm q N] at hsigma_fun
    exact hsigma_fun
  have hnorm :
      Summable (fun q : ℕ => ‖kappaTermR q N‖) := by
    exact hsigma.norm.of_nonneg_of_le
      (fun q => norm_nonneg _)
      (fun q => norm_kappaTermR_le_sigmaTerm q N)
  exact Summable.of_norm hnorm

/-- The finite weighted kernel is the `Q0` cutoff of the infinite weighted summand. -/
theorem kappaLeQ0R_eq_sum_kappaTermR (N : ℕ) :
    kappaLeQ0R N = ∑ q ∈ Finset.Icc (1 : ℕ) Q0, kappaTermR q N := by
  refine Finset.sum_congr rfl ?_
  intro q hq
  symm
  exact kappaTermR_eq_of_pos ((Finset.mem_Icc.mp hq).1)

/-- The weighted tail series past any cutoff is summable whenever `N ≠ 0`. -/
theorem summable_kappaTailSeriesR (Q N : ℕ) (hN0 : N ≠ 0) :
    Summable (fun q : ℕ => if Q < q then kappaTermR q N else 0) := by
  have hkappa : Summable (fun q : ℕ => kappaTermR q N) := summable_kappaTermR N hN0
  have hnorm :
      Summable (fun q : ℕ => ‖if Q < q then kappaTermR q N else 0‖) := by
    refine hkappa.norm.of_nonneg_of_le ?_ ?_
    · intro q
      exact norm_nonneg _
    · intro q
      by_cases hq : Q < q
      · simp [hq]
      · simp [hq]
  exact Summable.of_norm hnorm

/--
The infinite weighted kernel splits exactly into its finite `Q0` cutoff plus the honest tail.
-/
theorem kappaSeriesR_eq_kappaLeQ0R_add_tail (N : ℕ) (hN0 : N ≠ 0) :
    kappaSeriesR N
      =
    kappaLeQ0R N + ∑' q : ℕ, if Q0 < q then kappaTermR q N else 0 := by
  let f : ℕ → ℝ := fun q => kappaTermR q N
  let g : ℕ → ℝ := fun n => f (n + 1)
  let t : ℕ → ℝ := fun q => if Q0 < q then f q else 0
  have hsum_f : Summable f := summable_kappaTermR N hN0
  have hsum_g : Summable g := hsum_f.comp_injective Nat.succ_injective
  have hsplit_g :
      ∑ i ∈ Finset.range Q0, g i + ∑' i : ℕ, g (i + Q0) = ∑' i : ℕ, g i :=
    Summable.sum_add_tsum_nat_add Q0 hsum_g
  have hsum_t : Summable t := by
    simpa [t, f] using summable_kappaTailSeriesR Q0 N hN0
  have htrunc :
      ∑ i ∈ Finset.range Q0, g i = kappaLeQ0R N := by
    rw [kappaLeQ0R_eq_sum_kappaTermR, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [g, f, Nat.add_comm]
  have htail_t :
      ∑' i : ℕ, t (i + (Q0 + 1)) = ∑' q : ℕ, if Q0 < q then kappaTermR q N else 0 := by
    have hsplit_t := Summable.sum_add_tsum_nat_add (Q0 + 1) hsum_t
    have hinit_t : ∑ i ∈ Finset.range (Q0 + 1), t i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hi_le : i ≤ Q0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi_not : ¬ Q0 < i := not_lt_of_ge hi_le
      unfold t
      rw [if_neg hi_not]
    rw [hinit_t, zero_add] at hsplit_t
    simpa [t, f] using hsplit_t
  have htail :
      ∑' i : ℕ, g (i + Q0) = ∑' q : ℕ, if Q0 < q then kappaTermR q N else 0 := by
    refine (tsum_congr ?_).trans htail_t
    intro i
    have hi : Q0 < i + (Q0 + 1) := by omega
    simp [g, t, f, hi, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hdrop0 : ∑' i : ℕ, g i = ∑' q : ℕ, f q := by
    have hdrop := hsum_f.tsum_eq_zero_add
    have hf0 : f 0 = 0 := by simp [f, kappaTermR_eq_zero]
    rw [hf0, zero_add] at hdrop
    simpa [g] using hdrop.symm
  calc
    kappaSeriesR N = ∑' q : ℕ, f q := rfl
    _ = ∑' i : ℕ, g i := hdrop0.symm
    _ = ∑ i ∈ Finset.range Q0, g i + ∑' i : ℕ, g (i + Q0) := hsplit_g.symm
    _ = kappaLeQ0R N + ∑' q : ℕ, if Q0 < q then kappaTermR q N else 0 := by
          rw [htrunc, htail]

/--
Norm gap between the infinite weighted kernel and its finite `Q0` cutoff.

This is the arithmetic tail seam that remains after identifying the honest post-freeze kernel.
-/
theorem norm_kappaSeriesR_sub_kappaLeQ0R_le_tsum_tail_norm (N : ℕ) (hN0 : N ≠ 0) :
    ‖kappaSeriesR N - kappaLeQ0R N‖
      ≤
    ∑' q : ℕ, ‖if Q0 < q then kappaTermR q N else 0‖ := by
  let t : ℕ → ℝ := fun q => if Q0 < q then kappaTermR q N else 0
  have hsum_t : Summable t := by
    simpa [t] using summable_kappaTailSeriesR Q0 N hN0
  have hsplit := kappaSeriesR_eq_kappaLeQ0R_add_tail N hN0
  have hsub : kappaSeriesR N - kappaLeQ0R N = ∑' q : ℕ, t q := by
    rw [hsplit]
    ring
  calc
    ‖kappaSeriesR N - kappaLeQ0R N‖ = ‖∑' q : ℕ, t q‖ := by rw [hsub]
    _ ≤ ∑' q : ℕ, ‖t q‖ := norm_tsum_le_tsum_norm hsum_t.norm
    _ = ∑' q : ℕ, ‖if Q0 < q then kappaTermR q N else 0‖ := by simp [t]

/-- The weighted kernel viewed as an arithmetic function in the modulus variable. -/
noncomputable def kappaAFR (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => kappaTermR q N, kappaTermR_eq_zero N⟩

@[simp] theorem kappaAFR_apply (N q : ℕ) : kappaAFR N q = kappaTermR q N := rfl

private lemma ramanujanR_one (N : ℕ) : Goldbach.AO_OffDiag.TailBlock.ramanujanR 1 N = 1 := by
  simp [Goldbach.AO_OffDiag.TailBlock.ramanujanR, Goldbach.AO_OffDiag.TailBlock.ramanujanZ]

/-- Prime-local weighted coefficient for the direct squarefree Euler expansion of `κ`. -/
noncomputable def kappaPrimeCoeffR (p N : ℕ) : ℝ :=
  if p ∣ N then 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))
  else - (1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2)))


private lemma ramanujanR_prime_eq_neg_one_of_not_dvd
    {p N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR p N = -1 := by
  have hgcd : Nat.gcd p N = 1 := (hp.coprime_iff_not_dvd).2 hpN |>.gcd_eq_one
  simp [Goldbach.AO_OffDiag.TailBlock.ramanujanR, Goldbach.AO_OffDiag.TailBlock.ramanujanZ,
    hgcd, ArithmeticFunction.moebius_apply_prime hp]

private lemma ramanujanR_prime_eq_sub_one_of_dvd
    {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR p N = (p - 1 : ℕ) := by
  have hgcd : Nat.gcd p N = p := Nat.gcd_eq_left hpN
  have hdiv : p / p = 1 := by
    exact Nat.div_eq_of_eq_mul_left hp.pos (by simp)
  rw [Goldbach.AO_OffDiag.TailBlock.ramanujanR, Goldbach.AO_OffDiag.TailBlock.ramanujanZ]
  simp [hgcd, hdiv, Nat.totient_prime hp, ArithmeticFunction.moebius_apply_one]

private lemma kappaTermR_prime_eq_kappaPrimeCoeffR
    {p N : ℕ} (hp : p.Prime) :
    kappaTermR p N = kappaPrimeCoeffR p N := by
  by_cases hpN : p ∣ N
  · have hp_ne_zero : p ≠ 0 := hp.ne_zero
    have hp_minus_one_ne : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
    rw [kappaTermR_eq_of_pos hp.pos, kappaPrimeCoeffR, if_pos hpN,
      ramanujanR_prime_eq_sub_one_of_dvd hp hpN]
    simp [Goldbach.AO_OffDiag.TailBlock.muSq, hp.squarefree, Nat.totient_prime hp,
      hp_ne_zero, hp_minus_one_ne]
    field_simp [hp_ne_zero, hp_minus_one_ne]
  · have hp_ne_zero : p ≠ 0 := hp.ne_zero
    have hp_minus_one_ne : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
    rw [kappaTermR_eq_of_pos hp.pos, kappaPrimeCoeffR, if_neg hpN,
      ramanujanR_prime_eq_neg_one_of_not_dvd hp hpN]
    simp [Goldbach.AO_OffDiag.TailBlock.muSq, hp.squarefree, Nat.totient_prime hp,
      hp_ne_zero, hp_minus_one_ne]

private lemma ramanujanR_mul_prime_eq_neg_of_not_dvd
    {r N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hpr : ¬ p ∣ r) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (p * r) N
      =
    -Goldbach.AO_OffDiag.TailBlock.ramanujanR r N := by
  set d : ℕ := Nat.gcd r N with hd
  have hpCN : Nat.Coprime p N := (hp.coprime_iff_not_dvd).2 hpN
  have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
  have hd_dvd_r : d ∣ r := by simpa [hd] using Nat.gcd_dvd_left r N
  have hgcd :
      Nat.gcd (p * r) N = d := by
    simpa [d, hd, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      hpCN.gcd_mul_left_cancel r
  have hmulDiv : (p * r) / d = p * (r / d) := by
    simpa [Nat.mul_assoc] using (Nat.mul_div_assoc p hd_dvd_r)
  have hpCrd : Nat.Coprime p (r / d) := hpCr.of_dvd_right (Nat.div_dvd_of_dvd hd_dvd_r)
  have hmu :
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
        =
      (ArithmeticFunction.moebius p : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := by
    have hg : Nat.gcd p (r / d) = 1 := hpCrd.gcd_eq_one
    rw [hmulDiv]
    exact
      (ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))
        ArithmeticFunction.isMultiplicative_moebius hg)
  have hmu_p : (ArithmeticFunction.moebius p : ℤ) = -1 := by
    simpa using (ArithmeticFunction.moebius_apply_prime hp)
  have hmu' :
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
        = -(ArithmeticFunction.moebius (r / d) : ℤ) := by
    calc
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
          = (ArithmeticFunction.moebius p : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := hmu
      _ = (-1) * (ArithmeticFunction.moebius (r / d) : ℤ) := by simpa [hmu_p]
      _ = -(ArithmeticFunction.moebius (r / d) : ℤ) := by simp
  have hleft :
      Goldbach.AO_OffDiag.TailBlock.ramanujanZ (p * r) N
        =
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := by
    simp [Goldbach.AO_OffDiag.TailBlock.ramanujanZ, hgcd, d, hd]
  have hright :
      Goldbach.AO_OffDiag.TailBlock.ramanujanZ r N
        =
      (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d) := by
    simp [Goldbach.AO_OffDiag.TailBlock.ramanujanZ, d, hd]
  have hZ :
      Goldbach.AO_OffDiag.TailBlock.ramanujanZ (p * r) N
        = -Goldbach.AO_OffDiag.TailBlock.ramanujanZ r N := by
    calc
      Goldbach.AO_OffDiag.TailBlock.ramanujanZ (p * r) N
          = (ArithmeticFunction.moebius ((p * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := hleft
      _ = (-(ArithmeticFunction.moebius (r / d) : ℤ)) * Int.ofNat (Nat.totient d) := by simp [hmu']
      _ = -((ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d)) := by simp [neg_mul]
      _ = -Goldbach.AO_OffDiag.TailBlock.ramanujanZ r N := by simpa [hright]
  simpa [Goldbach.AO_OffDiag.TailBlock.ramanujanR] using congrArg (fun z : ℤ => (z : ℝ)) hZ

private lemma ramanujanR_mul_prime_eq_scale_of_dvd
    {r N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpr : ¬ p ∣ r) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (p * r) N
      =
    ((p - 1 : ℕ) : ℝ) * Goldbach.AO_OffDiag.TailBlock.ramanujanR r N := by
  set d : ℕ := Nat.gcd r N with hd
  have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
  have hd_dvd_r : d ∣ r := by simpa [hd] using Nat.gcd_dvd_left r N
  have hdivN : N = p * (N / p) := by
    exact (Nat.mul_div_cancel' hpN).symm
  have hgcd_r :
      Nat.gcd r (N / p) = d := by
    have htmp' : Nat.gcd (p * (N / p)) r = Nat.gcd (N / p) r := by
      simpa [Nat.mul_comm] using hpCr.gcd_mul_right_cancel (N / p)
    have htmp : Nat.gcd r N = Nat.gcd r (N / p) := by
      calc
        Nat.gcd r N = Nat.gcd r (p * (N / p)) := congrArg (Nat.gcd r) hdivN
        _ = Nat.gcd (p * (N / p)) r := by rw [Nat.gcd_comm]
        _ = Nat.gcd (N / p) r := htmp'
        _ = Nat.gcd r (N / p) := by rw [Nat.gcd_comm]
    simpa [hd] using htmp.symm
  have hgcd :
      Nat.gcd (p * r) N = p * d := by
    rw [hdivN]
    calc
      Nat.gcd (p * r) (p * (N / p)) = p * Nat.gcd r (N / p) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.gcd_mul_left p r (N / p)
      _ = p * d := by rw [hgcd_r]
  have hpCd : Nat.Coprime p d := hpCr.of_dvd_right hd_dvd_r
  have hphi : Nat.totient (p * d) = (p - 1) * Nat.totient d := by
    simpa [Nat.totient_prime hp] using (Nat.totient_mul hpCd)
  have hdiv : (p * r) / (p * d) = r / d := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_div_mul_left r d hp.pos)
  have hZ :
      Goldbach.AO_OffDiag.TailBlock.ramanujanZ (p * r) N
        = (p - 1 : ℕ) * Goldbach.AO_OffDiag.TailBlock.ramanujanZ r N := by
    calc
      Goldbach.AO_OffDiag.TailBlock.ramanujanZ (p * r) N
          = (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient (p * d)) := by
              simp [Goldbach.AO_OffDiag.TailBlock.ramanujanZ, hgcd, d, hd, hdiv]
      _ = (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat ((p - 1) * Nat.totient d) := by
            rw [hphi]
      _ = ((p - 1 : ℕ) : ℤ)
            * ((ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d)) := by
            simp [Int.ofNat_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = (p - 1 : ℕ) * Goldbach.AO_OffDiag.TailBlock.ramanujanZ r N := by
            simp [Goldbach.AO_OffDiag.TailBlock.ramanujanZ, d, hd, Int.ofNat_mul,
              mul_assoc, mul_left_comm, mul_comm]
  simpa [Goldbach.AO_OffDiag.TailBlock.ramanujanR, Int.cast_mul] using
    congrArg (fun z : ℤ => (z : ℝ)) hZ

private lemma kappaTermR_mul_prime_eq_mul_kappaPrimeCoeffR
    {r p N : ℕ} (hp : p.Prime) (hsq : Squarefree r) (hpr : ¬ p ∣ r) :
    kappaTermR (p * r) N = kappaPrimeCoeffR p N * kappaTermR r N := by
  have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
  have hsq_pr : Squarefree (p * r) := (Nat.squarefree_mul hpCr).2 ⟨by simpa using hp.squarefree, hsq⟩
  have hphi : Nat.totient (p * r) = Nat.totient p * Nat.totient r := Nat.totient_mul hpCr
  have hphi_p : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hmu_r : Goldbach.AO_OffDiag.TailBlock.muSq r = 1 := by
    simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hmu_pr : Goldbach.AO_OffDiag.TailBlock.muSq (p * r) = 1 := by
    simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq_pr]
  have hr0 : r ≠ 0 := hsq.ne_zero
  have hp_ne_zero : p ≠ 0 := hp.ne_zero
  have hphi_r_pos : 0 < Nat.totient r := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr0)
  have hphi_r_ne : ((Nat.totient r : ℝ) ^ 2) ≠ 0 := by positivity
  have hp_minus_one_ne : (((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
  have hphi_sq :
      ((Nat.totient (p * r) : ℝ) ^ 2)
        =
      (((p - 1 : ℕ) : ℝ) ^ 2) * ((Nat.totient r : ℝ) ^ 2) := by
    rw [hphi, hphi_p, Nat.cast_mul]
    ring
  by_cases hpN : p ∣ N
  · rw [kappaPrimeCoeffR, if_pos hpN, kappaTermR_eq_of_pos (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hr0)),
      kappaTermR_eq_of_pos (Nat.pos_of_ne_zero hr0), hmu_pr, hmu_r,
      ramanujanR_mul_prime_eq_scale_of_dvd hp hpN hpr]
    rw [hphi_sq]
    have hr_ne_zeroR : ((r : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hr0
    field_simp [hp_ne_zero, hr_ne_zeroR, hp_minus_one_ne, hphi_r_ne]
    rw [Nat.cast_mul]
    ring
  · rw [kappaPrimeCoeffR, if_neg hpN, kappaTermR_eq_of_pos (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hr0)),
      kappaTermR_eq_of_pos (Nat.pos_of_ne_zero hr0), hmu_pr, hmu_r,
      ramanujanR_mul_prime_eq_neg_of_not_dvd hp hpN hpr]
    rw [hphi_sq]
    have hr_ne_zeroR : ((r : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hr0
    field_simp [hp_ne_zero, hr_ne_zeroR, hp_minus_one_ne, hphi_r_ne]
    rw [Nat.cast_mul]
    ring

private lemma squarefree_prod_primes
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    simp
  · intro p s hp_not_mem ih hs_all
    have hp : p.Prime := hs_all p (by simp [hp_not_mem])
    have hs' : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hs_all q (by simp [hq, hp_not_mem])
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right ?_
      intro q hq
      have hqprime : q.Prime := hs' q hq
      refine (hp.coprime_iff_not_dvd).2 ?_
      intro hpq
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).1 hpq
      exact hp_not_mem (this ▸ hq)
    rw [Finset.prod_insert hp_not_mem]
    exact (Nat.squarefree_mul hcop).2 ⟨by simpa using hp.squarefree, ih hs'⟩

private lemma kappaTermR_prod_primes_eq_prod_kappaPrimeCoeffR
    (N : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    kappaTermR (∏ p ∈ s, p) N = ∏ p ∈ s, kappaPrimeCoeffR p N := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    simp [kappaTermR_eq_of_pos, ramanujanR_one, Goldbach.AO_OffDiag.TailBlock.muSq]
  · intro p s hp_not_mem ih hs_all
    have hp : p.Prime := hs_all p (by simp [hp_not_mem])
    have hs' : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hs_all q (by simp [hq, hp_not_mem])
    have hpr : ¬ p ∣ ∏ q ∈ s, q := by
      refine (hp.coprime_iff_not_dvd).1 ?_
      refine Nat.Coprime.prod_right ?_
      intro q hq
      have hqprime : q.Prime := hs' q hq
      refine (hp.coprime_iff_not_dvd).2 ?_
      intro hpq
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).1 hpq
      exact hp_not_mem (this ▸ hq)
    have hsq : Squarefree (∏ q ∈ s, q) := squarefree_prod_primes hs'
    rw [Finset.prod_insert hp_not_mem, kappaTermR_mul_prime_eq_mul_kappaPrimeCoeffR hp hsq hpr, ih hs']
    simp [Finset.prod_insert, hp_not_mem, mul_assoc, mul_left_comm, mul_comm]

/-- Direct finite Euler-product identity for the weighted kernel over a finite prime set. -/
theorem sum_powerset_prod_kappaPrimeCoeffR_eq_prod_one_add
    (N : ℕ) {s : Finset ℕ} :
    (∑ t ∈ s.powerset, ∏ p ∈ t, kappaPrimeCoeffR p N)
      =
    ∏ p ∈ s, (1 + kappaPrimeCoeffR p N) := by
  simpa using (Finset.prod_one_add (s := s) (f := fun p => kappaPrimeCoeffR p N)).symm

/-- The squarefree prime product used for finite Euler approximants. -/
noncomputable def primeProdBelow (n : ℕ) : ℕ :=
  ∏ p ∈ n.primesBelow, p

/-- Prime-local coefficient extended to all naturals by zero off the primes. -/
noncomputable def kappaPrimeNatCoeffR (p N : ℕ) : ℝ :=
  if p.Prime then kappaPrimeCoeffR p N else 0

/-- Finite set exhausting the support of `kappaTermR` along the prime-product divisors. -/
noncomputable def kappaApproxFinset (n : ℕ) : Finset ℕ :=
  (primeProdBelow n).divisors ∪ Finset.range n

private lemma primeProdBelow_ne_zero (n : ℕ) : primeProdBelow n ≠ 0 := by
  unfold primeProdBelow
  exact Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primesBelow hp).ne_zero

private lemma primeProdBelow_squarefree (n : ℕ) : Squarefree (primeProdBelow n) := by
  unfold primeProdBelow
  exact squarefree_prod_primes (fun p hp => Nat.prime_of_mem_primesBelow hp)

private lemma primeFactors_primeProdBelow (n : ℕ) :
    (primeProdBelow n).primeFactors = n.primesBelow := by
  unfold primeProdBelow
  exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primesBelow hp)

private lemma kappaPrimeNatCoeffR_eq_prime {p N : ℕ} (hp : p.Prime) :
    kappaPrimeNatCoeffR p N = kappaPrimeCoeffR p N := by
  simp [kappaPrimeNatCoeffR, hp]

private lemma prod_range_one_add_kappaPrimeNatCoeffR (n N : ℕ) :
    ∏ p ∈ Finset.range n, (1 + kappaPrimeNatCoeffR p N)
      =
    ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N) := by
  let F : ℕ → ℝ := fun p => 1 + kappaPrimeCoeffR p N
  calc
    ∏ p ∈ Finset.range n, (1 + kappaPrimeNatCoeffR p N)
      = ∏ p ∈ Finset.range n, Set.mulIndicator {p | Nat.Prime p} F p := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          by_cases hpp : p.Prime
          · simp [Set.mulIndicator, F, kappaPrimeNatCoeffR, hpp]
          · simp [Set.mulIndicator, F, kappaPrimeNatCoeffR, hpp]
    _ = ∏ p ∈ n.primesBelow, F p := by
          simpa [Nat.primesBelow, F] using
            (Finset.prod_mulIndicator_eq_prod_filter (s := Finset.range n) (f := fun _ => F)
              (t := fun _ => {p | Nat.Prime p}) (g := id))
    _ = ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N) := by rfl

private lemma summable_kappaPrimeNatCoeffR (N : ℕ) (hN0 : N ≠ 0) :
    Summable (fun p : ℕ => kappaPrimeNatCoeffR p N) := by
  have hkappa : Summable (fun q : ℕ => ‖kappaTermR q N‖) := (summable_kappaTermR N hN0).norm
  have hnorm : Summable (fun p : ℕ => ‖kappaPrimeNatCoeffR p N‖) := by
    refine hkappa.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    intro p
    by_cases hp : p.Prime
    · rw [kappaPrimeNatCoeffR_eq_prime hp, kappaTermR_prime_eq_kappaPrimeCoeffR hp]
    · simp [kappaPrimeNatCoeffR, hp]
  exact hnorm.of_norm

private lemma kappaTermR_eq_zero_of_not_squarefree {q N : ℕ} (hq : ¬ Squarefree q) :
    kappaTermR q N = 0 := by
  by_cases hq0 : q = 0
  · simp [kappaTermR, hq0]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    simp [kappaTermR_eq_of_pos hqpos, Goldbach.AO_OffDiag.TailBlock.muSq, hq]

private lemma mem_divisors_primeProdBelow_of_lt_of_kappaTermR_ne_zero
    {q n N : ℕ} (hqn : q < n) (hq : kappaTermR q N ≠ 0) :
    q ∈ (primeProdBelow n).divisors := by
  have hq0 : q ≠ 0 := by
    intro h0
    simp [h0, kappaTermR_eq_zero] at hq
  have hsq : Squarefree q := by
    by_contra hnsq
    exact hq (kappaTermR_eq_zero_of_not_squarefree hnsq)
  have hsubset : q.primeFactors ⊆ n.primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr
      ⟨lt_of_le_of_lt (Nat.le_of_mem_primeFactors hp) hqn, Nat.prime_of_mem_primeFactors hp⟩
  have hdvd_prod :
      ∏ p ∈ q.primeFactors, p ∣ primeProdBelow n := by
    unfold primeProdBelow
    exact Finset.prod_dvd_prod_of_subset q.primeFactors n.primesBelow (fun p => p) hsubset
  have hdvd : q ∣ primeProdBelow n := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact hdvd_prod
  exact Nat.mem_divisors.mpr ⟨hdvd, primeProdBelow_ne_zero n⟩

private lemma kappaApproxFinset_sum_eq_divisor_sum (n N : ℕ) :
    ∑ q ∈ kappaApproxFinset n, kappaTermR q N
      =
    ∑ q ∈ (primeProdBelow n).divisors, kappaTermR q N := by
  classical
  set A : Finset ℕ := (primeProdBelow n).divisors
  set B : Finset ℕ := Finset.range n
  have hunion : A ∪ B = A ∪ (B \ A) := by
    ext q
    by_cases hq : q ∈ A <;> simp [hq]
  have hdisj : Disjoint A (B \ A) := Finset.disjoint_sdiff
  rw [show kappaApproxFinset n = A ∪ B by rfl, hunion, Finset.sum_union hdisj]
  suffices hzero : ∑ q ∈ B \ A, kappaTermR q N = 0 by simp [A, hzero]
  refine Finset.sum_eq_zero ?_
  intro q hq
  have hqn : q < n := Finset.mem_range.mp ((Finset.mem_sdiff.mp hq).1)
  have hnot : q ∉ A := (Finset.mem_sdiff.mp hq).2
  by_cases hterm : kappaTermR q N = 0
  · simpa [hterm]
  · exact (hnot (by simpa [A] using mem_divisors_primeProdBelow_of_lt_of_kappaTermR_ne_zero hqn hterm)).elim

private lemma divisor_sum_primeProdBelow_eq_prime_product (n N : ℕ) :
    ∑ q ∈ (primeProdBelow n).divisors, kappaTermR q N
      =
    ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N) := by
  let f : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => kappaPrimeCoeffR p N)
  have hsq : Squarefree (primeProdBelow n) := primeProdBelow_squarefree n
  calc
    ∑ q ∈ (primeProdBelow n).divisors, kappaTermR q N
      =
    ∑ q ∈ (primeProdBelow n).divisors, f q := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      have hq_sq : Squarefree q := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hq)
      have hq0 : q ≠ 0 := (Nat.pos_of_mem_divisors hq).ne'
      have hterm :
          kappaTermR q N = ∏ p ∈ q.primeFactors, kappaPrimeCoeffR p N := by
        calc
          kappaTermR q N = kappaTermR (∏ p ∈ q.primeFactors, p) N := by
            rw [Nat.prod_primeFactors_of_squarefree hq_sq]
          _ = ∏ p ∈ q.primeFactors, kappaPrimeCoeffR p N :=
            kappaTermR_prod_primes_eq_prod_kappaPrimeCoeffR N
              (fun p hp => Nat.prime_of_mem_primeFactors hp)
      rw [ArithmeticFunction.prodPrimeFactors_apply hq0]
      exact hterm
    _ = ∏ p ∈ (primeProdBelow n).primeFactors, (1 + f p) := by
      symm
      exact
        ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
          (ArithmeticFunction.IsMultiplicative.prodPrimeFactors (fun p => kappaPrimeCoeffR p N))
          hsq
    _ = ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N) := by
      rw [primeFactors_primeProdBelow]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hp' : p.Prime := Nat.prime_of_mem_primesBelow hp
      rw [show f p = kappaPrimeCoeffR p N by
        rw [ArithmeticFunction.prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors]
        simp]

private theorem tendsto_kappaApproxFinset_atTop :
    Filter.Tendsto kappaApproxFinset Filter.atTop Filter.atTop := by
  exact Filter.tendsto_atTop_mono
    (f := Finset.range) (g := kappaApproxFinset)
    (fun n => Finset.subset_union_right)
    Filter.tendsto_finset_range

theorem tendsto_prod_primesBelow_one_add_kappaPrimeCoeffR
    (N : ℕ) (hN0 : N ≠ 0) :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N))
      Filter.atTop (nhds (kappaSeriesR N)) := by
  have hcoeff : Summable (fun p : ℕ => kappaPrimeNatCoeffR p N) :=
    summable_kappaPrimeNatCoeffR N hN0
  have hprod :
      Filter.Tendsto (fun n : ℕ => ∏ p ∈ Finset.range n, (1 + kappaPrimeNatCoeffR p N))
        Filter.atTop (nhds (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N))) := by
    exact (Real.multipliable_one_add_of_summable hcoeff).tendsto_prod_tprod_nat
  have hEq1 :
      (fun n : ℕ => ∏ p ∈ Finset.range n, (1 + kappaPrimeNatCoeffR p N))
        =ᶠ[Filter.atTop] (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N)) := by
    exact Filter.Eventually.of_forall fun n => prod_range_one_add_kappaPrimeNatCoeffR n N
  have hprod' :
      Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N))
        Filter.atTop (nhds (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N))) := by
    exact Filter.Tendsto.congr' hEq1 hprod
  have hsum_norm : Summable (fun q : ℕ => ‖kappaTermR q N‖) := (summable_kappaTermR N hN0).norm
  have hEq2 :
      (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N))
        =ᶠ[Filter.atTop] (fun n : ℕ => ∑ q ∈ kappaApproxFinset n, kappaTermR q N) := by
    exact Filter.Eventually.of_forall fun n => by
      symm
      simpa using
        (kappaApproxFinset_sum_eq_divisor_sum n N).trans
          (divisor_sum_primeProdBelow_eq_prime_product n N)
  have hsum_subseq :
      Filter.Tendsto (fun n : ℕ => ∑ q ∈ kappaApproxFinset n, kappaTermR q N)
        Filter.atTop (nhds (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N))) := by
    exact Filter.Tendsto.congr' hEq2 hprod'
  have hHas :
      HasSum (fun q : ℕ => kappaTermR q N) (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N)) :=
    hasSum_of_subseq_of_summable hsum_norm tendsto_kappaApproxFinset_atTop hsum_subseq
  have hkappa :
      kappaSeriesR N = ∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N) := by
    simpa [kappaSeriesR] using hHas.tsum_eq
  simpa [hkappa] using hprod'

theorem kappaSeriesR_eq_tprod_one_add_kappaPrimeNatCoeffR
    (N : ℕ) (hN0 : N ≠ 0) :
    kappaSeriesR N = ∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N) := by
  have hcoeff : Summable (fun p : ℕ => kappaPrimeNatCoeffR p N) :=
    summable_kappaPrimeNatCoeffR N hN0
  have hrange :
      Filter.Tendsto (fun n : ℕ => ∏ p ∈ Finset.range n, (1 + kappaPrimeNatCoeffR p N))
        Filter.atTop (nhds (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N))) := by
    exact (Real.multipliable_one_add_of_summable hcoeff).tendsto_prod_tprod_nat
  have hEq :
      (fun n : ℕ => ∏ p ∈ Finset.range n, (1 + kappaPrimeNatCoeffR p N))
        =ᶠ[Filter.atTop] (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N)) := by
    exact Filter.Eventually.of_forall fun n => prod_range_one_add_kappaPrimeNatCoeffR n N
  have hprimes :
      Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + kappaPrimeCoeffR p N))
        Filter.atTop (nhds (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p N))) := by
    exact Filter.Tendsto.congr' hEq hrange
  exact tendsto_nhds_unique (tendsto_prod_primesBelow_one_add_kappaPrimeCoeffR N hN0) hprimes

/-- The smaller prime-local factor, attained when `p ∤ N`. -/
noncomputable def kappaPrimeLowerFactorR (p : ℕ) : ℝ :=
  1 - 1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))

private lemma one_add_kappaPrimeCoeffR_eq_lower_of_not_dvd
    {p N : ℕ} (hpN : ¬ p ∣ N) :
    1 + kappaPrimeCoeffR p N = kappaPrimeLowerFactorR p := by
  simp [kappaPrimeCoeffR, kappaPrimeLowerFactorR, hpN, sub_eq_add_neg]

private lemma one_add_kappaPrimeCoeffR_eq_raise_of_dvd
    {p N : ℕ} (hpN : p ∣ N) :
    1 + kappaPrimeCoeffR p N = 1 + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
  simp [kappaPrimeCoeffR, hpN]

lemma kappaPrimeLowerFactorR_pos {p : ℕ} (hp : p.Prime) :
    0 < kappaPrimeLowerFactorR p := by
  have hp_ne_zero : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_minus_one_pos : 0 < (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hden_pos : 0 < (p : ℝ) * ((((p - 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hfrac_lt_one : 1 / ((p : ℝ) * ((((p - 1 : ℕ) : ℝ) ^ 2))) < 1 := by
    have hden_gt_one : 1 < (p : ℝ) * ((((p - 1 : ℕ) : ℝ) ^ 2)) := by
      have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hpm1_ge_one_nat : 1 ≤ p - 1 := by
        exact Nat.le_sub_of_add_le hp.two_le
      have hsq_ge_one : (1 : ℝ) ≤ (((p - 1 : ℕ) : ℝ) ^ 2) := by
        have hpm1_ge_one : (1 : ℝ) ≤ (((p - 1 : ℕ) : ℝ)) := by
          exact_mod_cast hpm1_ge_one_nat
        nlinarith
      nlinarith
    simpa using (div_lt_one hden_pos).2 hden_gt_one
  dsimp [kappaPrimeLowerFactorR]
  linarith

lemma kappaPrimeCoeffR_one_add_pos {p N : ℕ} (hp : p.Prime) :
    0 < 1 + kappaPrimeCoeffR p N := by
  by_cases hpN : p ∣ N
  · rw [one_add_kappaPrimeCoeffR_eq_raise_of_dvd hpN]
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hp_minus_one_pos : 0 < (((p - 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
    positivity
  · rw [one_add_kappaPrimeCoeffR_eq_lower_of_not_dvd hpN]
    exact kappaPrimeLowerFactorR_pos hp

lemma kappaPrimeLowerFactorR_le_one_add_kappaPrimeCoeffR
    {p N : ℕ} (hp : p.Prime) :
    kappaPrimeLowerFactorR p ≤ 1 + kappaPrimeCoeffR p N := by
  by_cases hpN : p ∣ N
  · rw [one_add_kappaPrimeCoeffR_eq_raise_of_dvd hpN]
    dsimp [kappaPrimeLowerFactorR]
    have hnonneg :
        0 ≤ 1 / ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2)) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
      positivity
    linarith
  · rw [one_add_kappaPrimeCoeffR_eq_lower_of_not_dvd hpN]

lemma prod_kappaPrimeLowerFactorR_le_prod_one_add_kappaPrimeCoeffR
    {N : ℕ} {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, kappaPrimeLowerFactorR p
      ≤
    ∏ p ∈ s, (1 + kappaPrimeCoeffR p N) := by
  classical
  refine Finset.prod_le_prod ?hnonneg ?hle
  · intro p hp
    exact le_of_lt (kappaPrimeLowerFactorR_pos (hs p hp))
  · intro p hp
    exact kappaPrimeLowerFactorR_le_one_add_kappaPrimeCoeffR (hs p hp)

theorem tendsto_prod_primesBelow_kappaPrimeLowerFactorR :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, kappaPrimeLowerFactorR p)
      Filter.atTop (nhds (kappaSeriesR 1)) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_prod_primesBelow_one_add_kappaPrimeCoeffR 1 one_ne_zero)
  exact Filter.Eventually.of_forall fun n => by
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact one_add_kappaPrimeCoeffR_eq_lower_of_not_dvd
      ((Nat.prime_of_mem_primesBelow hp).not_dvd_one)

theorem kappaSeriesR_one_pos : 0 < kappaSeriesR 1 := by
  have hnonneg : 0 ≤ kappaSeriesR 1 := by
    refine ge_of_tendsto' tendsto_prod_primesBelow_kappaPrimeLowerFactorR ?_
    intro n
    exact (Finset.prod_pos fun p hp => kappaPrimeLowerFactorR_pos
      (Nat.prime_of_mem_primesBelow hp)).le
  have hneq_tprod : (∏' p : ℕ, (1 + kappaPrimeNatCoeffR p 1)) ≠ 0 := by
    apply tprod_one_add_ne_zero_of_summable
    · intro p
      by_cases hp : p.Prime
      · rw [kappaPrimeNatCoeffR_eq_prime hp,
          one_add_kappaPrimeCoeffR_eq_lower_of_not_dvd hp.not_dvd_one]
        exact ne_of_gt (kappaPrimeLowerFactorR_pos hp)
      · simp [kappaPrimeNatCoeffR, hp]
    · simpa using (summable_kappaPrimeNatCoeffR 1 one_ne_zero).norm
  have hneq : kappaSeriesR 1 ≠ 0 := by
    rw [kappaSeriesR_eq_tprod_one_add_kappaPrimeNatCoeffR 1 one_ne_zero]
    exact hneq_tprod
  exact lt_of_le_of_ne hnonneg (Ne.symm hneq)

theorem kappaSeriesR_one_le (N : ℕ) (hN0 : N ≠ 0) :
    kappaSeriesR 1 ≤ kappaSeriesR N := by
  refine le_of_tendsto_of_tendsto'
    tendsto_prod_primesBelow_kappaPrimeLowerFactorR
    (tendsto_prod_primesBelow_one_add_kappaPrimeCoeffR N hN0) ?_
  intro n
  exact prod_kappaPrimeLowerFactorR_le_prod_one_add_kappaPrimeCoeffR
    (fun p hp => Nat.prime_of_mem_primesBelow hp)

theorem kappaSeriesR_pos (N : ℕ) (hN0 : N ≠ 0) :
    0 < kappaSeriesR N := by
  exact lt_of_lt_of_le kappaSeriesR_one_pos (kappaSeriesR_one_le N hN0)

theorem norm_kappaSeriesR_sub_kappaLeQ0R_le_ninety_div
    (N : ℕ) (hN0 : N ≠ 0) :
    ‖kappaSeriesR N - kappaLeQ0R N‖ ≤ (90 : ℝ) / Q0 := by
  have hQ0 : 1 ≤ Q0 := by native_decide
  exact (norm_kappaSeriesR_sub_kappaLeQ0R_le_tsum_tail_norm N hN0).trans
    (tsum_norm_kappaTail_le_ninety_div Q0 N hQ0)

end

end Goldbach.BankPieces.Cert.RawScaleWeightedKernel
