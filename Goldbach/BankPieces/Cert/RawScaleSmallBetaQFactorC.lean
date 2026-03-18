import Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC

open scoped BigOperators Interval ArithmeticFunction.Moebius

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaArcFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private lemma weight_mass_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hx : (1 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) this
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hband : 0 < (2 * (Goldbach.BG_Bank.H : ℝ) + 1) := by positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    unfold Goldbach.BG_Bank.wScale
    exact one_div_pos.mpr (mul_pos hlog hband)
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

/-- Complex `q`-dependent small-`β` model matching the exact local factorization. -/
noncomputable def smallBetaModelWeightedQC
    (Aq : ℕ → ℕ → ℕ → ℂ) (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, Aq X N q * qPhaseFactor q N

/--
The honest complex `q`-level archimedean scalar family.

For `q ≥ 2` this is the centered `a`-independent scalar `AqC`. For the exceptional arc `q = 1`,
there is only one reduced residue `a = 0`, so we define the scalar directly from that local
archimedean extracted arc.
-/
noncomputable def AqLocalC (X N q : ℕ) : ℂ :=
  if _hq : q = 1 then
    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
      * smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)
  else
    AqC X N q (1 : ℝ)

theorem AqLocalC_q1_eq_inv_weight_mass_mul_inv_X_mul_rescaled_half
    (X N : ℕ) (hX : 2 ≤ X) :
    AqLocalC X N 1
      =
    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
      * ((((X : ℝ) : ℂ))⁻¹)
      * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β) := by
  unfold AqLocalC
  simp
  rw [smallBetaLocalArchExtractedArc_q1_eq_inv_X_mul_rescaled_half X N hX]
  simp [mul_assoc]

private lemma rcop_one_mem_zero :
    0 ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop 1 := by
  simp [Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop]

private lemma eq_zero_of_mem_Rcop_one
    {a : ℕ} (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop 1) :
    a = 0 := by
  have hlt : a < 1 := by
    exact Finset.mem_range.mp ((Finset.mem_filter.mp ha).1)
  omega

private lemma localPhaseFactor_one_zero (N : ℕ) :
    localPhaseFactor 1 0 N = 1 := by
  unfold localPhaseFactor
  simp [Goldbach.Cert.MajorArcExponential.e]

private lemma smallBetaLocalArchExtractedArc_eq_weight_mass_mul_AqLocalC_q1
    (X N a : ℕ) (hX : 2 ≤ X)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop 1) :
    smallBetaLocalArchExtractedArc X N 1 a (1 : ℝ)
      =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N 1 := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hwneR : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hwneC : (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hwneR
  have ha0 : a = 0 := eq_zero_of_mem_Rcop_one ha
  subst a
  unfold AqLocalC
  set w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  have hwne : w ≠ 0 := by simpa [w] using hwneC
  change smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)
    = w * (w⁻¹ * smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ))
  calc
    smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)
      = (w * w⁻¹) * smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ) := by
          rw [mul_inv_cancel₀ hwne, one_mul]
    _ = w * (w⁻¹ * smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)) := by ring

private lemma smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_weight_mass_mul_AqLocalC
    (X N q a : ℕ) (hX : 2 ≤ X)
    (hq : q ∈ Finset.Icc (1 : ℕ) Q0)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    smallBetaLocalExtractedArc X N q a (1 : ℝ)
      =
    localPhaseFactor q a N
      * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N q) := by
  rcases Nat.eq_or_lt_of_le (Finset.mem_Icc.mp hq).1 with rfl | hqgt
  · have ha0 : a = 0 := eq_zero_of_mem_Rcop_one ha
    subst a
    calc
      smallBetaLocalExtractedArc X N 1 0 (1 : ℝ)
          =
        localPhaseFactor 1 0 N * smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ) := by
          exact smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_archExtractedArc
            X N 1 0 (by decide) (1 : ℝ)
      _ =
        localPhaseFactor 1 0 N
          * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N 1) := by
            rw [smallBetaLocalArchExtractedArc_eq_weight_mass_mul_AqLocalC_q1 X N 0 hX rcop_one_mem_zero]
      _ =
        localPhaseFactor 1 0 N
          * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N 1) := by rfl
  · have hq2 : 2 ≤ q := by omega
    have hqne : q ≠ 1 := by omega
    calc
      smallBetaLocalExtractedArc X N q a (1 : ℝ)
          =
        localPhaseFactor q a N
          * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqC X N q (1 : ℝ)) := by
            exact smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_weight_mass_mul_AqC
              X N q a hX hq2 ha
      _ =
        localPhaseFactor q a N
          * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N q) := by
            unfold AqLocalC
            simp [hqne]

/--
Exact weighted small-`β` factorization into the honest complex `q`-level scalar family.

This is the exact summed form of the local factorization theorem. No scalar-collapse estimate has
been used yet.
-/
theorem smallBetaExtractedWeighted_eq_smallBetaModelWeightedQC_AqLocalC
    (X N : ℕ) (hX : 2 ≤ X) :
    Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
      =
    smallBetaModelWeightedQC AqLocalC X N := by
  rw [smallBetaExtractedWeighted_eq_sum_localArc]
  unfold smallBetaModelWeightedQC
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          smallBetaLocalExtractedArc X N q a (1 : ℝ)
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          localPhaseFactor q a N
            * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N q) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              refine Finset.sum_congr rfl ?_
              intro a ha
              exact smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_weight_mass_mul_AqLocalC
                X N q a hX hq ha
    _ =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
      * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          AqLocalC X N q
            * (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, localPhaseFactor q a N) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro q hq
              calc
                ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                    localPhaseFactor q a N
                      * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N q)
                  =
                ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N q)
                      * localPhaseFactor q a N := by
                        refine Finset.sum_congr rfl ?_
                        intro a ha
                        ring
                _ =
                ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N q)
                  * (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                      localPhaseFactor q a N) := by
                        rw [Finset.mul_sum]
                _ =
                (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                  * (AqLocalC X N q
                    * (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                        localPhaseFactor q a N)) := by
                          ring
    _ =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
      * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          AqLocalC X N q * qPhaseFactor q N := by
            refine congrArg (fun z : ℂ => (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * z) ?_
            refine Finset.sum_congr rfl ?_
            intro q hq
            rw [qPhaseFactor_eq_sum_localPhaseFactor]

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
