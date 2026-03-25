import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm

open scoped BigOperators Interval ArithmeticFunction.Moebius

open Complex
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
The exact principal-arc `q = 1` small-`β` contribution, written directly on the rescaled
half-interval surface `u ∈ [0,1]`.

This is the candidate replacement principal main term, independent of any frozen comparison.
-/
noncomputable def smallBetaPrincipalQ1MainTermC (X N : ℕ) : ℂ :=
  ((((X : ℝ) : ℂ))⁻¹)
    * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)

/--
The exact secondary small-`β` contribution from the arcs `2 ≤ q ≤ Q0`, with the arithmetic
weight kept in place.
-/
noncomputable def smallBetaSecondaryGe2MainTermC (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * ∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N

theorem smallBetaPrincipalQ1MainTermC_eq_weight_mass_mul_AqLocalC
    (X N : ℕ) (hX : 2 ≤ X) :
    smallBetaPrincipalQ1MainTermC X N
      =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqLocalC X N 1 := by
  set w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := by
    have hx : (1 : ℝ) < (X : ℝ) := by
      have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) this
    have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hx
    have hband : 0 < (2 * (Goldbach.BG_Bank.H : ℝ) + 1) := by positivity
    have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
      unfold Goldbach.BG_Bank.wScale
      exact one_div_pos.mpr (mul_pos hlog hband)
    simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos
  have hwne : w ≠ 0 := by
    unfold w
    exact_mod_cast (ne_of_gt hwpos : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0)
  have hq1 := AqLocalC_q1_eq_inv_weight_mass_mul_inv_X_mul_rescaled_half X N hX
  let I : ℂ :=
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
  have hq1' : AqLocalC X N 1 = w⁻¹ * ((((X : ℝ) : ℂ))⁻¹) * I := by
    rw [show (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) = w by rfl] at hq1
    change AqLocalC X N 1 = w⁻¹ * ((((X : ℝ) : ℂ))⁻¹) * I
    simpa [I, mul_assoc] using hq1
  have hmul : w * AqLocalC X N 1 = (((X : ℝ) : ℂ))⁻¹ * I := by
    calc
      w * AqLocalC X N 1
          = w * (w⁻¹ * ((((X : ℝ) : ℂ))⁻¹) * I) := by
              rw [hq1']
      _ = (w * w⁻¹) * ((((X : ℝ) : ℂ))⁻¹) * I := by ring
      _ = ((((X : ℝ) : ℂ))⁻¹) * I := by rw [mul_inv_cancel₀ hwne, one_mul]
  unfold smallBetaPrincipalQ1MainTermC
  simpa [I] using hmul.symm

private lemma qPhaseFactor_one (N : ℕ) : qPhaseFactor 1 N = 1 := by
  unfold qPhaseFactor
  simp [Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop, Goldbach.Cert.MajorArcExponential.e]

theorem smallBetaModelWeightedQC_AqLocalC_eq_principal_plus_secondary
    (X N : ℕ) (hX : 2 ≤ X) :
    smallBetaModelWeightedQC AqLocalC X N
      =
    smallBetaPrincipalQ1MainTermC X N + smallBetaSecondaryGe2MainTermC X N := by
  have hsplit :
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N
        =
      AqLocalC X N 1 * qPhaseFactor 1 N
        + ∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N := by
    have hset :
        Finset.Icc (1 : ℕ) Q0 = insert 1 (Finset.Icc (2 : ℕ) Q0) := by
      ext q
      simp [Nat.succ_le_iff]
      omega
    have hnotmem : 1 ∉ Finset.Icc (2 : ℕ) Q0 := by simp
    rw [hset, Finset.sum_insert hnotmem]
  unfold smallBetaModelWeightedQC smallBetaSecondaryGe2MainTermC
  rw [hsplit, qPhaseFactor_one]
  rw [smallBetaPrincipalQ1MainTermC_eq_weight_mass_mul_AqLocalC X N hX]
  ring

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
