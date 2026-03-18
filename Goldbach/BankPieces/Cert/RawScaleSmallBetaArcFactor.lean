import Goldbach.BankPieces.Cert.RawScaleSmallBetaQGap

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaArcFactor

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

open scoped BigOperators Interval ArithmeticFunction.Moebius

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/--
The exact local extracted small-`β` contribution on a single textbook arc `(q,a)`.

This is the honest local object whose factorization is the next mathematical target.
-/
noncomputable def smallBetaLocalExtractedArc (X N q a : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ α in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
          (fun α => smallBetaLocalMainTerm X N q a α β) α) β

/-- The local `(q,a)` arithmetic phase factor expected after exact arcwise factorization. -/
noncomputable def localPhaseFactor (q a N : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℂ) ^ 2)
      * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ))
    * Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (a : ℝ) / q))

lemma qPhaseFactor_eq_sum_localPhaseFactor (q N : ℕ) :
    qPhaseFactor q N = ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, localPhaseFactor q a N := by
  simp [qPhaseFactor, localPhaseFactor, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma smallBetaExtractedWeighted_eq_sum_localArc (X N : ℕ) (Δ : ℝ) :
    smallBetaExtractedWeighted X N Δ
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
      smallBetaLocalExtractedArc X N q a Δ := by
  rfl

/--
Exact extracted-to-`q`-model factorization from a local arcwise factorization hypothesis.

This is the clean theorem surface for the next proof: produce the family `Aq(X,N,q)` directly from
the local Step-21 extraction algebra, and then show each textbook arc contributes exactly the local
phase factor multiplied by that common `q`-level scalar.
-/
theorem smallBetaExtractedWeighted_eq_smallBetaModelWeightedQ_of_local_factorization
    (Aq : ℕ → ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ : ℝ}
    (hlocal :
      ∀ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        smallBetaLocalExtractedArc X N q a Δ
          =
        (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
          * ((((Aq X N q : ℝ) : ℂ)) * localPhaseFactor q a N)) :
    smallBetaExtractedWeighted X N Δ = smallBetaModelWeightedQ Aq X N := by
  rw [smallBetaExtractedWeighted_eq_sum_localArc]
  unfold smallBetaModelWeightedQ
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        smallBetaLocalExtractedArc X N q a Δ
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
          * ((((Aq X N q : ℝ) : ℂ)) * localPhaseFactor q a N) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact hlocal q hq a ha
    _ =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
      * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          (((Aq X N q : ℝ) : ℂ))
            * (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, localPhaseFactor q a N) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro q hq
              calc
                ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                      * ((((Aq X N q : ℝ) : ℂ)) * localPhaseFactor q a N)
                  =
                ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                      * (((Aq X N q : ℝ) : ℂ))) * localPhaseFactor q a N := by
                        refine Finset.sum_congr rfl ?_
                        intro a ha
                        ring
                _ =
                ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                  * (((Aq X N q : ℝ) : ℂ)))
                    * (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, localPhaseFactor q a N) := by
                      rw [Finset.mul_sum]
                _ =
                (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
                  * ((((Aq X N q : ℝ) : ℂ))
                    * (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, localPhaseFactor q a N)) := by
                      ring
    _ =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
      * ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          (((Aq X N q : ℝ) : ℂ)) * qPhaseFactor q N := by
            refine congrArg (fun z : ℂ => (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * z) ?_
            refine Finset.sum_congr rfl ?_
            intro q hq
            rw [qPhaseFactor_eq_sum_localPhaseFactor]

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaArcFactor
