import Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion
import Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge

/-!
# Identification of the normalized truncation with its finite divisor observable

This is an equality for the existing observable.  It introduces neither a new normalization nor
an assumption about the missing uniform moment/discrepancy estimates.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncDivisorBridge

open scoped BigOperators
open Goldbach.AO_OffDiag.TailBlock
open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion

noncomputable section

def normalizedDivisorObservable (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℂ :=
  Complex.ofReal
    ((∑ d ∈ Finset.Icc 1 Q0,
      if d ∣ N then
        divisorCoefficient Q0 (fun q => muSq q * (1 / (Nat.totient q : ℝ) ^ 2)) d
      else 0) / (2 * S.C.C2))

theorem normalizedSigmaTruncQ0_eq_normalizedDivisorObservable
    (S : TrueSingularSeriesOnWindow) (N : ℕ) :
    normalizedSigmaTruncQ0 S N = normalizedDivisorObservable S N := by
  unfold normalizedSigmaTruncQ0 normalizedDivisorObservable
  rw [sigma_trunc_Q0_eq_sum_divisorCoefficient]

theorem canonicalNormalizedSigmaTruncQ0_eq_normalizedDivisorObservable (N : ℕ) :
    canonicalNormalizedSigmaTruncQ0 N =
      normalizedDivisorObservable ramanujanSeriesOnWindow N := by
  rw [canonicalNormalizedSigmaTruncQ0_eq_normalizedSigmaTruncQ0_ramanujanSeriesOnWindow,
    normalizedSigmaTruncQ0_eq_normalizedDivisorObservable]

end
end Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncDivisorBridge
