import Goldbach.BankPieces.Cert.TrueSingularSeries

/-!
Canonical finite-truncation observables, independent of geometric zero-mode machinery.
These declarations retain their historical namespaces and exact definitions.
-/

open scoped BigOperators
open Goldbach.BankParams Goldbach.Windows
open Goldbach.BankPieces.Cert.TrueSingularSeries

namespace Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge

/-- The normalized fixed-`Q0` truncation. -/
noncomputable def normalizedSigmaTruncQ0 (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℂ :=
  (((Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N / ((2 : ℝ) * S.C.C2)) : ℝ) : ℂ)

end Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail

open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge

/-- Raw window sum of the normalized fixed-`Q0` truncation on the canonical even window. -/
noncomputable def normalizedSigmaTruncWindowRawSum
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, normalizedSigmaTruncQ0 S N

/-- Canonical even-window average of the normalized fixed-`Q0` truncation. -/
noncomputable def normalizedSigmaTruncWindowAverage
    (S : TrueSingularSeriesOnWindow) (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * normalizedSigmaTruncWindowRawSum S X

/-- Centered normalized fixed-`Q0` truncation on the canonical even window. -/
noncomputable def centeredNormalizedSigmaTrunc
    (S : TrueSingularSeriesOnWindow) (X N : ℕ) : ℂ :=
  normalizedSigmaTruncQ0 S N - normalizedSigmaTruncWindowAverage S X

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
