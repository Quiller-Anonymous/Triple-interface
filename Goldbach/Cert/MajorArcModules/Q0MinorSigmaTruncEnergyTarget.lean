import Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncObservables

/-!
The canonical truncation-energy surface, separated from the historical certificate machinery.
The declarations keep their original namespace and definitions.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators
open Goldbach.BankParams Goldbach.Windows
open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail

/-- Squared `ℓ²(EvenIn X H)` energy of the centered fixed-`Q0` truncation on the canonical window. -/
noncomputable def centeredNormalizedSigmaTruncWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredNormalizedSigmaTrunc ramanujanSeriesOnWindow X N‖ ^ 2

/-- Native truncation window-energy target on the direct normalized route. -/
structure CenteredNormalizedSigmaTruncWindowEnergyTarget (Cτ : ℝ) : Prop where
  Cτ_nonneg : 0 ≤ Cτ
  bound : ∀ {X : ℕ}, X0 ≤ X → centeredNormalizedSigmaTruncWindowEnergy X ≤ Cτ

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
