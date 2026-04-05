import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowQCorrection
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassCorrectionSummands
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
import Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
import Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
import Goldbach.BankPieces.Cert.RawScaleSmallBetaS7Decomposition
import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowQCorrection
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassCorrectionSummands
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
open Goldbach.BankPieces.Cert.RawScaleSmallBetaS7Decomposition
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze

noncomputable section

local notation "canonicalTrueSeam" =>
  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesOnWindow

/--
Abstract `q ≤ Q0` summand expansion for the raw series-correction term.

This is the exact family-level seam needed for the next arithmetic diagnostics: the live object is
not the truncation summands by themselves, but the combined finite-truncation summands coming from
`rawHalfMassTrueSeriesCorrection + canonicalNormalizedSigmaTruncQ0`.
-/
structure CanonicalSeriesTruncCombinationSummandData where
  scalarPart : ℕ → ℂ
  correctionSummand : ℕ → ℕ → ℕ → ℂ
  sum_correction :
    ∀ X N,
      rawHalfMassTrueSeriesCorrection canonicalTrueSeam X N
        =
      scalarPart X
        + ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, correctionSummand X q N

/--
Canonical combined-summand data induced by an exact `q ≤ Q0` correction expansion on the true
Ramanujan seam.
-/
noncomputable def canonicalSeriesTruncCombinationSummandDataOfCorrection
    (A : RawHalfMassTrueSeriesCorrectionSummandData canonicalTrueSeam) :
    CanonicalSeriesTruncCombinationSummandData where
  scalarPart := A.scalarPart
  correctionSummand := A.summand
  sum_correction := fun X N => A.sum_eq X N

/--
Canonical combined-summand data induced directly by the live `kappaTermR` expansion target.

This is the current intended instantiation route for the low-rank arithmetic main-term surface:
first prove `RawHalfMassTrueSeriesCorrectionKappaExpansionTarget`, then transport it into the
exact combined finite-truncation family used here.
-/
noncomputable def canonicalSeriesTruncCombinationSummandDataOfKappaExpansion
    (hT : RawHalfMassTrueSeriesCorrectionKappaExpansionTarget) :
    CanonicalSeriesTruncCombinationSummandData :=
  canonicalSeriesTruncCombinationSummandDataOfCorrection hT.to_summandData

/--
The `q`-indexed combined finite-truncation summand governing the exact arithmetic object.

This is the mathematically aligned family suggested by the latest diagnostics: correction summand
plus canonical truncation summand, not the truncation family in isolation.
-/
noncomputable def canonicalSeriesTruncCombinationSummand
    (A : CanonicalSeriesTruncCombinationSummandData) (X q N : ℕ) : ℂ :=
  A.correctionSummand X q N + canonicalNormalizedSigmaTruncSummand q N

theorem canonicalRawHalfMassSeriesTruncCombination_eq_scalar_add_sum_seriesTruncCombinationSummand
    (A : CanonicalSeriesTruncCombinationSummandData) (X N : ℕ) :
    canonicalRawHalfMassSeriesTruncCombination X N
      =
    A.scalarPart X
      + ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          canonicalSeriesTruncCombinationSummand A X q N := by
  unfold canonicalRawHalfMassSeriesTruncCombination canonicalSeriesTruncCombinationSummand
  rw [A.sum_correction X N, canonicalNormalizedSigmaTruncQ0_eq_sum_truncSummand]
  rw [Finset.sum_add_distrib]
  ring

/-- Raw window sum of a single combined finite-truncation summand on the canonical even window. -/
noncomputable def canonicalSeriesTruncCombinationSummandWindowRawSum
    (A : CanonicalSeriesTruncCombinationSummandData) (X q : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, canonicalSeriesTruncCombinationSummand A X q N

/-- Canonical even-window average of a single combined finite-truncation summand. -/
noncomputable def canonicalSeriesTruncCombinationSummandWindowAverage
    (A : CanonicalSeriesTruncCombinationSummandData) (X q : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * canonicalSeriesTruncCombinationSummandWindowRawSum A X q

/-- Centered profile of the exact combined finite-truncation summand on the canonical even window. -/
noncomputable def centeredCanonicalSeriesTruncCombinationSummandProfile
    (A : CanonicalSeriesTruncCombinationSummandData) (X q N : ℕ) : ℂ :=
  canonicalSeriesTruncCombinationSummand A X q N
    - canonicalSeriesTruncCombinationSummandWindowAverage A X q

/--
Target centered expansion for the exact combined finite-truncation family.

The uncentered finite-`q` expansion is already exact. This structure records the next theorem that
would put the centered canonical combination directly on the centered combined-summand family.
-/
structure CenteredCanonicalSeriesTruncCombinationExpansion
    (A : CanonicalSeriesTruncCombinationSummandData) : Prop where
  eq_sum :
    ∀ X N,
      centeredCanonicalRawHalfMassSeriesTruncCombination X N
        =
      ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        centeredCanonicalSeriesTruncCombinationSummandProfile A X q N

/--
The centered exact combined-family expansion after factoring out an allowed `X`-only scalar.

This is the theorem one wants once the raw correction summands have been exposed explicitly.
-/
theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_sum_centeredSeriesTruncCombinationSummand
    (A : CanonicalSeriesTruncCombinationSummandData)
    (hExp : CenteredCanonicalSeriesTruncCombinationExpansion A)
    (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
      centeredCanonicalSeriesTruncCombinationSummandProfile A X q N :=
  hExp.eq_sum X N

/--
Centered canonical truncation summand profile on the canonical even window.

This is the basic family suggested by the low-rank diagnostics: the arithmetic main term is
allowed to live in a finite-dimensional span of these explicit centered `q ≤ lowQCutoff`
profiles.
-/
noncomputable def centeredCanonicalNormalizedSigmaTruncSummandProfile
    (X q N : ℕ) : ℂ :=
  canonicalNormalizedSigmaTruncSummand q N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalNormalizedSigmaTruncSummand q M

/--
Abstract finite-rank arithmetic data built from explicit `q ≤ lowQCutoff` truncation-summand
profiles.

The basis is not chosen numerically inside Lean. Instead, one supplies a concrete finite family of
moduli together with `X`-dependent coefficients. This keeps the theorem surface honest while still
tracking the low-rank shape suggested by the diagnostics.
-/
structure CanonicalLowRankData (r : ℕ) where
  basisModulus : Fin r → ℕ
  basis_in_range : ∀ i, basisModulus i ∈ Finset.Icc (1 : ℕ) lowQCutoff
  coeff : ℕ → Fin r → ℂ

/-- Explicit finite-dimensional arithmetic main term built from the chosen low-rank data. -/
noncomputable def canonicalLowRankMainTerm
    {r : ℕ} (D : CanonicalLowRankData r) (X N : ℕ) : ℂ :=
  ∑ i : Fin r,
    D.coeff X i * centeredCanonicalNormalizedSigmaTruncSummandProfile X (D.basisModulus i) N

/--
Residual after removing the explicit finite-dimensional arithmetic main term from the centered
canonical finite-truncation combination.
-/
noncomputable def canonicalLowRankResidual
    {r : ℕ} (D : CanonicalLowRankData r) (X N : ℕ) : ℂ :=
  centeredCanonicalRawHalfMassSeriesTruncCombination X N - canonicalLowRankMainTerm D X N

theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_lowRankMainTerm_add_lowRankResidual
    {r : ℕ} (D : CanonicalLowRankData r) (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    canonicalLowRankMainTerm D X N + canonicalLowRankResidual D X N := by
  unfold canonicalLowRankResidual
  ring

/-- Squared `ℓ²(EvenIn X H)` energy of the explicit finite-dimensional arithmetic main term. -/
noncomputable def canonicalLowRankMainTermWindowEnergy
    {r : ℕ} (D : CanonicalLowRankData r) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalLowRankMainTerm D X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the low-rank residual. -/
noncomputable def canonicalLowRankResidualWindowEnergy
    {r : ℕ} (D : CanonicalLowRankData r) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalLowRankResidual D X N‖ ^ 2

/--
Residual target for the finite-dimensional arithmetic main-term decomposition.

This is the theorem surface suggested by the diagnostics: the explicit low-rank main term is kept
deterministic, and only the residual is asked to satisfy the route-sized budget.
-/
structure CenteredCanonicalLowRankResidualWindowTarget
    {r : ℕ} (D : CanonicalLowRankData r) (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalLowRankResidualWindowEnergy D X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Abstract low-rank arithmetic data built from the exact combined finite-truncation summand family.

This supersedes the earlier truncation-only and frozen-augmented candidates as the theorem-level
surface for the live arithmetic program: explicit finite-dimensional arithmetic main term plus
route-sized residual.
-/
structure CanonicalCombinedLowRankData (r : ℕ) where
  basisModulus : Fin r → ℕ
  basis_in_range :
    ∀ i,
      basisModulus i ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0
  coeff : ℕ → Fin r → ℂ

/-- Explicit finite-dimensional arithmetic main term built from the exact combined summand family. -/
noncomputable def canonicalCombinedLowRankMainTerm
    (A : CanonicalSeriesTruncCombinationSummandData)
    {r : ℕ} (D : CanonicalCombinedLowRankData r) (X N : ℕ) : ℂ :=
  ∑ i : Fin r,
    D.coeff X i
      * centeredCanonicalSeriesTruncCombinationSummandProfile A X (D.basisModulus i) N

/--
Residual after removing the explicit finite-dimensional arithmetic main term coming from the exact
combined finite-truncation family.
-/
noncomputable def canonicalCombinedLowRankResidual
    (A : CanonicalSeriesTruncCombinationSummandData)
    {r : ℕ} (D : CanonicalCombinedLowRankData r) (X N : ℕ) : ℂ :=
  centeredCanonicalRawHalfMassSeriesTruncCombination X N
    - canonicalCombinedLowRankMainTerm A D X N

theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_combinedLowRankMainTerm_add_combinedLowRankResidual
    (A : CanonicalSeriesTruncCombinationSummandData)
    {r : ℕ} (D : CanonicalCombinedLowRankData r) (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    canonicalCombinedLowRankMainTerm A D X N
      + canonicalCombinedLowRankResidual A D X N := by
  unfold canonicalCombinedLowRankResidual
  ring

/-- Squared `ℓ²(EvenIn X H)` energy of the combined-family low-rank main term. -/
noncomputable def canonicalCombinedLowRankMainTermWindowEnergy
    (A : CanonicalSeriesTruncCombinationSummandData)
    {r : ℕ} (D : CanonicalCombinedLowRankData r) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalCombinedLowRankMainTerm A D X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the combined-family low-rank residual. -/
noncomputable def canonicalCombinedLowRankResidualWindowEnergy
    (A : CanonicalSeriesTruncCombinationSummandData)
    {r : ℕ} (D : CanonicalCombinedLowRankData r) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalCombinedLowRankResidual A D X N‖ ^ 2

/--
Residual target for the low-rank decomposition built from the exact combined finite-truncation
summand family.

This is the current live theorem surface. Concrete instantiations should come from the exact
combined family, for example via `canonicalSeriesTruncCombinationSummandDataOfKappaExpansion`.
-/
structure CenteredCanonicalCombinedLowRankResidualWindowTarget
    (A : CanonicalSeriesTruncCombinationSummandData)
    {r : ℕ} (D : CanonicalCombinedLowRankData r) (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalCombinedLowRankResidualWindowEnergy A D X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Abstract finite explicit family of exact arithmetic profiles on the canonical even window.

This is the next-level live surface after the failure of the currently tested exact `q`-families:
the arithmetic main term may come from a hybrid finite list of exact profiles rather than from a
single Ramanujan-indexed family.
-/
structure CanonicalExplicitProfileFamily (m : ℕ) where
  profile : Fin m → ℕ → ℕ → ℂ

/-- Centered version of an explicit exact profile on the canonical even window. -/
noncomputable def centeredCanonicalExplicitProfile
    {m : ℕ} (F : CanonicalExplicitProfileFamily m) (i : Fin m) (X N : ℕ) : ℂ :=
  F.profile i X N
    - ((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, F.profile i X M

/--
Finite-dimensional arithmetic main-term data selected from a finite explicit exact family.

The selected basis profiles need not be indexed by moduli. They can come from any exact family of
profiles discovered to align with the centered canonical arithmetic object.
-/
structure CanonicalExplicitLowRankData (m r : ℕ) where
  basisIndex : Fin r → Fin m
  coeff : ℕ → Fin r → ℂ

/--
Full-span selector for an explicit exact profile family.

This is the theorem-facing specialization suggested by the current experiments: the arithmetic main
term is first treated as living in the full explicit span, rather than by imposing a numerically
unstable low-rank compression law.
-/
noncomputable def canonicalExplicitFullSpanData
    (m : ℕ) (coeff : ℕ → Fin m → ℂ) : CanonicalExplicitLowRankData m m where
  basisIndex i := i
  coeff := coeff

/-- Explicit finite-dimensional main term built from a finite exact family of profiles. -/
noncomputable def canonicalExplicitLowRankMainTerm
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r) (X N : ℕ) : ℂ :=
  ∑ i : Fin r,
    D.coeff X i * centeredCanonicalExplicitProfile F (D.basisIndex i) X N

/-- Residual after removing the explicit finite-dimensional main term from the centered target. -/
noncomputable def canonicalExplicitLowRankResidual
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r) (X N : ℕ) : ℂ :=
  centeredCanonicalRawHalfMassSeriesTruncCombination X N
    - canonicalExplicitLowRankMainTerm F D X N

theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_explicitLowRankMainTerm_add_explicitLowRankResidual
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r) (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    canonicalExplicitLowRankMainTerm F D X N
      + canonicalExplicitLowRankResidual F D X N := by
  unfold canonicalExplicitLowRankResidual
  ring

/-- Squared `ℓ²(EvenIn X H)` energy of the explicit-family low-rank residual. -/
noncomputable def canonicalExplicitLowRankResidualWindowEnergy
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalExplicitLowRankResidual F D X N‖ ^ 2

/--
Live abstract residual target for a finite-dimensional arithmetic main term built from an explicit
finite exact family.

This is the broad theorem surface to keep live while the correct exact family is still being
identified empirically.
-/
structure CenteredCanonicalExplicitLowRankResidualWindowTarget
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r) (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalExplicitLowRankResidualWindowEnergy F D X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Single exact residual-profile family on the canonical even window.

The current experimental picture suggests a Type I theorem surface: explicit full-span main term
plus one additional residual profile family, then a genuinely small leftover.
-/
structure CanonicalExplicitResidualProfileFamily where
  profile : ℕ → ℕ → ℂ

/-- Centered version of a single exact residual profile on the canonical even window. -/
noncomputable def centeredCanonicalExplicitResidualProfile
    (R : CanonicalExplicitResidualProfileFamily) (X N : ℕ) : ℂ :=
  R.profile X N
    - ((EvenIn X H).card : ℂ)⁻¹ * ∑ M ∈ EvenIn X H, R.profile X M

/-- `X`-dependent scalar multiple of the centered residual profile. -/
noncomputable def canonicalExplicitRankOneResidualTerm
    (R : CanonicalExplicitResidualProfileFamily) (a : ℕ → ℂ) (X N : ℕ) : ℂ :=
  a X * centeredCanonicalExplicitResidualProfile R X N

/--
Centered canonical target with an explicit full-span main term and one additional residual-profile
family.
-/
noncomputable def canonicalExplicitFullSpanWithRankOneResidual
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r)
    (R : CanonicalExplicitResidualProfileFamily) (a : ℕ → ℂ) (X N : ℕ) : ℂ :=
  canonicalExplicitLowRankMainTerm F D X N + canonicalExplicitRankOneResidualTerm R a X N

/-- Leftover after removing the explicit full-span main term and the rank-one residual family. -/
noncomputable def canonicalExplicitPostResidualRemainder
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r)
    (R : CanonicalExplicitResidualProfileFamily) (a : ℕ → ℂ) (X N : ℕ) : ℂ :=
  centeredCanonicalRawHalfMassSeriesTruncCombination X N
    - canonicalExplicitFullSpanWithRankOneResidual F D R a X N

theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_explicitFullSpan_add_rankOneResidual_add_postResidual
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r)
    (R : CanonicalExplicitResidualProfileFamily) (a : ℕ → ℂ) (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    canonicalExplicitLowRankMainTerm F D X N
      + canonicalExplicitRankOneResidualTerm R a X N
      + canonicalExplicitPostResidualRemainder F D R a X N := by
  unfold canonicalExplicitPostResidualRemainder canonicalExplicitFullSpanWithRankOneResidual
    canonicalExplicitRankOneResidualTerm
  ring

/-- Squared `ℓ²(EvenIn X H)` energy of the post-residual leftover. -/
noncomputable def canonicalExplicitPostResidualRemainderWindowEnergy
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r)
    (R : CanonicalExplicitResidualProfileFamily) (a : ℕ → ℂ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalExplicitPostResidualRemainder F D R a X N‖ ^ 2

/--
Residual target for the explicit full-span family plus one additional residual-profile family.

This is the next theorem-facing surface suggested by the current experiments: the main span is kept
explicit, the additional residual profile is rank 1, and only the post-residual leftover is pushed
into the route-sized budget.
-/
structure CenteredCanonicalExplicitRankOneResidualWindowTarget
    {m r : ℕ} (F : CanonicalExplicitProfileFamily m)
    (D : CanonicalExplicitLowRankData m r)
    (R : CanonicalExplicitResidualProfileFamily) (a : ℕ → ℂ)
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalExplicitPostResidualRemainderWindowEnergy F D R a X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
The exact combined finite-truncation summand family, repackaged as a finite explicit profile family
indexed by the initial `m` positive integers.
-/
noncomputable def canonicalExplicitProfileFamilyOfCombinedSummands
    (A : CanonicalSeriesTruncCombinationSummandData) (m : ℕ) :
    CanonicalExplicitProfileFamily m where
  profile i X N :=
    canonicalSeriesTruncCombinationSummand A X (i.1 + 1) N

/--
The first positive exact candidate family from the supervised dictionary search.

This is the Lean-facing full-span version of the experimental `bank_bridge_g_ss` family:
the frozen bridge formulas `G` and `SS`, together with their exact bank-side geometric source
channels. The current theorem stance is to keep the full exact span live and defer any low-rank
compression until the full-even-window experiment has been checked.
-/
noncomputable def canonicalExplicitProfileFamilyOfBankBridgeGSS :
    CanonicalExplicitProfileFamily 4 where
  profile i X N :=
    match i.1 with
    | 0 => G_formula X N
    | 1 => SS_formula X N
    | 2 => geometricMeanChannelScalar X N
    | _ => zeroModeSigmaBaseline X N

/--
Full-span selector for the exact bank bridge family.

This keeps the live Lean surface at the full exact bank-family span. The coefficients remain
abstract `X`-dependent data; no rank-2 or rank-3 compression is committed here.
-/
noncomputable def canonicalExplicitLowRankDataOfBankBridgeGSS
    (coeff : ℕ → Fin 4 → ℂ) : CanonicalExplicitLowRankData 4 4 where
  basisIndex i := i
  coeff := coeff

/--
The exact scalar channel used by the experiment-side `q0_sigma_*` ambient profiles.

This is kept theorem-facing but deliberately simple: the current arithmetic evidence supports the
span generated by this scalar times the canonical sigma objects, not a rigid coefficient law.
-/
noncomputable def q0LogScaleScalar (N : ℕ) : ℂ :=
  Complex.ofReal <| ((1 / 800 : ℝ) * ((Real.log (N : ℝ)) ^ (2 : ℕ))⁻¹)

/-- The six ambient sigma/scale profiles used by the current explicit-family candidate. -/
noncomputable def canonicalExplicitProfileFamilyOfSigmaScale :
    CanonicalExplicitProfileFamily 6 where
  profile i _X N :=
    match i.1 with
    | 0 => canonicalNormalizedSigmaTruncQ0 N
    | 1 => canonicalTrueSigmaNormalizedSeries N
    | 2 => ((N : ℂ)) * canonicalNormalizedSigmaTruncQ0 N
    | 3 => ((N : ℂ)) * canonicalTrueSigmaNormalizedSeries N
    | 4 => q0LogScaleScalar N * canonicalNormalizedSigmaTruncQ0 N
    | _ => q0LogScaleScalar N * canonicalTrueSigmaNormalizedSeries N

/--
The principal extracted `q = 1` profile from the small-`β` split main term.

This is one of the experimentally indispensable directions in the current explicit arithmetic
candidate family.
-/
noncomputable def canonicalExplicitExtractedPrincipalQ1Profile (X N : ℕ) : ℂ :=
  smallBetaPrincipalQ1MainTermC X N

/--
The exact extracted secondary profile supported on a single modulus.

For the live arithmetic candidate we only use the core moduli `q = 3,5,6,10`, but keeping the
definition general makes the theorem-facing family easier to extend if the residual analysis
forces one additional explicit secondary direction later.
-/
noncomputable def canonicalExplicitExtractedSecondarySingletonProfile
    (q X N : ℕ) : ℂ :=
  smallBetaSecondaryOnModuliC ({q} : Finset ℕ) X N

/-- The exact extracted secondary block supported on the core moduli `{3,5,6,10}`. -/
noncomputable def canonicalExplicitExtractedSecondaryCore5Block (X N : ℕ) : ℂ :=
  smallBetaSecondaryOnModuliC ({3, 5, 6, 10} : Finset ℕ) X N

/-- The exact extracted secondary block supported on the complementary low moduli `{2,4}`. -/
noncomputable def canonicalExplicitExtractedSecondaryLowRemainderBlock (X N : ℕ) : ℂ :=
  smallBetaSecondaryS7MainTermC X N - canonicalExplicitExtractedSecondaryCore5Block X N

/--
The fixed extracted core-5 correction used by the live explicit arithmetic family:

- principal `q = 1`
- secondary moduli `{3,5,6,10}`
-/
noncomputable def canonicalExplicitExtractedCore5Correction (X N : ℕ) : ℂ :=
  canonicalExplicitExtractedPrincipalQ1Profile X N
    + canonicalExplicitExtractedSecondaryCore5Block X N

/--
The exact extracted remainder after removing the core-5 correction from the full weighted
small-`β` extracted model.

This is kept as an exact arithmetic discrepancy built from trusted extracted identities; it is not
claimed to be the live theorem-level residual, only an exact decomposition term.
-/
noncomputable def canonicalExplicitExtractedPostCore5Remainder (X N : ℕ) : ℂ :=
  smallBetaModelWeightedQC AqLocalC X N - canonicalExplicitExtractedCore5Correction X N

/--
Exact extracted decomposition of the weighted small-`β` model into:

- the fixed extracted core-5 correction
- the exact complementary low-modulus block inside `S7`
- the exact beyond-`S7` extracted remainder
-/
theorem smallBetaModelWeightedQC_AqLocalC_eq_extractedCore5_add_postCore5Remainder
    (X N : ℕ) (hX : 2 ≤ X) :
    smallBetaModelWeightedQC AqLocalC X N
      =
    canonicalExplicitExtractedCore5Correction X N
      + (canonicalExplicitExtractedSecondaryLowRemainderBlock X N
          + smallBetaSecondaryBeyondS7MainTermC X N) := by
  rw [smallBetaModelWeightedQC_AqLocalC_eq_principal_plus_secondary (X := X) (N := N) hX]
  rw [smallBetaSecondaryGe2MainTermC_eq_S7_plus_beyondS7]
  unfold canonicalExplicitExtractedCore5Correction canonicalExplicitExtractedPrincipalQ1Profile
    canonicalExplicitExtractedSecondaryLowRemainderBlock
  ring

theorem canonicalExplicitExtractedPostCore5Remainder_eq_lowRemainder_add_beyondS7
    (X N : ℕ) (hX : 2 ≤ X) :
    canonicalExplicitExtractedPostCore5Remainder X N
      =
    canonicalExplicitExtractedSecondaryLowRemainderBlock X N
      + smallBetaSecondaryBeyondS7MainTermC X N := by
  unfold canonicalExplicitExtractedPostCore5Remainder
  rw [smallBetaModelWeightedQC_AqLocalC_eq_extractedCore5_add_postCore5Remainder (X := X) (N := N) hX]
  unfold canonicalExplicitExtractedCore5Correction
  ring

/--
The exact corrected extracted-minus-frozen discrepancy at the trusted `q = 1`/`q ≥ 2` seam.

This packages the existing freeze theorem as a named arithmetic discrepancy object for the current
residual program.
-/
noncomputable def canonicalCorrectedFreezeDiscrepancy (X N : ℕ) : ℂ :=
  smallBetaModelWeightedQC AqLocalC X N - frozenWeightedMainTermQ1CorrectedC X N

theorem canonicalCorrectedFreezeDiscrepancy_eq_integral_doubleSumDefect_add_weightedGe2
    (X N : ℕ) (hX : 2 ≤ X) :
    canonicalCorrectedFreezeDiscrepancy X N
      =
    ((((X : ℝ) : ℂ))⁻¹)
      * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β) β)
      + (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
          * (∑ q ∈ Finset.Icc (2 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
              (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.AqCRescaled X N q (1 : ℝ)
                  - AqFrozenC X N q (1 : ℝ))
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor.qPhaseFactor q N) := by
  unfold canonicalCorrectedFreezeDiscrepancy
  simpa using
    smallBetaModelWeightedQC_sub_frozenWeightedMainTermQ1CorrectedC_eq_integral_doubleSumDefect_add_weightedGe2
      (X := X) (N := N) hX

/--
The current live explicit arithmetic family:

- the sigma/scale ambient span from the canonical true-seam sigma objects
- plus the extracted core-5 correction `{q = 1, 3, 5, 6, 10}`

This is the theorem-facing version of the best family found by the exact full-even experiments.
It is intentionally a full-span family; no unstable coefficient law or low-rank compression is
encoded here.
-/
noncomputable def canonicalExplicitProfileFamilyOfSigmaScaleExtractedCore5 :
    CanonicalExplicitProfileFamily 11 where
  profile i X N :=
    match i.1 with
    | 0 => canonicalNormalizedSigmaTruncQ0 N
    | 1 => canonicalTrueSigmaNormalizedSeries N
    | 2 => ((N : ℂ)) * canonicalNormalizedSigmaTruncQ0 N
    | 3 => ((N : ℂ)) * canonicalTrueSigmaNormalizedSeries N
    | 4 => q0LogScaleScalar N * canonicalNormalizedSigmaTruncQ0 N
    | 5 => q0LogScaleScalar N * canonicalTrueSigmaNormalizedSeries N
    | 6 => canonicalExplicitExtractedPrincipalQ1Profile X N
    | 7 => canonicalExplicitExtractedSecondarySingletonProfile 3 X N
    | 8 => canonicalExplicitExtractedSecondarySingletonProfile 5 X N
    | 9 => canonicalExplicitExtractedSecondarySingletonProfile 6 X N
    | _ => canonicalExplicitExtractedSecondarySingletonProfile 10 X N

/--
Full-span selector for the sigma/scale + extracted core-5 candidate family.

The current experiments support the span itself, not any particular non-orthogonal coordinate law,
so the theorem-facing stance stays at the full exact span.
-/
noncomputable def canonicalExplicitLowRankDataOfSigmaScaleExtractedCore5
    (coeff : ℕ → Fin 11 → ℂ) : CanonicalExplicitLowRankData 11 11 where
  basisIndex i := i
  coeff := coeff

/--
The fixed explicit arithmetic main term currently supported by the experiments:

- the sigma/scale ambient span
- the extracted core-5 correction `{q = 1, 3, 5, 6, 10}`

The coefficients remain abstract `X`-dependent data. The secure theorem stance is now to keep this
family fixed and treat only the post-subtraction remainder as the live arithmetic problem.
-/
noncomputable def canonicalSigmaScaleExtractedCore5MainTerm
    (coeff : ℕ → Fin 11 → ℂ) (X N : ℕ) : ℂ :=
  canonicalExplicitLowRankMainTerm
    canonicalExplicitProfileFamilyOfSigmaScaleExtractedCore5
    (canonicalExplicitLowRankDataOfSigmaScaleExtractedCore5 coeff) X N

/--
Abstract residual after subtracting the fixed sigma/scale + core-5 main term from the centered
canonical arithmetic target.

This is the new live arithmetic residual. No further explicit residual-family identification is
built into the theorem surface.
-/
noncomputable def canonicalSigmaScaleExtractedCore5Residual
    (coeff : ℕ → Fin 11 → ℂ) (X N : ℕ) : ℂ :=
  centeredCanonicalRawHalfMassSeriesTruncCombination X N
    - canonicalSigmaScaleExtractedCore5MainTerm coeff X N

theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_sigmaScaleExtractedCore5MainTerm_add_residual
    (coeff : ℕ → Fin 11 → ℂ) (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    canonicalSigmaScaleExtractedCore5MainTerm coeff X N
      + canonicalSigmaScaleExtractedCore5Residual coeff X N := by
  unfold canonicalSigmaScaleExtractedCore5Residual
    canonicalSigmaScaleExtractedCore5MainTerm
  ring

/-- Squared `ℓ²(EvenIn X H)` energy of the post-core5 residual. -/
noncomputable def canonicalSigmaScaleExtractedCore5ResidualWindowEnergy
    (coeff : ℕ → Fin 11 → ℂ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖canonicalSigmaScaleExtractedCore5Residual coeff X N‖ ^ 2

/--
Live residual-energy target after subtracting the fixed sigma/scale + core-5 main term.

This is the conservative reset supported by the current evidence: the main term is explicit and
fixed, while the residual remains exact but abstract and is asked directly to satisfy the
route-sized window-energy bound.
-/
structure CenteredCanonicalSigmaScaleExtractedCore5ResidualWindowTarget
    (coeff : ℕ → Fin 11 → ℂ) (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSigmaScaleExtractedCore5ResidualWindowEnergy coeff X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm
