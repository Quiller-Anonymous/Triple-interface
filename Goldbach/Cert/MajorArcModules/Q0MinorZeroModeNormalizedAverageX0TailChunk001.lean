import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailAggregateCheck
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailSupportBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def surrogateDiagonalTailChunk001ExplicitSupportSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001SupportExplicit,
      surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

theorem TailChunk001SupportExplicit_subchunks_disjoint :
    Disjoint TailChunk001Sub000SupportExplicit TailChunk001Sub001SupportExplicit := by
  refine Finset.disjoint_left.mpr ?_
  intro q hq0 hq1
  rcases Finset.mem_filter.mp hq0 with ⟨hqIcc0, _⟩
  rcases Finset.mem_filter.mp hq1 with ⟨hqIcc1, _⟩
  have hle : q ≤ 24726 := (Finset.mem_Icc.mp hqIcc0).2
  have hgt : 24726 < q := by
    have hlow : 24727 ≤ q := (Finset.mem_Icc.mp hqIcc1).1
    omega
  omega

theorem TailChunk001SupportExplicit_eq_subchunks :
    TailChunk001SupportExplicit =
      TailChunk001Sub000SupportExplicit ∪ TailChunk001Sub001SupportExplicit := by
  unfold TailChunk001SupportExplicit
    TailChunk001Sub000SupportExplicit
    TailChunk001Sub001SupportExplicit
  apply Finset.ext
  intro q
  constructor
  · intro hq
    rw [Finset.mem_union]
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hlow, hupp⟩
    by_cases hsplit : q ≤ 24726
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hsplit⟩, hsq⟩
    · right
      have hsplit' : 24727 ≤ q := by
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsplit', hupp⟩, hsq⟩
  · intro hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨hlow, hsplit⟩
      have hupp : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
        change q ≤ 30000
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hupp⟩, hsq⟩
    · rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨_hsplit, hupp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hupp⟩, hsq⟩

theorem surrogateDiagTailChunk001_explicitSupport_eq_subchunk_sum
    (hsub000 :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000First5000)
    (hsub001 :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001First3211) :
    surrogateDiagonalTailChunk001ExplicitSupportSum X0 =
      surrogateDiagTailX0RatChunk001 := by
  unfold surrogateDiagonalTailChunk001ExplicitSupportSum
  rw [TailChunk001SupportExplicit_eq_subchunks]
  rw [Finset.sum_union TailChunk001SupportExplicit_subchunks_disjoint, hsub000, hsub001]
  exact surrogateDiagTailX0RatChunk001_generated_eq_global_check

theorem surrogateDiagTailChunk001_mainSupport_sum_eq_cert
    (hsub000 :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000First5000)
    (hsub001 :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001First3211) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001SupportAtX0,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
      surrogateDiagTailX0RatChunk001 := by
  rw [sum_chunk001_over_main_eq_explicit]
  exact surrogateDiagTailChunk001_explicitSupport_eq_subchunk_sum hsub000 hsub001

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
