import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailAggregateCheck
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailSupportBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def surrogateDiagonalTailChunk000ExplicitSupportSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000SupportExplicit,
      surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

theorem TailChunk000SupportExplicit_subchunks_disjoint :
    Disjoint TailChunk000Sub000SupportExplicit TailChunk000Sub001SupportExplicit := by
  refine Finset.disjoint_left.mpr ?_
  intro q hq0 hq1
  rcases Finset.mem_filter.mp hq0 with ⟨hqIcc0, _⟩
  rcases Finset.mem_filter.mp hq1 with ⟨hqIcc1, _⟩
  have hle : q ≤ 8269 := (Finset.mem_Icc.mp hqIcc0).2
  have hgt : 8269 < q := by
    have hlow : 8270 ≤ q := (Finset.mem_Icc.mp hqIcc1).1
    omega
  omega

theorem TailChunk000SupportExplicit_eq_subchunks :
    TailChunk000SupportExplicit =
      TailChunk000Sub000SupportExplicit ∪ TailChunk000Sub001SupportExplicit := by
  unfold TailChunk000SupportExplicit
    TailChunk000Sub000SupportExplicit
    TailChunk000Sub001SupportExplicit
  apply Finset.ext
  intro q
  constructor
  · intro hq
    rw [Finset.mem_union]
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hlow, hupp⟩
    by_cases hsplit : q ≤ 8269
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hsplit⟩, hsq⟩
    · right
      have hsplit' : 8270 ≤ q := by
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsplit', hupp⟩, hsq⟩
  · intro hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨hlow, _hsplit⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, by omega⟩, hsq⟩
    · rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨_hsplit, hupp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hupp⟩, hsq⟩

theorem surrogateDiagTailChunk000_explicitSupport_eq_subchunk_sum
    (hsub000 :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000First5000)
    (hsub001 :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001First5000) :
    surrogateDiagonalTailChunk000ExplicitSupportSum X0 =
      surrogateDiagTailX0RatChunk000 := by
  unfold surrogateDiagonalTailChunk000ExplicitSupportSum
  rw [TailChunk000SupportExplicit_eq_subchunks]
  rw [Finset.sum_union TailChunk000SupportExplicit_subchunks_disjoint, hsub000, hsub001]
  exact surrogateDiagTailX0RatChunk000_generated_eq_global_check

theorem surrogateDiagTailChunk000_mainSupport_sum_eq_cert
    (hsub000 :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000First5000)
    (hsub001 :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001First5000) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000SupportAtX0,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
      surrogateDiagTailX0RatChunk000 := by
  rw [sum_chunk000_over_main_eq_explicit]
  exact surrogateDiagTailChunk000_explicitSupport_eq_subchunk_sum hsub000 hsub001

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
