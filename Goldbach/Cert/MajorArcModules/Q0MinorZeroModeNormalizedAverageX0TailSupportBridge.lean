import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def TailChunk000Sub000SupportExplicit : Finset ℕ :=
  (Finset.Icc 51 8269).filter Squarefree

def TailChunk000Sub001SupportExplicit : Finset ℕ :=
  (Finset.Icc 8270 16495).filter Squarefree

def TailChunk001Sub000SupportExplicit : Finset ℕ :=
  (Finset.Icc 16496 24726).filter Squarefree

def TailChunk001Sub001SupportExplicit : Finset ℕ :=
  (Finset.Icc 24727 Goldbach.AO_OffDiag.TailBlock.Q0).filter Squarefree

def TailChunk000SupportExplicit : Finset ℕ :=
  (Finset.Icc 51 16495).filter Squarefree

def TailChunk001SupportExplicit : Finset ℕ :=
  (Finset.Icc 16496 Goldbach.AO_OffDiag.TailBlock.Q0).filter Squarefree

def TailSupportExplicit : Finset ℕ :=
  (Finset.Icc 51 Goldbach.AO_OffDiag.TailBlock.Q0).filter Squarefree

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub000SupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub000SupportAtX0 =
      TailChunk000Sub000SupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hq000, hq8269⟩
    rcases Finset.mem_filter.mp hq000 with ⟨hqTail, _hq16495⟩
    rcases Finset.mem_filter.mp hqTail with ⟨hqCoeff, _hnotlow, hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨hqIcc, hsq⟩
    have hq51 : 51 ≤ q := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq51, hq8269⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq51, hq8269⟩
    have hq16495 : q ≤ 16495 := by omega
    have hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
      change q ≤ 30000
      omega
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    refine Finset.mem_filter.mpr ⟨?_, hq8269⟩
    refine Finset.mem_filter.mpr ⟨?_, hq16495⟩
    exact Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub001SupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub001SupportAtX0 =
      TailChunk000Sub001SupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hq000, hqgt8269⟩
    rcases Finset.mem_filter.mp hq000 with ⟨hqTail, hq16495⟩
    rcases Finset.mem_filter.mp hqTail with ⟨hqCoeff, _hnotlow, _hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨_hqIcc, hsq⟩
    have hq8270 : 8270 ≤ q := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq8270, hq16495⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq8270, hq16495⟩
    have hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
      change q ≤ 30000
      omega
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    refine Finset.mem_filter.mpr ⟨?_, by omega⟩
    refine Finset.mem_filter.mpr ⟨?_, hq16495⟩
    exact Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub000SupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub000SupportAtX0 =
      TailChunk001Sub000SupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hq001, hq24726⟩
    rcases Finset.mem_filter.mp hq001 with ⟨hqTail, hqgt16495⟩
    rcases Finset.mem_filter.mp hqTail with ⟨hqCoeff, _hnotlow, _hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨_hqIcc, hsq⟩
    have hq16496 : 16496 ≤ q := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq16496, hq24726⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq16496, hq24726⟩
    have hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
      change q ≤ 30000
      omega
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    refine Finset.mem_filter.mpr ⟨?_, hq24726⟩
    refine Finset.mem_filter.mpr ⟨?_, by omega⟩
    exact Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub001SupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub001SupportAtX0 =
      TailChunk001Sub001SupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hq001, hqgt24726⟩
    rcases Finset.mem_filter.mp hq001 with ⟨hqTail, hqgt16495⟩
    rcases Finset.mem_filter.mp hqTail with ⟨hqCoeff, _hnotlow, _hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨hqIcc, hsq⟩
    have hq24727 : 24727 ≤ q := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq24727, (Finset.mem_Icc.mp hqIcc).2⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq24727, hqQ0⟩
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    refine Finset.mem_filter.mpr ⟨?_, by omega⟩
    refine Finset.mem_filter.mpr ⟨?_, by omega⟩
    exact Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000SupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000SupportAtX0 =
      TailChunk000SupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqTail, hq16495⟩
    rcases Finset.mem_filter.mp hqTail with ⟨hqCoeff, _hnotlow, hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨_hqIcc, hsq⟩
    have hq51 : 51 ≤ q := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq51, hq16495⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq51, hq16495⟩
    have hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
      change q ≤ 30000
      omega
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    exact Finset.mem_filter.mpr <|
      ⟨Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩, hq16495⟩

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001SupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001SupportAtX0 =
      TailChunk001SupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqTail, hqgt16495⟩
    rcases Finset.mem_filter.mp hqTail with ⟨hqCoeff, _hnotlow, hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨hqIcc, hsq⟩
    have hq16496 : 16496 ≤ q := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq16496, (Finset.mem_Icc.mp hqIcc).2⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq16496, hqQ0⟩
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    exact Finset.mem_filter.mpr <|
      ⟨Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩, by omega⟩

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailSupportAtX0_eq_explicit :
    centeredNormalizedSigmaTruncSurrogateDiagonalTailSupportAtX0 =
      TailSupportExplicit := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqCoeff, _hnotlow, hqgt50⟩
    rcases mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hqCoeff with ⟨hqIcc, hsq⟩
    have hq51 : 51 ≤ q := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq51, (Finset.mem_Icc.mp hqIcc).2⟩, hsq⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hsq⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq51, hqQ0⟩
    have hqCoeff : q ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ0⟩, hsq⟩
    have hnotlow : q ∉ centeredNormalizedSigmaTruncDiagonalMainLowQSupport := by
      simp [centeredNormalizedSigmaTruncDiagonalMainLowQSupport]
      omega
    exact Finset.mem_filter.mpr ⟨hqCoeff, hnotlow, by omega⟩

theorem sum_chunk000Sub000_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub000SupportAtX0, f q) =
      ∑ q ∈ TailChunk000Sub000SupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub000SupportAtX0_eq_explicit]

theorem sum_chunk000Sub001_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub001SupportAtX0, f q) =
      ∑ q ∈ TailChunk000Sub001SupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub001SupportAtX0_eq_explicit]

theorem sum_chunk001Sub000_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub000SupportAtX0, f q) =
      ∑ q ∈ TailChunk001Sub000SupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub000SupportAtX0_eq_explicit]

theorem sum_chunk001Sub001_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub001SupportAtX0, f q) =
      ∑ q ∈ TailChunk001Sub001SupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub001SupportAtX0_eq_explicit]

theorem sum_chunk000_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000SupportAtX0, f q) =
      ∑ q ∈ TailChunk000SupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000SupportAtX0_eq_explicit]

theorem sum_chunk001_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001SupportAtX0, f q) =
      ∑ q ∈ TailChunk001SupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001SupportAtX0_eq_explicit]

theorem sum_tail_over_main_eq_explicit
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailSupportAtX0, f q) =
      ∑ q ∈ TailSupportExplicit, f q := by
  rw [centeredNormalizedSigmaTruncSurrogateDiagonalTailSupportAtX0_eq_explicit]

theorem chunk000Sub000_main_sum_eq_of_explicit
    (h :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub000SupportAtX0,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
      surrogateDiagTailX0RatChunk000Sub000 := by
  rw [sum_chunk000Sub000_over_main_eq_explicit]
  exact h

theorem chunk000Sub001_main_sum_eq_of_explicit
    (h :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000Sub001SupportAtX0,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
      surrogateDiagTailX0RatChunk000Sub001 := by
  rw [sum_chunk000Sub001_over_main_eq_explicit]
  exact h

theorem chunk001Sub000_main_sum_eq_of_explicit
    (h :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub000SupportAtX0,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
      surrogateDiagTailX0RatChunk001Sub000 := by
  rw [sum_chunk001Sub000_over_main_eq_explicit]
  exact h

theorem chunk001Sub001_main_sum_eq_of_explicit
    (h :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001) :
    (∑ q ∈ centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001Sub001SupportAtX0,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
      surrogateDiagTailX0RatChunk001Sub001 := by
  rw [sum_chunk001Sub001_over_main_eq_explicit]
  exact h

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
