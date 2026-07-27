import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidual

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

theorem leftOnlyThree_forall_mem_of_bad_filter_card_zero
    {α : Type*} [DecidableEq α] {s : Finset α} {P : α → Prop}
    [DecidablePred P]
    (hcard : (s.filter (fun x => ! decide (P x))).card = 0) :
    ∀ x ∈ s, P x := by
  intro x hx
  by_contra hPx
  have hxBad : x ∈ s.filter (fun x => ! decide (P x)) := by
    exact Finset.mem_filter.mpr ⟨hx, by simp [hPx]⟩
  have hEmpty : s.filter (fun x => ! decide (P x)) = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hEmpty] at hxBad
  simp at hxBad

def leftOnlyThreeLexLe (a b : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < a ∨ (p.1 = a ∧ p.2 ≤ b)

instance instDecidableLeftOnlyThreeLexLe (a b : ℕ) (p : ℕ × ℕ) :
    Decidable (leftOnlyThreeLexLe a b p) := by
  unfold leftOnlyThreeLexLe
  infer_instance

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice0 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => leftOnlyThreeLexLe 42 146 p)

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice1 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 42 146 p ∧ leftOnlyThreeLexLe 102 74 p)

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice2 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 102 74 p ∧ leftOnlyThreeLexLe 258 34 p)

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice3 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 258 34 p ∧ leftOnlyThreeLexLe 678 10 p)

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice4 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 678 10 p ∧ leftOnlyThreeLexLe 2307 1538 p)

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 2307 1538 p)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
