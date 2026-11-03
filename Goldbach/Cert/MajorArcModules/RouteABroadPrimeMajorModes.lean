import Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProjector
import Goldbach.Cert.MajorArcStep15Parameters

/-!
# Sampled textbook major frequencies for the corrected Route A

This module samples the repository's coefficient-independent textbook major-arc predicate on the
finite cyclic frequency grid for `[X, 2X]`.  The resulting set is then closed under negation so
that conjugate frequencies are retained together.

This is a hard mode mask.  It fixes the arithmetic definition of a candidate frequency bank, but
does not claim an edge-leakage or taper estimate.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeMajorModes

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProjector
open Goldbach.Cert.MajorArcStep15Parameters

noncomputable section

/-- Frequency in `[0,1)` represented by a cyclic DFT coordinate. -/
def sampledFrequency (X : ℕ) (k : CyclicIndex X) : ℝ :=
  (k.val : ℝ) / (X + 1 : ℕ)

/-- Raw DFT coordinates lying in the textbook major arcs. -/
noncomputable def rawTextbookMajorModes
    (X B : ℕ) (Δ : ℝ) : Finset (CyclicIndex X) := by
  classical
  exact Finset.univ.filter fun k => IsMajorArcTextbook X B Δ (sampledFrequency X k)

/-- Close a finite cyclic mode set under conjugate frequency `k ↦ -k`. -/
noncomputable def conjugationSymmetricClosure
    {X : ℕ} (modes : Finset (CyclicIndex X)) : Finset (CyclicIndex X) := by
  classical
  exact modes ∪ modes.image fun k => -k

theorem mem_conjugationSymmetricClosure_iff
    {X : ℕ} {modes : Finset (CyclicIndex X)} {k : CyclicIndex X} :
    k ∈ conjugationSymmetricClosure modes ↔ k ∈ modes ∨ -k ∈ modes := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact Or.inl hk
    · rcases Finset.mem_image.mp hk with ⟨j, hj, hjk⟩
      right
      have hkj : -k = j := by
        rw [← hjk]
        simp
      simpa [hkj] using hj
  · rintro (hk | hk)
    · exact Finset.mem_union_left _ hk
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ?_)
      exact ⟨-k, hk, by simp⟩

theorem neg_mem_conjugationSymmetricClosure_iff
    {X : ℕ} {modes : Finset (CyclicIndex X)} {k : CyclicIndex X} :
    -k ∈ conjugationSymmetricClosure modes ↔
      k ∈ conjugationSymmetricClosure modes := by
  rw [mem_conjugationSymmetricClosure_iff, mem_conjugationSymmetricClosure_iff]
  simp [or_comm]

/--
Candidate major-frequency bank: textbook rational arcs sampled on the finite DFT grid and closed
under conjugation.
-/
noncomputable def sampledTextbookMajorModes
    (X B : ℕ) (Δ : ℝ) : Finset (CyclicIndex X) :=
  conjugationSymmetricClosure (rawTextbookMajorModes X B Δ)

theorem neg_mem_sampledTextbookMajorModes_iff
    {X B : ℕ} {Δ : ℝ} {k : CyclicIndex X} :
    -k ∈ sampledTextbookMajorModes X B Δ ↔
      k ∈ sampledTextbookMajorModes X B Δ :=
  neg_mem_conjugationSymmetricClosure_iff

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeMajorModes
