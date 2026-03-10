import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
import Mathlib.Data.Int.NatAbs
import SSU.Hilbert.DistZ

/-!
SSU-facing adapter for the Goldbach dyadic minor-arc packets.

This file does not prove any analytic decay. It only repackages the existing Goldbach data
`JX`, `dyadicV`, `dyadicD` as a fixed-`X` family indexed by `ℤ`, matching the index
conventions used by SSU's interzone layer.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUAdapter

open scoped BigOperators

open Goldbach.BankParams
open Goldbach.Windows
open SSU.Hilbert

open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle

noncomputable section

/-- The Goldbach dyadic Hilbert space at fixed `X`. -/
abbrev DyadicSignal (X : ℕ) : Type :=
  EuclideanSpace ℂ (EvenIn X H)

/-- The canonical Goldbach dyadic index set, now viewed as a finite subset of `ℤ`. -/
noncomputable def JXZ (X : ℕ) : Finset ℤ :=
  (JX X).image Int.ofNat

/-- The Goldbach dyadic vectors, promoted to a total `ℤ → DyadicSignal X` family. -/
noncomputable def dyadicVZ (X : ℕ) (Δ : ℝ) (z : ℤ) : DyadicSignal X :=
  if _hz : 0 ≤ z then dyadicV X Δ z.toNat else 0

/-- The Goldbach dyadic diagonal weights, promoted to a total `ℤ → ℝ` family. -/
noncomputable def dyadicDZ (X : ℕ) (Δ : ℝ) (z : ℤ) : ℝ :=
  if _hz : 0 ≤ z then dyadicD X Δ z.toNat else 0

lemma mem_JXZ_iff {X : ℕ} {z : ℤ} :
    z ∈ JXZ X ↔ ∃ j ∈ JX X, Int.ofNat j = z := by
  constructor
  · intro hz
    simpa [JXZ] using Finset.mem_image.mp hz
  · intro hz
    simpa [JXZ] using Finset.mem_image.mpr hz

lemma nonneg_of_mem_JXZ {X : ℕ} {z : ℤ} (hz : z ∈ JXZ X) : 0 ≤ z := by
  rcases mem_JXZ_iff.mp hz with ⟨j, _hj, rfl⟩
  exact Int.natCast_nonneg j

lemma mem_JXZ_of_mem_JX {X j : ℕ} (hj : j ∈ JX X) : Int.ofNat j ∈ JXZ X := by
  exact mem_JXZ_iff.mpr ⟨j, hj, rfl⟩

@[simp] lemma dyadicVZ_ofNat (X : ℕ) (Δ : ℝ) (j : ℕ) :
    dyadicVZ X Δ (Int.ofNat j) = dyadicV X Δ j := by
  simp [dyadicVZ]

@[simp] lemma dyadicDZ_ofNat (X : ℕ) (Δ : ℝ) (j : ℕ) :
    dyadicDZ X Δ (Int.ofNat j) = dyadicD X Δ j := by
  simp [dyadicDZ]

lemma dyadicVZ_eq_toNat {X : ℕ} {Δ : ℝ} {z : ℤ} (hz : z ∈ JXZ X) :
    dyadicVZ X Δ z = dyadicV X Δ z.toNat := by
  have hz0 : 0 ≤ z := nonneg_of_mem_JXZ hz
  simp [dyadicVZ, hz0]

lemma dyadicDZ_eq_toNat {X : ℕ} {Δ : ℝ} {z : ℤ} (hz : z ∈ JXZ X) :
    dyadicDZ X Δ z = dyadicD X Δ z.toNat := by
  have hz0 : 0 ≤ z := nonneg_of_mem_JXZ hz
  simp [dyadicDZ, hz0]

lemma distZ_ofNat_eq_natDist (i j : ℕ) :
    distZ (Int.ofNat i) (Int.ofNat j) = Nat.dist i j := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij, distZ]
    simpa using Int.natAbs_natCast_sub_natCast_of_le hij
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji, distZ]
    simpa [sub_eq_add_neg, add_comm] using Int.natAbs_natCast_sub_natCast_of_ge hji

lemma sum_JXZ_eq_sum_JX {X : ℕ} {β : Type*} [AddCommMonoid β] (f : ℤ → β) :
    ∑ z ∈ JXZ X, f z = ∑ j ∈ JX X, f (Int.ofNat j) := by
  classical
  unfold JXZ
  refine Finset.sum_image ?_
  intro a _ha b _hb hab
  exact Int.ofNat.inj hab

lemma sum_JXZ_dyadicDZ_eq_sum_JX_dyadicD (X : ℕ) (Δ : ℝ) :
    ∑ z ∈ JXZ X, dyadicDZ X Δ z = ∑ j ∈ JX X, dyadicD X Δ j := by
  rw [sum_JXZ_eq_sum_JX]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact dyadicDZ_ofNat X Δ j

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUAdapter
