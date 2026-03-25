import Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge

noncomputable section

/--
Turn an externally supplied ordered mode list into a finite mode set inside the chosen ambient
support by filtering to the support and keeping the first `K` entries.

This is intentionally basis-agnostic: the caller may supply Fourier-, cosine-, or otherwise ranked
modes without changing the core minor bridge.
-/
noncomputable def topKModesFromList (support : Finset ℤ) (orderedModes : List ℤ) (K : ℕ) : Finset ℤ :=
  ((orderedModes.filter fun t => t ∈ support).take K).toFinset

/-- Project a coefficient object onto the first `K` modes from an externally supplied ordering. -/
noncomputable def projectTopKFromList
    (support : Finset ℤ) (orderedModes : List ℤ) (K : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  rankKProjector (topKModesFromList support orderedModes K) f

/-- Residual after projecting onto the first `K` modes from an externally supplied ordering. -/
noncomputable def residualAfterTopKFromList
    (support : Finset ℤ) (orderedModes : List ℤ) (K : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun t => f t - projectTopKFromList support orderedModes K f t

/-- The canonical ambient support for experiment-facing window-stable minor mode selection. -/
noncomputable def canonicalMinorAmbientSupport (X : ℕ) : Finset ℤ :=
  (windowMinorCoeffSupport X).erase 0

/-- Top-`K` projector on the centered weighted minor coefficient object. -/
noncomputable def coeffCenteredProjectTopK
    (X N : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℤ → ℂ :=
  projectTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffCentered X N)

/-- Top-`K` residual on the centered weighted minor coefficient object. -/
noncomputable def coeffCenteredResidualTopK
    (X N : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℤ → ℂ :=
  residualAfterTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffCentered X N)

/-- Top-`K` projector on the weight-regressed arithmetic residual object. -/
noncomputable def coeffArithProjectTopK
    (X N : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℤ → ℂ :=
  projectTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffArith X N)

/-- Top-`K` residual on the weight-regressed arithmetic residual object. -/
noncomputable def coeffArithResidualTopK
    (X N : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℤ → ℂ :=
  residualAfterTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffArith X N)

theorem topKModesFromList_subset_support
    (support : Finset ℤ) (orderedModes : List ℤ) (K : ℕ) :
    topKModesFromList support orderedModes K ⊆ support := by
  intro t ht
  have ht' : t ∈ ((orderedModes.filter fun u => u ∈ support).take K) := by
    exact List.mem_toFinset.mp ht
  have ht'' : t ∈ orderedModes.filter fun u => u ∈ support := by
    exact List.mem_of_mem_take ht'
  simpa using (List.mem_filter.mp ht'').2

theorem projectTopKFromList_apply_mem
    {support : Finset ℤ} {orderedModes : List ℤ} {K : ℕ} {f : ℤ → ℂ} {t : ℤ}
    (ht : t ∈ topKModesFromList support orderedModes K) :
    projectTopKFromList support orderedModes K f t = f t := by
  unfold projectTopKFromList rankKProjector finiteModeProjector
  simp [ht]

theorem projectTopKFromList_apply_not_mem
    {support : Finset ℤ} {orderedModes : List ℤ} {K : ℕ} {f : ℤ → ℂ} {t : ℤ}
    (ht : t ∉ topKModesFromList support orderedModes K) :
    projectTopKFromList support orderedModes K f t = 0 := by
  unfold projectTopKFromList rankKProjector finiteModeProjector
  simp [ht]

theorem coeffArithResidualTopK_eq_coeffArith_sub_projector
    (X N : ℕ) (orderedModes : List ℤ) (K : ℕ) (t : ℤ) :
    coeffArithResidualTopK X N orderedModes K t
      =
    coeffArith X N t - coeffArithProjectTopK X N orderedModes K t := by
  rfl

theorem coeffCenteredResidualTopK_eq_coeffCentered_sub_projector
    (X N : ℕ) (orderedModes : List ℤ) (K : ℕ) (t : ℤ) :
    coeffCenteredResidualTopK X N orderedModes K t
      =
    coeffCentered X N t - coeffCenteredProjectTopK X N orderedModes K t := by
  rfl

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
