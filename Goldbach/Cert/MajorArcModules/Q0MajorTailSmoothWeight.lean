import Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
import Goldbach.Cert.MajorArcModules.Q0MajorTailWindows
import Goldbach.Cert.MajorArcStep23RamanujanSum

/-!
Option-3 preparation: a smooth majorant weight for the hard `Q0` major arcs (Δ = 1).

The notes’ hybrid large sieve / alias suppression statements are phrased for weighted windows
around rationals. In the Lean pipeline, the major arcs are a hard indicator `1_{majorArcSetQ0}`.

This module provides a deterministic bridge: a windowed weight built from `wTextbook` that
dominates the hard major-arc indicator pointwise.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight

open scoped BigOperators

open Goldbach
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction

open Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
open Goldbach.Cert.MajorArcModules.Q0MajorTailWindows

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
Smooth majorant weight (Δ = 1) built from the explicit piecewise-linear window `wTextbook`.

This is intended to match the kind of weighted major-arc detector used in the notes.
-/
noncomputable def majorArcWeightSmooth (X : ℕ) : ℝ → ℝ :=
  fun α =>
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ∑ a ∈ Rcop q,
        wTextbook X q a α

lemma majorArcWeight_le_majorArcWeightSmooth (X : ℕ) (α : ℝ) :
    majorArcWeight X (1 : ℝ) α ≤ majorArcWeightSmooth X α := by
  classical
  by_cases hα : α ∈ majorArcSetQ0 X (1 : ℝ)
  · have hW : majorArcWeight X (1 : ℝ) α = 1 := by
      simp [majorArcWeight, hα]
    -- Extract witnesses `q,a` for membership in the union.
    rcases (Set.mem_iUnion.mp hα) with ⟨q, hq'⟩
    rcases (Set.mem_iUnion.mp hq') with ⟨hq, ha'⟩
    rcases (Set.mem_iUnion.mp ha') with ⟨a, ha''⟩
    rcases (Set.mem_iUnion.mp ha'') with ⟨ha, hmem⟩

    have hw : (1 : ℝ) ≤ wTextbook X q a α := by
      have hle :=
        indicator_arcSetTextbook_le_wTextbook (X := X) (q := q) (a := a) (Δ := (1 : ℝ))
          (hΔ := rfl) (α := α)
      have hind :
          (arcSetTextbook X q a (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) α = (1 : ℝ) := by
        simp [Set.indicator_of_mem hmem]
      -- rewrite the indicator to `1` and conclude
      simpa [hind] using hle

    have hsum :
        wTextbook X q a α ≤ majorArcWeightSmooth X α := by
      unfold majorArcWeightSmooth
      -- first: bound by the inner sum at fixed `q`
      have hinner :
          wTextbook X q a α ≤ ∑ a' ∈ Rcop q, wTextbook X q a' α :=
        Finset.single_le_sum
          (s := Rcop q)
          (f := fun a' : ℕ => wTextbook X q a' α)
          (by
            intro a' ha'
            exact wTextbook_nonneg (X := X) (q := q) (a := a') (α := α))
          ha
      -- second: bound that inner sum by the full outer sum
      have houter :
          (∑ a' ∈ Rcop q, wTextbook X q a' α)
            ≤
          ∑ q' ∈ Finset.Icc (1 : ℕ) Q0, ∑ a' ∈ Rcop q', wTextbook X q' a' α :=
        Finset.single_le_sum
          (s := Finset.Icc (1 : ℕ) Q0)
          (f := fun q' : ℕ => ∑ a' ∈ Rcop q', wTextbook X q' a' α)
          (by
            intro q' hq'
            refine Finset.sum_nonneg ?_
            intro a' ha'
            exact wTextbook_nonneg (X := X) (q := q') (a := a') (α := α))
          hq
      exact le_trans hinner houter

    have h1 : (1 : ℝ) ≤ majorArcWeightSmooth X α := le_trans hw hsum
    simpa [hW] using h1
  · -- Off the hard major arcs, `majorArcWeight = 0 ≤ smooth`.
    have : majorArcWeight X (1 : ℝ) α = 0 := by
      simp [majorArcWeight, hα]
    -- The smooth weight is a sum of nonnegative terms.
    have hnonneg : 0 ≤ majorArcWeightSmooth X α := by
      unfold majorArcWeightSmooth
      refine Finset.sum_nonneg ?_
      intro q hq
      refine Finset.sum_nonneg ?_
      intro a ha
      exact wTextbook_nonneg (X := X) (q := q) (a := a) (α := α)
    simpa [this] using hnonneg

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight
