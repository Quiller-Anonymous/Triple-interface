import Goldbach.Cert.MajorArcStep25MinorArcBound

/-!
Major arcs (Step 25, canonical certificate): a pinned minor-arc cap on the canonical window.

`MajorArcStep25MinorArcBound` provides the measure-theory reduction
`‖corr_integral_minor‖ ≤ kernelCap * M^2` from pointwise minor-arc bounds on the shifted exponential
sums.

This file records the remaining analytic input as a *certificate axiom* on the canonical window:
uniform pointwise bounds on the shifted exponential sums on the minor arcs.

LEGACY FILE NOT CURRENTLY IN THE PIPELINE
-/

namespace Goldbach.Cert
namespace MajorArcStep25MinorArcCert

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep15Parameters
open Goldbach.Cert.MajorArcStep25MinorArcBound

noncomputable section

-- Canonical “textbook” major-arc parameters used for the split.
-- (These can be adjusted later once the analytic minor-arc theory is in place.)
abbrev B_canon : ℕ := 2
noncomputable abbrev Δ_canon : ℝ := 1

-- Canonical minor-arc sup-norm cap for the shifted exponential sums.
noncomputable abbrev Mminor_canon : ℝ := 1

lemma Mminor_canon_nonneg : 0 ≤ Mminor_canon := by
  simp [Mminor_canon]

/--
Certificate axiom: on the canonical window, the shifted exponential sums are uniformly bounded
by `Mminor_canon` on the α-minor arcs (for all β).

This is the genuine analytic content needed to turn Step 25’s “plumbing” into a numeric bound.
-/
axiom expSum_minor_bound_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      ∀ {β α : ℝ},
        α ∈ (majorArcSetTextbook X B_canon Δ_canon)ᶜ →
          ‖expSum X N ((α : UC) - (β : UC))‖ ≤ Mminor_canon ∧
          ‖expSum X N ((α : UC) + (β : UC))‖ ≤ Mminor_canon

/-- The resulting pinned minor-arc bound for `corr_integral_minor` on the canonical window. -/
theorem norm_corr_integral_minor_le_kernelCap_mul_sq_canon
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖corr_integral_minor X N B_canon Δ_canon‖ ≤ kernelCap * (Mminor_canon ^ 2) := by
  have hsub :
      ∀ {β α : ℝ}, α ∈ (majorArcSetTextbook X B_canon Δ_canon)ᶜ →
        ‖expSum X N ((α : UC) - (β : UC))‖ ≤ Mminor_canon := by
    intro β α hα
    exact (expSum_minor_bound_canon (X := X) (N := N) hX hN (β := β) (α := α) hα).1
  have hadd :
      ∀ {β α : ℝ}, α ∈ (majorArcSetTextbook X B_canon Δ_canon)ᶜ →
        ‖expSum X N ((α : UC) + (β : UC))‖ ≤ Mminor_canon := by
    intro β α hα
    exact (expSum_minor_bound_canon (X := X) (N := N) hX hN (β := β) (α := α) hα).2
  exact
    norm_corr_integral_minor_le_kernelCap_mul_sq_of_expSum_bound
      (X := X) (N := N) (B := B_canon) (Δ := Δ_canon) (M := Mminor_canon)
      (hM := Mminor_canon_nonneg) hsub hadd

end

end MajorArcStep25MinorArcCert
end Goldbach.Cert
