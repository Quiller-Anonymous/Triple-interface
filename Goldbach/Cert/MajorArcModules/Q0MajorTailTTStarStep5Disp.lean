import Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionEngine
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
import Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

/-!
Step 5 (ε₂-large TT*/Toeplitz): dispersion-ready wrapper.

This file is a *staging* layer for successive approximation.

Today we already have a fully deterministic bound
`sum_kSupport_sq ≤ toeplitzExprTopTight` (Step 5a–5c in `Q0MajorTailTTStarStep5ABC.lean`), and a
numeric certificate artifact providing `U ≤ M2^2`.

The next tightening step (“Step 5d”) is to introduce a **dispersion refinement** that suppresses
`q ≠ q'` cross terms *after squaring/averaging*, before absolute values, using conventional
Ramanujan orthogonality/dispersion.

To keep downstream plumbing stable, we provide a `toeplitzExprTopDisp` *name* and a corresponding
lemma, while keeping the current definition equal to `toeplitzExprTopTight`.

Future work: redefine `toeplitzExprTopDisp` using the dispersion axiom/interface and keep the
lemma statement unchanged.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5Disp

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionEngine
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

noncomputable section

/-!
## Dispersion-ready Toeplitz top expression (scaffold)

This file is intentionally *scaffold-only*: it isolates the exact place where a project-neutral
Ramanujan dispersion / large-sieve-on-arcs lemma must enter to improve the Step-5 TT*/Toeplitz
upper bound.

The key point is that `sum_kSupport_sq ≤ toeplitzExprTopTight` is already proved deterministically.
The remaining “dispersion” work is to replace the kernel-mass terms
`kernelMassNZEven/kernelMassNZOdd` by better upper bounds, *before* multiplying by the coefficient
masses.

We therefore package the missing ingredient as a clean interface `Step5KernelMassDispersionUpper`.
Once an instance is supplied (either by a proof, or by a checker/certificate that is later proved
sound), this file gives a one-line bridge to a full TT* bound.
-/

/-!
### Missing ingredient interface (project-neutral analytic input)

The intent is that a “dispersion” lemma proves these bounds from conventional tools (Ramanujan
orthogonality, large sieve on arcs, alias suppression, …), yielding constants that scale like
`O(1/X)` rather than `O(Q0^2/X)` in the relevant regimes.
-/

structure Step5KernelMassDispersionUpper (Δ : ℝ) (BW_even BW_odd : ℝ) : Prop where
  even : ∀ {X : ℕ}, X0 ≤ X → kernelMassNZEven X Δ (X + H) ≤ BW_even
  odd : ∀ {X : ℕ}, X0 ≤ X → kernelMassNZOdd X Δ (X + H) ≤ BW_odd

/-!
### The dispersion-refined Toeplitz top expression

This is the same Toeplitz top expression as `toeplitzExprTopTight`, but with the nonzero kernel
masses replaced by the abstract dispersion bounds `BW_even/BW_odd`.
-/

noncomputable def toeplitzExprTopDisp (X : ℕ) (Δ : ℝ) (BW_even BW_odd : ℝ) : ℝ :=
  ((1 + 1 / δ_split) * BW_even) * (coeffMass X (X + H)) ^ 2
    +
  (2 * (1 + 1 / δ_split) * BW_odd) * (aTerm2Mass X) * (coeffMass X (X + H))
    +
  ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2)
    * diagBoundTight X (X + H)

theorem toeplitzExprTopTight_le_toeplitzExprTopDisp
    {X : ℕ} {Δ BW_even BW_odd : ℝ} (hX : X0 ≤ X)
    (hdisp : Step5KernelMassDispersionUpper Δ BW_even BW_odd) :
    toeplitzExprTopTight X Δ ≤ toeplitzExprTopDisp X Δ BW_even BW_odd := by
  classical
  unfold toeplitzExprTopTight toeplitzExprTopDisp
  have hδ1 : 0 ≤ (1 + 1 / δ_split : ℝ) := by
    have : 0 ≤ (1 / δ_split : ℝ) := le_of_lt (one_div_pos.mpr δ_split_pos)
    nlinarith
  have hδ1' : 0 ≤ (2 * (1 + 1 / δ_split) : ℝ) := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg this hδ1
  have hcoeffsq : 0 ≤ (coeffMass X (X + H)) ^ 2 := sq_nonneg _
  have hcoeff : 0 ≤ coeffMass X (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha2 : 0 ≤ aTerm2Mass X := aTerm2Mass_nonneg X
  have hdiag : 0 ≤ diagBoundTight X (X + H) := by
    unfold diagBoundTight
    have : 0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := sq_nonneg _
    exact mul_nonneg this hcoeff
  refine add_le_add (add_le_add ?_ ?_) le_rfl
  · -- even term
    have hEven :
        (1 + 1 / δ_split) * kernelMassNZEven X Δ (X + H)
          ≤ (1 + 1 / δ_split) * BW_even :=
      mul_le_mul_of_nonneg_left (hdisp.even hX) hδ1
    exact mul_le_mul_of_nonneg_right hEven hcoeffsq
  · -- odd term
    have hOdd :
        2 * (1 + 1 / δ_split) * kernelMassNZOdd X Δ (X + H)
          ≤ 2 * (1 + 1 / δ_split) * BW_odd :=
      mul_le_mul_of_nonneg_left (hdisp.odd hX) hδ1'
    have hOdd' :
        (2 * (1 + 1 / δ_split) * kernelMassNZOdd X Δ (X + H)) * aTerm2Mass X
          ≤ (2 * (1 + 1 / δ_split) * BW_odd) * aTerm2Mass X :=
      mul_le_mul_of_nonneg_right hOdd ha2
    have :
        (2 * (1 + 1 / δ_split) * kernelMassNZOdd X Δ (X + H)) * aTerm2Mass X *
              coeffMass X (X + H)
          ≤
        (2 * (1 + 1 / δ_split) * BW_odd) * aTerm2Mass X *
              coeffMass X (X + H) :=
      mul_le_mul_of_nonneg_right hOdd' hcoeff
    simpa [mul_assoc] using this

theorem sum_kSupport_sq_le_toeplitzExprTopDisp
    {X N : ℕ} {Δ BW_even BW_odd : ℝ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hdisp : Step5KernelMassDispersionUpper Δ BW_even BW_odd) :
    (∑ k ∈ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport.kSupport N,
        ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
            (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤ toeplitzExprTopDisp X Δ BW_even BW_odd := by
  have htoe :
      (∑ k ∈ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport.kSupport N,
          ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
              (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤ toeplitzExprTopTight X Δ :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC.sum_kSupport_sq_le_toeplitzExprTopTight
      (X := X) (N := N) (Δ := Δ) hX hN
  exact le_trans htoe (toeplitzExprTopTight_le_toeplitzExprTopDisp (X := X) (Δ := Δ) (BW_even := BW_even)
    (BW_odd := BW_odd) hX hdisp)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5Disp
