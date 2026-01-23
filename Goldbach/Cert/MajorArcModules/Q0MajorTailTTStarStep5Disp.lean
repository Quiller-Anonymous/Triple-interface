import Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionEngine
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
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
open Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

noncomputable section

/-!
## Dispersion-ready Toeplitz top expression

`CAS` is the (conventional) alias-suppression constant for the balanced α-weight, used by the
future dispersion refinement.  In the current deterministic placeholder, it is unused.
-/

noncomputable def toeplitzExprTopDisp (X : ℕ) (Δ : ℝ) (_CAS : ℝ) : ℝ :=
  toeplitzExprTopTight X Δ

theorem sum_kSupport_sq_le_toeplitzExprTopDisp
    {X N : ℕ} (Δ : ℝ) (CAS : ℝ) (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (∑ k ∈ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport.kSupport N,
        ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
            (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤ toeplitzExprTopDisp X Δ CAS := by
  -- For now, `toeplitzExprTopDisp = toeplitzExprTopTight`.
  simpa [toeplitzExprTopDisp] using
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC.sum_kSupport_sq_le_toeplitzExprTopTight
      (X := X) (N := N) (Δ := Δ) hX hN

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5Disp

