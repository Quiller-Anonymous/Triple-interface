-- Twin/SW/DeepSW.lean
/-
DeepSW is an optional, out-of-core provider of class instances.
It SHOULD NOT hardwire any particular analytic proof; instead it packages
your deep inputs (zero-free region + explicit formula, etc.) and registers
the reusable instances that the rest of the project consumes.

How to use:
* Fill one of the structures below with your preferred deep result.
* Call the `.toSiegelWalfisz` or `.toSmoothedMajorArc` adapter to register an instance.
-/

import Twin.SW.SiegelWalfisz
import Twin.SW.Defs
import Twin.SW.PartialSummation
import Twin.MajorArc.SWUniform
import Mathlib.Analysis.SpecialFunctions.Log

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-! ## 1) Adapter for the classical (unsmoothed) Siegel–Walfisz statement

We keep this deliberately simple: if you can deliver a uniform ψ-bound with
some constant `C`, we package that as a `SiegelWalfisz A B` instance.
-/

/-- A packaged ψ-bound in the Siegel–Walfisz range (Λ-model), ready to be
registered as a `SiegelWalfisz A B` instance.  Provide this from your
zero-free region + explicit formula pipeline. -/
structure PsiTwistBound (A B : ℝ) : Prop :=
  (C  : ℝ)
  (bound :
    ∀ ⦃x : ℝ⦄, 3 ≤ x →
    ∀ ⦃q : ℕ⦄, 1 ≤ q ∧ (q : ℝ) ≤ (Real.log x)^B →
    ∀ (χ : DirichletCharacter q),
      Complex.abs (twistedPsi χ x)
        ≤ C * x / (Real.log x)^A)

/-- Turn a packaged ψ-bound into a `SiegelWalfisz` instance. -/
def PsiTwistBound.toSiegelWalfisz {A B : ℝ}
  (I : PsiTwistBound A B) : SiegelWalfisz A B :=
{ C := I.C, bound := I.bound }

/-! ## 2) Adapter for the smoothed major-arc Siegel–Walfisz statement

This collects *exactly* the bound your project uses:
with fixed `Λ, W, W_hat` and the major-arc neighborhood, the difference
between the smoothed exponential sum and the main term is
`≪ X / (log X)^A`.  Provide this from your Poisson/Fejér analysis
plus the control of non-principal characters.

This is intentionally project-agnostic: it fixes normalization (via `NewUniform`)
and only packages the result you can then re-export as a class instance.
-/

/-- A packaged *smoothed major-arc* SW bound for the fixed normalization
in `Twin.SW.Defs`.  Supply `C, δ, X0` and the bound; we can convert this into
both the canonical `SmoothMajorArcEstimate` record and the major-arc
`Twin.MajorArc.SiegelWalfisz` class instance. -/
structure SmoothedMajorArcBound
  (A B : ℝ) (Λ : ℕ → ℝ) (W W_hat : ℝ → ℝ) : Prop :=
  (C  : ℝ)
  (δ  : ℝ) (δ_pos : 0 < δ)
  (X0 : ℝ)
  (bound :
    ∀ {X H : ℝ}, X0 ≤ X → 1 ≤ H →
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ (Real.log X)^B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      Complex.abs
        (sumValue Λ W X H α - mainTerm W_hat X H α a q)
      ≤ C * (X / (Real.log X)^A))

/-- Turn a packaged smoothed major-arc bound into the canonical
`SmoothMajorArcEstimate` record in `Twin.SW.Defs`. -/
def SmoothedMajorArcBound.toSmoothMajorArcEstimate {A B : ℝ}
  {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (I : SmoothedMajorArcBound A B Λ W W_hat) :
  SmoothMajorArcEstimate A B Λ W W_hat :=
{ δ    := I.δ
, δ_pos:= I.δ_pos
, X0   := I.X0
, C    := I.C
, bound := by
    intro X H hX hH q a hq hqlog hcop α harc
    simpa using I.bound (X:=X) (H:=H) hX hH (q:=q) (a:=a) hq hqlog hcop (α:=α) harc }

/-- Turn a packaged smoothed major-arc bound into the major-arc
`Twin.MajorArc.SiegelWalfisz` class instance used by the pinning engine. -/
def SmoothedMajorArcBound.toMajorArcSiegelWalfisz {A B : ℝ}
  {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (I : SmoothedMajorArcBound A B Λ W W_hat) :
  Twin.MajorArc.SiegelWalfisz A B Λ W W_hat :=
{ δ    := I.δ
, δ_pos:= I.δ_pos
, X0   := I.X0
, C    := I.C
, bound := by
    intro X H hX hH q a hq hqlog hcop α harc
    simpa using I.bound (X:=X) (H:=H) hX hH (q:=q) (a:=a) hq hqlog hcop (α:=α) harc }

end Twin.SW
