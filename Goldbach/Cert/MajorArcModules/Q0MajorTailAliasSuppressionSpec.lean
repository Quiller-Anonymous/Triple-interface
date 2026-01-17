import Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight
import Goldbach.Cert.MajorArcStep7FourierOrthogonality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Option-3 preparation: a Lean-facing interface for the “hybrid large sieve + alias suppression”
payload used to control the ε₂ large-β tail.

This module does **not** try to prove the analytic lemma; it records the intended statement
in a form that can be assumed (axiomatically) or discharged later by a certificate/checker.

The deterministic pieces (explicit detector windows dominating hard arcs, mean-zero decomposition,
remainder bounds) live in:

- `Q0MajorTailWindows.lean`
- `Q0MajorTailSmoothWeight.lean`
- `Q0MajorTailMeanZero.lean`
- `Q0MajorTailRemainderBound.lean`

The remaining analytic work is a constant-tracked inequality controlling integrals of `|S|^2`
against a balanced major-arc weight (alias suppression removes the barrier term).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionSpec

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight
open Goldbach.Cert.MajorArcStep7FourierOrthogonality

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

noncomputable def coeffRange (X : ℕ) : Finset ℕ :=
  Finset.Icc (1 : ℕ) X

noncomputable def trigSum (X : ℕ) (coeff : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ coeffRange X, coeff n * (fourier (T := (1 : ℝ)) (n : ℤ) (θ : UC) : ℂ)

noncomputable def trigSumShift (X : ℕ) (coeff : ℕ → ℂ) (β : ℝ) : ℝ → ℂ :=
  fun α => trigSum X coeff (α + β)

noncomputable def majorArcConstModeSmooth (X : ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightSmooth X α

noncomputable def majorArcWeightSmoothBalanced (X : ℕ) : ℝ → ℝ :=
  fun α => majorArcWeightSmooth X α - majorArcConstModeSmooth X

/-!
## Interface: alias-suppressed hybrid large sieve on arcs

This is the “mathematician payload” we need to close the option-3 ε₂-large tail:
an explicit bound on integrals of `|S|^2` against the *balanced* major-arc weight.

The intended use is:
- instantiate this interface with a constant `C_AS`,
- combine with TT*/Parseval-in-β bookkeeping to get a `Q0InnerMajorLargeBetaTTStarBound`,
- then discharge the tail via `Q0MajorTailSpec.largeBound_of_innerMajorQ0_energy`.
-/

structure Q0AliasSuppressedHybridLargeSieve (C_AS : ℝ) : Prop where
  nonneg : 0 ≤ C_AS
  bound :
    ∀ {X : ℕ},
      X0 ≤ X →
        ∀ (coeff : ℕ → ℂ) (β : ℝ),
          |∫ α in (0 : ℝ)..(1 : ℝ),
              majorArcWeightSmoothBalanced X α * ‖trigSumShift X coeff β α‖ ^ 2|
            ≤
          C_AS * (X : ℝ) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionSpec
