import Goldbach.Cert.MajorArcModules.Q0MajorBound
import Goldbach.Cert.MajorArcModules.Q0MajorBoundFromSplit

/-!
`MajorArcModules/Q0MajorRoute` packages Step 4 of the turnkey `Q0` route.

The `Q0` reduction asks for a uniform bound

`‖corr_integral_major_Q0 X N Δ - corrModel N‖ ≤ ε₂`

on the canonical window.  The existing module `Q0MajorBoundFromSplit` already provides the
bookkeeping lemma reducing this to:

- interval integrability of the β-integrand on `[-1/2, 1/2]`,
- a bound on the “small β” piece `corr_integral_major_Q0_small - corrModel`, and
- a bound on the “large β” tail `corr_integral_major_Q0_large`.

This file just repackages those three inputs as named interfaces, and provides the one-line
combination lemma producing `Q0MajorDeviationBound`.

No analytic number theory is proved here.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorRoute

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.Q0MajorBound
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.Q0MajorBoundFromSplit

noncomputable section

set_option maxRecDepth 2048

-- Match the ambient circle type used throughout the major-arc pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-- Interface: β-integrand is interval-integrable on `[-1/2, 1/2]`. -/
structure Q0MajorIntegrable (Δ : ℝ) : Prop where
  integrable :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
          volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)

/-- Interface: small-β deviation bound. -/
structure Q0MajorSmallBound (Δ εs : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral_major_Q0_small X N Δ - corrModel N‖ ≤ εs

/-- Interface: large-β tail bound. -/
structure Q0MajorLargeBound (Δ εl : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl

/--
Combine the three Step-4 inputs into the `Q0` major deviation bound
`‖corr_integral_major_Q0 - corrModel‖ ≤ ε₂`.
-/
theorem q0MajorDeviationBound_of_components
    {Δ εs εl : ℝ}
    (hInt : Q0MajorIntegrable Δ)
    (hSmall : Q0MajorSmallBound Δ εs)
    (hLarge : Q0MajorLargeBound Δ εl) :
    Q0MajorDeviationBound Δ (εs + εl) := by
  refine
    q0MajorDeviationBound_of_small_large
      (Δ := Δ) (εs := εs) (εl := εl)
      (hInt := ?_) (hSmall := ?_) (hLarge := ?_)
  · intro X N hX hN
    exact hInt.integrable hX hN
  · intro X N hX hN
    exact hSmall.bound hX hN
  · intro X N hX hN
    exact hLarge.bound hX hN

end

end Goldbach.Cert.MajorArcModules.Q0MajorRoute
