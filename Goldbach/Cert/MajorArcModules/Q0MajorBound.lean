import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction

/-!
`MajorArcModules/Q0MajorBound` is a small interface/hook for the *remaining* analytic task in the
turnkey/certificate route:

provide a uniform bound on the `Q0`-major-arc deviation

`‖corr_integral_major_Q0 X N Δ - corrModel N‖ ≤ ε₂`

on the canonical window.

This file intentionally contains **no** proof of such a bound; it just packages the statement in a
stable way so it can later be discharged either by:
- a proved theorem (from BMOR/Siegel–Walfisz + major-arc analysis), or
- a data-driven numeric certificate (after reduction to finitely many inequalities).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorBound

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.IntegralPipeline

noncomputable section

/-!
### Interface
-/

structure Q0MajorDeviationBound (Δ ε₂ : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral_major_Q0 X N Δ - corrModel N‖ ≤ ε₂

end

end Goldbach.Cert.MajorArcModules.Q0MajorBound
